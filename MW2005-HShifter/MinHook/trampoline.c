/*
 *  MinHook - The Minimalistic API Hooking Library for x64/x86
 *  Copyright (C) 2009-2017 Tsuda Kageyu.
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *   1. Redistributions of source code must retain the above copyright
 *      notice, this list of conditions and the following disclaimer.
 *   2. Redistributions in binary form must reproduce the above copyright
 *      notice, this list of conditions and the following disclaimer in the
 *      documentation and/or other materials provided with the distribution.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 *  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 *  PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER
 *  OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 *  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 *  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 *  PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 *  LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 *  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 *  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


#include <windows.h>

#if defined(_MSC_VER) && !defined(MINHOOK_DISABLE_INTRINSICS)
    #define ALLOW_INTRINSICS
    #include <intrin.h>
#endif

#ifndef ARRAYSIZE
    #define ARRAYSIZE(A) (sizeof(A)/sizeof((A)[0]))
#endif

#if defined(_M_X64) || defined(__x86_64__)
    #include "./hde/hde64.h"
    typedef hde64s HDE;
    #define HDE_DISASM(code, hs) hde64_disasm(code, hs)
#else
    #include "./hde/hde32.h" // imports functioning decoder
    typedef hde32s HDE;
    #define HDE_DISASM(code, hs) hde32_disasm(code, hs)
#endif

#include "trampoline.h"
#include "buffer.h"

// Maximum size of a trampoline function.
#if defined(_M_X64) || defined(__x86_64__)
    #define TRAMPOLINE_MAX_SIZE (MEMORY_SLOT_SIZE - sizeof(JMP_ABS))
#else
    #define TRAMPOLINE_MAX_SIZE MEMORY_SLOT_SIZE
#endif


static BOOL IsCodePadding(LPBYTE pInst, UINT size) 
{
    UINT i;

    if (pInst[0] != 0x00 && pInst[0] != 0x90 && pInst[0] != 0xCC) // accepts only zero-fill, NOP, or INT3 as the first padding byte.
        return FALSE;

    for (i = 1; i < size; ++i)
    {
        if (pInst[i] != pInst[0])
            return FALSE;
    }
    return TRUE;
}

BOOL CreateTrampolineFunction(PTRAMPOLINE ct)
{
#if defined(_M_X64) || defined(__x86_64__)
    CALL_ABS call = { // creates a mutable x64 absolute-call template on the stack.
        0xFF, 0x15, 0x00000002, // FF15 00000002: CALL [RIP+8]
        0xEB, 0x08,             // EB 08:         JMP +10
        0x0000000000000000ULL   // Absolute destination address
    };
    JMP_ABS jmp = { // creates a mutable x64 absolute-jump template.
        0xFF, 0x25, 0x00000000, // FF25 00000000: JMP [RIP+6]
        0x0000000000000000ULL   // Absolute destination address
    };
    JCC_ABS jcc = { // creates a mutable x64 conditional-absolute-jump template.
        0x70, 0x0E,             // 7* 0E:         J** +16
        0xFF, 0x25, 0x00000000, // FF25 00000000: JMP [RIP+6]
        0x0000000000000000ULL   // Absolute destination address
    };
#else
    CALL_REL call = { // creates the active Win32 relative-call template.
        0xE8,                   // E8 xxxxxxxx: CALL +5+xxxxxxxx
        0x00000000              // Relative destination address
    };
    JMP_REL jmp = { // creates the active Win32 relative-jump template.
        0xE9,                   // E9 xxxxxxxx: JMP +5+xxxxxxxx
        0x00000000              // Relative destination address
    };
    JCC_REL jcc = { // creates the active Win32 near-conditional-jump template.
        0x0F, 0x80,             // 0F8* xxxxxxxx: J** +6+xxxxxxxx
        0x00000000              // Relative destination address
    };
#endif

    /**
    * oldPos counts bytes consumed from the target function.
    * newPos counts bytes emitted into the trampoline.
    *
    * They can differ because a short branch may be expanded into a longer form.
    *
    * jmpDest tracks the furthest destination of a branch that stays inside the
    * first five target bytes. MinHook must continue copying through that point.
    */
    UINT8     oldPos   = 0; // starts at the first byte of the target.
    UINT8     newPos   = 0; // starts at the first byte of the trampoline slot.
    ULONG_PTR jmpDest  = 0;     // Destination address of an internal jump.
    BOOL      finished = FALSE; // Is the function completed?
#if defined(_M_X64) || defined(__x86_64__)
    UINT8     instBuf[16]; // provides temporary editable instruction storage for x64 RIP-relative relocation.
#endif

/* Reset the output-only fields before beginning generation. */
    ct->patchAbove = FALSE; // assumes the normal entry-patch strategy until proven otherwise.
    ct->nIP        = 0; // clears the output instruction-boundary count.

    /**
    * Process one original instruction per iteration. The loop finishes only after
    * a return, an external unconditional jump, an x64 indirect jump, or an
    * appended jump back to the untouched target code completes the trampoline.
    */
    do
    {
        HDE       hs; // allocates one decoder result for the current original instruction.
        UINT      copySize; // will hold the number of bytes emitted this iteration.
        LPVOID    pCopySrc; // will point to original bytes or a rewritten local template.
        ULONG_PTR pOldInst = (ULONG_PTR)ct->pTarget     + oldPos; // addresses the next unconsumed target instruction.
        ULONG_PTR pNewInst = (ULONG_PTR)ct->pTrampoline + newPos; // addresses the next free trampoline byte.

        /**
        * Decode one complete target instruction. In the Win32 game build this
        * expands to hde32_disasm(). Any HDE error makes the target unsupported rather
        * than risking a malformed trampoline.
        */
        copySize = HDE_DISASM((LPVOID)pOldInst, &hs); // decodes the current target instruction and returns its original length.
        if (hs.flags & F_ERROR) // checks HDE's summary error flag.
            return FALSE; // rejects undecodable or invalid target code.

        pCopySrc = (LPVOID)pOldInst; // defaults to copying the original instruction unchanged.
        if (oldPos >= sizeof(JMP_REL))
        {
            // The trampoline function is long enough.
            // Complete the function with the jump to the target function.
#if defined(_M_X64) || defined(__x86_64__)
            jmp.address = pOldInst; // sets the x64 absolute jump-back destination.
#else
            jmp.operand = (UINT32)(pOldInst - (pNewInst + sizeof(jmp))); // calculates the Win32 rel32 jump-back displacement.
#endif
            pCopySrc = &jmp; // selects the generated jump template as this iteration's source.
            copySize = sizeof(jmp); // emits the jump template's full encoded size.

            finished = TRUE; // marks the trampoline complete after the jump-back is emitted.
        }
#if defined(_M_X64) || defined(__x86_64__)
        else if ((hs.modrm & 0xC7) == 0x05)
        {
            // Instructions using RIP relative addressing. (ModR/M = 00???101B)

            // Modify the RIP relative address.
            PUINT32 pRelAddr;

            // Avoid using memcpy to reduce the footprint.
#ifndef ALLOW_INTRINSICS
            memcpy(instBuf, (LPBYTE)pOldInst, copySize);
#else
            __movsb(instBuf, (LPBYTE)pOldInst, copySize);
#endif
            pCopySrc = instBuf;

            // Relative address is stored at (instruction length - immediate value length - 4).
            pRelAddr = (PUINT32)(instBuf + hs.len - ((hs.flags & 0x3C) >> 2) - 4);
            *pRelAddr
                = (UINT32)((pOldInst + hs.len + (INT32)hs.disp.disp32) - (pNewInst + hs.len));

            // Complete the function if JMP (FF /4).
            if (hs.opcode == 0xFF && hs.modrm_reg == 4)
                finished = TRUE;
        }
#endif
        else if (hs.opcode == 0xE8)
        {
            // Direct relative CALL
            ULONG_PTR dest = pOldInst + hs.len + (INT32)hs.imm.imm32;
#if defined(_M_X64) || defined(__x86_64__)
            call.address = dest;
#else
            call.operand = (UINT32)(dest - (pNewInst + sizeof(call)));
#endif
            pCopySrc = &call;
            copySize = sizeof(call);
        }
        else if ((hs.opcode & 0xFD) == 0xE9)
        {
            // Direct relative JMP (EB or E9)
            ULONG_PTR dest = pOldInst + hs.len;

            if (hs.opcode == 0xEB) // isShort jmp
                dest += (INT8)hs.imm.imm8;
            else
                dest += (INT32)hs.imm.imm32;

            // Simply copy an internal jump.
            if ((ULONG_PTR)ct->pTarget <= dest
                && dest < ((ULONG_PTR)ct->pTarget + sizeof(JMP_REL)))
            {
                if (jmpDest < dest)
                    jmpDest = dest;
            }
            else
            {
#if defined(_M_X64) || defined(__x86_64__)
                jmp.address = dest;
#else
                jmp.operand = (UINT32)(dest - (pNewInst + sizeof(jmp)));
#endif
                pCopySrc = &jmp;
                copySize = sizeof(jmp);

                // Exit the function if it is not in the branch.
                finished = (pOldInst >= jmpDest);
            }
        }
        else if ((hs.opcode & 0xF0) == 0x70
            || (hs.opcode & 0xFC) == 0xE0
            || (hs.opcode2 & 0xF0) == 0x80)
        {
            // Direct relative Jcc
            ULONG_PTR dest = pOldInst + hs.len;

            if ((hs.opcode & 0xF0) == 0x70      // Jcc
                || (hs.opcode & 0xFC) == 0xE0)  // LOOPNZ/LOOPZ/LOOP/JECXZ
                dest += (INT8)hs.imm.imm8;
            else
                dest += (INT32)hs.imm.imm32;

            // Simply copy an internal jump.
            if ((ULONG_PTR)ct->pTarget <= dest
                && dest < ((ULONG_PTR)ct->pTarget + sizeof(JMP_REL)))
            {
                if (jmpDest < dest)
                    jmpDest = dest;
            }
            else if ((hs.opcode & 0xFC) == 0xE0)
            {
                // LOOPNZ/LOOPZ/LOOP/JCXZ/JECXZ to the outside are not supported.
                return FALSE;
            }
            else
            {
                UINT8 cond = ((hs.opcode != 0x0F ? hs.opcode : hs.opcode2) & 0x0F);
#if defined(_M_X64) || defined(__x86_64__)
                // Invert the condition in x64 mode to simplify the conditional jump logic.
                jcc.opcode  = 0x71 ^ cond;
                jcc.address = dest;
#else
                jcc.opcode1 = 0x80 | cond;
                jcc.operand = (UINT32)(dest - (pNewInst + sizeof(jcc)));
#endif
                pCopySrc = &jcc;
                copySize = sizeof(jcc);
            }
        }
        else if ((hs.opcode & 0xFE) == 0xC2)
        {
            // RET (C2 or C3)

            // Complete the function if not in a branch.
            finished = (pOldInst >= jmpDest);
        }

        // Can't alter the instruction length in a branch.
        if (pOldInst < jmpDest && copySize != hs.len)
            return FALSE;

        // Trampoline function is too large.
        if ((newPos + copySize) > TRAMPOLINE_MAX_SIZE)
            return FALSE;

        // Trampoline function has too many instructions.
        if (ct->nIP >= ARRAYSIZE(ct->oldIPs))
            return FALSE;

        ct->oldIPs[ct->nIP] = oldPos;
        ct->newIPs[ct->nIP] = newPos;
        ct->nIP++;

        // Avoid using memcpy to reduce the footprint.
#ifndef ALLOW_INTRINSICS
        memcpy((LPBYTE)ct->pTrampoline + newPos, pCopySrc, copySize);
#else
        __movsb((LPBYTE)ct->pTrampoline + newPos, (LPBYTE)pCopySrc, copySize);
#endif
        newPos += copySize;
        oldPos += hs.len;
    } while (!finished);

    // Is there enough place for a long jump?
    if (oldPos < sizeof(JMP_REL)
        && !IsCodePadding((LPBYTE)ct->pTarget + oldPos, sizeof(JMP_REL) - oldPos))
    {
        // Is there enough place for a short jump?
        if (oldPos < sizeof(JMP_REL_SHORT)
            && !IsCodePadding((LPBYTE)ct->pTarget + oldPos, sizeof(JMP_REL_SHORT) - oldPos))
        {
            return FALSE;
        }

        // Can we place the long jump above the function?
        if (!IsExecutableAddress((LPBYTE)ct->pTarget - sizeof(JMP_REL)))
            return FALSE;

        if (!IsCodePadding((LPBYTE)ct->pTarget - sizeof(JMP_REL), sizeof(JMP_REL)))
            return FALSE;

        ct->patchAbove = TRUE;
    }

#if defined(_M_X64) || defined(__x86_64__)
    // Create a relay function.
    jmp.address = (ULONG_PTR)ct->pDetour;

    ct->pRelay = (LPBYTE)ct->pTrampoline + newPos;
    memcpy(ct->pRelay, &jmp, sizeof(jmp));
#endif

    return TRUE;
}
