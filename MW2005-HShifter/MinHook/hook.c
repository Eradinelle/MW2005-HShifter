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
#include <tlhelp32.h>
#include <limits.h>

#include "MinHook.h"
#include "buffer.h"
#include "trampoline.h"

#ifndef ARRAYSIZE
    #define ARRAYSIZE(A) (sizeof(A)/sizeof((A)[0]))
#endif

// Initial capacity of the HOOK_ENTRY buffer.
#define INITIAL_HOOK_CAPACITY   32

// Initial capacity of the thread IDs buffer.
#define INITIAL_THREAD_CAPACITY 128

// Special hook position values.
#define INVALID_HOOK_POS UINT_MAX
#define ALL_HOOKS_POS    UINT_MAX

// Freeze() action argument defines.
#define ACTION_DISABLE      0 // translate trampoline addresses back to original code before trampoline memory can be removed
#define ACTION_ENABLE       1 // translate original overwritten addresses into the trampoline before the detour patch is installed
#define ACTION_APPLY_QUEUED 2 // choose translation direction separately from each hook's queued state

// Thread access rights for suspending/resuming threads.
#define THREAD_ACCESS \
    (THREAD_SUSPEND_RESUME | THREAD_GET_CONTEXT | THREAD_QUERY_INFORMATION | THREAD_SET_CONTEXT)

// Hook information.
typedef struct _HOOK_ENTRY
{
    LPVOID pTarget;             // Address of the target function.
    LPVOID pDetour;             // Address of the detour or relay function.
    LPVOID pTrampoline;         // Address of the trampoline function.
    UINT8  backup[8];           // Original prologue of the target function.

    UINT8  patchAbove  : 1;     // Uses the hot patch area.
    UINT8  isEnabled   : 1;     // Enabled.
    UINT8  queueEnable : 1;     // Queued for enabling/disabling when != isEnabled.

    UINT   nIP : 4;             // Count of the instruction boundaries.
    UINT8  oldIPs[8];           // Instruction boundaries of the target function.
    UINT8  newIPs[8];           // Instruction boundaries of the trampoline function.
} HOOK_ENTRY, *PHOOK_ENTRY;

// Suspended threads for Freeze()/Unfreeze().
typedef struct _FROZEN_THREADS
{
    LPDWORD pItems;         // Data heap
    UINT    capacity;       // Size of allocated data heap, items
    UINT    size;           // Actual number of data items
} FROZEN_THREADS, *PFROZEN_THREADS;

//-------------------------------------------------------------------------
// Global Variables:
//-------------------------------------------------------------------------

// Spin lock flag for EnterSpinLock()/LeaveSpinLock().
static volatile LONG g_isLocked = FALSE;

// Private heap handle. If not NULL, this library is initialized.
static HANDLE g_hHeap = NULL;

// Hook entries.
static struct
{
    PHOOK_ENTRY pItems;     // Data heap
    UINT        capacity;   // Size of allocated data heap, items
    UINT        size;       // Actual number of data items
} g_hooks;

//-------------------------------------------------------------------------
static UINT FindHookEntry(LPVOID pTarget)
{
    UINT i;
    for (i = 0; i < g_hooks.size; ++i)
    {
        if ((ULONG_PTR)pTarget == (ULONG_PTR)g_hooks.pItems[i].pTarget)
            return i;
    }

    return INVALID_HOOK_POS;
}

//-------------------------------------------------------------------------
static PHOOK_ENTRY AddHookEntry()
{
    if (g_hooks.pItems == NULL) // checks whether the hook array has never been allocated
    {
        g_hooks.capacity = INITIAL_HOOK_CAPACITY; // establishes the first allocation's element capacity
        g_hooks.pItems = (PHOOK_ENTRY)HeapAlloc( // requests raw, uninitialized storage from MinHook's private heap
            g_hHeap, 0, g_hooks.capacity * sizeof(HOOK_ENTRY)); // allocates capacity multiplied by one record's byte size
        if (g_hooks.pItems == NULL) // detects ordinary allocation failure
            return NULL; // leaves size unchanged and reports failure to MH_CreateHook
    }
    else if (g_hooks.size >= g_hooks.capacity) // detects that every allocated record slot is occupied
    {
        PHOOK_ENTRY p = (PHOOK_ENTRY)HeapReAlloc( // attempts to resize while preserving existing hook records
            g_hHeap, 0, g_hooks.pItems, (g_hooks.capacity * 2) * sizeof(HOOK_ENTRY));
        if (p == NULL) // HeapReAlloc leaves the original block valid when it fails
            return NULL; // reports failure without losing existing hooks

        g_hooks.capacity *= 2; // records the successful doubled capacity
        g_hooks.pItems = p; // replaces the possibly moved allocation pointer
    }

    return &g_hooks.pItems[g_hooks.size++]; // returns the next free slot, then increases the active record count
}

//-------------------------------------------------------------------------

static VOID DeleteHookEntry(UINT pos)
{
    if (pos < g_hooks.size - 1) // checks whether the removed record is not already the final one
        g_hooks.pItems[pos] = g_hooks.pItems[g_hooks.size - 1]; // fills the gap by moving the last active hook record into it

    g_hooks.size--; // removes the former final slot from the active range

    if (g_hooks.capacity / 2 >= INITIAL_HOOK_CAPACITY && g_hooks.capacity / 2 >= g_hooks.size)
    // refuses to shrink below the original 32-record allocation
    // shrinks only when every active record still fits in half the space
    {
        PHOOK_ENTRY p = (PHOOK_ENTRY)HeapReAlloc( // requests a smaller block while preserving remaining records
            g_hHeap, 0, g_hooks.pItems, (g_hooks.capacity / 2) * sizeof(HOOK_ENTRY));
        if (p == NULL) // detects that optional shrinking failed
            return; // keeps the old valid allocation and completed logical deletion

        g_hooks.capacity /= 2; // records the smaller successful capacity
        g_hooks.pItems = p; // stores the resized allocation's address
    }
}

//-------------------------------------------------------------------------
static DWORD_PTR FindOldIP(PHOOK_ENTRY pHook, DWORD_PTR ip)
{
    UINT i; // instruction-boundary map index

    // checks whether this hook uses the hot-patch area before the function
    if (pHook->patchAbove && ip == ((DWORD_PTR)pHook->pTarget - sizeof(JMP_REL))) // detects a thread stopped at the five-byte patch-above jump
        return (DWORD_PTR)pHook->pTarget; // redirects it to the restored original function entry

    for (i = 0; i < pHook->nIP; ++i) // examines every original/trampoline boundary pair
    {
        if (ip == ((DWORD_PTR)pHook->pTrampoline + pHook->newIPs[i])) // tests whether the thread is at a recorded trampoline boundary
            return (DWORD_PTR)pHook->pTarget + pHook->oldIPs[i]; // returns the matching boundary in the original function
    }

#if defined(_M_X64) || defined(__x86_64__)
    // Check relay function.
    if (ip == (DWORD_PTR)pHook->pDetour) // detects a thread positioned at the x64 relay stub
        return (DWORD_PTR)pHook->pTarget; // sends it to the original entry before relay memory is freed
#endif

    return 0; // indicates that this hook does not require IP translation
}

//-------------------------------------------------------------------------
static DWORD_PTR FindNewIP(PHOOK_ENTRY pHook, DWORD_PTR ip)
{
    UINT i;
    for (i = 0; i < pHook->nIP; ++i) // examines every recorded original instruction boundary
    {
        if (ip == ((DWORD_PTR)pHook->pTarget + pHook->oldIPs[i])) // detects a thread at a soon-to-be-overwritten original boundary
            return (DWORD_PTR)pHook->pTrampoline + pHook->newIPs[i]; // returns the equivalent relocated trampoline boundary
    }

    return 0; // no translation is needed for this instruction pointer
}

//-------------------------------------------------------------------------
static VOID ProcessThreadIPs(HANDLE hThread, UINT pos, UINT action)
{
    // If the thread suspended in the overwritten area,
    // move IP to the proper address.

    CONTEXT c; // architecture-specific register snapshot supplied by Windows
#if defined(_M_X64) || defined(__x86_64__)
    DWORD64 *pIP = &c.Rip; // selects the 64-bit instruction-pointer member for x64 builds
#else
    DWORD   *pIP = &c.Eip; // selects the 32-bit instruction-pointer member used by NFSMW
#endif
    UINT count; // exclusive end position of the hook range to examine

    c.ContextFlags = CONTEXT_CONTROL; // requests control registers, including EIP/RIP and stack/control state
    if (!GetThreadContext(hThread, &c)) // obtains the register state of the suspended thread
        return; // abandons translation when Windows cannot provide the context

    if (pos == ALL_HOOKS_POS) // checks whether every created hook should be considered
    {
        pos = 0; // begins at the first hook record
        count = g_hooks.size; // ends after the active hook count
    }
    else
    {
        count = pos + 1; // configures a one-element range containing only the requested hook
    }

    for (; pos < count; ++pos) // processes either one hook or the complete hook array
    {
        PHOOK_ENTRY pHook = &g_hooks.pItems[pos]; // obtains the hook whose mapping may apply
        BOOL        enable; // desired patch state used for this translation decision
        DWORD_PTR   ip; // receives a translated address or zero

        switch (action) // converts the operation category into one desired state
        {
        case ACTION_DISABLE:
            enable = FALSE; // disabling before buffer removal requires trampoline-to-original translation
            break;

        case ACTION_ENABLE:
            enable = TRUE; // enabling requires original-to-trampoline translation
            break;

        default: // ACTION_APPLY_QUEUED
            enable = pHook->queueEnable; // queued batches choose the desired state from each hook record
            break;
        }
        if (pHook->isEnabled == enable) // skips hooks whose current state already equals the transition state
            continue;

        if (enable) // selects translation direction for a hook being enabled
            ip = FindNewIP(pHook, *pIP); // maps original overwritten boundaries into the trampoline
        else // selects translation for disabling/removing hook code
            ip = FindOldIP(pHook, *pIP); // maps trampoline/relay boundaries back into the original function

        if (ip != 0) // checks whether the current instruction pointer matched a recorded boundary
        {
            *pIP = ip; // places the translated address into the context structure
            SetThreadContext(hThread, &c); // asks Windows to resume this thread from the translated address
        }
    }
}

//-------------------------------------------------------------------------
static BOOL EnumerateThreads(PFROZEN_THREADS pThreads)
{
    BOOL succeeded = FALSE; // remains false unless snapshot traversal starts successfully

    HANDLE hSnapshot = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0); // creates a point-in-time list of system thread metadata
    if (hSnapshot != INVALID_HANDLE_VALUE) // confirms that Windows returned a usable snapshot handle
    {
        THREADENTRY32 te; // receives one thread entry at a time
        te.dwSize = sizeof(THREADENTRY32); // supplies the structure version/size required by Toolhelp APIs
        if (Thread32First(hSnapshot, &te)) // retrieves the first thread in the snapshot
        {
            succeeded = TRUE; // assumes success unless allocation or later enumeration fails
            do
            {
                if (te.dwSize >= (FIELD_OFFSET(THREADENTRY32, th32OwnerProcessID) + sizeof(DWORD)) // ensures the owner-PID field exists in this returned structure version
                    && te.th32OwnerProcessID == GetCurrentProcessId() // keeps only threads belonging to the current NFSMW process
                    && te.th32ThreadID != GetCurrentThreadId()) // excludes the MinHook caller so it does not suspend itself
                {
                    if (pThreads->pItems == NULL) // allocates the list only when the first eligible thread is found
                    {
                        pThreads->capacity = INITIAL_THREAD_CAPACITY; // reserves space for 128 thread IDs initially
                        pThreads->pItems
                            = (LPDWORD)HeapAlloc(g_hHeap, 0, pThreads->capacity * sizeof(DWORD));
                        if (pThreads->pItems == NULL) // detects private-heap allocation failure
                        {
                            succeeded = FALSE; // records that Freeze cannot safely continue
                            break; // exits snapshot traversal
                        }
                    }
                    else if (pThreads->size >= pThreads->capacity) // detects a full thread-ID array
                    {
                        LPDWORD p; // receives the resized allocation address
                        pThreads->capacity *= 2; // doubles capacity before attempting reallocation
                        p = (LPDWORD)HeapReAlloc( // preserves existing thread IDs while enlarging storage
                            g_hHeap, 0, pThreads->pItems, pThreads->capacity * sizeof(DWORD));
                        if (p == NULL) // detects resize failure
                        {
                            succeeded = FALSE; // marks enumeration as unusable
                            break; // stops adding thread IDs
                        }

                        pThreads->pItems = p; // stores the potentially moved allocation
                    }
                    pThreads->pItems[pThreads->size++] = te.th32ThreadID; // appends this current-process thread ID
                }

                te.dwSize = sizeof(THREADENTRY32); // resets size because Toolhelp APIs may modify it
            } while (Thread32Next(hSnapshot, &te)); // advances until no additional snapshot entry is available

            if (succeeded && GetLastError() != ERROR_NO_MORE_FILES) // distinguishes normal end-of-enumeration from an actual API failure
                succeeded = FALSE; // rejects an incomplete snapshot traversal

            if (!succeeded && pThreads->pItems != NULL) // releases a partially built list after any failure
            {
                HeapFree(g_hHeap, 0, pThreads->pItems); // returns temporary storage to MinHook's private heap
                pThreads->pItems = NULL; // prevents Freeze/Unfreeze from treating freed memory as a list
            }
        }
        CloseHandle(hSnapshot); // releases the Toolhelp snapshot kernel handle on every opened path
    }

    return succeeded; // reports whether a complete usable list was built
}

//-------------------------------------------------------------------------
static MH_STATUS Freeze(PFROZEN_THREADS pThreads, UINT pos, UINT action)
{
    MH_STATUS status = MH_OK; // assumes freezing can proceed

    pThreads->pItems   = NULL; // initializes the temporary dynamic array pointer
    pThreads->capacity = 0; // initializes allocated element capacity
    pThreads->size     = 0; // initializes active element count
    if (!EnumerateThreads(pThreads)) // snapshots other threads and builds the ID list
    {
        status = MH_ERROR_MEMORY_ALLOC; // uses a broad legacy error code for enumeration/allocation failure
    }
    else if (pThreads->pItems != NULL) // skips the loop when the process has no other threads
    {
        UINT i; // thread-list index
        for (i = 0; i < pThreads->size; ++i) // attempts to suspend every captured current-process thread
        {
            HANDLE hThread = OpenThread(THREAD_ACCESS, FALSE, pThreads->pItems[i]); // obtains the rights required for suspension and context editing
            BOOL suspended = FALSE; // tracks whether this exact entry may later be resumed
            if (hThread != NULL) // proceeds only when the thread still exists and access was granted
            {
                DWORD result = SuspendThread(hThread); // increments the target thread's suspend count
                if (result != 0xFFFFFFFF) // checks for SuspendThread's failure sentinel
                {
                    suspended = TRUE; // records that Unfreeze should resume this thread once
                    ProcessThreadIPs(hThread, pos, action); // translates EIP/RIP when the patch transition requires it
                }
                CloseHandle(hThread); // releases this temporary thread handle while the thread remains suspended
            }

            if (!suspended) // handles OpenThread or SuspendThread failure
            {
                // Mark thread as not suspended, so it's not resumed later on.
                pThreads->pItems[i] = 0; // preserves array shape while invalidating this resume entry
            }
        }
    }

    return status; // reports list-level success even if individual threads could not be suspended
}

//-------------------------------------------------------------------------
static VOID Unfreeze(PFROZEN_THREADS pThreads)
{
    if (pThreads->pItems != NULL) // checks whether a temporary thread list exists
    {
        UINT i;
        for (i = 0; i < pThreads->size; ++i) // examines every enumerated thread entry
        {
            DWORD threadId = pThreads->pItems[i]; // copies the ID so zero can be tested clearly
            if (threadId != 0) // skips entries Freeze could not suspend
            {
                HANDLE hThread = OpenThread(THREAD_ACCESS, FALSE, threadId); // reopens the suspended thread by ID
                if (hThread != NULL) // handles threads that may have terminated before this point
                {
                    ResumeThread(hThread); // decrements the suspend count added by Freeze()
                    CloseHandle(hThread); // releases the temporary resume handle
                }
            }
        }

        HeapFree(g_hHeap, 0, pThreads->pItems); // releases the temporary thread-ID allocation
    }
}

//-------------------------------------------------------------------------
static MH_STATUS EnableHookLL(UINT pos, BOOL enable)
{
    PHOOK_ENTRY pHook = &g_hooks.pItems[pos]; // obtains the permanent record for this target
    DWORD  oldProtect; // receives the page's original protection flags
    SIZE_T patchSize    = sizeof(JMP_REL); // normal patch overwrites one five-byte E9 rel32 instruction
    LPBYTE pPatchTarget = (LPBYTE)pHook->pTarget; // begins at the target function entry by default

    if (pHook->patchAbove) // checks whether trampoline construction selected the hot-patch strategy
    {
        pPatchTarget -= sizeof(JMP_REL); // moves five bytes before the function entry
        patchSize    += sizeof(JMP_REL_SHORT); // covers the five-byte jump plus the two-byte short jump at the entry
    }

    if (!VirtualProtect(pPatchTarget, patchSize, PAGE_EXECUTE_READWRITE, &oldProtect)) // temporarily permits code bytes to be written
        return MH_ERROR_MEMORY_PROTECT; // leaves the target unchanged when protection modification fails

    if (enable) // selects detour installation
    {
        PJMP_REL pJmp = (PJMP_REL)pPatchTarget; // interprets patch bytes as a packed five-byte relative-jump structure
        pJmp->opcode = 0xE9; // writes the x86 near-relative JMP opcode

        // calculates destination minus the address after this instruction
        // stores the low 32-bit two's-complement displacement bits
        pJmp->operand = (UINT32)((LPBYTE)pHook->pDetour - (pPatchTarget + sizeof(JMP_REL)));

        if (pHook->patchAbove)// completes the two-stage hot-patch layout when required
        {
            PJMP_REL_SHORT pShortJmp = (PJMP_REL_SHORT)pHook->pTarget; // views the original two-byte entry as a short-jump structure
            pShortJmp->opcode = 0xEB; // writes the short relative JMP opcode
            pShortJmp->operand = (UINT8)(0 - (sizeof(JMP_REL_SHORT) + sizeof(JMP_REL))); // computes a negative seven-byte displacement modulo 256
        }
    }
    else // selects hook disabling/restoration
    {
        if (pHook->patchAbove) // restores all seven bytes used by the patch-above form
            memcpy(pPatchTarget, pHook->backup, sizeof(JMP_REL) + sizeof(JMP_REL_SHORT));
        else // restores the normal five overwritten bytes
            memcpy(pPatchTarget, pHook->backup, sizeof(JMP_REL));
    }

    VirtualProtect(pPatchTarget, patchSize, oldProtect, &oldProtect); // attempts to restore the original page protection; this version ignores failure

    // Just-in-case measure.
    FlushInstructionCache(GetCurrentProcess(), pPatchTarget, patchSize); // invalidates stale decoded instructions after executable bytes changed

    pHook->isEnabled   = enable; // records the actual patch state expected after this operation
    pHook->queueEnable = enable; // synchronizes queued state with the now-applied state

    return MH_OK; // reports success after writing/restoring the patch
}

//-------------------------------------------------------------------------
static MH_STATUS EnableAllHooksLL(BOOL enable)
{
    MH_STATUS status = MH_OK; // assumes no state change will fail
    UINT i, first = INVALID_HOOK_POS; // tracks the first hook that differs from the requested state

    for (i = 0; i < g_hooks.size; ++i) // searches for work before performing expensive thread suspension
    {
        if (g_hooks.pItems[i].isEnabled != enable) // detects a hook whose actual state must change
        {
            first = i; // remembers where the update loop can begin
            break; // stops because at least one change is required
        }
    }

    if (first != INVALID_HOOK_POS) // skips thread suspension when every hook already matches
    {
        FROZEN_THREADS threads; // receives suspended current-process thread IDs

        // translates IPs across all changing hooks
        // chooses original-to-trampoline or trampoline-to-original direction
        status = Freeze(&threads, ALL_HOOKS_POS, enable ? ACTION_ENABLE : ACTION_DISABLE);
        if (status == MH_OK) // modifies code only after the thread list was created successfully
        {
            for (i = first; i < g_hooks.size; ++i) // examines remaining hooks from the first mismatch onward
            {
                if (g_hooks.pItems[i].isEnabled != enable) // skips hooks already in the requested state
                {
                    status = EnableHookLL(i, enable); // writes or restores this hook's patch bytes
                    if (status != MH_OK) // stops at the first memory-protection failure
                        break;
                }
            }

            Unfreeze(&threads); // resumes threads even when one hook update failed
        }
    }

    return status;
}

//-------------------------------------------------------------------------
static VOID EnterSpinLock(VOID)
{
    SIZE_T spinCount = 0; // counts failed acquisition attempts to choose a yielding strategy

    // Wait until the flag is FALSE.
    while (InterlockedCompareExchange(&g_isLocked, TRUE, FALSE) != FALSE) // atomically acquires only when the previous state was unlocked
    {
        // No need to generate a memory barrier here, since InterlockedCompareExchange()
        // generates a full memory barrier itself.

        // Prevent the loop from being too busy.
        if (spinCount < 32) // uses short scheduler yields during early contention
            Sleep(0); // yields the remaining time slice to an equal-priority ready thread
        else
            Sleep(1); // waits at least approximately one scheduler tick after prolonged contention

        spinCount++; // records another failed acquisition attempt
    }
}

//-------------------------------------------------------------------------
static VOID LeaveSpinLock(VOID)
{
    // No need to generate a memory barrier here, since InterlockedExchange()
    // generates a full memory barrier itself.

    InterlockedExchange(&g_isLocked, FALSE); // publishes prior protected writes and marks MinHook state unlocked
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_Initialize(VOID)
{
    MH_STATUS status = MH_OK; // assumes first-time initialization succeeds

    EnterSpinLock(); // serializes initialization against every other public MinHook operation

    if (g_hHeap == NULL) // treats a null private-heap handle as uninitialized state
    {
        g_hHeap = HeapCreate(0, 0, 0); // creates a growable private heap with system-selected initial size
        if (g_hHeap != NULL) // confirms that metadata allocations can now be served
        {
            // Initialize the internal function buffer.
            InitializeBuffer(); // resets buffer.c's executable-memory block list/state
        }
        else
        {
            status = MH_ERROR_MEMORY_ALLOC; // reports inability to create MinHook's allocator
        }
    }
    else
    {
        status = MH_ERROR_ALREADY_INITIALIZED; // enforces the API's exactly-once initialization contract
    }

    LeaveSpinLock(); // exposes the final initialized state to other callers

    return status;
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_Uninitialize(VOID)
{
    MH_STATUS status = MH_OK; // assumes cleanup can complete

    EnterSpinLock(); // prevents concurrent hook creation or patch-state changes

    if (g_hHeap != NULL) // confirms that MinHook currently owns initialized state
    {
        status = EnableAllHooksLL(FALSE); // restores original bytes and translates thread IPs before buffers are freed
        if (status == MH_OK) // destroys memory only after every active hook was safely disabled
        {
            // Free the internal function buffer.

            // HeapFree is actually not required, but some tools detect a false
            // memory leak without HeapFree.

            UninitializeBuffer(); // releases executable trampoline-memory blocks managed by buffer.c

            HeapFree(g_hHeap, 0, g_hooks.pItems); // releases the hook-record array; Windows permits NULL here
            HeapDestroy(g_hHeap); // destroys all remaining allocations belonging to the private heap

            g_hHeap = NULL; // publishes the uninitialized-state marker

            g_hooks.pItems   = NULL; // clears the now-invalid array pointer
            g_hooks.capacity = 0; // clears its former allocation capacity
            g_hooks.size     = 0; // clears the active hook count
        }
    }
    else
    {
        status = MH_ERROR_NOT_INITIALIZED; // reports an invalid cleanup call order
    }

    LeaveSpinLock(); // allows future initialization or status-reporting operations

    return status;
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_CreateHook(LPVOID pTarget, LPVOID pDetour, LPVOID *ppOriginal)
{
    MH_STATUS status = MH_OK; // assumes hook construction succeeds

    EnterSpinLock(); // protects heap, buffer list, and hook array from concurrent modification

    if (g_hHeap != NULL) // requires successful MH_Initialize first
    {
        if (IsExecutableAddress(pTarget) && IsExecutableAddress(pDetour)) // rejects null, uncommitted, or non-executable target/detour pages
        {
            UINT pos = FindHookEntry(pTarget); // checks whether this exact function was already hooked
            if (pos == INVALID_HOOK_POS) // proceeds only for a new target address
            {
                LPVOID pBuffer = AllocateBuffer(pTarget); // reserves nearby executable storage for the trampoline/relay
                if (pBuffer != NULL) // confirms that buffer.c found usable memory
                {
                    TRAMPOLINE ct; // temporary construction descriptor shared with trampoline.c

                    ct.pTarget     = pTarget; // supplies the original GetRawInputData entry
                    ct.pDetour     = pDetour; // supplies HookGetRawInputData
                    ct.pTrampoline = pBuffer; // supplies writable executable output storage
                    if (CreateTrampolineFunction(&ct)) // decodes, relocates, and emits a safe original-function trampoline
                    {
                        PHOOK_ENTRY pHook = AddHookEntry(); // reserves permanent metadata only after trampoline construction succeeds
                        if (pHook != NULL) // confirms hook-registry allocation success
                        {
                            pHook->pTarget     = ct.pTarget; // permanently records the function being intercepted
#if defined(_M_X64) || defined(__x86_64__)
                            pHook->pDetour     = ct.pRelay; // x64 target jump reaches a nearby relay that can then reach the detour
#else
                            pHook->pDetour     = ct.pDetour; // x86 target jump reaches HookGetRawInputData directly
#endif
                            pHook->pTrampoline = ct.pTrampoline; // stores the callable original-function path returned to main.c
                            pHook->patchAbove  = ct.patchAbove; // records whether patch bytes belong before the target entry
                            pHook->isEnabled   = FALSE; // creation leaves original code untouched
                            pHook->queueEnable = FALSE; // queued state initially agrees with disabled actual state
                            pHook->nIP         = ct.nIP; // stores the number of instruction-boundary mappings
                            memcpy(pHook->oldIPs, ct.oldIPs, ARRAYSIZE(ct.oldIPs)); // copies eight one-byte original offsets
                            memcpy(pHook->newIPs, ct.newIPs, ARRAYSIZE(ct.newIPs)); // copies eight one-byte trampoline offsets

                            // Back up the target function.

                            if (ct.patchAbove) // saves all bytes that a patch-above installation will modify
                            {
                                memcpy(
                                    pHook->backup,
                                    (LPBYTE)pTarget - sizeof(JMP_REL), // begins five bytes before the function
                                    sizeof(JMP_REL) + sizeof(JMP_REL_SHORT)); // copies five preceding bytes plus two entry bytes
                            }
                            else
                            {
                                memcpy(pHook->backup, pTarget, sizeof(JMP_REL)); // saves the normal five-byte target prologue
                            }

                            if (ppOriginal != NULL) // supports callers that want to invoke the original function
                                *ppOriginal = pHook->pTrampoline; // gives main.c the oGetRawInputData trampoline address
                        }
                        else
                        {
                            status = MH_ERROR_MEMORY_ALLOC; // reports inability to append permanent hook metadata
                        }
                    }
                    else
                    {
                        status = MH_ERROR_UNSUPPORTED_FUNCTION; // reports a target prologue trampoline.c cannot safely relocate
                    }

                    if (status != MH_OK) // cleans up a temporary buffer after any later construction failure
                    {
                        FreeBuffer(pBuffer); // returns the trampoline slot to buffer.c
                    }
                }
                else
                {
                    status = MH_ERROR_MEMORY_ALLOC;// reports inability to allocate suitable trampoline storage
                }
            }
            else
            {
                status = MH_ERROR_ALREADY_CREATED; // prevents duplicate records for the same target entry
            }
        }
        else
        {
            status = MH_ERROR_NOT_EXECUTABLE; // rejects invalid target or detour addresses before reading/writing them
        }
    }
    else
    {
        status = MH_ERROR_NOT_INITIALIZED;// enforces the required MH_Initialize call order
    }

    LeaveSpinLock(); // releases all MinHook global state

    return status; // reports creation result without enabling the patch
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_RemoveHook(LPVOID pTarget)
{
    MH_STATUS status = MH_OK; // assumes a valid removable hook exists

    EnterSpinLock(); // serializes lookup, code restoration, buffer release, and array deletion

    if (g_hHeap != NULL) // requires initialized MinHook state
    {
        UINT pos = FindHookEntry(pTarget); // locates the target's permanent hook record
        if (pos != INVALID_HOOK_POS) // proceeds only when a hook was previously created
        {
            if (g_hooks.pItems[pos].isEnabled) // restores target code before removing an active hook
            {
                FROZEN_THREADS threads; // receives other NFSMW thread IDs
                status = Freeze(&threads, pos, ACTION_DISABLE); // maps endangered trampoline IPs back into original code
                if (status == MH_OK) // writes restoration bytes only after thread-list setup succeeds
                {
                    status = EnableHookLL(pos, FALSE); // restores the saved five/seven original bytes

                    Unfreeze(&threads); 
                }
            }

            if (status == MH_OK) // frees metadata only when original code is no longer actively detoured
            {
                FreeBuffer(g_hooks.pItems[pos].pTrampoline); // releases this hook's executable trampoline slot
                DeleteHookEntry(pos); // removes the record from the dynamic hook array
            }
        }
        else
        {
            status = MH_ERROR_NOT_CREATED; // reports that the supplied target has no hook record
        }
    }
    else
    {
        status = MH_ERROR_NOT_INITIALIZED; // rejects removal before initialization
    }

    LeaveSpinLock(); // exposes the final hook registry state

    return status;
}

//-------------------------------------------------------------------------
static MH_STATUS EnableHook(LPVOID pTarget, BOOL enable)
{
    MH_STATUS status = MH_OK; // assumes the requested transition can be applied

    EnterSpinLock(); // serializes hook lookup and executable-code modification

    if (g_hHeap != NULL)
    {
        if (pTarget == MH_ALL_HOOKS) // recognizes the public NULL sentinel meaning every hook
        {
            status = EnableAllHooksLL(enable); // batches all state changes under one freeze/unfreeze interval
        }
        else
        {
            UINT pos = FindHookEntry(pTarget); // locates the exact target hook
            if (pos != INVALID_HOOK_POS) // proceeds only for a created hook
            {
                if (g_hooks.pItems[pos].isEnabled != enable) // avoids rewriting code when the requested state already exists
                {
                    FROZEN_THREADS threads; // receives other current-process thread IDs
                    status = Freeze(&threads, pos, ACTION_ENABLE); // translates only during enable; disable keeps allocated trampoline valid
                    if (status == MH_OK) // modifies code only after successful thread-list preparation
                    {
                        status = EnableHookLL(pos, enable); // installs or restores the five/seven patch bytes

                        Unfreeze(&threads);
                    }
                }
                else
                {
                    status = enable ? MH_ERROR_ENABLED : MH_ERROR_DISABLED; // reports redundant state request explicitly
                }
            }
            else
            {
                status = MH_ERROR_NOT_CREATED; // reports that no hook exists for this target address
            }
        }
    }
    else
    {
        status = MH_ERROR_NOT_INITIALIZED; // rejects enable/disable calls before MH_Initialize
    }

    LeaveSpinLock(); // publishes the final state and permits another API operation

    return status;
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_EnableHook(LPVOID pTarget)
{
    return EnableHook(pTarget, TRUE); // delegates to the shared state-transition implementation
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_DisableHook(LPVOID pTarget)
{
    return EnableHook(pTarget, FALSE); // restores target bytes but intentionally retains hook metadata/trampoline
}

//-------------------------------------------------------------------------
static MH_STATUS QueueHook(LPVOID pTarget, BOOL queueEnable)
{
    MH_STATUS status = MH_OK; // assumes queue update succeeds

    EnterSpinLock(); // protects hook records from concurrent changes

    if (g_hHeap != NULL)
    {
        if (pTarget == MH_ALL_HOOKS) // applies the desired state to every created hook
        {
            UINT i; // hook-array index
            for (i = 0; i < g_hooks.size; ++i) // updates all active records without patching code
                g_hooks.pItems[i].queueEnable = queueEnable;
        }
        else
        {
            UINT pos = FindHookEntry(pTarget); // locates one exact target record
            if (pos != INVALID_HOOK_POS) // proceeds only when that hook exists
            {
                g_hooks.pItems[pos].queueEnable = queueEnable; // records the desired future state
            }
            else
            {
                status = MH_ERROR_NOT_CREATED;
            }
        }
    }
    else
    {
        status = MH_ERROR_NOT_INITIALIZED;
    }

    LeaveSpinLock();

    return status;
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_QueueEnableHook(LPVOID pTarget)
{
    return QueueHook(pTarget, TRUE);
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_QueueDisableHook(LPVOID pTarget)
{
    return QueueHook(pTarget, FALSE);
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_ApplyQueued(VOID)
{
    MH_STATUS status = MH_OK;
    UINT i, first = INVALID_HOOK_POS;

    EnterSpinLock();

    if (g_hHeap != NULL)
    {
        for (i = 0; i < g_hooks.size; ++i)
        {
            if (g_hooks.pItems[i].isEnabled != g_hooks.pItems[i].queueEnable)
            {
                first = i;
                break;
            }
        }

        if (first != INVALID_HOOK_POS)
        {
            FROZEN_THREADS threads;
            status = Freeze(&threads, ALL_HOOKS_POS, ACTION_APPLY_QUEUED);
            if (status == MH_OK)
            {
                for (i = first; i < g_hooks.size; ++i)
                {
                    PHOOK_ENTRY pHook = &g_hooks.pItems[i];
                    if (pHook->isEnabled != pHook->queueEnable)
                    {
                        status = EnableHookLL(i, pHook->queueEnable);
                        if (status != MH_OK)
                            break;
                    }
                }

                Unfreeze(&threads);
            }
        }
    }
    else
    {
        status = MH_ERROR_NOT_INITIALIZED;
    }

    LeaveSpinLock();

    return status;
}

//-------------------------------------------------------------------------
MH_STATUS WINAPI MH_CreateHookApiEx(
    LPCWSTR pszModule, LPCSTR pszProcName, LPVOID pDetour,
    LPVOID *ppOriginal, LPVOID *ppTarget)
{
    HMODULE hModule; // receives the base handle of an already loaded module
    LPVOID  pTarget; // receives the resolved exported function address

    hModule = GetModuleHandleW(pszModule); // searches only the current process's loaded module list
    if (hModule == NULL) 
        return MH_ERROR_MODULE_NOT_FOUND;

    pTarget = (LPVOID)GetProcAddress(hModule, pszProcName); // searches that module's export table by name
    if (pTarget == NULL)
        return MH_ERROR_FUNCTION_NOT_FOUND;

    if (ppTarget != NULL) // supports callers that need the resolved address for later API calls
        *ppTarget = pTarget; // publishes the target before normal hook construction

    return MH_CreateHook(pTarget, pDetour, ppOriginal); // validates executable pages and creates the disabled hook/trampoline
}

//-------------------------------------------------------------------------
/** @brief convenience wrapper around MH_CreateHookApiEx without target output. */
MH_STATUS WINAPI MH_CreateHookApi(
    LPCWSTR pszModule, LPCSTR pszProcName, LPVOID pDetour, LPVOID *ppOriginal)
{
    return MH_CreateHookApiEx(pszModule, pszProcName, pDetour, ppOriginal, NULL); // delegates all resolution and creation work
}

//-------------------------------------------------------------------------
const char *WINAPI MH_StatusToString(MH_STATUS status)
{
#define MH_ST2STR(x)    \
    case x:             \
        return #x;

    switch (status) {
        MH_ST2STR(MH_UNKNOWN)
        MH_ST2STR(MH_OK)
        MH_ST2STR(MH_ERROR_ALREADY_INITIALIZED)
        MH_ST2STR(MH_ERROR_NOT_INITIALIZED)
        MH_ST2STR(MH_ERROR_ALREADY_CREATED)
        MH_ST2STR(MH_ERROR_NOT_CREATED)
        MH_ST2STR(MH_ERROR_ENABLED)
        MH_ST2STR(MH_ERROR_DISABLED)
        MH_ST2STR(MH_ERROR_NOT_EXECUTABLE)
        MH_ST2STR(MH_ERROR_UNSUPPORTED_FUNCTION)
        MH_ST2STR(MH_ERROR_MEMORY_ALLOC)
        MH_ST2STR(MH_ERROR_MEMORY_PROTECT)
        MH_ST2STR(MH_ERROR_MODULE_NOT_FOUND)
        MH_ST2STR(MH_ERROR_FUNCTION_NOT_FOUND)
    }

#undef MH_ST2STR

    return "(unknown)"; // handles out-of-range values not represented by the enum
}
