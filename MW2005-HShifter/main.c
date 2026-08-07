///
/// MIT License
/// 
/// Copyright (c) 2025 x0reaxeax
/// 
/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the "Software"), to deal
/// in the Software without restriction, including without limitation the rights
/// to use, copy, modify, merge, publish, distribute, sublicense, and /or sell
/// copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions :
/// 
/// The above copyright notice and this permission notice shall be included in all
/// copies or substantial portions of the Software.
/// 
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
/// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
/// SOFTWARE.
/// 
/// 
/// H-Shifter emulation for Need for Speed: Most Wanted (2005)
/// https://github.com/x0reaxeax/MW2005-HShifter

#include <Windows.h>

#include <stdio.h>
#include <stdint.h>

#include "MinHook/MinHook.h"

#if !defined(_M_IX86) && !defined(__i386__) // verifies that the mod is being compiled for 32 bit x86
#error MW2005-HShifter must be built for Win32/x86. // prevents an unusable x64 build with invalid pointer sizes and calling conventions
#endif

#define MWSHIFTER_VERSION_MAJOR 1
#define MWSHIFTER_VERSION_MINOR 0
#define MWSHIFTER_VERSION_PATCH 0


#define STATIC static
#define NAKED __declspec(naked)
#define NORETURN __declspec(noreturn)
#define GLOBAL
#define MAYBE_UNUSED


#define MW_FUNC_SHIFTGEAR 0x006920D0
#define MW_FUNC_SUB_404010 0x00404010
#define MW_OBJ_REGISTRY_CONTAINER 0x0092CD28

#ifdef __cplusplus

typedef bool (__thiscall *fn_ShiftGear)(
    PDWORD thisptr,
    int gear
);

#else

typedef BOOLEAN (*fn_ShiftGear)(
    PDWORD thisptr,
    int gear
);

#endif

typedef UINT(WINAPI* GetRawInputData_t)(
    HRAWINPUT hRawInput,
    UINT uiCommand,
    LPVOID pData,
    PUINT pcbSize,
    UINT cbSizeHeader
);

typedef enum _GEAR_SHIFT {
    GEAR_REVERSE = 0,
    GEAR_NEUTRAL = 1,
    GEAR_FIRST = 2,
    GEAR_SECOND = 3,
    GEAR_THIRD = 4,
    GEAR_FOURTH = 5,
    GEAR_FIFTH = 6,
    GEAR_SIXTH = 7,
    GEAR_SEVENTH = 8,
    GEAR_NOCHANGE = 0xFFFFFFFF
} GEAR_SHIFT, *PGEAR_SHIFT;

GLOBAL HANDLE g_hShifterThread = NULL;
GLOBAL MAYBE_UNUSED DWORD g_dwLastGear = 0;
GLOBAL GetRawInputData_t oGetRawInputData = NULL;

DWORD sub_404010 = MW_FUNC_SUB_404010;
fn_ShiftGear ShiftGear = (fn_ShiftGear) MW_FUNC_SHIFTGEAR;

DWORD CallShiftGear(
    DWORD dwTargetGear
);

/**
 * @brief updated raw-input hook with additional validation and safer gear-event handling.
 *
 * changes:
 * - verifies that GetRawInputData succeeded before reading the output buffer.
 * - ignores RID_HEADER/size-query calls and null data buffers.
 * - ignores non-keyboard raw-input events.
 * - processes only key-down events, preventing duplicate shifts on key release.
 * - makes gear mappings mutually exclusive with an else-if chain.
 * - limits forward-gear input to the six positions supported by this shifter setup.
 * - replaces the previous magic-number conversion with a clearer mapping based on
 *   GEAR_FIRST.
 * - treats the returned RAWINPUT/RAWKEYBOARD data as read-only.
 *
 * the original Windows raw-input result and buffer contents are still preserved
 * and returned unchanged to the game.
 */
UINT WINAPI HookGetRawInputData(
    HRAWINPUT hRawInput,
    UINT uiCommand,
    LPVOID pData,
    PUINT pcbSize,
    UINT cbSizeHeader
) {
    UINT ret = oGetRawInputData(
        hRawInput,
        uiCommand,
        pData,
        pcbSize,
        cbSizeHeader
    );

    if (ret == (UINT)-1) {
        return ret;
    }

    if (uiCommand != RID_INPUT || pData == NULL) {
        return ret;
    }

    const RAWINPUT *pRaw = (const RAWINPUT *)pData;

    if (pRaw->header.dwType != RIM_TYPEKEYBOARD) {
        return ret;
    }

    const RAWKEYBOARD *keyboard = &pRaw->data.keyboard;

    if (keyboard->Flags & RI_KEY_BREAK) {
        return ret;
    }

    USHORT vkCode = keyboard->VKey;

    if (vkCode == 'N') {
        CallShiftGear(GEAR_NEUTRAL);
    } else if (vkCode == '0') {
        CallShiftGear(GEAR_REVERSE);
    } else if (vkCode >= '1' && vkCode <= '6') {
        CallShiftGear(
            (DWORD)(vkCode - '1') + (DWORD)GEAR_FIRST
        );
    }

    return ret;
}

/**
 * @brief centralized minhook error-reporting helper.
 *
 * change:
 * - reports the actual MH_STATUS value returned by MinHook instead of relying
 *   on GetLastError(), which is not the correct error source for MinHook APIs.
 * - uses MH_StatusToString() to provide a readable symbolic error description.
 * - also prints the numeric MH_STATUS value for easier debugging and comparison.
 * - removes duplicated MinHook error-formatting code from the hook installer.
 *
 * for diagnostics only.
 */
static VOID ReportMinHookError(
    const char *operation,
    MH_STATUS status
) {
    fprintf(
        stderr,
        "%s(): %s (%d)\n",
        operation,
        MH_StatusToString(status),
        (int)status
    );
}

/**
 * @brief installs the GetRawInputData detour with improved error handling and
 * cleanup of partially initialized MinHook state.
 *
 * changes:
 * - preserves the exact MH_STATUS returned by each MinHook operation.
 * - reports MinHook failures through ReportMinHookError() instead of incorrectly
 *   using GetLastError().
 * - continues to use GetLastError() only for Windows APIs where it is applicable,
 *   such as GetModuleHandleA() and GetProcAddress().
 * - explicitly uninitializes MinHook if setup fails after MH_Initialize().
 * - removes the created hook if MH_EnableHook() fails, preventing an unused
 *   trampoline and hook record from remaining allocated.
 * - clears oGetRawInputData whenever hook creation or activation fails so later
 *   code cannot accidentally call an invalid trampoline pointer.
 * - separates hook creation from hook activation more clearly while preserving
 *   the original successful runtime behavior.
 *
 * on success, the function still produces the same intended result:
 * user32!GetRawInputData is redirected to HookGetRawInputData, while
 * oGetRawInputData points to MinHook's callable trampoline for the original
 * Windows function.
 */
BOOLEAN InstallRawInputHook(VOID)
{
    MH_STATUS mhStatus = MH_Initialize();

    if (mhStatus != MH_OK) { // requires a fresh successful initialization exactly once
        ReportMinHookError( // reports the actual minhook result
            "MH_Initialize", // identifies the failed operation
            mhStatus // supplies the returned status
        );

        return FALSE;
    }

    HMODULE hUser32 = GetModuleHandleA( // obtains the handle of user32 already loaded in the game process
        "user32.dll" // identifies the module that exports getrawinputdata
    );

    if (hUser32 == NULL) { // detects failure to locate user32
        fprintf( // reports the windows-api error
            stderr,
            "GetModuleHandleA(): Windows error %lu\n", // labels the relevant windows error code
            GetLastError()
        );

        (VOID)MH_Uninitialize(); // releases the minhook instance initialized above
        return FALSE; // stops because the target module is unavailable
    }

    LPVOID pTarget = (LPVOID)GetProcAddress( // resolves the runtime address of getrawinputdata
        hUser32, // searches user32's exported functions
        "GetRawInputData" // requests the target function by name
    ); // stores the target function address

    if (pTarget == NULL) { // detects failure to resolve the export
        fprintf(
            stderr,
            "GetProcAddress(): Windows error %lu\n",
            GetLastError()
        );

        (VOID)MH_Uninitialize();
        return FALSE;
    }

    mhStatus = MH_CreateHook( // creates the disabled hook and its original-function trampoline
        pTarget, // identifies user32!getrawinputdata as the target
        (LPVOID)HookGetRawInputData, // identifies the mod's detour function
        (LPVOID *)&oGetRawInputData // receives the callable original-function trampoline
    );

    if (mhStatus != MH_OK) {
        ReportMinHookError(
            "MH_CreateHook",
            mhStatus
        );

        oGetRawInputData = NULL; // prevents accidental use of an invalid trampoline pointer
        (VOID)MH_Uninitialize(); // releases minhook because no active hook was created
        return FALSE;
    }

    mhStatus = MH_EnableHook( // activates the newly created getrawinputdata hook
        pTarget // identifies the hook that should be enabled
    );

    if (mhStatus != MH_OK) {
        ReportMinHookError(
            "MH_EnableHook",
            mhStatus
        );

        (VOID)MH_RemoveHook(pTarget);
        oGetRawInputData = NULL;
        (VOID)MH_Uninitialize();
        return FALSE;
    }

    return TRUE; // reports that the raw-input hook is active
}

DWORD *__cdecl sub_5D49F0( // defines a helper corresponding to game code originally identified at address 0x005d49f0
    DWORD *a1, // receives the address of a variable where the resulting record pointer will be written
    int a2, // receives the numeric start address of the sorted record array
    int a3, // receives the numeric end address immediately after the final record
    DWORD *a4 // points to a two-dword search record whose first dword is the desired key
) { // begins the binary-search helper
    int v4; // tracks the start address of the current search range
    int v5; // tracks the number of eight-byte records in the current search range
    int v6; // stores the midpoint record index
    DWORD *result; // stores the function's returned output-pointer value

    v4 = a2; // begins the search at the array's first record
    v5 = (a3 - a2) >> 3; // converts the byte distance between end and begin into an eight-byte record count

    while (v5 > 0) { // continues until the candidate range contains no records
        v6 = v5 / 2; // chooses the midpoint index of the current range

        if (*(DWORD *) (v4 + 8 * (v5 / 2)) >= *a4) { // compares the midpoint record's key against the requested key
            v5 /= 2; // keeps the lower half because the midpoint may be the first record not less than the key
        } else { // handles a midpoint key that is smaller than the requested key
            v4 += 8 * v6 + 8; // moves the range start to the record immediately after the midpoint
            v5 += -1 - v6; // removes the midpoint and lower half from the remaining record count
        } // ends midpoint comparison
    }

    result = a1; // prepares to return the output-storage pointer supplied by the caller
    *a1 = v4; // writes the resulting record address into the caller's variable
    return result; // returns the same output-storage pointer
}

/**
 * @brief searches a registry object for an exact key and returns its associated
 * value pointer.
 *
 * the registry object appears to hold a begin pointer at index one and an end
 * pointer at index two. sub_5d49f0 locates the lower-bound record, after which
 * this function verifies that the key matches exactly.
 */
 PDWORD sub_5D59F0( // defines a second reconstructed game helper originally associated with address 0x005d59f0
    DWORD *thisptr, // points to the game's registry object or container-like data structure
    DWORD *a2 // initially contains the desired key value represented as a pointer
) { // begins exact registry lookup
    DWORD *v2; // stores the record-array end pointer
    DWORD *v3; // preserves the original requested key because a2 will later be overwritten
    int v5; // stores the numeric record-array begin address
    DWORD v6[2]; // creates an eight-byte temporary search record containing a key and a zero value

    v2 = (DWORD *) thisptr[2]; // reads the end pointer from the third dword of the registry object
    v3 = a2; // preserves the original lookup key
    v5 = thisptr[1]; // reads the begin pointer from the second dword of the registry object
    v6[0] = (DWORD) a2; // places the numeric key in the first dword of the temporary record
    v6[1] = 0; // clears the unused value portion of the temporary search record

    sub_5D49F0( // searches the sorted range for the first record not less than the requested key
        (DWORD *) &a2, // allows the helper to overwrite the local a2 variable with the resulting record address
        v5, // supplies the record-array begin address
        (DWORD) v2, // supplies the record-array end address
        v6 // supplies the temporary record whose first dword is the desired key
    ); // completes the lower-bound search

    if (a2 == v2 || (DWORD *) *a2 != v3) // rejects end-of-range and nonmatching lower-bound results
        return 0; // reports that the registry contains no exact entry for this key
    else // handles an exact key match
        return (PDWORD) a2[1]; // returns the second dword of the matched eight-byte record as an object pointer
}

/**
 * @brief locates the vehicle object with additional validation of the game's
 * registry state before performing the reverse-engineered lookup.
 *
 * changes:
 * - validates the global registry-container pointer before dereferencing it.
 * - validates the registry-object pointer before passing it to the lookup code.
 * - reads the registry begin and end addresses explicitly and verifies that
 *   both are present before searching.
 * - rejects reversed registry ranges where the end address is below the start.
 * - verifies that the registry range is aligned to the expected eight-byte
 *   key/value record size used by sub_5D49F0().
 * - avoids calling the registry search when the game is in a state where the
 *   relevant registry data is unavailable or only partially initialized.
 * - preserves the original successful lookup behavior and the reverse-engineered
 *   pVehicle - 19 adjustment required by ShiftGear().
 *
 * these checks primarily improve stability outside normal active-race states,
 * where the original code could dereference missing or incomplete registry
 * pointers and cause an access violation.
 */
DWORD *GetVehicleObject(VOID)
{
    PDWORD registryContainer = *(PDWORD *)MW_OBJ_REGISTRY_CONTAINER; // reads the registry-container pointer stored at the fixed game address 0x0092cd28

    if (registryContainer == NULL) {
        return NULL;
    }

    PDWORD registryObject = // declares the pointer to the searchable registry object
        *(PDWORD *)((BYTE *)registryContainer + 4); // reads the pointer stored four bytes into the registry container

    if (registryObject == NULL) {
        return NULL; // stops safely because sub_5d59f0 expects a valid registry object
    }

    DWORD beginAddress = registryObject[1];
    DWORD endAddress = registryObject[2];

    if (beginAddress == 0 || endAddress == 0) { // checks whether either registry-array boundary is missing
        return NULL;
    }

    if (endAddress < beginAddress) { // checks whether the registry range is structurally impossible
        return NULL;
    }

    if (((endAddress - beginAddress) % 8) != 0) { // verifies that the range consists of complete eight-byte registry records
        return NULL;
    }

    PDWORD pVehicle = sub_5D59F0( // searches the registry for the vehicle-related entry
        registryObject, // passes the validated registry object directly as the search object's this pointer
        (PDWORD)sub_404010 // passes 0x00404010 as the reverse-engineered registry lookup key
    );

    if (pVehicle == NULL) {
        return NULL;
    }

    return pVehicle - 19; // moves backward nineteen dwords, or 0x4c bytes, to obtain the shiftgear object base
}

/**
 * @brief invokes NFSMW's internal ShiftGear function with additional validation
 * and compiler-correct x86 calling-convention handling.
 *
 * changes:
 * - validates the requested internal gear value before entering game code.
 * - limits accepted values to reverse, neutral, and first through sixth for the
 *   current six-speed shifter configuration.
 * - returns GEAR_NOCHANGE immediately when an unsupported gear value is supplied.
 * - continues to verify that GetVehicleObject() returned a usable object before
 *   calling the game's fixed ShiftGear address.
 * - replaces the previous GNU-style inline-assembly syntax with MSVC-compatible
 *   __asm syntax required by this Visual Studio Win32 build.
 * - preserves the game's x86 __thiscall convention explicitly by placing the
 *   vehicle-object pointer in ECX and the gear argument on the stack.
 * - explicitly casts the gear value in the C++ call path to match ShiftGear's
 *   declared integer parameter type.
 * - preserves the original successful behavior and returns the value produced
 *   by NFSMW's internal ShiftGear function.
 *
 * these checks prevent invalid gear numbers and missing vehicle objects from
 * reaching the game's internal function.
 */
DWORD CallShiftGear(
    DWORD dwTargetGear
) {
    if (dwTargetGear > (DWORD)GEAR_SIXTH) { // rejects values outside reverse, neutral, and first through sixth
        return GEAR_NOCHANGE;
    }

    DWORD *pVehicle = GetVehicleObject(); // resolves the current object required as the game's this pointer

    if (pVehicle == NULL) { // detects menus or game states without a usable vehicle
        return GEAR_NOCHANGE; // declines the shift without calling the fixed game address
    }

    DWORD dwResult;

#ifdef __cplusplus // selects the compiler-generated thiscall path in a c++ build
    dwResult = ShiftGear( // invokes the game function through the typed pointer
        pVehicle, // supplies the vehicle object as this
        (int)dwTargetGear // supplies the validated internal gear value
    ); // stores the game's result
#else // selects manual thiscall setup for the actual c source build
    __asm { // begins a valid microsoft x86 inline-assembly block
        push dwTargetGear // places the explicit gear argument on the stack
        mov ecx, pVehicle // places the vehicle-object this pointer in ecx
        call ShiftGear // calls the function pointer targeting address 0x006920d0
        mov dwResult, eax // copies the game's return value into the c variable
    }
#endif

    return dwResult; // returns the game's shift function result
}

/**
 * @brief installs the raw-input hook outside the immediate dllmain body.
 *
 * after installation, the thread exits. the hook remains active because the
 * dll stays loaded and minhook's patch remains in getrawinputdata.
 */
 DWORD WINAPI ShifterThread(
    LPVOID lpParam
) {
    if (!InstallRawInputHook()) {
        printf(
            "[-] Failed to install raw input hook\n"
        );
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;
}

/**
 * @brief receives lifecycle notifications when the asi/dll is loaded into or
 * unloaded from the nfsmw process.
 */
 BOOL APIENTRY DllMain(

    HMODULE hModule,

    DWORD ul_reason_for_call,

    LPVOID lpReserved

) {
    switch (ul_reason_for_call) {

        case DLL_PROCESS_ATTACH: // handles the first loading of this asi into speed.exe

            g_hShifterThread = CreateThread( // creates a worker thread to install the minhook detour
                NULL, // uses default thread security attributes
                0, // uses the default initial stack size
                ShifterThread, // identifies the function at which the new thread begins execution
                NULL, // passes no custom argument to the thread
                0, // starts the thread immediately rather than suspended
                NULL // does not request the newly assigned thread identifier
            ); // stores the returned thread handle globally

            if (NULL == g_hShifterThread) { // detects failure to create the initialization thread
                MessageBoxA(
                    NULL, // creates an unowned message box
                    "Failed to initialize H-Shifter",
                    "Error", // title
                    MB_OK | MB_ICONERROR // requests an ok button and error icon
                );
                return FALSE; // tells the loader that dll initialization failed
            }

            break;

        case DLL_THREAD_ATTACH:
            break;

        case DLL_THREAD_DETACH:
            break;

        case DLL_PROCESS_DETACH:
            break;
    }

    return TRUE;
}