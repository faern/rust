// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use mem;
use ptr;
use sync::atomic::{AtomicUsize, Ordering};
use time::Instant;

use sys::c::{TRUE, ULONG};
use sys::c::NTSTATUS;
use sys::c::{STATUS_SUCCESS, STATUS_TIMEOUT};
use sys::c::CloseHandle;
use sys::c::{GetModuleHandleA, GetProcAddress};
use sys::c::{ACCESS_MASK, GENERIC_READ, GENERIC_WRITE, LPCSTR};
use sys::c::{BOOLEAN, HANDLE, LARGE_INTEGER, LPHANDLE, PLARGE_INTEGER, LPVOID};

const STATE_UNPARKED: usize = 0;
const STATE_PARKED: usize = 1;
const STATE_TIMED_OUT: usize = 2;

#[allow(non_snake_case)]
pub struct KeyedEvent {
    handle: HANDLE,
    NtReleaseKeyedEvent: extern "system" fn(
        EventHandle: HANDLE,
        Key: LPVOID,
        Alertable: BOOLEAN,
        Timeout: PLARGE_INTEGER,
    ) -> NTSTATUS,
    NtWaitForKeyedEvent: extern "system" fn(
        EventHandle: HANDLE,
        Key: LPVOID,
        Alertable: BOOLEAN,
        Timeout: PLARGE_INTEGER,
    ) -> NTSTATUS,
}

impl KeyedEvent {
    unsafe fn wait_for(&self, key: LPVOID, timeout: PLARGE_INTEGER) -> NTSTATUS {
        (self.NtWaitForKeyedEvent)(self.handle, key, 0, timeout)
    }

    unsafe fn release(&self, key: LPVOID) -> NTSTATUS {
        (self.NtReleaseKeyedEvent)(self.handle, key, 0, ptr::null_mut())
    }

    #[allow(non_snake_case)]
    pub fn create() -> Option<KeyedEvent> {
        unsafe {
            let ntdll = GetModuleHandleA(b"ntdll.dll\0".as_ptr() as LPCSTR);
            if ntdll.is_null() {
                return None;
            }

            let NtCreateKeyedEvent =
                GetProcAddress(ntdll, b"NtCreateKeyedEvent\0".as_ptr() as LPCSTR);
            if NtCreateKeyedEvent.is_null() {
                return None;
            }
            let NtReleaseKeyedEvent =
                GetProcAddress(ntdll, b"NtReleaseKeyedEvent\0".as_ptr() as LPCSTR);
            if NtReleaseKeyedEvent.is_null() {
                return None;
            }
            let NtWaitForKeyedEvent =
                GetProcAddress(ntdll, b"NtWaitForKeyedEvent\0".as_ptr() as LPCSTR);
            if NtWaitForKeyedEvent.is_null() {
                return None;
            }

            let NtCreateKeyedEvent: extern "system" fn(
                KeyedEventHandle: LPHANDLE,
                DesiredAccess: ACCESS_MASK,
                ObjectAttributes: LPVOID,
                Flags: ULONG,
            ) -> NTSTATUS = mem::transmute(NtCreateKeyedEvent);
            let mut handle = mem::uninitialized();
            let status = NtCreateKeyedEvent(
                &mut handle,
                GENERIC_READ | GENERIC_WRITE,
                ptr::null_mut(),
                0,
            );
            if status != STATUS_SUCCESS {
                return None;
            }

            Some(KeyedEvent {
                handle,
                NtReleaseKeyedEvent: mem::transmute(NtReleaseKeyedEvent),
                NtWaitForKeyedEvent: mem::transmute(NtWaitForKeyedEvent),
            })
        }
    }

    pub fn prepare_park(&'static self, key: &AtomicUsize) {
        key.store(STATE_PARKED, Ordering::Relaxed);
    }

    pub fn timed_out(&'static self, key: &AtomicUsize) -> bool {
        key.load(Ordering::Relaxed) == STATE_TIMED_OUT
    }

    pub unsafe fn park(&'static self, key: &AtomicUsize) {
        let status = self.wait_for(key as *const _ as LPVOID, ptr::null_mut());
        debug_assert_eq!(status, STATUS_SUCCESS);
    }

    pub unsafe fn park_until(&'static self, key: &AtomicUsize, timeout: Instant) -> bool {
        let now = Instant::now();
        if timeout <= now {
            // If another thread unparked us, we need to call
            // NtWaitForKeyedEvent otherwise that thread will stay stuck at
            // NtReleaseKeyedEvent.
            if key.swap(STATE_TIMED_OUT, Ordering::Relaxed) == STATE_UNPARKED {
                self.park(key);
                return true;
            }
            return false;
        }

        // NT uses a timeout in units of 100ns. We use a negative value to
        // indicate a relative timeout based on a monotonic clock.
        let mut nt_timeout: LARGE_INTEGER = 0;
        let diff = timeout - now;
        let value = (diff.as_secs() as i64)
            .checked_mul(-10000000)
            .and_then(|x| x.checked_sub((diff.subsec_nanos() as i64 + 99) / 100));

        match value {
            Some(x) => nt_timeout = x,
            None => {
                // Timeout overflowed, just sleep indefinitely
                self.park(key);
                return true;
            }
        };

        let status = self.wait_for(key as *const _ as LPVOID, &mut nt_timeout);
        if status == STATUS_SUCCESS {
            return true;
        }
        debug_assert_eq!(status, STATUS_TIMEOUT);

        // If another thread unparked us, we need to call NtWaitForKeyedEvent
        // otherwise that thread will stay stuck at NtReleaseKeyedEvent.
        if key.swap(STATE_TIMED_OUT, Ordering::Relaxed) == STATE_UNPARKED {
            self.park(key);
            return true;
        }
        false
    }

    pub unsafe fn unpark_lock(&'static self, key: &AtomicUsize) -> UnparkHandle {
        // If the state was STATE_PARKED then we need to wake up the thread
        if key.swap(STATE_UNPARKED, Ordering::Relaxed) == STATE_PARKED {
            UnparkHandle {
                key: key,
                keyed_event: self,
            }
        } else {
            UnparkHandle {
                key: ptr::null(),
                keyed_event: self,
            }
        }
    }
}

impl Drop for KeyedEvent {
    fn drop(&mut self) {
        unsafe {
            let ok = CloseHandle(self.handle);
            debug_assert_eq!(ok, TRUE);
        }
    }
}

// Handle for a thread that is about to be unparked. We need to mark the thread
// as unparked while holding the queue lock, but we delay the actual unparking
// until after the queue lock is released.
pub struct UnparkHandle {
    key: *const AtomicUsize,
    keyed_event: &'static KeyedEvent,
}

impl UnparkHandle {
    // Wakes up the parked thread. This should be called after the queue lock is
    // released to avoid blocking the queue for too long.
    pub unsafe fn unpark(self) {
        if !self.key.is_null() {
            let status = self.keyed_event.release(self.key as LPVOID);
            debug_assert_eq!(status, STATUS_SUCCESS);
        }
    }
}
