// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::raw_mutex::RawMutex;
use cell::Cell;
use mem;
use sync::atomic::{AtomicUsize, Ordering};

/// Implementation of the `GetThreadId` trait for `lock_api::ReentrantMutex`.
pub struct RawThreadId;

impl RawThreadId {
    pub const INIT: RawThreadId = RawThreadId;

    pub fn nonzero_thread_id(&self) -> usize {
        // The address of a thread-local variable is guaranteed to be unique to the
        // current thread, and is also guaranteed to be non-zero.
        thread_local!(static KEY: u8 = unsafe { mem::uninitialized() });
        KEY.with(|x| x as *const _ as usize)
    }
}

pub struct RawReentrantMutex {
    owner: AtomicUsize,
    lock_count: Cell<usize>,
    mutex: RawMutex,
    get_thread_id: RawThreadId,
}

impl RawReentrantMutex {
    pub const INIT: RawReentrantMutex = RawReentrantMutex {
        owner: AtomicUsize::new(0),
        lock_count: Cell::new(0),
        mutex: RawMutex::INIT,
        get_thread_id: RawThreadId::INIT,
    };

    #[inline]
    fn lock_internal<F: FnOnce() -> bool>(&self, try_lock: F) -> bool {
        let id = self.get_thread_id.nonzero_thread_id();
        if self.owner.load(Ordering::Relaxed) == id {
            self.lock_count.set(
                self.lock_count
                    .get()
                    .checked_add(1)
                    .expect("ReentrantMutex lock count overflow"),
            );
        } else {
            if !try_lock() {
                return false;
            }
            self.owner.store(id, Ordering::Relaxed);
            self.lock_count.set(1);
        }
        true
    }

    #[inline]
    pub fn lock(&self) {
        self.lock_internal(|| {
            self.mutex.lock();
            true
        });
    }

    #[inline]
    pub fn try_lock(&self) -> bool {
        self.lock_internal(|| self.mutex.try_lock())
    }

    #[inline]
    pub fn unlock(&self) {
        let lock_count = self.lock_count.get() - 1;
        if lock_count == 0 {
            self.owner.store(0, Ordering::Relaxed);
            self.mutex.unlock();
        } else {
            self.lock_count.set(lock_count);
        }
    }
}
