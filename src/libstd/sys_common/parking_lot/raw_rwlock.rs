// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::elision::{have_elision, AtomicElisionExt};
use super::super::parking_lot_core::{
    self,
    deadlock,
    FilterOp,
    ParkResult,
    ParkToken,
    SpinWait,
    UnparkResult
};
use super::raw_mutex::{TOKEN_HANDOFF, TOKEN_NORMAL};
use cell::Cell;
use sync::atomic::{AtomicUsize, Ordering, ATOMIC_USIZE_INIT};
use time::Instant;

const PARKED_BIT: usize = 0b001;
const UPGRADING_BIT: usize = 0b010;
// A shared guard acquires a single guard resource
const SHARED_GUARD: usize = 0b100;
const GUARD_COUNT_MASK: usize = !(SHARED_GUARD - 1);
// An exclusive lock acquires all of guard resource (i.e. it is exclusive)
const EXCLUSIVE_GUARD: usize = GUARD_COUNT_MASK;
// An upgradable lock acquires just over half of the guard resource
// This should be (GUARD_COUNT_MASK + SHARED_GUARD) >> 1, however this might
// overflow, so we shift before adding (which is okay since the least
// significant bit is zero for both GUARD_COUNT_MASK and SHARED_GUARD)
const UPGRADABLE_GUARD: usize = (GUARD_COUNT_MASK >> 1) + (SHARED_GUARD >> 1);

// Token indicating what type of lock queued threads are trying to acquire
const TOKEN_SHARED: ParkToken = ParkToken(SHARED_GUARD);
const TOKEN_EXCLUSIVE: ParkToken = ParkToken(EXCLUSIVE_GUARD);
const TOKEN_UPGRADABLE: ParkToken = ParkToken(UPGRADABLE_GUARD);
const TOKEN_UPGRADING: ParkToken = ParkToken((EXCLUSIVE_GUARD - UPGRADABLE_GUARD) | UPGRADING_BIT);

/// Raw reader-writer lock type backed by the parking lot.
pub struct RawRwLock {
    state: AtomicUsize,
}

impl RawRwLock {
    /// Initial value for an unlocked `RwLock`.
    pub const INIT: RawRwLock = RawRwLock {
        state: ATOMIC_USIZE_INIT,
    };

    /// Acquires an exclusive lock, blocking the current thread until it is able to do so.
    #[inline]
    pub fn lock_exclusive(&self) {
        if self
            .state
            .compare_exchange_weak(0, EXCLUSIVE_GUARD, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            let result = self.lock_exclusive_slow(None);
            debug_assert!(result);
        }
        unsafe { deadlock::acquire_resource(self as *const _ as usize) };
    }

    /// Attempts to acquire an exclusive lock without blocking.
    #[inline]
    pub fn try_lock_exclusive(&self) -> bool {
        if self
            .state
            .compare_exchange(0, EXCLUSIVE_GUARD, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            unsafe { deadlock::acquire_resource(self as *const _ as usize) };
            true
        } else {
            false
        }
    }

    /// Releases an exclusive lock.
    #[inline]
    pub fn unlock_exclusive(&self) {
        unsafe { deadlock::release_resource(self as *const _ as usize) };
        if self
            .state
            .compare_exchange_weak(EXCLUSIVE_GUARD, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        }
        self.unlock_exclusive_slow(false);
    }

    /// Acquires a shared lock, blocking the current thread until it is able to do so.
    #[inline]
    pub fn lock_shared(&self) {
        if !self.try_lock_shared_fast(false) {
            let result = self.lock_shared_slow(false, None);
            debug_assert!(result);
        }
        unsafe { deadlock::acquire_resource(self as *const _ as usize) };
    }

    /// Attempts to acquire a shared lock without blocking.
    #[inline]
    pub fn try_lock_shared(&self) -> bool {
        let result = if self.try_lock_shared_fast(false) {
            true
        } else {
            self.try_lock_shared_slow(false)
        };
        if result {
            unsafe { deadlock::acquire_resource(self as *const _ as usize) };
        }
        result
    }

    /// Releases a shared lock.
    #[inline]
    pub fn unlock_shared(&self) {
        unsafe { deadlock::release_resource(self as *const _ as usize) };
        let state = self.state.load(Ordering::Relaxed);
        if state & PARKED_BIT == 0
            || (state & UPGRADING_BIT == 0 && state & GUARD_COUNT_MASK != SHARED_GUARD)
        {
            if have_elision() {
                if self
                    .state
                    .elision_release(state, state - SHARED_GUARD)
                    .is_ok()
                {
                    return;
                }
            } else {
                if self
                    .state
                    .compare_exchange_weak(
                        state,
                        state - SHARED_GUARD,
                        Ordering::Release,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    return;
                }
            }
        }
        self.unlock_shared_slow(false);
    }
}


impl RawRwLock {
    #[inline(always)]
    fn try_lock_shared_fast(&self, recursive: bool) -> bool {
        let state = self.state.load(Ordering::Relaxed);

        // We can't allow grabbing a shared lock while there are parked threads
        // since that could lead to writer starvation.
        if !recursive && state & PARKED_BIT != 0 {
            return false;
        }

        // Use hardware lock elision to avoid cache conflicts when multiple
        // readers try to acquire the lock. We only do this if the lock is
        // completely empty since elision handles conflicts poorly.
        if have_elision() && state == 0 {
            self.state.elision_acquire(0, SHARED_GUARD).is_ok()
        } else if let Some(new_state) = state.checked_add(SHARED_GUARD) {
            self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
        } else {
            false
        }
    }

    #[inline(always)]
    fn try_lock_upgradable_fast(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);

        // We can't allow grabbing an upgradable lock while there are parked threads
        // since that could lead to writer starvation.
        if state & PARKED_BIT != 0 {
            return false;
        }

        if let Some(new_state) = state.checked_add(UPGRADABLE_GUARD) {
            self.state
                .compare_exchange_weak(state, new_state, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
        } else {
            false
        }
    }

    #[cold]
    #[inline(never)]
    fn lock_exclusive_slow(&self, timeout: Option<Instant>) -> bool {
        let mut spinwait = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if it isn't locked, even if there are other
            // threads parked.
            if let Some(new_state) = state.checked_add(EXCLUSIVE_GUARD) {
                match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                }
                continue;
            }

            // If there are no parked threads and only one reader or writer, try
            // spinning a few times.
            if (state == EXCLUSIVE_GUARD || state == SHARED_GUARD || state == UPGRADABLE_GUARD)
                && spinwait.spin()
            {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = || {
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        // If the rwlock is free, abort the park and try to grab
                        // it immediately.
                        if state & GUARD_COUNT_MASK == 0 {
                            return false;
                        }

                        // Nothing to do if the parked bit is already set
                        if state & PARKED_BIT != 0 {
                            return true;
                        }

                        // Set the parked bit
                        match self.state.compare_exchange_weak(
                            state,
                            state | PARKED_BIT,
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(x) => state = x,
                        }
                    }
                };
                let before_sleep = || {};
                let timed_out = |_, was_last_thread| {
                    // Clear the parked bit if we were the last parked thread
                    if was_last_thread {
                        self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                    }
                };
                match parking_lot_core::park(
                    addr,
                    validate,
                    before_sleep,
                    timed_out,
                    TOKEN_EXCLUSIVE,
                    timeout,
                ) {
                    // The thread that unparked us passed the lock on to us
                    // directly without unlocking it.
                    ParkResult::Unparked(TOKEN_HANDOFF) => return true,

                    // We were unparked normally, try acquiring the lock again
                    ParkResult::Unparked(_) => (),

                    // The validation function failed, try locking again
                    ParkResult::Invalid => (),

                    // Timeout expired
                    ParkResult::TimedOut => return false,
                }
            }

            // Loop back and try locking again
            spinwait.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_exclusive_slow(&self, force_fair: bool) {
        // Unlock directly if there are no parked threads
        if self
            .state
            .compare_exchange(EXCLUSIVE_GUARD, 0, Ordering::Release, Ordering::Relaxed)
            .is_ok()
        {
            return;
        };

        // There are threads to unpark. We unpark threads up to the guard capacity.
        let guard_count = Cell::new(0usize);
        unsafe {
            let addr = self as *const _ as usize;
            let filter = |ParkToken(token)| -> FilterOp {
                match guard_count.get().checked_add(token) {
                    Some(new_guard_count) => {
                        guard_count.set(new_guard_count);
                        FilterOp::Unpark
                    }
                    None => FilterOp::Stop,
                }
            };
            let callback = |result: UnparkResult| {
                // If we are using a fair unlock then we should keep the
                // rwlock locked and hand it off to the unparked threads.
                if result.unparked_threads != 0 && (force_fair || result.be_fair) {
                    // We need to set the guard count accordingly.
                    let mut new_state = guard_count.get();

                    if result.have_more_threads {
                        new_state |= PARKED_BIT;
                    }

                    self.state.store(new_state, Ordering::Release);
                    TOKEN_HANDOFF
                } else {
                    // Clear the parked bit if there are no more parked threads.
                    if result.have_more_threads {
                        self.state.store(PARKED_BIT, Ordering::Release);
                    } else {
                        self.state.store(0, Ordering::Release);
                    }
                    TOKEN_NORMAL
                }
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn downgrade_slow(&self) {
        unsafe {
            let addr = self as *const _ as usize;
            let mut guard_count = SHARED_GUARD;
            let filter = |ParkToken(token)| -> FilterOp {
                match guard_count.checked_add(token) {
                    Some(new_guard_count) => {
                        guard_count = new_guard_count;
                        FilterOp::Unpark
                    }
                    None => FilterOp::Stop,
                }
            };
            let callback = |result: UnparkResult| {
                // Clear the parked bit if there no more parked threads
                if !result.have_more_threads {
                    self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                }
                TOKEN_NORMAL
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn downgrade_to_upgradable_slow(&self) {
        unsafe {
            let addr = self as *const _ as usize;
            let mut guard_count = UPGRADABLE_GUARD;
            let filter = |ParkToken(token)| -> FilterOp {
                match guard_count.checked_add(token) {
                    Some(new_guard_count) => {
                        guard_count = new_guard_count;
                        FilterOp::Unpark
                    }
                    None => FilterOp::Stop,
                }
            };
            let callback = |result: UnparkResult| {
                // Clear the parked bit if there no more parked threads
                if !result.have_more_threads {
                    self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                }
                TOKEN_NORMAL
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn lock_shared_slow(&self, recursive: bool, timeout: Option<Instant>) -> bool {
        let mut spinwait = SpinWait::new();
        let mut spinwait_shared = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        let mut unparked = false;
        loop {
            // Use hardware lock elision to avoid cache conflicts when multiple
            // readers try to acquire the lock. We only do this if the lock is
            // completely empty since elision handles conflicts poorly.
            if have_elision() && state == 0 {
                match self.state.elision_acquire(0, SHARED_GUARD) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                }
            }

            // Grab the lock if there are no exclusive threads locked or
            // waiting. However if we were unparked then we are allowed to grab
            // the lock even if there are pending exclusive threads.
            if unparked || recursive || state & PARKED_BIT == 0 {
                if let Some(new_state) = state.checked_add(SHARED_GUARD) {
                    if self
                        .state
                        .compare_exchange_weak(
                            state,
                            new_state,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        )
                        .is_ok()
                    {
                        return true;
                    }

                    // If there is high contention on the reader count then we want
                    // to leave some time between attempts to acquire the lock to
                    // let other threads make progress.
                    spinwait_shared.spin_no_yield();
                    state = self.state.load(Ordering::Relaxed);
                    continue;
                } else {
                    // We were unparked spuriously, reset unparked flag.
                    unparked = false;
                }
            }

            // If there are no parked threads, try spinning a few times
            if state & PARKED_BIT == 0 && spinwait.spin() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = || {
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        // Nothing to do if the parked bit is already set
                        if state & PARKED_BIT != 0 {
                            return true;
                        }

                        // If the parked bit is not set then it means we are at
                        // the front of the queue. If there is space for another
                        // lock then we should abort the park and try acquiring
                        // the lock again.
                        if state & GUARD_COUNT_MASK != GUARD_COUNT_MASK {
                            return false;
                        }

                        // Set the parked bit
                        match self.state.compare_exchange_weak(
                            state,
                            state | PARKED_BIT,
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(x) => state = x,
                        }
                    }
                };
                let before_sleep = || {};
                let timed_out = |_, was_last_thread| {
                    // Clear the parked bit if we were the last parked thread
                    if was_last_thread {
                        self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                    }
                };
                match parking_lot_core::park(
                    addr,
                    validate,
                    before_sleep,
                    timed_out,
                    TOKEN_SHARED,
                    timeout,
                ) {
                    // The thread that unparked us passed the lock on to us
                    // directly without unlocking it.
                    ParkResult::Unparked(TOKEN_HANDOFF) => return true,

                    // We were unparked normally, try acquiring the lock again
                    ParkResult::Unparked(_) => (),

                    // The validation function failed, try locking again
                    ParkResult::Invalid => (),

                    // Timeout expired
                    ParkResult::TimedOut => return false,
                }
            }

            // Loop back and try locking again
            spinwait.reset();
            spinwait_shared.reset();
            state = self.state.load(Ordering::Relaxed);
            unparked = true;
        }
    }

    #[cold]
    #[inline(never)]
    fn try_lock_shared_slow(&self, recursive: bool) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if !recursive && state & PARKED_BIT != 0 {
                return false;
            }
            if have_elision() && state == 0 {
                match self.state.elision_acquire(0, SHARED_GUARD) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                }
            } else {
                match state.checked_add(SHARED_GUARD) {
                    Some(new_state) => match self.state.compare_exchange_weak(
                        state,
                        new_state,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(x) => state = x,
                    },
                    None => return false,
                }
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_shared_slow(&self, force_fair: bool) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Just release the lock if there are no parked thread or if we are
            // not the last shared thread.
            if state & PARKED_BIT == 0
                || (state & UPGRADING_BIT == 0 && state & GUARD_COUNT_MASK != SHARED_GUARD)
                || (state & UPGRADING_BIT != 0
                    && state & GUARD_COUNT_MASK != UPGRADABLE_GUARD + SHARED_GUARD)
            {
                match self.state.compare_exchange_weak(
                    state,
                    state - SHARED_GUARD,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            break;
        }

        // There are threads to unpark. If there is a thread waiting to be
        // upgraded, we find that thread and let it upgrade, otherwise we
        // unpark threads up to the guard capacity. Note that there is a
        // potential race condition here: another thread might grab a shared
        // lock between now and when we actually release our lock.
        let additional_guards = Cell::new(0usize);
        let has_upgraded = Cell::new(if state & UPGRADING_BIT == 0 {
            None
        } else {
            Some(false)
        });
        unsafe {
            let addr = self as *const _ as usize;
            let filter = |ParkToken(token)| -> FilterOp {
                match has_upgraded.get() {
                    None => match additional_guards.get().checked_add(token) {
                        Some(x) => {
                            additional_guards.set(x);
                            FilterOp::Unpark
                        }
                        None => FilterOp::Stop,
                    },
                    Some(false) => {
                        if token & UPGRADING_BIT != 0 {
                            additional_guards.set(token & !UPGRADING_BIT);
                            has_upgraded.set(Some(true));
                            FilterOp::Unpark
                        } else {
                            FilterOp::Skip
                        }
                    }
                    Some(true) => FilterOp::Stop,
                }
            };
            let callback = |result: UnparkResult| {
                let mut state = self.state.load(Ordering::Relaxed);
                loop {
                    // Release our shared lock
                    let mut new_state = state - SHARED_GUARD;

                    // Clear the parked bit if there are no more threads in
                    // the queue.
                    if !result.have_more_threads {
                        new_state &= !PARKED_BIT;
                    }

                    // Clear the upgrading bit if we are upgrading a thread.
                    if let Some(true) = has_upgraded.get() {
                        new_state &= !UPGRADING_BIT;
                    }

                    // Consider using fair unlocking. If we are, then we should set
                    // the state to the new value and tell the threads that we are
                    // handing the lock directly.
                    let token = if result.unparked_threads != 0 && (force_fair || result.be_fair) {
                        match new_state.checked_add(additional_guards.get()) {
                            Some(x) => {
                                new_state = x;
                                TOKEN_HANDOFF
                            }
                            None => TOKEN_NORMAL,
                        }
                    } else {
                        TOKEN_NORMAL
                    };

                    match self.state.compare_exchange_weak(
                        state,
                        new_state,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return token,
                        Err(x) => state = x,
                    }
                }
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn lock_upgradable_slow(&self, timeout: Option<Instant>) -> bool {
        let mut spinwait = SpinWait::new();
        let mut spinwait_shared = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        let mut unparked = false;
        loop {
            // Grab the lock if there are no exclusive or upgradable threads
            // locked or waiting. However if we were unparked then we are
            // allowed to grab the lock even if there are pending exclusive threads.
            if unparked || state & PARKED_BIT == 0 {
                if let Some(new_state) = state.checked_add(UPGRADABLE_GUARD) {
                    if self
                        .state
                        .compare_exchange_weak(
                            state,
                            new_state,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        ).is_ok()
                    {
                        return true;
                    }

                    // If there is high contention on the reader count then we want
                    // to leave some time between attempts to acquire the lock to
                    // let other threads make progress.
                    spinwait_shared.spin_no_yield();
                    state = self.state.load(Ordering::Relaxed);
                    continue;
                } else {
                    // We were unparked spuriously, reset unparked flag.
                    unparked = false;
                }
            }

            // If there are no parked threads, try spinning a few times
            if state & PARKED_BIT == 0 && spinwait.spin() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = || {
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        // Nothing to do if the parked bit is already set
                        if state & PARKED_BIT != 0 {
                            return true;
                        }

                        // If the parked bit is not set then it means we are at
                        // the front of the queue. If there is space for an
                        // upgradable lock then we should abort the park and try
                        // acquiring the lock again.
                        if state & UPGRADABLE_GUARD != UPGRADABLE_GUARD {
                            return false;
                        }

                        // Set the parked bit
                        match self.state.compare_exchange_weak(
                            state,
                            state | PARKED_BIT,
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(x) => state = x,
                        }
                    }
                };
                let before_sleep = || {};
                let timed_out = |_, was_last_thread| {
                    // Clear the parked bit if we were the last parked thread
                    if was_last_thread {
                        self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                    }
                };
                match parking_lot_core::park(
                    addr,
                    validate,
                    before_sleep,
                    timed_out,
                    TOKEN_UPGRADABLE,
                    timeout,
                ) {
                    // The thread that unparked us passed the lock on to us
                    // directly without unlocking it.
                    ParkResult::Unparked(TOKEN_HANDOFF) => return true,

                    // We were unparked normally, try acquiring the lock again
                    ParkResult::Unparked(_) => (),

                    // The validation function failed, try locking again
                    ParkResult::Invalid => (),

                    // Timeout expired
                    ParkResult::TimedOut => return false,
                }
            }

            // Loop back and try locking again
            spinwait.reset();
            spinwait_shared.reset();
            state = self.state.load(Ordering::Relaxed);
            unparked = true;
        }
    }

    #[cold]
    #[inline(never)]
    fn try_lock_upgradable_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & PARKED_BIT != 0 {
                return false;
            }

            match state.checked_add(UPGRADABLE_GUARD) {
                Some(new_state) => match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                },
                None => return false,
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn unlock_upgradable_slow(&self, force_fair: bool) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Just release the lock if there are no parked threads.
            if state & PARKED_BIT == 0 {
                match self.state.compare_exchange_weak(
                    state,
                    state - UPGRADABLE_GUARD,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            break;
        }

        // There are threads to unpark. We unpark threads up to the guard capacity.
        let additional_guards = Cell::new(0usize);
        unsafe {
            let addr = self as *const _ as usize;
            let filter = |ParkToken(token)| -> FilterOp {
                match additional_guards.get().checked_add(token) {
                    Some(x) => {
                        additional_guards.set(x);
                        FilterOp::Unpark
                    }
                    None => FilterOp::Stop,
                }
            };
            let callback = |result: UnparkResult| {
                let mut state = self.state.load(Ordering::Relaxed);
                loop {
                    // Release our upgradable lock
                    let mut new_state = state - UPGRADABLE_GUARD;

                    // Clear the parked bit if there are no more threads in
                    // the queue
                    if !result.have_more_threads {
                        new_state &= !PARKED_BIT;
                    }

                    // Consider using fair unlocking. If we are, then we should set
                    // the state to the new value and tell the threads that we are
                    // handing the lock directly.
                    let token = if result.unparked_threads != 0 && (force_fair || result.be_fair) {
                        match new_state.checked_add(additional_guards.get()) {
                            Some(x) => {
                                new_state = x;
                                TOKEN_HANDOFF
                            }
                            None => TOKEN_NORMAL,
                        }
                    } else {
                        TOKEN_NORMAL
                    };

                    match self.state.compare_exchange_weak(
                        state,
                        new_state,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return token,
                        Err(x) => state = x,
                    }
                }
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn downgrade_upgradable_slow(&self, state: usize) {
        unsafe {
            let addr = self as *const _ as usize;
            let mut guard_count = (state & GUARD_COUNT_MASK) - UPGRADABLE_GUARD;
            let filter = |ParkToken(token)| -> FilterOp {
                match guard_count.checked_add(token) {
                    Some(x) => {
                        guard_count = x;
                        FilterOp::Unpark
                    }
                    None => FilterOp::Stop,
                }
            };
            let callback = |result: UnparkResult| {
                // Clear the parked bit if there no more parked threads
                if !result.have_more_threads {
                    self.state.fetch_and(!PARKED_BIT, Ordering::Relaxed);
                }
                TOKEN_NORMAL
            };
            parking_lot_core::unpark_filter(addr, filter, callback);
        }
    }

    #[cold]
    #[inline(never)]
    fn try_upgrade_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match state.checked_add(EXCLUSIVE_GUARD - SHARED_GUARD) {
                Some(new_state) => match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                },
                None => return false,
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn upgrade_slow(&self, timeout: Option<Instant>) -> bool {
        let mut spinwait = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            // Grab the lock if it isn't locked, even if there are other
            // threads parked.
            if let Some(new_state) = state.checked_add(EXCLUSIVE_GUARD - UPGRADABLE_GUARD) {
                match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return true,
                    Err(x) => state = x,
                }
                continue;
            }

            // If there are no parked threads and only one other reader, try
            // spinning a few times.
            if state == UPGRADABLE_GUARD | SHARED_GUARD && spinwait.spin() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            // Park our thread until we are woken up by an unlock
            unsafe {
                let addr = self as *const _ as usize;
                let validate = || {
                    let mut state = self.state.load(Ordering::Relaxed);
                    loop {
                        // If the rwlock is free, abort the park and try to grab
                        // it immediately.
                        if state & GUARD_COUNT_MASK == UPGRADABLE_GUARD {
                            return false;
                        }

                        // Set the upgrading and parked bits
                        match self.state.compare_exchange_weak(
                            state,
                            state | (UPGRADING_BIT | PARKED_BIT),
                            Ordering::Relaxed,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return true,
                            Err(x) => state = x,
                        }
                    }
                };
                let before_sleep = || {};
                let timed_out = |_, was_last_thread| {
                    // Clear the upgrading bit
                    let mut flags = UPGRADING_BIT;

                    // Clear the parked bit if we were the last parked thread
                    if was_last_thread {
                        flags |= PARKED_BIT;
                    }

                    self.state.fetch_and(!flags, Ordering::Relaxed);
                };
                match parking_lot_core::park(
                    addr,
                    validate,
                    before_sleep,
                    timed_out,
                    TOKEN_UPGRADING,
                    timeout,
                ) {
                    // The thread that unparked us passed the lock on to us
                    // directly without unlocking it.
                    ParkResult::Unparked(TOKEN_HANDOFF) => return true,

                    // We were unparked normally, try acquiring the lock again
                    ParkResult::Unparked(_) => (),

                    // The validation function failed, try locking again
                    ParkResult::Invalid => (),

                    // Timeout expired
                    ParkResult::TimedOut => return false,
                }
            }

            // Loop back and try locking again
            spinwait.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[cold]
    #[inline(never)]
    fn bump_shared_slow(&self) {
        unsafe { deadlock::release_resource(self as *const _ as usize) };
        self.unlock_shared_slow(true);
        self.lock_shared();
    }

    #[cold]
    #[inline(never)]
    fn bump_exclusive_slow(&self) {
        unsafe { deadlock::release_resource(self as *const _ as usize) };
        self.unlock_exclusive_slow(true);
        self.lock_exclusive();
    }
}
