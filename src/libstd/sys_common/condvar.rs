// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use time::Duration;
use sys_common::mutex::{self, Mutex};
use sys_common::parking_lot::condvar::Condvar as RawCondvar;

/// An OS-based condition variable.
///
/// This structure is the lowest layer possible on top of the OS-provided
/// condition variables. It is consequently entirely unsafe to use. It is
/// recommended to use the safer types at the top level of this crate instead of
/// this type.
pub struct Condvar(RawCondvar);

impl Condvar {
    /// Creates a new condition variable for use.
    ///
    /// Behavior is undefined if the condition variable is moved after it is
    /// first used with any of the functions below.
    #[unstable(feature = "sys_internals", issue = "0")] // FIXME: min_const_fn
    pub const fn new() -> Condvar { Condvar(RawCondvar::new()) }

    /// Signals one waiter on this condition variable to wake up.
    #[inline]
    pub unsafe fn notify_one(&self) { self.0.notify_one(); }

    /// Awakens all current waiters on this condition variable.
    #[inline]
    pub unsafe fn notify_all(&self) { self.0.notify_all(); }

    /// Waits for a signal on the specified mutex.
    ///
    /// Behavior is undefined if the mutex is not locked by the current thread.
    /// Behavior is also undefined if more than one mutex is used concurrently
    /// on this condition variable.
    #[inline]
    pub unsafe fn wait(&self, mutex: &Mutex) { self.0.wait(mutex::raw(mutex)) }

    /// Waits for a signal on the specified mutex with a timeout duration
    /// specified by `dur` (a relative time into the future).
    ///
    /// Behavior is undefined if the mutex is not locked by the current thread.
    /// Behavior is also undefined if more than one mutex is used concurrently
    /// on this condition variable.
    #[inline]
    pub unsafe fn wait_timeout(&self, mutex: &Mutex, dur: Duration) -> bool {
        !self.0.wait_for(mutex::raw(mutex), dur).timed_out()
    }
}
