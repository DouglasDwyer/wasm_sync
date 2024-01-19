use js_sys::*;
use std::cell::*;
use std::hint::*;
use std::marker::*;
use std::mem::*;
use std::panic::*;
use std::sync::*;
use std::sync::atomic::*;
use std::time::*;

/// Whether this thread is allowed to block and use synchronization primitives.
#[inline(always)]
fn can_block() -> bool {
    thread_local! {
        static CAN_BLOCK: bool = web_sys::window().is_none();
    }

    CAN_BLOCK.with(|x| *x)
}

/// A Condition Variable
///
/// Condition variables represent the ability to block a thread such that it
/// consumes no CPU time while waiting for an event to occur. Condition
/// variables are typically associated with a boolean predicate (a condition)
/// and a mutex. The predicate is always verified inside of the mutex before
/// determining that a thread must block.
///
/// Functions in this module will block the current **thread** of execution.
/// Note that any attempt to use multiple mutexes on the same condition
/// variable may result in a runtime panic.
///
/// # Examples
///
/// ```
/// use std::sync::{Arc, Mutex, Condvar};
/// use std::thread;
///
/// let pair = Arc::new((Mutex::new(false), Condvar::new()));
/// let pair2 = Arc::clone(&pair);
///
/// // Inside of our lock, spawn a new thread, and then wait for it to start.
/// thread::spawn(move|| {
///     let (lock, cvar) = &*pair2;
///     let mut started = lock.lock().unwrap();
///     *started = true;
///     // We notify the condvar that the value has changed.
///     cvar.notify_one();
/// });
///
/// // Wait for the thread to start up.
/// let (lock, cvar) = &*pair;
/// let mut started = lock.lock().unwrap();
/// while !*started {
///     started = cvar.wait(started).unwrap();
/// }
/// ```
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct Condvar {
    /// The backing condition variable.
    inner: std::sync::Condvar
}

impl Condvar {
    /// Represents the result of timeout not having occurred during waiting on a condition variable.
    const FALSE_TIMEOUT_RESULT: WaitTimeoutResult = unsafe { transmute(false) };

    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    #[must_use]
    #[inline]
    pub const fn new() -> Condvar {
        Condvar { inner: std::sync::Condvar::new() }
    }

    /// Blocks the current thread until this condition variable receives a
    /// notification.
    ///
    /// This function will atomically unlock the mutex specified (represented by
    /// `guard`) and block the current thread. This means that any calls
    /// to `notify_one` or `notify_all` which happen logically after the
    /// mutex is unlocked are candidates to wake this thread up. When this
    /// function call returns, the lock specified will have been re-acquired.
    ///
    /// Note that this function is susceptible to spurious wakeups. Condition
    /// variables normally have a boolean predicate associated with them, and
    /// the predicate must always be checked each time this function returns to
    /// protect against spurious wakeups.
    ///
    /// # Errors
    ///
    /// This function will return an error if the mutex being waited on is
    /// poisoned when this thread re-acquires the lock. For more information,
    /// see information about poisoning on the `Mutex` type.
    ///
    /// # Panics
    ///
    /// This function may [`panic!`] if it is used with more than one mutex
    /// over time.
    pub fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> LockResult<MutexGuard<'a, T>> {
        if can_block() {
            self.inner.wait(guard)
        }
        else {
            Self::guard_to_mutex(guard).lock()
        }
    }
    

    /// Blocks the current thread until this condition variable receives a
    /// notification and the provided condition is false.
    ///
    /// This function will atomically unlock the mutex specified (represented by
    /// `guard`) and block the current thread. This means that any calls
    /// to `notify_one` or `notify_all` which happen logically after the
    /// mutex is unlocked are candidates to wake this thread up. When this
    /// function call returns, the lock specified will have been re-acquired.
    ///
    /// # Errors
    ///
    /// This function will return an error if the mutex being waited on is
    /// poisoned when this thread re-acquires the lock. For more information,
    /// see information about poisoning on the `Mutex` type.
    pub fn wait_while<'a, T, F>(
        &self,
        mut guard: MutexGuard<'a, T>,
        mut condition: F,
    ) -> LockResult<MutexGuard<'a, T>>
    where
        F: FnMut(&mut T) -> bool,
    {
        while condition(&mut *guard) {
            guard = self.wait(guard)?;
        }

        Ok(guard)
    }

    /// Waits on this condition variable for a notification, timing out after a
    /// specified duration.
    ///
    /// The semantics of this function are equivalent to `wait`
    /// except that the thread will be blocked for roughly no longer
    /// than `ms` milliseconds. This method should not be used for
    /// precise timing due to anomalies such as preemption or platform
    /// differences that might not cause the maximum amount of time
    /// waited to be precisely `ms`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned boolean is `false` only if the timeout is known
    /// to have elapsed.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    #[allow(deprecated)]
    #[deprecated(since = "1.6.0", note = "replaced by `std::sync::Condvar::wait_timeout`")]
    pub fn wait_timeout_ms<'a, T>(
        &self,
        guard: MutexGuard<'a, T>,
        ms: u32,
    ) -> LockResult<(MutexGuard<'a, T>, bool)> {
        unsafe {
            if can_block() {
                self.inner.wait_timeout_ms(guard, ms)
            }
            else {
                Self::guard_to_mutex(guard).lock().map(|guard| (guard, false)).map_err(|poison| transmute((poison.into_inner(), false)))
            }
        }
    }

    /// Waits on this condition variable for a notification, timing out after a
    /// specified duration.
    ///
    /// The semantics of this function are equivalent to `wait` except that
    /// the thread will be blocked for roughly no longer than `dur`. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that might not cause the maximum
    /// amount of time waited to be precisely `dur`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time. This function is susceptible to spurious wakeups.
    /// Condition variables normally have a boolean predicate associated with
    /// them, and the predicate must always be checked each time this function
    /// returns to protect against spurious wakeups. Additionally, it is
    /// typically desirable for the timeout to not exceed some duration in
    /// spite of spurious wakes, thus the sleep-duration is decremented by the
    /// amount slept. Alternatively, use the `wait_timeout_while` method
    /// to wait with a timeout while a predicate is true.
    ///
    /// The returned [`WaitTimeoutResult`] value indicates if the timeout is
    /// known to have elapsed.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    pub fn wait_timeout<'a, T>(
        &self,
        guard: MutexGuard<'a, T>,
        dur: Duration,
    ) -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)> {
        unsafe {
            if can_block() {
                self.inner.wait_timeout(guard, dur)
            }
            else {
                Self::guard_to_mutex(guard).lock().map(|guard| (guard, Self::FALSE_TIMEOUT_RESULT)).map_err(|poison| transmute((poison.into_inner(), Self::FALSE_TIMEOUT_RESULT)))
            }
        }
    }

    /// Waits on this condition variable for a notification, timing out after a
    /// specified duration.
    ///
    /// The semantics of this function are equivalent to `wait_while` except
    /// that the thread will be blocked for roughly no longer than `dur`. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that might not cause the maximum
    /// amount of time waited to be precisely `dur`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned [`WaitTimeoutResult`] value indicates if the timeout is
    /// known to have elapsed without the condition being met.
    ///
    /// Like `wait_while`, the lock specified will be re-acquired when this
    /// function returns, regardless of whether the timeout elapsed or not.
    pub fn wait_timeout_while<'a, T, F>(
        &self,
        guard: MutexGuard<'a, T>,
        dur: Duration,
        condition: F,
    ) -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)>
    where
        F: FnMut(&mut T) -> bool,
    {
        unsafe {
            if can_block() {
                self.inner.wait_timeout_while(guard, dur, condition)
            }
            else {
                Self::guard_to_mutex(guard).lock().map(|guard| (guard, Self::FALSE_TIMEOUT_RESULT)).map_err(|poison| transmute((poison.into_inner(), Self::FALSE_TIMEOUT_RESULT)))
            }
        }
    }

    /// Wakes up one blocked thread on this condvar.
    ///
    /// If there is a blocked thread on this condition variable, then it will
    /// be woken up from its call to `wait` or `wait_timeout`. Calls to
    /// `notify_one` are not buffered in any way.
    ///
    /// To wake up all threads, see `notify_all`.
    pub fn notify_one(&self) {
        self.inner.notify_one()
    }

    /// Wakes up all blocked threads on this condvar.
    ///
    /// This method will ensure that any current waiters on the condition
    /// variable are awoken. Calls to `notify_all()` are not buffered in any
    /// way.
    ///
    /// To wake up only one thread, see `notify_one`.
    pub fn notify_all(&self) {
        self.inner.notify_all()
    }

    /// Releases the guard and returns a reference to the underlying mutex.
    fn guard_to_mutex<T: ?Sized>(guard: MutexGuard<T>) -> &Mutex<T> {
        unsafe {
            transmute::<_, &&Mutex<T>>(&guard)
        }
    }
}

/// A mutual exclusion primitive useful for protecting shared data
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can be created via a `new` constructor. Each mutex has a type parameter
/// which represents the data that it is protecting. The data can only be accessed
/// through the RAII guards returned from `lock` and `try_lock`, which
/// guarantees that the data is only ever accessed when the mutex is locked.
///
/// # Poisoning
///
/// The mutexes in this module implement a strategy called "poisoning" where a
/// mutex is considered poisoned whenever a thread panics while holding the
/// mutex. Once a mutex is poisoned, all other threads are unable to access the
/// data by default as it is likely tainted (some invariant is not being
/// upheld).
///
/// For a mutex, this means that the `lock` and `try_lock` methods return a
/// [`Result`] which indicates whether a mutex has been poisoned or not. Most
/// usage of a mutex will simply `unwrap()` these results, propagating panics
/// among threads to ensure that a possibly invalid invariant is not witnessed.
///
/// A poisoned mutex, however, does not prevent all access to the underlying
/// data. The [`PoisonError`] type has an `into_inner` method which will return
/// the guard that would have otherwise been returned on a successful lock. This
/// allows access to the data, despite the lock being poisoned.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct Mutex<T: ?Sized> {
    /// The backing mutex.
    inner: std::sync::Mutex<T>
}

impl<T> Mutex<T> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[inline]
    pub const fn new(t: T) -> Mutex<T> {
        Mutex { inner: std::sync::Mutex::new(t) }
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// The exact behavior on locking a mutex in the thread which already holds
    /// the lock is left unspecified. However, this function will not return on
    /// the second call (it might panic or deadlock, for example).
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return an error once the mutex is acquired.
    ///
    /// # Panics
    ///
    /// This function might panic when called if the lock is already held by
    /// the current thread.
    pub fn lock(&self) -> LockResult<MutexGuard<'_, T>> {
        if can_block() {
            self.inner.lock()
        }
        else {
            loop {
                match self.inner.try_lock() {
                    Ok(guard) => return Ok(guard),
                    Err(TryLockError::WouldBlock) => {},
                    Err(TryLockError::Poisoned(err)) => return Err(err)
                }
            }
        }
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then [`Err`] is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return the `Poisoned` error if the mutex would
    /// otherwise be acquired.
    ///
    /// If the mutex could not be acquired because it is already locked, then
    /// this call will return the `WouldBlock` error.
    pub fn try_lock(&self) -> TryLockResult<MutexGuard<'_, T>> {
        self.inner.try_lock()
    }

    /// Immediately drops the guard, and consequently unlocks the mutex.
    ///
    /// This function is equivalent to calling [`drop`] on the guard but is more self-documenting.
    /// Alternately, the guard will be automatically dropped when it goes out of scope.
    ///
    /// ```
    /// #![feature(mutex_unlock)]
    ///
    /// use std::sync::Mutex;
    /// let mutex = Mutex::new(0);
    ///
    /// let mut guard = mutex.lock().unwrap();
    /// *guard += 20;
    /// Mutex::unlock(guard);
    /// ```
    /// 
    #[cfg(feature = "mutex_unlock")]
    pub fn unlock(guard: MutexGuard<'_, T>) {
        std::sync::Mutex::unlock(guard);
    }

    /// Determines whether the mutex is poisoned.
    ///
    /// If another thread is active, the mutex can still become poisoned at any
    /// time. You should not trust a `false` value for program correctness
    /// without additional synchronization.
    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.inner.is_poisoned()
    }

    /// Clear the poisoned state from a mutex
    ///
    /// If the mutex is poisoned, it will remain poisoned until this function is called. This
    /// allows recovering from a poisoned state and marking that it has recovered. For example, if
    /// the value is overwritten by a known-good value, then the mutex can be marked as
    /// un-poisoned. Or possibly, the value could be inspected to determine if it is in a
    /// consistent state, and if so the poison is removed.
    #[inline]
    #[cfg(feature = "mutex_unpoison")]
    pub fn clear_poison(&self) {
        self.inner.clear_poison();
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return an error instead.
    pub fn into_inner(self) -> LockResult<T>
    where
        T: Sized,
    {
        self.inner.into_inner()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place -- the mutable borrow statically guarantees no locks exist.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return an error instead.
    pub fn get_mut(&mut self) -> LockResult<&mut T> {
        self.inner.get_mut()
    }
}

impl<T> From<T> for Mutex<T> {
    /// Creates a new mutex in an unlocked state ready for use.
    /// This is equivalent to [`Mutex::new`].
    fn from(t: T) -> Self {
        Mutex::new(t)
    }
}

/// A reader-writer lock
///
/// This type of lock allows a number of readers or at most one writer at any
/// point in time. The write portion of this lock typically allows modification
/// of the underlying data (exclusive access) and the read portion of this lock
/// typically allows for read-only access (shared access).
///
/// In comparison, a [`Mutex`] does not distinguish between readers or writers
/// that acquire the lock, therefore blocking any threads waiting for the lock to
/// become available. An `RwLock` will allow any number of readers to acquire the
/// lock as long as a writer is not holding the lock.
///
/// The priority policy of the lock is dependent on the underlying operating
/// system's implementation, and this type does not guarantee that any
/// particular policy will be used. In particular, a writer which is waiting to
/// acquire the lock in `write` might or might not block concurrent calls to
/// `read`, e.g.:
///
/// <details><summary>Potential deadlock example</summary>
///
/// ```text
/// // Thread 1             |  // Thread 2
/// let _rg = lock.read();  |
///                         |  // will block
///                         |  let _wg = lock.write();
/// // may deadlock         |
/// let _rg = lock.read();  |
/// ```
/// </details>
///
/// The type parameter `T` represents the data that this lock protects. It is
/// required that `T` satisfies [`Send`] to be shared across threads and
/// [`Sync`] to allow concurrent access through readers. The RAII guards
/// returned from the locking methods implement `Deref` (and `DerefMut`
/// for the `write` methods) to allow access to the content of the lock.
///
/// # Poisoning
///
/// An `RwLock`, like [`Mutex`], will become poisoned on a panic. Note, however,
/// that an `RwLock` may only be poisoned if a panic occurs while it is locked
/// exclusively (write mode). If a panic occurs in any reader, then the lock
/// will not be poisoned.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct RwLock<T: ?Sized> {
    /// The backing lock.
    inner: std::sync::RwLock<T>
}

impl<T> RwLock<T> {
    /// Creates a new instance of an `RwLock<T>` which is unlocked.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::RwLock;
    ///
    /// let lock = RwLock::new(5);
    /// ```
    #[inline]
    pub const fn new(t: T) -> RwLock<T> {
        RwLock { inner: std::sync::RwLock::new(t) }
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Locks this `RwLock` with shared read access, blocking the current thread
    /// until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more writers which
    /// hold the lock. There may be other readers currently inside the lock when
    /// this method returns. This method does not provide any guarantees with
    /// respect to the ordering of whether contentious readers or writers will
    /// acquire the lock first.
    ///
    /// Returns an RAII guard which will release this thread's shared access
    /// once it is dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `RwLock` is poisoned. An
    /// `RwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. The failure will occur immediately after the lock has been
    /// acquired.
    ///
    /// # Panics
    ///
    /// This function might panic when called if the lock is already held by the current thread.
    #[inline]
    pub fn read(&self) -> LockResult<RwLockReadGuard<'_, T>> {
        if can_block() {
            self.inner.read()
        }
        else {
            loop {
                match self.inner.try_read() {
                    Ok(guard) => return Ok(guard),
                    Err(TryLockError::WouldBlock) => {},
                    Err(TryLockError::Poisoned(err)) => return Err(err)
                }
            }
        }
    }

    /// Attempts to acquire this `RwLock` with shared read access.
    ///
    /// If the access could not be granted at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared access
    /// when it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the `Poisoned` error if the `RwLock` is
    /// poisoned. An `RwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired.
    ///
    /// This function will return the `WouldBlock` error if the `RwLock` could
    /// not be acquired because it was already locked exclusively.
    #[inline]
    pub fn try_read(&self) -> TryLockResult<RwLockReadGuard<'_, T>> {
        self.inner.try_read()
    }

    /// Locks this `RwLock` with exclusive write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other writers or other readers
    /// currently have access to the lock.
    ///
    /// Returns an RAII guard which will drop the write access of this `RwLock`
    /// when dropped.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `RwLock` is poisoned. An
    /// `RwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will be returned when the lock is acquired.
    ///
    /// # Panics
    ///
    /// This function might panic when called if the lock is already held by the current thread.
    #[inline]
    pub fn write(&self) -> LockResult<RwLockWriteGuard<'_, T>> {
        if can_block() {
            self.inner.write()
        }
        else {
            loop {
                match self.inner.try_write() {
                    Ok(guard) => return Ok(guard),
                    Err(TryLockError::WouldBlock) => {},
                    Err(TryLockError::Poisoned(err)) => return Err(err)
                }
            }
        }
    }

    /// Attempts to lock this `RwLock` with exclusive write access.
    ///
    /// If the lock could not be acquired at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned which will release the lock when
    /// it is dropped.
    ///
    /// This function does not block.
    ///
    /// This function does not provide any guarantees with respect to the ordering
    /// of whether contentious readers or writers will acquire the lock first.
    ///
    /// # Errors
    ///
    /// This function will return the `Poisoned` error if the `RwLock` is
    /// poisoned. An `RwLock` is poisoned whenever a writer panics while holding
    /// an exclusive lock. `Poisoned` will only be returned if the lock would
    /// have otherwise been acquired.
    ///
    /// This function will return the `WouldBlock` error if the `RwLock` could
    /// not be acquired because it was already locked exclusively.
    #[inline]
    pub fn try_write(&self) -> TryLockResult<RwLockWriteGuard<'_, T>> {
        self.inner.try_write()
    }

    /// Determines whether the lock is poisoned.
    ///
    /// If another thread is active, the lock can still become poisoned at any
    /// time. You should not trust a `false` value for program correctness
    /// without additional synchronization.
    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.inner.is_poisoned()
    }

    /// Clear the poisoned state from a lock
    ///
    /// If the lock is poisoned, it will remain poisoned until this function is called. This allows
    /// recovering from a poisoned state and marking that it has recovered. For example, if the
    /// value is overwritten by a known-good value, then the mutex can be marked as un-poisoned. Or
    /// possibly, the value could be inspected to determine if it is in a consistent state, and if
    /// so the poison is removed.
    #[inline]
    #[cfg(feature = "mutex_unpoison")]
    pub fn clear_poison(&self) {
        self.inner.clear_poison();
    }

    /// Consumes this `RwLock`, returning the underlying data.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `RwLock` is poisoned. An
    /// `RwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will only be returned if the lock would have otherwise
    /// been acquired.
    pub fn into_inner(self) -> LockResult<T>
    where
        T: Sized,
    {
        self.inner.into_inner()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `RwLock` mutably, no actual locking needs to
    /// take place -- the mutable borrow statically guarantees no locks exist.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `RwLock` is poisoned. An
    /// `RwLock` is poisoned whenever a writer panics while holding an exclusive
    /// lock. An error will only be returned if the lock would have otherwise
    /// been acquired.
    pub fn get_mut(&mut self) -> LockResult<&mut T> {
        self.inner.get_mut()
    }
}

impl<T> From<T> for RwLock<T> {
    /// Creates a new instance of an `RwLock<T>` which is unlocked.
    /// This is equivalent to [`RwLock::new`].
    fn from(t: T) -> Self {
        RwLock::new(t)
    }
}

/// Initialization value for static [`Once`] values.
///
/// # Examples
///
/// ```
/// use std::sync::{Once, ONCE_INIT};
///
/// static START: Once = ONCE_INIT;
/// ```
#[deprecated(
    since = "1.38.0",
    note = "the `new` function is now preferred"
)]
pub const ONCE_INIT: Once = Once::new();

/// A synchronization primitive which can be used to run a one-time global
/// initialization. Useful for one-time initialization for FFI or related
/// functionality. This type can only be constructed with [`Once::new()`].
///
/// # Examples
///
/// ```
/// use std::sync::Once;
///
/// static START: Once = Once::new();
///
/// START.call_once(|| {
///     // run initialization here
/// });
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct Once {
    /// The backing lock.
    inner: std::sync::Once,
}

impl Once {
    /// No initialization has run yet, and no thread is currently using the Once.
    const INCOMPLETE: u32 = 0;
    /// Some thread has previously attempted to initialize the Once, but it panicked,
    /// so the Once is now poisoned. There are no other threads currently accessing
    /// this Once.
    const POISONED: u32 = 1;
    /// Some thread is currently attempting to run initialization. It may succeed,
    /// so all future threads need to wait for it to finish.
    const RUNNING: u32 = 2;
    /// Some thread is currently attempting to run initialization and there are threads
    /// waiting for it to finish.
    const QUEUED: u32 = 3;
    /// Initialization has completed and all future calls should finish immediately.
    const COMPLETE: u32 = 4; 

    /// Creates a new `Once` value.
    #[inline]
    #[must_use]
    pub const fn new() -> Once {
        Once { inner: std::sync::Once::new() }
    }

    /// Performs an initialization routine once and only once. The given closure
    /// will be executed if this is the first time `call_once` has been called,
    /// and otherwise the routine will *not* be invoked.
    ///
    /// This method will block the calling thread if another initialization
    /// routine is currently running.
    ///
    /// When this function returns, it is guaranteed that some initialization
    /// has run and completed (it might not be the closure specified). It is also
    /// guaranteed that any memory writes performed by the executed closure can
    /// be reliably observed by other threads at this point (there is a
    /// happens-before relation between the closure and code executing after the
    /// return).
    ///
    /// If the given closure recursively invokes `call_once` on the same [`Once`]
    /// instance, the exact behavior is not specified: allowed outcomes are
    /// a panic or a deadlock.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Once;
    ///
    /// static mut VAL: usize = 0;
    /// static INIT: Once = Once::new();
    ///
    /// // Accessing a `static mut` is unsafe much of the time, but if we do so
    /// // in a synchronized fashion (e.g., write once or read all) then we're
    /// // good to go!
    /// //
    /// // This function will only call `expensive_computation` once, and will
    /// // otherwise always return the value returned from the first invocation.
    /// fn get_cached_val() -> usize {
    ///     unsafe {
    ///         INIT.call_once(|| {
    ///             VAL = expensive_computation();
    ///         });
    ///         VAL
    ///     }
    /// }
    ///
    /// fn expensive_computation() -> usize {
    ///     // ...
    /// # 2
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// The closure `f` will only be executed once even if this is called
    /// concurrently amongst many threads. If that closure panics, however, then
    /// it will *poison* this [`Once`] instance, causing all future invocations of
    /// `call_once` to also panic.
    ///
    /// This is similar to [poisoning with mutexes][poison].
    ///
    /// [poison]: struct.Mutex.html#poisoning
    #[inline]
    #[track_caller]
    pub fn call_once<F>(&self, f: F)
    where
        F: FnOnce(),
    {
        if can_block() {
            self.inner.call_once(f);
        }
        else {
            let mut f = Some(f);
            self.call_spin(false, &mut |_| f.take().unwrap()());
        }
    }

    /// Performs the same function as [`call_once()`] except ignores poisoning.
    ///
    /// Unlike [`call_once()`], if this [`Once`] has been poisoned (i.e., a previous
    /// call to [`call_once()`] or [`call_once_force()`] caused a panic), calling
    /// [`call_once_force()`] will still invoke the closure `f` and will _not_
    /// result in an immediate panic. If `f` panics, the [`Once`] will remain
    /// in a poison state. If `f` does _not_ panic, the [`Once`] will no
    /// longer be in a poison state and all future calls to [`call_once()`] or
    /// [`call_once_force()`] will be no-ops.
    ///
    /// The closure `f` is yielded a [`std::sync::OnceState`] structure which can be used
    /// to query the poison status of the [`Once`].
    ///
    /// [`call_once()`]: Once::call_once
    /// [`call_once_force()`]: Once::call_once_force
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Once;
    /// use std::thread;
    ///
    /// static INIT: Once = Once::new();
    ///
    /// // poison the once
    /// let handle = thread::spawn(|| {
    ///     INIT.call_once(|| panic!());
    /// });
    /// assert!(handle.join().is_err());
    ///
    /// // poisoning propagates
    /// let handle = thread::spawn(|| {
    ///     INIT.call_once(|| {});
    /// });
    /// assert!(handle.join().is_err());
    ///
    /// // call_once_force will still run and reset the poisoned state
    /// INIT.call_once_force(|state| {
    ///     assert!(state.is_poisoned());
    /// });
    ///
    /// // once any success happens, we stop propagating the poison
    /// INIT.call_once(|| {});
    /// ```
    #[inline]
    pub fn call_once_force<F>(&self, f: F)
    where
        F: FnOnce(&std::sync::OnceState),
    {
        if can_block() {
            self.inner.call_once_force(f);
        }
        else {
            let mut f = Some(f);
            self.call_spin(true, &mut |p| f.take().unwrap()(p));
        }
    }

    /// Returns `true` if some [`call_once()`] call has completed
    /// successfully. Specifically, `is_completed` will return false in
    /// the following situations:
    ///   * [`call_once()`] was not called at all,
    ///   * [`call_once()`] was called, but has not yet completed,
    ///   * the [`Once`] instance is poisoned
    ///
    /// This function returning `false` does not mean that [`Once`] has not been
    /// executed. For example, it may have been executed in the time between
    /// when `is_completed` starts executing and when it returns, in which case
    /// the `false` return value would be stale (but still permissible).
    ///
    /// [`call_once()`]: Once::call_once
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Once;
    ///
    /// static INIT: Once = Once::new();
    ///
    /// assert_eq!(INIT.is_completed(), false);
    /// INIT.call_once(|| {
    ///     assert_eq!(INIT.is_completed(), false);
    /// });
    /// assert_eq!(INIT.is_completed(), true);
    /// ```
    ///
    /// ```
    /// use std::sync::Once;
    /// use std::thread;
    ///
    /// static INIT: Once = Once::new();
    ///
    /// assert_eq!(INIT.is_completed(), false);
    /// let handle = thread::spawn(|| {
    ///     INIT.call_once(|| panic!());
    /// });
    /// assert!(handle.join().is_err());
    /// assert_eq!(INIT.is_completed(), false);
    /// ```
    #[inline]
    pub fn is_completed(&self) -> bool {
        self.inner.is_completed()
    }

    /// Internally calls the function if the `Once` has not yet completed.
    #[cold]
    #[track_caller]
    fn call_spin(&self, ignore_poisoning: bool, f: &mut impl FnMut(&std::sync::OnceState)) {
        unsafe {
            let mut state = self.state().load(Ordering::Acquire);
            loop {
                match state {
                    Self::POISONED if !ignore_poisoning => {
                        // Panic to propagate the poison.
                        panic!("Once instance has previously been poisoned");
                    }
                    Self::INCOMPLETE | Self::POISONED => {
                        // Try to register the current thread as the one running.
                        if let Err(new) =
                            self.state().compare_exchange_weak(state, Self::RUNNING, Ordering::Acquire, Ordering::Acquire)
                        {
                            state = new;
                            continue;
                        }
    
                        // `waiter_queue` will manage other waiting threads, and
                        // wake them up on drop.
                        let mut waiter_queue =
                            CompletionGuard { state: self.state(), set_state_on_drop_to: Self::POISONED };
                        // Run the function, letting it know if we're poisoned or not.
                        let f_state = OnceState {
                            poisoned: state == Self::POISONED,
                            set_state_to: Cell::new(Self::COMPLETE),
                        };
                        f(transmute(&f_state));
                        waiter_queue.set_state_on_drop_to = f_state.set_state_to.get();
                        drop(waiter_queue);
                        return;
                    }
                    Self::RUNNING | Self::QUEUED => {
                        // Set the state to QUEUED if it is not already.
                        if state == Self::RUNNING {
                            if let Err(new) = self.state().compare_exchange_weak(Self::RUNNING, Self::QUEUED, Ordering::Relaxed, Ordering::Acquire) {
                                state = new;
                                continue;
                            }
                        }
    
                        state = self.state().load(Ordering::Acquire);
                    }
                    Self::COMPLETE => return,
                    _ => unreachable!("state is never set to invalid values"),
                }
            }
        }
    }

    /// Gets a reference to the inner atomic state backing this once.
    fn state(&self) -> &AtomicU32 {
        unsafe {
            transmute(self)
        }
    }
}

/// Ensures that the proper state of a value is set when exiting scope.
struct CompletionGuard<'a> {
    /// The state to update.
    state: &'a AtomicU32,
    /// The state type to set on drop.
    set_state_on_drop_to: u32,
}

impl<'a> Drop for CompletionGuard<'a> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            // Use release ordering to propagate changes to all threads checking
            // up on the Once. `memory_atomic_notify` does its own synchronization, hence
            // we do not need `AcqRel`.
            if self.state.swap(self.set_state_on_drop_to, Ordering::Release) == Once::QUEUED {
                let view = Int32Array::view_mut_raw(self.state as *const _ as *mut _, 1);
                let _ = Atomics::notify(&view, 0);
            }
        }
    }
}

/// Holds the state for querying the poison parameter of a [`Once`].
#[allow(dead_code)]
struct OnceState {
    /// Whether the [`Once`] is poisoned.
    poisoned: bool,
    /// The state that should be used after the closure completes.
    set_state_to: Cell<u32>,
}

/// A synchronization primitive which can be written to only once.
///
/// This type is a thread-safe [`OnceCell`], and can be used in statics.
///
/// [`OnceCell`]: crate::cell::OnceCell
///
/// # Examples
///
/// Using `OnceCell` to store a function’s previously computed value (a.k.a.
/// ‘lazy static’ or ‘memoizing’):
///
/// ```
/// use std::sync::OnceLock;
///
/// struct DeepThought {
///     answer: String,
/// }
///
/// impl DeepThought {
/// #   fn great_question() -> String {
/// #       "42".to_string()
/// #   }
/// #
///     fn new() -> Self {
///         Self {
///             // M3 Ultra takes about 16 million years in --release config
///             answer: Self::great_question(),
///         }
///     }
/// }
///
/// fn computation() -> &'static DeepThought {
///     // n.b. static items do not call [`Drop`] on program termination, so if
///     // [`DeepThought`] impls Drop, that will not be used for this instance.
///     static COMPUTATION: OnceLock<DeepThought> = OnceLock::new();
///     COMPUTATION.get_or_init(|| DeepThought::new())
/// }
///
/// // The `DeepThought` is built, stored in the `OnceLock`, and returned.
/// let _ = computation().answer;
/// // The `DeepThought` is retrieved from the `OnceLock` and returned.
/// let _ = computation().answer;
/// ```
///
/// Writing to a `OnceLock` from a separate thread:
///
/// ```
/// use std::sync::OnceLock;
///
/// static CELL: OnceLock<usize> = OnceLock::new();
///
/// // `OnceLock` has not been written to yet.
/// assert!(CELL.get().is_none());
///
/// // Spawn a thread and write to `OnceLock`.
/// std::thread::spawn(|| {
///     let value = CELL.get_or_init(|| 12345);
///     assert_eq!(value, &12345);
/// })
/// .join()
/// .unwrap();
///
/// // `OnceLock` now contains the value.
/// assert_eq!(
///     CELL.get(),
///     Some(&12345),
/// );
/// ```
#[repr(C)]
pub struct OnceLock<T> {
    once: Once,
    // Whether or not the value is initialized is tracked by `once.is_completed()`.
    value: UnsafeCell<MaybeUninit<T>>,
    /// `PhantomData` to make sure dropck understands we're dropping T in our Drop impl.
    ///
    /// ```compile_fail,E0597
    /// use std::sync::OnceLock;
    ///
    /// struct A<'a>(&'a str);
    ///
    /// impl<'a> Drop for A<'a> {
    ///     fn drop(&mut self) {}
    /// }
    ///
    /// let cell = OnceLock::new();
    /// {
    ///     let s = String::new();
    ///     let _ = cell.set(A(&s));
    /// }
    /// ```
    _marker: PhantomData<T>,
}

impl<T> OnceLock<T> {
    /// Creates a new empty cell.
    #[inline]
    #[must_use]
    pub const fn new() -> OnceLock<T> {
        OnceLock {
            once: Once::new(),
            value: UnsafeCell::new(MaybeUninit::uninit()),
            _marker: PhantomData,
        }
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty, or being initialized. This
    /// method never blocks.
    #[inline]
    pub fn get(&self) -> Option<&T> {
        if self.is_initialized() {
            // Safe b/c checked is_initialized
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    /// Gets the mutable reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty. This method never blocks.
    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.is_initialized() {
            // Safe b/c checked is_initialized and we have a unique access
            Some(unsafe { self.get_unchecked_mut() })
        } else {
            None
        }
    }

    /// Sets the contents of this cell to `value`.
    ///
    /// May block if another thread is currently attempting to initialize the cell. The cell is
    /// guaranteed to contain a value when set returns, though not necessarily the one provided.
    ///
    /// Returns `Ok(())` if the cell's value was set by this call.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::OnceLock;
    ///
    /// static CELL: OnceLock<i32> = OnceLock::new();
    ///
    /// fn main() {
    ///     assert!(CELL.get().is_none());
    ///
    ///     std::thread::spawn(|| {
    ///         assert_eq!(CELL.set(92), Ok(()));
    ///     }).join().unwrap();
    ///
    ///     assert_eq!(CELL.set(62), Err(62));
    ///     assert_eq!(CELL.get(), Some(&92));
    /// }
    /// ```
    #[inline]
    pub fn set(&self, value: T) -> Result<(), T> {
        match self.try_insert(value) {
            Ok(_) => Ok(()),
            Err((_, value)) => Err(value),
        }
    }

    /// Sets the contents of this cell to `value` if the cell was empty, then
    /// returns a reference to it.
    ///
    /// May block if another thread is currently attempting to initialize the cell. The cell is
    /// guaranteed to contain a value when set returns, though not necessarily the one provided.
    ///
    /// Returns `Ok(&value)` if the cell was empty and `Err(&current_value, value)` if it was full.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(once_cell_try_insert)]
    ///
    /// use std::sync::OnceLock;
    ///
    /// static CELL: OnceLock<i32> = OnceLock::new();
    ///
    /// fn main() {
    ///     assert!(CELL.get().is_none());
    ///
    ///     std::thread::spawn(|| {
    ///         assert_eq!(CELL.try_insert(92), Ok(&92));
    ///     }).join().unwrap();
    ///
    ///     assert_eq!(CELL.try_insert(62), Err((&92, 62)));
    ///     assert_eq!(CELL.get(), Some(&92));
    /// }
    /// ```
    #[inline]
    #[cfg(feature = "once_cell_try_insert")]
    pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
        let mut value = Some(value);
        let res = self.get_or_init(|| value.take().unwrap());
        match value {
            None => Ok(res),
            Some(value) => Err((res, value)),
        }
    }

    /// Sets the contents of this cell to `value` if the cell was empty, then
    /// returns a reference to it.
    ///
    /// May block if another thread is currently attempting to initialize the cell. The cell is
    /// guaranteed to contain a value when set returns, though not necessarily the one provided.
    ///
    /// Returns `Ok(&value)` if the cell was empty and `Err(&current_value, value)` if it was full.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(once_cell_try_insert)]
    ///
    /// use std::sync::OnceLock;
    ///
    /// static CELL: OnceLock<i32> = OnceLock::new();
    ///
    /// fn main() {
    ///     assert!(CELL.get().is_none());
    ///
    ///     std::thread::spawn(|| {
    ///         assert_eq!(CELL.try_insert(92), Ok(&92));
    ///     }).join().unwrap();
    ///
    ///     assert_eq!(CELL.try_insert(62), Err((&92, 62)));
    ///     assert_eq!(CELL.get(), Some(&92));
    /// }
    /// ```
    #[inline]
    pub fn try_insert(&self, value: T) -> Result<&T, (&T, T)> {
        let mut value = Some(value);
        let res = self.get_or_init(|| value.take().unwrap());
        match value {
            None => Ok(res),
            Some(value) => Err((res, value)),
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if the cell
    /// was empty.
    ///
    /// Many threads may call `get_or_init` concurrently with different
    /// initializing functions, but it is guaranteed that only one function
    /// will be executed.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. The
    /// exact outcome is unspecified. Current implementation deadlocks, but
    /// this may be changed to a panic in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::OnceLock;
    ///
    /// let cell = OnceLock::new();
    /// let value = cell.get_or_init(|| 92);
    /// assert_eq!(value, &92);
    /// let value = cell.get_or_init(|| unreachable!());
    /// assert_eq!(value, &92);
    /// ```
    #[inline]
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        unsafe {
            // Fast path check
            // NOTE: We need to perform an acquire on the state in this method
            // in order to correctly synchronize `LazyLock::force`. This is
            // currently done by calling `self.get()`, which in turn calls
            // `self.is_initialized()`, which in turn performs the acquire.
            if let Some(value) = self.get() {
                return value;
            }
    
            if self.initialize(|| Ok::<T, ()>(f())).is_err() {
                unreachable_unchecked();
            }
    
            debug_assert!(self.is_initialized());
    
            // SAFETY: The inner value has been initialized
            self.get_unchecked()
        }
    }

    /// Gets the contents of the cell, initializing it with `f` if
    /// the cell was empty. If the cell was empty and `f` failed, an
    /// error is returned.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and
    /// the cell remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`.
    /// The exact outcome is unspecified. Current implementation
    /// deadlocks, but this may be changed to a panic in the future.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(once_cell_try)]
    ///
    /// use std::sync::OnceLock;
    ///
    /// let cell = OnceLock::new();
    /// assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
    /// assert!(cell.get().is_none());
    /// let value = cell.get_or_try_init(|| -> Result<i32, ()> {
    ///     Ok(92)
    /// });
    /// assert_eq!(value, Ok(&92));
    /// assert_eq!(cell.get(), Some(&92))
    /// ```
    #[inline]
    #[cfg(feature = "once_cell_try")]
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        // Fast path check
        // NOTE: We need to perform an acquire on the state in this method
        // in order to correctly synchronize `LazyLock::force`. This is
        // currently done by calling `self.get()`, which in turn calls
        // `self.is_initialized()`, which in turn performs the acquire.
        if let Some(value) = self.get() {
            return Ok(value);
        }
        self.initialize(f)?;

        debug_assert!(self.is_initialized());

        // SAFETY: The inner value has been initialized
        Ok(unsafe { self.get_unchecked() })
    }

    /// Consumes the `OnceLock`, returning the wrapped value. Returns
    /// `None` if the cell was empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::OnceLock;
    ///
    /// let cell: OnceLock<String> = OnceLock::new();
    /// assert_eq!(cell.into_inner(), None);
    ///
    /// let cell = OnceLock::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.into_inner(), Some("hello".to_string()));
    /// ```
    #[inline]
    pub fn into_inner(mut self) -> Option<T> {
        self.take()
    }

    /// Takes the value out of this `OnceLock`, moving it back to an uninitialized state.
    ///
    /// Has no effect and returns `None` if the `OnceLock` hasn't been initialized.
    ///
    /// Safety is guaranteed by requiring a mutable reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::OnceLock;
    ///
    /// let mut cell: OnceLock<String> = OnceLock::new();
    /// assert_eq!(cell.take(), None);
    ///
    /// let mut cell = OnceLock::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.take(), Some("hello".to_string()));
    /// assert_eq!(cell.get(), None);
    /// ```
    #[inline]
    pub fn take(&mut self) -> Option<T> {
        if self.is_initialized() {
            self.once = Once::new();
            // SAFETY: `self.value` is initialized and contains a valid `T`.
            // `self.once` is reset, so `is_initialized()` will be false again
            // which prevents the value from being read twice.
            unsafe { Some((&mut *self.value.get()).assume_init_read()) }
        } else {
            None
        }
    }

    #[inline]
    fn is_initialized(&self) -> bool {
        self.once.is_completed()
    }

    #[cold]
    fn initialize<F, E>(&self, f: F) -> Result<(), E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        unsafe {
            let mut res: Result<(), E> = Ok(());
            let slot = &self.value;
    
            // Ignore poisoning from other threads
            // If another thread panics, then we'll be able to run our closure
            self.once.call_once_force(|p| {
                match f() {
                    Ok(value) => {
                        (&mut *slot.get()).write(value);
                    }
                    Err(e) => {
                        res = Err(e);
                        transmute::<_, &OnceState>(p).set_state_to.set(Once::POISONED);
                    }
                }
            });
            res
        }
    }

    /// # Safety
    ///
    /// The value must be initialized
    #[inline]
    unsafe fn get_unchecked(&self) -> &T {
        debug_assert!(self.is_initialized());
        (&*self.value.get()).assume_init_ref()
    }

    /// # Safety
    ///
    /// The value must be initialized
    #[inline]
    unsafe fn get_unchecked_mut(&mut self) -> &mut T {
        debug_assert!(self.is_initialized());
        (&mut *self.value.get()).assume_init_mut()
    }
}

// Why do we need `T: Send`?
// Thread A creates a `OnceLock` and shares it with
// scoped thread B, which fills the cell, which is
// then destroyed by A. That is, destructor observes
// a sent value.
unsafe impl<T: Sync + Send> Sync for OnceLock<T> {}
unsafe impl<T: Send> Send for OnceLock<T> {}

impl<T: RefUnwindSafe + UnwindSafe> RefUnwindSafe for OnceLock<T> {}
impl<T: UnwindSafe> UnwindSafe for OnceLock<T> {}

impl<T> Default for OnceLock<T> {
    /// Creates a new empty cell.
    ///
    /// # Example
    ///
    /// ```
    /// use std::sync::OnceLock;
    ///
    /// fn main() {
    ///     assert_eq!(OnceLock::<()>::new(), OnceLock::default());
    /// }
    /// ```
    #[inline]
    fn default() -> OnceLock<T> {
        OnceLock::new()
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for OnceLock<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut d = f.debug_tuple("OnceLock");
        match self.get() {
            Some(v) => d.field(v),
            None => d.field(&format_args!("<uninit>")),
        };
        d.finish()
    }
}

impl<T: Clone> Clone for OnceLock<T> {
    #[inline]
    fn clone(&self) -> OnceLock<T> {
        let cell = Self::new();
        if let Some(value) = self.get() {
            match cell.set(value.clone()) {
                Ok(()) => (),
                Err(_) => unreachable!(),
            }
        }
        cell
    }
}

impl<T> From<T> for OnceLock<T> {
    /// Create a new cell with its contents set to `value`.
    ///
    /// # Example
    ///
    /// ```
    /// use std::sync::OnceLock;
    ///
    /// # fn main() -> Result<(), i32> {
    /// let a = OnceLock::from(3);
    /// let b = OnceLock::new();
    /// b.set(3)?;
    /// assert_eq!(a, b);
    /// Ok(())
    /// # }
    /// ```
    #[inline]
    fn from(value: T) -> Self {
        let cell = Self::new();
        match cell.set(value) {
            Ok(()) => cell,
            Err(_) => unreachable!(),
        }
    }
}

impl<T: PartialEq> PartialEq for OnceLock<T> {
    #[inline]
    fn eq(&self, other: &OnceLock<T>) -> bool {
        self.get() == other.get()
    }
}

impl<T: Eq> Eq for OnceLock<T> {}

impl<T> Drop for OnceLock<T> {
    #[inline]
    fn drop(&mut self) {
        if self.is_initialized() {
            unsafe { (&mut *self.value.get()).assume_init_drop() };
        }
    }
}