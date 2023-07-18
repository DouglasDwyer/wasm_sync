use std::mem::*;
use std::sync::*;
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