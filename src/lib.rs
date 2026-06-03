// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

flux_rs::defs! {
    fn set_emp() -> Set<int> {
        set_empty(0)
    }

    fn set_add(x: int, s: Set<int>) -> Set<int> {
        set_union(set_singleton(x), s)
    }

    fn set_del(x: int, s: Set<int>) -> Set<int> {
        set_difference(s, set_singleton(x))
    }

    fn rb_len(rb: RingBuffer) -> int {
        if rb.tl > rb.hd { rb.tl - rb.hd }
        else if rb.tl < rb.hd { rb.ring.len - rb.hd + rb.tl }
        else { 0 }
    }

    fn rb_is_full(rb: RingBuffer) -> bool {
        rb.hd == (rb.tl + 1) % rb.ring.len
    }

    fn rb_is_empty(rb: RingBuffer) -> bool {
        rb.hd == rb.tl
    }

    fn rb_next(rb: RingBuffer, index: int) -> int {
        (index + 1) % rb.ring.len
    }

    fn rb_is_valid(rb: RingBuffer, index: int) -> bool {
        ((index + rb.ring.len - rb.hd) % rb.ring.len) < rb_len(rb)
    }

    fn rb_valid_iff_init(rb: RingBuffer, index: int) -> bool {
        rb_is_valid(rb, index) == set_is_in(index, rb.ring.inits)
    }
}

// ======== Extern specs ========

mod flux_specs {
    #[flux_rs::extern_spec]
    #[flux_rs::refined_by(b: bool)]
    enum Option<T> {
        #[variant(Option<T>[false])]
        None,
        #[variant({T} -> Option<T>[true])]
        Some(T),
    }
}

// ===== FluxSlice =====

#[flux_rs::opaque]
#[flux_rs::refined_by(len: int, inits: Set<int>)]
#[repr(transparent)]
pub struct FluxSlice<'a, T>(&'a mut [T]);
    
impl<'a, T> FluxSlice<'a, T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut [T][@n]) -> &mut FluxSlice<T>{fs: fs.len == n})]
    pub fn from_mut(slice: &'a mut [T]) -> &mut FluxSlice<'a, T> {
        // SAFETY: FluxSlice<T> is repr(transparent) over [T]
        unsafe { &mut *(slice as *mut [T] as *mut FluxSlice<'a, T>) }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @s]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &mut FluxSlice<T>[@n, @s], index: RbIndex{index < n})
        -> T
        requires set_is_in(index, s)
        ensures self: FluxSlice<T>[n, set_del(index, s)]
    )]
    pub fn take(&mut self, index: RbIndex) -> T
    where
        T: Copy,
    {
        self.0[index]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &mut FluxSlice<T>[@n, @s], index: RbIndex{index < n}, val: T)
        requires !set_is_in(index, s)
        ensures self: FluxSlice<T>[n, set_add(index, s)]
    )]
    pub fn set(&mut self, index: RbIndex, val: T) {
        self.0[index] = val;
    }
}


// ===== RingBuffer =====
type RbIndex = usize;
#[flux_rs::refined_by(ring: FluxSlice, hd: int, tl: int)]

// #[flux_rs::invariant(hd == tl => ring.inits == set_emp())] // when Rb is empty, inits is empty
// #[flux_rs::invariant(hd != tl => set_is_in(hd, ring.inits))] // when Rb is not empty, head is in the set
// #[flux_rs::invariant(!set_is_in(tl, ring.inits))] // tail is never in the set
pub struct RingBuffer<'a, T: Copy> {
    #[flux_rs::field({FluxSlice<T>[ring] | ring.len > 0})]
    ring: FluxSlice<'a, T>,
    #[flux_rs::field({RbIndex[hd] | hd < ring.len})]
    head: RbIndex,
    #[flux_rs::field({RbIndex[tl] | tl < ring.len})]
    tail: RbIndex,
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    // Done
    #[flux_rs::sig(fn({FluxSlice<T>[@ring] | ring.len > 0 && ring.inits == set_emp()}) -> RingBuffer<T>[ring, 0, 0])]
    pub fn new(ring: FluxSlice<T>) -> RingBuffer<T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
        }
    }

    // Done
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[rb_is_full(s)])]
    pub fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    // Done
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[!rb_is_empty(s)])]
    fn has_elements(&self) -> bool {
        self.head != self.tail
    }

    // Done
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> usize[rb_len(s)])]
    fn len(&self) -> usize {
        if self.tail > self.head {
            self.tail - self.head
        } else if self.tail < self.head {
            (self.ring.len() - self.head) + self.tail
        } else {
            0
        }
    }

    // Done
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: RbIndex) -> bool[rb_is_valid(s, index)])]
    fn is_valid(&self, index: RbIndex) -> bool {
        let capacity = self.ring.len();
        let position_in_ring = (index + capacity - self.head) % capacity;
        position_in_ring < self.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: RbIndex)
        ensures rb_valid_iff_init(s, index))]
    fn assume_valid_iff_init(&self, index: RbIndex) {}

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: RbIndex)
        requires rb_valid_iff_init(s, index))]
    fn assert_valid_iff_init(&self, index: RbIndex) {
    }

    // #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s], val: T) -> bool ensures self: RingBuffer<T>)]
    pub fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            false
        } else {
            self.assume_valid_iff_init(self.tail);
            self.ring.set(self.tail, val);
            self.assert_valid_iff_init((self.tail + 1) % self.ring.len());
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }

    // #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s]) -> Option<T> ensures self: RingBuffer<T>)]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.has_elements() {
            self.assume_valid_iff_init(self.head);
            let val = self.ring.take(self.head);
            self.assert_valid_iff_init((self.head + 1) % self.ring.len());
            self.head = (self.head + 1) % self.ring.len();
            Some(val)
        } else {
            None
        }
    }
}



// TODO: top-level invariant
// index < s.ring.len && is_valid(index) => s.ring.init(index)
// maybe implement something based on the fact that empty => hd is valid?


// TODO: more complex methods
// TODO: back to MaybeUninit
// TODO: remove FluxSlice