// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

flux_rs::defs! {
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

    fn rb_is_valid(rb: RingBuffer, index: int) -> bool {
        ((index + rb.ring.len - rb.hd) % rb.ring.len) < rb_len(rb)
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
#[flux_rs::refined_by(len: int, hdl get: int -> bool)]
#[repr(transparent)]
pub struct FluxSlice<T>([T]);

impl<T> FluxSlice<T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut [T][@n]) -> &mut FluxSlice<T>{fs: fs.len == n})]
    pub fn from_mut(slice: &mut [T]) -> &mut FluxSlice<T> {
        // SAFETY: FluxSlice<T> is repr(transparent) over [T]
        unsafe { &mut *(slice as *mut [T] as *mut FluxSlice<T>) }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f], index: usize{index < n}) -> T)]
    pub fn get(&self, index: usize) -> T
    where
        T: Copy,
    {
        self.0[index]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &strg FluxSlice<T>[@n, @f], index: usize{index < n}, val: T)
        ensures self: FluxSlice<T>[n, |j| j == index || f(j)]
    )]
    pub fn set(&mut self, index: usize, val: T) {
        self.0[index] = val;
    }
}

// ===== RingBuffer =====

#[flux_rs::refined_by(ring: FluxSlice, hd: int, tl: int)]
pub struct RingBuffer<'a, T: Copy + 'a> {
    #[flux_rs::field({&mut FluxSlice<T>[ring] | ring.len > 0})]
    ring: &'a mut FluxSlice<T>,
    #[flux_rs::field({usize[hd] | hd < ring.len})]
    head: usize,
    #[flux_rs::field({usize[tl] | tl < ring.len})]
    tail: usize,
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    // Done
    #[flux_rs::sig(fn({&mut FluxSlice<T>[@ring] | ring.len > 0}) -> RingBuffer<T>[ring, 0, 0])]
    pub fn new(ring: &'a mut FluxSlice<T>) -> RingBuffer<'a, T> {
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
    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize) -> bool[rb_is_valid(s, index)])]
    fn is_valid(&self, index: usize) -> bool {
        let capacity = self.ring.len();
        let position_in_ring = (index + capacity - self.head) % capacity;
        position_in_ring < self.len()
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize{index < s.ring.len}) -> Option<T>)]
    fn get_internal(&self, index: usize) -> Option<T> {
        if !self.is_valid(index) {
            None
        } else {
            Some(self.ring.get(index))
        }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>[@s], val: T) -> bool[!rb_is_full(s)]
        ensures self: RingBuffer<T>[
            { len: s.ring.len, get: s.ring.get },
            s.hd,
            if rb_is_full(s) { s.tl } else { (s.tl + 1) % s.ring.len }
        ]
    )]
    pub fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            false
        } else {
            self.ring.set(self.tail, val);
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }

    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s]) -> Option<T> ensures self: RingBuffer<T>)]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.head != self.tail {
            let val = self.get_internal(self.head);
            self.head = (self.head + 1) % self.ring.len();
            val
        } else {
            None
        }
    }
}
