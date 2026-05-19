// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

// ======== Extern specs ========

mod flux_specs {
    #[flux_rs::extern_spec]
    impl<T> [T] {
        #[flux_rs::sig(fn(&mut [T][@len], usize[@mid]) -> (&mut [T][mid], &mut [T][len - mid]))]
        fn split_at_mut(v: &mut [T], mid: usize) -> (&mut [T], &mut [T]);
    }

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
#[flux_rs::refined_by(len: int, get: int -> T)]
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
}

#[flux_rs::trusted]
impl<T: Copy> core::ops::Index<usize> for FluxSlice<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        &self.0[index]
    }
}

#[flux_rs::trusted]
impl<T: Copy> core::ops::IndexMut<usize> for FluxSlice<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.0[index]
    }
}

// ===== RingBuffer =====

#[flux_rs::refined_by(ring: FluxSlice<Option<T>>, hd: int, tl: int)]
pub struct RingBuffer<'a, T: Copy + 'a> {
    #[flux_rs::field({&mut FluxSlice<Option<T>>[ring] | ring.len > 0})]
    ring: &'a mut FluxSlice<Option<T>>,
    #[flux_rs::field({usize[hd] | hd < ring.len})]
    head: usize,
    #[flux_rs::field({usize[tl] | tl < ring.len})]
    tail: usize,
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    #[flux_rs::sig(fn({&mut FluxSlice<Option<T>>[@ring] | ring.len > 0}) -> RingBuffer<T>[ring, 0, 0])]
    pub fn new(ring: &'a mut FluxSlice<Option<T>>) -> RingBuffer<'a, T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
        }
    }

    pub fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    fn len(&self) -> usize {
        if self.tail > self.head {
            self.tail - self.head
        } else if self.tail < self.head {
            (self.ring.len() - self.head) + self.tail
        } else {
            0
        }
    }

    fn is_valid(&self, index: usize) -> bool {
        let capacity = self.ring.len();
        let position_in_ring = (index + capacity - self.head) % capacity;
        position_in_ring < self.len()
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize{index < s.ring_len}) -> Option<T>)]
    fn get_internal(&self, index: usize) -> Option<T> {
        if !self.is_valid(index) {
            None
        } else {
            self.ring[index]
        }
    }

    #[flux_rs::sig(fn(self: &mut RingBuffer<T>, val: T) -> bool ensures self: RingBuffer<T>)]
    pub fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            false
        } else {
            self.ring[self.tail] = Some(val);
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }

    #[flux_rs::sig(fn(self: &mut RingBuffer<T>) -> Option<T> ensures self: RingBuffer<T>)]
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
