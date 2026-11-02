/*
 * Copyright 2018 The Starlark in Rust Authors.
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Detect recursion when doing `repr` or `to_json`.

use std::cell::Cell;

use crate::collections::SmallSet;
use crate::hint::unlikely;
use crate::values::Value;
use crate::values::layout::pointer::RawPointer;

/// Pop the stack on drop.
pub(crate) struct ReprStackGuard;

/// Pop the stack on drop.
pub(crate) struct JsonStackGuard;

impl Drop for ReprStackGuard {
    fn drop(&mut self) {
        REPR_STACK.with(|repr_stack| {
            let mut stack = Cell::take(repr_stack);
            let popped = stack.pop();
            debug_assert!(popped.is_some());
            repr_stack.set(stack);
        })
    }
}

impl Drop for JsonStackGuard {
    fn drop(&mut self) {
        JSON_STACK.with(|json_stack| {
            let mut stack = Cell::take(json_stack);
            let popped = stack.pop();
            debug_assert!(popped.is_some());
            json_stack.set(stack);
        })
    }
}

/// Returned when `repr` is called recursively and a cycle is detected.
pub(crate) struct ReprCycle;

/// Why a value cannot be serialized to JSON.
pub(crate) enum JsonStackError {
    /// The value contains itself.
    Cycle,
    /// The value is nested more than [`JSON_ENCODE_DEPTH_LIMIT`] deep.
    TooDeep,
}

/// Nesting `to_json` allows, counting every value from the outermost to the innermost, so a deeply
/// nested value returns an error rather than overflowing the native stack.
///
/// Each level costs 10-30 KiB of stack in `erased_serde` and `serde_json` frames: a debug build
/// overflows a 1 MiB stack (the Windows main thread) at about 60 levels. A fixed limit, rather than
/// asking how much stack is left, gives the same answer on every platform, build and thread.
pub(crate) const JSON_ENCODE_DEPTH_LIMIT: usize = 32;

thread_local! {
    static REPR_STACK: Cell<SmallSet<RawPointer>> = const { Cell::new(SmallSet::new()) };
}

thread_local! {
    static JSON_STACK: Cell<SmallSet<RawPointer>> = const { Cell::new(SmallSet::new()) };
}

/// Push a value to the stack, return error if it is already on the stack.
pub(crate) fn repr_stack_push(value: Value) -> Result<ReprStackGuard, ReprCycle> {
    REPR_STACK.with(|repr_stack| {
        let mut stack = Cell::take(repr_stack);
        let res = if unlikely(!stack.insert(value.ptr_value())) {
            Err(ReprCycle)
        } else {
            Ok(ReprStackGuard)
        };
        repr_stack.set(stack);
        res
    })
}

/// Push a value to the stack, return error if it is already on the stack, or if the stack is
/// already [`JSON_ENCODE_DEPTH_LIMIT`] deep.
pub(crate) fn json_stack_push(value: Value) -> Result<JsonStackGuard, JsonStackError> {
    JSON_STACK.with(|json_stack| {
        let mut stack = Cell::take(json_stack);
        let res = if unlikely(stack.len() >= JSON_ENCODE_DEPTH_LIMIT) {
            Err(JsonStackError::TooDeep)
        } else if unlikely(!stack.insert(value.ptr_value())) {
            Err(JsonStackError::Cycle)
        } else {
            Ok(JsonStackGuard)
        };
        json_stack.set(stack);
        res
    })
}
