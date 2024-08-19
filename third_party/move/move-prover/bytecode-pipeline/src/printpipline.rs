// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;

use move_model::{model::FunctionEnv};
use move_stackless_bytecode::{
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
};

pub struct PrintProcessor {}
//update
impl PrintProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {})
    }
}

impl FunctionTargetProcessor for PrintProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if fun_env.is_native() {
            return data;
        }

        let mut builder = FunctionDataBuilder::new(fun_env, data);

        // Transform bytecode.
        for bc in std::mem::take(&mut builder.data.code) {
            use Bytecode::*;
            use Operation::*;
            match bc {
                Call(attr_id, dests, op, srcs, aa) => match op {
                Havoc(_) => {
                    print!("{} print\n",dests[0]);
                    builder.emit(Call(attr_id, dests, op, srcs, aa));
                },
                 _ => builder.emit(Call(attr_id, dests, op, srcs, aa))
                },

                _ => builder.emit(bc)
            }
        }

        builder.data
    }

    fn name(&self) -> String {
        "mut_ref_instrumentation".to_string()
    }
}
