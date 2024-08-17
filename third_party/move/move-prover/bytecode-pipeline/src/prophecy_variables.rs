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

pub struct FutureWriteBackProcessor {}
//update
impl FutureWriteBackProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self {})
    }
}

impl FunctionTargetProcessor for FutureWriteBackProcessor {
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
                BorrowField(mid, sid, type_actuals, offset) => {
                    //havoc a temp
                    //type should be the subfield being borrowed.
                    let (temp_i, tempexp) = builder.emit_let_havoc(builder.data
                        .local_types
                        .get(dests[0])
                        .expect("local variable")
                        .clone());
                    print!("{}\n",temp_i.to_string());

                    //borrowField
                    builder.emit(Call(
                        attr_id,
                        dests,
                        BorrowFieldProphecy(mid, sid, type_actuals, offset, temp_i),
                        srcs,
                        aa,
                    ));
                    /*
                    //write back temp
                    builder.emit(Call(
                        attr_id,
                        dests,
                        WriteBack(srcs[0], ),
                        srcs,
                        aa
                    ));*/
                },
                /*WriteBack(node, edge) => {
                    self.builder.emit(Call(
                        attr_id,
                        dests,
                        fullfilled(node, edge),
                        srcs,
                        aa,
                    ));
                    WriteBack(node.instantiate(params), edge.instantiate(params))
                },*/
                 _ => builder.emit(Call(attr_id, dests, op, srcs, aa))
                },

                _ => builder.emit(bc)
            }
        }

        let mut builder2 = FunctionDataBuilder::new(fun_env, builder.data);
        for bc in std::mem::take(&mut builder2.data.code) {
            use Bytecode::*;
            use Operation::*;
            match bc {
                Call(attr_id, dests, op, srcs, aa) => match op {
                Havoc(..) => {
                    print!("{}", dests[0]);
                    builder2.emit(Call(attr_id, dests, op, srcs, aa));
                }
                 _ => builder2.emit(Call(attr_id, dests, op, srcs, aa))
                },

                _ => builder2.emit(bc)
            }
        }
        builder2.data
    }

    fn name(&self) -> String {
        "mut_ref_instrumentation".to_string()
    }
}
