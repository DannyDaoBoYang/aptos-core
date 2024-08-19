// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{any::Any, io::Read};

use move_model::{model::FunctionEnv, ty::Type};
use move_stackless_bytecode::{
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
};
use move_model::exp_generator::ExpGenerator;
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

                    //idea
                    //1. read the value
                    //2. have a temp variable borrows this field, writes to it, then dies
                    //3. the actual borrowprophecy happens

                    //havoc a temp
                    //type should be the subfield being borrowed.
                    let (temp_i, tempexp) = builder.emit_let_havoc(builder.data
                        .local_types
                        .get(dests[0])
                        .expect("local variable")
                        .clone());
                    let mutsrc = &mut srcs.clone();
                    mutsrc.push(temp_i);
                    let type1 = builder.data
                    .local_types
                    .get(dests[0]).expect("local variable")
                    .clone();

                    let new_dests1 = builder.add_local(type1.clone());
                    let (new_dests2, tempexp2) = builder.emit_let_skip_reference(tempexp.clone()); //original val
                    let (new_dests3, tempexp3) = builder.emit_let_skip_reference(tempexp.clone()); //original val
                    builder.emit(Call(
                        attr_id,
                        [new_dests1].to_vec(),
                        BorrowField(mid, sid, type_actuals.clone(), offset),
                        srcs.clone(),
                        aa.clone(),
                    ));
                    //save orignal to temp2
                    builder.emit(Call(
                        attr_id,
                        [new_dests2].to_vec(),//temp dest
                        ReadRef,
                        [new_dests1].to_vec(),
                        aa.clone(),
                    ));
                    //write dereference havoc to temp1
                    builder.emit(Call(
                        attr_id,
                        [new_dests3].to_vec(),//temp dest
                        ReadRef,
                        [temp_i].to_vec(),
                        aa.clone(),
                    ));

                    builder.emit(Call(
                        attr_id,
                        [].to_vec(),//temp dest
                        WriteRef,
                        [new_dests1,new_dests3].to_vec(),
                        aa.clone(),
                    ));

                    //release
                    builder.emit(Call(
                        attr_id,
                        [].to_vec(),
                        Release,
                        [new_dests1].to_vec(),
                        aa.clone(),
                    ));
                    //borrowFieldProphecy

                    builder.emit(Call(
                        attr_id,
                        dests.clone(),
                        BorrowFieldProphecy(mid, sid, type_actuals.clone(), offset, temp_i),
                        [srcs[0], temp_i].to_vec(),
                        aa.clone(),
                    ));

                    //update value to the saved original value
                    builder.emit(Call(
                        attr_id,
                        [].to_vec(),
                        WriteRef,
                        [dests[0], new_dests2].to_vec(),
                        aa.clone(),
                    ));
                },
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
                    print!("{}prophecy_varaiables builder2\n", dests[0]);
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
