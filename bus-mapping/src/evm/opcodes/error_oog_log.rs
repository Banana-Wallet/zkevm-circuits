use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    evm::{Opcode, OpcodeId},
    operation::CallContextField,
    Error,
};
use eth_types::{GethExecStep, Word};

#[derive(Debug, Copy, Clone)]
pub(crate) struct ErrorOOGLog;

impl Opcode for ErrorOOGLog {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = if geth_steps.len() > 1 {
            Some(&geth_steps[1])
        } else {
            None
        };
        exec_step.error = state.get_step_err(geth_step, next_step)?;
        // assert op code can only be Log*
        assert!([
            OpcodeId::LOG0,
            OpcodeId::LOG1,
            OpcodeId::LOG2,
            OpcodeId::LOG3,
            OpcodeId::LOG4
        ]
        .contains(&geth_step.op));
        let _mstart = state.stack_pop(&mut exec_step)?;
        let _msize = state.stack_pop(&mut exec_step)?;
        #[cfg(feature = "enable-stack")]
        {
            assert_eq!(_mstart, geth_step.stack.nth_last(0)?);
            assert_eq!(_msize, geth_step.stack.nth_last(1)?);
        }

        // read static call property
        state.call_context_read(
            &mut exec_step,
            state.call()?.call_id,
            CallContextField::IsStatic,
            Word::from(state.call()?.is_static as u8),
        )?;

        state.handle_return(&mut [&mut exec_step], geth_steps, true)?;
        Ok(vec![exec_step])
    }
}
