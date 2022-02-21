use super::Opcode;
use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::{
    operation::{StorageOp, RW},
    Error,
};
use eth_types::GethExecStep;

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the [`OpcodeId::SLOAD`](crate::evm::OpcodeId::SLOAD)
/// `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Sload;

impl Opcode for Sload {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        exec_step: &mut ExecStep,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];

        // First stack read
        let stack_value_read = step.stack.last()?;
        let stack_position = step.stack.last_filled();

        // Manage first stack read at latest stack position
        state.push_stack_op(exec_step, RW::READ, stack_position, stack_value_read);

        // Storage read
        let storage_value_read = step.storage.get_or_err(&stack_value_read)?;
        state.push_op(
            exec_step,
            RW::READ,
            StorageOp::new(
                state.call().address,
                stack_value_read,
                storage_value_read,
                storage_value_read,
            ),
        );

        // First stack write
        state.push_stack_op(exec_step, RW::WRITE, stack_position, storage_value_read);

        Ok(())
    }
}

#[cfg(test)]
mod sload_tests {
    use super::*;
    use crate::circuit_input_builder::{ExecStep, TransactionContext};
    use eth_types::evm_types::StackAddress;
    use eth_types::{bytecode, Address, Word};
    use pretty_assertions::assert_eq;

    #[test]
    fn sload_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            // Write 0x6f to storage slot 0
            PUSH1(0x6fu64)
            PUSH1(0x00u64)
            SSTORE

            // Load storage slot 0
            PUSH1(0x00u64)
            #[start]
            SLOAD
            STOP
        };

        // Get the execution steps from the external tracer
        let block = crate::mock::BlockData::new_from_geth_data(
            mock::new_single_tx_trace_code_at_start(&code).unwrap(),
        );

        let mut builder = block.new_circuit_input_builder();
        builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

        let mut test_builder = block.new_circuit_input_builder();
        let mut tx = test_builder
            .new_tx(&block.eth_tx, !block.geth_trace.failed)
            .unwrap();
        let mut tx_ctx = TransactionContext::new(&block.eth_tx, &block.geth_trace).unwrap();

        // Generate step corresponding to SLOAD
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            0,
            test_builder.block_ctx.rwc,
            0,
        );
        let mut state_ref = test_builder.state_ref(&mut tx, &mut tx_ctx);
        // Add StackOp associated to the stack pop.
        state_ref.push_stack_op(
            &mut step,
            RW::READ,
            StackAddress::from(1023),
            Word::from(0x0u32),
        );
        // Add StorageOp associated to the storage read.
        state_ref.push_op(
            &mut step,
            RW::READ,
            StorageOp::new(
                Address::from([0u8; 20]),
                Word::from(0x0u32),
                Word::from(0x6fu32),
                Word::from(0x6fu32),
            ),
        );
        // Add StackOp associated to the stack push.
        state_ref.push_stack_op(
            &mut step,
            RW::WRITE,
            StackAddress::from(1023),
            Word::from(0x6fu32),
        );
        tx.steps_mut().push(step);
        test_builder.block.txs_mut().push(tx);

        assert_eq!(
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
            test_builder.block.txs()[0].steps()[0].bus_mapping_instance
        );
        assert_eq!(builder.block.container, test_builder.block.container);

        Ok(())
    }
}
