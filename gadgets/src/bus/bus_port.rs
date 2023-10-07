use super::{
    bus_builder::{BusAssigner, BusBuilder},
    bus_chip::BusTerm,
    bus_codec::{BusCodecExpr, BusCodecVal, BusMessageExpr, BusMessageF},
    port_assigner::Assigner,
    util::from_isize,
    Field,
};
use crate::util::query_expression;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, ThirdPhase},
    poly::Rotation,
};
use std::marker::PhantomData;

/// A bus operation, as expressions for circuit config.
pub type BusOpExpr<F, M> = BusOp<M, Expression<F>>;

/// A bus operation, as values for circuit assignment.
pub type BusOpF<M> = BusOp<M, isize>;

/// A bus operation.
#[derive(Clone, Debug)]
pub struct BusOp<M, C> {
    message: M,
    count: C,
}

impl<M, C> BusOp<M, C>
where
    M: Clone,
    C: Count,
{
    /// Receive a message, with the expectation that it carries a true fact. This can be a
    /// cross-circuit call answered by a `send`, or a lookup query answered by a `send_to_lookups`.
    pub fn receive(message: M) -> Self {
        Self {
            message,
            count: C::neg_one(),
        }
    }

    /// Send a message, with the responsibility to verify that it states a true fact, and the
    /// expectation that it is received exactly once somewhere else.
    pub fn send(message: M) -> Self {
        Self {
            message,
            count: C::one(),
        }
    }

    /// Expose an entry of a lookup table as a bus message, with the responsibility that it is a
    /// true fact. It can be received any number of times. This number is the `count` advice.
    pub fn send_to_lookups(message: M, count: C) -> Self {
        Self { message, count }
    }

    /// The message to send or receive.
    pub fn message(&self) -> M {
        self.message.clone()
    }

    /// The number of copies of the message to send (if positive) or receive (if negative).
    pub fn count(&self) -> C {
        self.count.clone()
    }
}

/// Trait usable as BusOp count (Expression or isize).
pub trait Count: Clone {
    /// 1
    fn one() -> Self;
    /// -1
    fn neg_one() -> Self;
}

impl<F: Field> Count for Expression<F> {
    fn one() -> Self {
        Self::Constant(F::one())
    }
    fn neg_one() -> Self {
        Self::Constant(-F::one())
    }
}

impl Count for isize {
    fn one() -> Self {
        1
    }
    fn neg_one() -> Self {
        -1
    }
}

/// A chip to access to the bus.
#[derive(Clone, Debug)]
pub struct BusPortSingle;

impl BusPortSingle {
    /// Create a new bus port with a single access.
    /// The helper cell can be used for something else when not enabled.
    pub fn connect<F: Field, M: BusMessageExpr<F>>(
        meta: &mut ConstraintSystem<F>,
        bus_builder: &mut BusBuilder<F, M>,
        enabled: Expression<F>,
        op: BusOpExpr<F, M>,
        helper: Expression<F>,
    ) {
        let term = Self::create_term(meta, bus_builder.codec(), enabled, op, helper);
        bus_builder.add_term(term);
    }

    /// Return the witness that must be assigned to the helper cell.
    /// Very slow. Prefer `PortAssigner::assign_later` instead.
    pub fn helper_witness<F: Field, M: BusMessageF<F>>(
        codec: &BusCodecVal<F, M>,
        op: BusOpF<M>,
    ) -> Value<F> {
        codec
            .compress(op.message())
            .map(|denom| from_isize::<F>(op.count()) * denom.invert().unwrap_or(F::zero()))
    }

    fn create_term<F: Field, M: BusMessageExpr<F>>(
        meta: &mut ConstraintSystem<F>,
        codec: &BusCodecExpr<F, M>,
        enabled: Expression<F>,
        op: BusOpExpr<F, M>,
        helper: Expression<F>,
    ) -> BusTerm<F> {
        let term = enabled.clone() * helper.clone();

        meta.create_gate("bus access", |_| {
            // Verify that `term = enabled * count / compress(message)`.
            //
            // With witness: helper = count / compress(message)
            //
            // If `enabled = 0`, then `term = 0` by definition. In that case, the helper cell is not
            // constrained, so it can be used for something else.
            [term.clone() * codec.compress(op.message()) - enabled * op.count()]
        });

        BusTerm::verified(term)
    }
}

/// A chip with two accesses to the bus. BusPortDual uses only one helper cell, however the
/// degree of input expressions is more limited than with BusPortSingle.
/// The helper cell can be used for something else if both op.count are zero.
pub struct BusPortDual;

impl BusPortDual {
    /// Create a new bus port with two accesses.
    pub fn connect<F: Field, M: BusMessageExpr<F>>(
        meta: &mut ConstraintSystem<F>,
        bus_builder: &mut BusBuilder<F, M>,
        enabled: Expression<F>,
        ops: [BusOpExpr<F, M>; 2],
        helper: Expression<F>,
    ) {
        let term = Self::create_term(meta, bus_builder.codec(), enabled, ops, helper);
        bus_builder.add_term(term);
    }

    /// Return the witness that must be assigned to the helper cell.
    /// Prefer using BusAssigner instead.
    pub fn helper_witness<F: Field, M: BusMessageF<F>>(
        codec: &BusCodecVal<F, M>,
        messages: [M; 2],
    ) -> Value<F> {
        let [m0, m1] = messages;
        (codec.compress(m0) * codec.compress(m1)).map(|x| x.invert().unwrap_or(F::zero()))
    }

    fn create_term<F: Field, M: BusMessageExpr<F>>(
        meta: &mut ConstraintSystem<F>,
        codec: &BusCodecExpr<F, M>,
        enabled: Expression<F>,
        ops: [BusOpExpr<F, M>; 2],
        helper: Expression<F>,
    ) -> BusTerm<F> {
        // TODO: no need for the count in the constraint.
        // TODO: only one constraint for both ops.
        let denom_0 = codec.compress(ops[0].message());
        let denom_1 = codec.compress(ops[1].message());

        // With witness: helper = 1 / (denom_0 * denom_1)

        // term_0 = count_0 * helper * denom_1
        let count_0 = ops[0].count();
        let term_0 = count_0.clone() * helper.clone() * denom_1.clone();

        // term_1 = count_1 * helper * denom_0
        let count_1 = ops[1].count();
        let term_1 = count_1.clone() * helper.clone() * denom_0.clone();

        // Verify that:
        //     term_0 == count_0 / denom_0
        //     term_0 * denom_0 - count_0 == 0
        //
        // And the same for term_1.
        //
        // In case both count_0 and count_1 are zero, then the helper cell is not constrained, so it
        // can be used for something else.
        meta.create_gate("bus access (dual)", |_| {
            [
                term_0.clone() * denom_0 - count_0,
                term_1.clone() * denom_1 - count_1,
            ]
        });

        BusTerm::verified(term_0 + term_1)
    }
}

/// A chip to access the bus. It manages its own helper column and gives one access per row.
#[derive(Clone, Debug)]
pub struct BusPortChip<F> {
    helper: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: Field> BusPortChip<F> {
    /// Create a new bus port with a single access.
    pub fn connect<M: BusMessageExpr<F>>(
        meta: &mut ConstraintSystem<F>,
        bus_builder: &mut BusBuilder<F, M>,
        enabled: Expression<F>,
        op: BusOpExpr<F, M>,
    ) -> Self {
        let helper = meta.advice_column_in(ThirdPhase);
        let helper_expr = query_expression(meta, |meta| meta.query_advice(helper, Rotation::cur()));

        BusPortSingle::connect(meta, bus_builder, enabled, op, helper_expr);

        Self {
            helper,
            _marker: PhantomData,
        }
    }

    /// Assign an operation.
    pub fn assign<M: BusMessageF<F>>(
        &self,
        bus_assigner: &mut BusAssigner<F, M>,
        offset: usize,
        op: BusOpF<M>,
    ) {
        let cmd = Box::new(BusPortAssigner {
            offset,
            column: self.helper,
            count: op.count(),
        });
        let denom = bus_assigner.codec().compress(op.message());

        bus_assigner.op_counter().track_op(&op);
        bus_assigner.port_assigner().assign_later(cmd, denom);
    }
}

struct BusPortAssigner {
    offset: usize,
    column: Column<Advice>,
    count: isize,
}

impl<F: Field> Assigner<F> for BusPortAssigner {
    fn assign(&self, region: &mut Region<'_, F>, inversed_denom: F) -> (usize, F) {
        let term = from_isize::<F>(self.count) * inversed_denom;

        region
            .assign_advice(
                || "BusPort_helper",
                self.column,
                self.offset,
                || Value::known(term),
            )
            .unwrap();

        (self.offset, term)
    }
}

/// A chip to access the bus. It manages its own helper columns and gives multiple accesses per row.
#[derive(Clone, Debug)]
pub struct BusPortMulti<F> {
    // TODO: implement with as few helper columns as possible.
    ports: Vec<BusPortChip<F>>,
}

impl<F: Field> BusPortMulti<F> {
    /// Create and connect a new bus port with multiple accesses.
    pub fn connect<M: BusMessageExpr<F>>(
        meta: &mut ConstraintSystem<F>,
        bus_builder: &mut BusBuilder<F, M>,
        enabled: Expression<F>,
        ops: Vec<BusOpExpr<F, M>>,
    ) -> Self {
        let ports = ops
            .into_iter()
            .map(|op| BusPortChip::connect(meta, bus_builder, enabled.clone(), op))
            .collect();
        Self { ports }
    }

    /// Assign operations.
    pub fn assign<M: BusMessageF<F>>(
        &self,
        bus_assigner: &mut BusAssigner<F, M>,
        offset: usize,
        ops: Vec<BusOpF<M>>,
    ) {
        assert_eq!(self.ports.len(), ops.len());
        for (port, op) in self.ports.iter().zip(ops) {
            port.assign(bus_assigner, offset, op);
        }
    }
}
