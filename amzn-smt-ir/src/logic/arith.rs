// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    logic::ALL, fold::Fold, visit::Visit, Ctx, IIndex, IOp, ISort, Logic, Operation, QualIdentifier, Sorted,
    Term, UnknownSort, Void, UF,
};
use smallvec::SmallVec;

use std::ops;

type Args<T> = SmallVec<[T; 2]>;

#[derive(Operation, Fold, Visit, Clone, Hash, PartialEq, Eq)]
pub enum LIAOp<Term> {
    #[symbol("+")]
    Plus(Args<Term>),
    #[symbol("-")]
    Neg(Term),
    #[symbol("-")]
    Minus(Args<Term>),
    #[symbol("*")]
    Mul(Args<Term>),
    #[symbol(">=")]
    Gte(Args<Term>),
    #[symbol(">")]
    Gt(Args<Term>),
    #[symbol("<=")]
    Lte(Args<Term>),
    #[symbol("<")]
    Lt(Args<Term>),
}

impl<L: Logic> Sorted<L> for LIAOp<Term<L>> {
    fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        match self {
            Self::Plus(..) | Self::Neg(..) | Self::Minus(..) | Self::Mul(..) => Ok(ISort::int()),
            Self::Gte(..) | Self::Gt(..) | Self::Lte(..) | Self::Lt(..) => Ok(ISort::bool()),
        }
    }
}

#[derive(Operation, Fold, Visit, Clone, Hash, PartialEq, Eq)]
pub enum ArithOp<Term> {
    #[symbol("+")]
    Plus(Args<Term>),
    #[symbol("-")]
    Neg(Term),
    #[symbol("-")]
    Minus(Args<Term>),
    #[symbol("*")]
    Mul(Args<Term>),
    #[symbol("div")]
    IntDiv(Args<Term>),
    #[symbol("/")]
    RealDiv(Args<Term>),
    Divisible([IIndex; 1], Term),
    Mod(Term, Term),
    Abs(Term),
    #[symbol(">=")]
    Gte(Args<Term>),
    #[symbol(">")]
    Gt(Args<Term>),
    #[symbol("<=")]
    Lte(Args<Term>),
    #[symbol("<")]
    Lt(Args<Term>),
    #[symbol("to_real")]
    ToReal(Term),
    #[symbol("to_int")]
    ToInt(Term),
    #[symbol("is_int")]
    IsInt(Term),
}

impl<L: Logic> Sorted<L> for ArithOp<Term<L>>
where
    Self: Into<L::Op>,
{
    fn sort(&self, ctx: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        use ArithOp::*;

        let bad = || UnknownSort(Term::from(IOp::new(self.clone().into())));
        match self {
            Neg(arg) => arg.sort(ctx),
            Plus(args) | Minus(args) | Mul(args) => args.first().ok_or_else(bad)?.sort(ctx),
            IntDiv(..) | Mod(..) | Abs(..) | ToInt(..) => Ok(ISort::int()),
            RealDiv(..) | ToReal(..) => Ok(ISort::real()),
            Gte(..) | Gt(..) | Lte(..) | Lt(..) | Divisible(..) | IsInt(..) => Ok(ISort::bool()),
        }
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_UFLIA;

impl Logic for QF_UFLIA {
    type Var = QualIdentifier;
    type Op = LIAOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = UF<Term<Self>>;
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
#[allow(non_camel_case_types)]
pub struct QF_LIA;

impl Logic for QF_LIA {
    type Var = QualIdentifier;
    type Op = LIAOp<Term<Self>>;
    type Quantifier = Void;
    type UninterpretedFunc = Void;
}

impl ops::Add for Term<ALL> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::OtherOp(ArithOp::Plus([self, rhs].into()).into())
    }
}

impl ops::Sub for Term<ALL> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::OtherOp(ArithOp::Minus([self, rhs].into()).into())
    }
}

impl ops::Neg for Term<ALL> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::OtherOp(ArithOp::Neg(self).into())
    }
}

impl ops::Mul for Term<ALL> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::OtherOp(ArithOp::Mul([self, rhs].into()).into())
    }
}

impl ops::Div for Term<ALL> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        Self::OtherOp(ArithOp::IntDiv([self, rhs].into()).into())
    }
}

impl ops::Rem for Term<ALL> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        Self::OtherOp(ArithOp::Mod(self, rhs).into())
    }
}

#[test]
fn add_overload() {
    use smt2parser::concrete::Constant;

    let zero = || Term::Constant(Constant::Numeral(0u8.into()).into());
    assert_eq!((zero() + zero()).to_string(), "(+ 0 0)");

    let x = Term::Variable("x".into());
    let y = Term::Variable("y".into());
    let z = x.clone() + y.clone();
    assert_eq!(z.to_string(), "(+ x y)");

    let z = x + y + zero();
    assert_eq!(z.to_string(), "(+ (+ x y) 0)");
}

#[test]
fn sub_overload() {
    use smt2parser::concrete::Constant;

    let zero = || Term::Constant(Constant::Numeral(0u8.into()).into());
    assert_eq!((zero() - zero()).to_string(), "(- 0 0)");

    let x = Term::Variable("x".into());
    let y = Term::Variable("y".into());
    let z = x.clone() - y.clone();
    assert_eq!(z.to_string(), "(- x y)");

    let z = x - y - zero();
    assert_eq!(z.to_string(), "(- (- x y) 0)");
}

#[test]
fn neg_overload() {
    use smt2parser::concrete::Constant;

    let zero = || Term::Constant(Constant::Numeral(0u8.into()).into());
    assert_eq!((- zero()).to_string(), "(- 0)");

    let x = Term::Variable("x".into());
    let z = - x.clone();
    assert_eq!(z.to_string(), "(- x)");
}

#[test]
fn mul_overload() {
    use smt2parser::concrete::Constant;

    let zero = || Term::Constant(Constant::Numeral(0u8.into()).into());
    assert_eq!((zero() * zero()).to_string(), "(* 0 0)");

    let x = Term::Variable("x".into());
    let y = Term::Variable("y".into());
    let z = x.clone() * y.clone();
    assert_eq!(z.to_string(), "(* x y)");

    let z = x * y * zero();
    assert_eq!(z.to_string(), "(* (* x y) 0)");
}

#[test]
fn div_overload() {
    use smt2parser::concrete::Constant;

    let zero = || Term::Constant(Constant::Numeral(0u8.into()).into());
    assert_eq!((zero() / zero()).to_string(), "(div 0 0)");

    let x = Term::Variable("x".into());
    let y = Term::Variable("y".into());
    let z = x.clone() / y.clone();
    assert_eq!(z.to_string(), "(div x y)");

    let z = x / y / zero();
    assert_eq!(z.to_string(), "(div (div x y) 0)");
}

#[test]
fn mod_overload() {
    use smt2parser::concrete::Constant;

    let zero = || Term::Constant(Constant::Numeral(0u8.into()).into());
    assert_eq!((zero() % zero()).to_string(), "(mod 0 0)");

    let x = Term::Variable("x".into());
    let y = Term::Variable("y".into());
    let z = x.clone() % y.clone();
    assert_eq!(z.to_string(), "(mod x y)");

    let z = x % y % zero();
    assert_eq!(z.to_string(), "(mod (mod x y) 0)");
}
