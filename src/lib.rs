#![feature(never_type)]

use nom::{self, IResult, InputLength};
use nom::error::ParseError;
use paste::paste;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum NomErr<E, F> {
    Error(E),
    Failure(F),
}

impl<E, F> NomErr<E, F> {
    pub fn map_err<X>(self, f: impl FnOnce(E) -> X) -> NomErr<X, F> {
        match self {
            NomErr::Error(e) => NomErr::Error(f(e)),
            NomErr::Failure(e) => NomErr::Failure(e),
        }
    }

    pub fn map_fail<X>(self, f: impl FnOnce(F) -> X) -> NomErr<E, X> {
        match self {
            NomErr::Error(e) => NomErr::Error(e),
            NomErr::Failure(e) => NomErr::Failure(f(e)),
        }
    }
}

impl<F> NomErr<!, F> {
    pub fn any_err<E>(self) -> NomErr<E, F> {
        self.map_err(|x| x)
    }
}

impl<E> NomErr<E, !> {
    pub fn any_fail<F>(self) -> NomErr<E, F> {
        self.map_fail(|x| x)
    }
}

impl<E> NomErr<E, E> {
    pub fn fail(self) -> NomErr<!, E> {
        match self {
            NomErr::Error(e) => NomErr::Failure(e),
            NomErr::Failure(e) => NomErr::Failure(e),
        }
    }
}

impl<I, E, F> ParseError<I> for NomErr<E, F> {
    fn from_error_kind(_input: I, _kind: nom::error::ErrorKind) -> Self { panic!() }

    fn append(_input: I, _kind: nom::error::ErrorKind, _other: Self) -> Self { panic!() }

    fn or(self, _other: Self) -> Self { panic!() }

    fn from_char(_input: I, _: char) -> Self { panic!() }
}

pub type NomRes<I, O, E, F> = IResult<I, O, NomErr<E, F>>;

pub fn parser_from_result<I, O, E, F>(r: Result<(I, O), NomErr<E, F>>) -> NomRes<I, O, E, F> {
    match r {
        Ok((i, o)) => Ok((i, o)),
        Err(NomErr::Error(e)) => Err(nom::Err::Error(NomErr::Error(e))),
        Err(NomErr::Failure(f)) => Err(nom::Err::Failure(NomErr::Failure(f))),
    }
}

pub fn result_from_parser<I, O, E, F>(r: NomRes<I, O, E, F>) -> Result<(I, O), NomErr<E, F>> {
    match r {
        Ok((i, o)) => Ok((i, o)),
        Err(nom::Err::Error(NomErr::Error(e))) => Err(NomErr::Error(e)),
        Err(nom::Err::Failure(NomErr::Failure(e))) => Err(NomErr::Failure(e)),
        _ => panic!()
    }
}

pub fn map_err<I: Clone, O, E, F, X>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>,
    mut f: impl FnMut(E, I) -> X
) -> impl FnMut(I) -> NomRes<I, O, X, F> {
    move |input: I| {
        parser_from_result(result_from_parser(parser(input.clone())).map_err(|e| e.map_err(|e| f(e, input))))
    }
}

pub fn any_err<I: Clone, O, F, X>(
    mut parser: impl FnMut(I) -> NomRes<I, O, !, F>,
) -> impl FnMut(I) -> NomRes<I, O, X, F> {
    move |input: I| parser_from_result(result_from_parser(parser(input.clone())).map_err(|e| e.any_err()))
}

pub fn uni_err_no_fail<I, O>(
    mut parser: impl FnMut(I) -> IResult<I, O, ()>
) -> impl FnMut(I) -> NomRes<I, O, (), !> {
    move |input: I| parser_from_result(match parser(input) {
        Ok((i, o)) => Ok((i, o)),
        Err(nom::Err::Error(())) => Err(NomErr::Error(())),
        _ => panic!(),
    })
}

pub fn seq_2<I, O1, O2, E, F>(
    mut a: impl FnMut(I) -> NomRes<I, O1, E, F>,
    mut b: impl FnMut(I) -> NomRes<I, O2, E, F>,
) -> impl FnMut(I) -> NomRes<I, (O1, O2), E, F> {
    move |input: I| parser_from_result(match result_from_parser(a(input)) {
        Err(e) => Err(e),
        Ok((input, a)) => result_from_parser(b(input)).map(|(i, b)| (i, (a, b)))
    })
}

macro_rules! seq_n {
    (
        $n:literal; $m:literal: $($i:literal),+
    ) => {
        paste! {
            pub fn [< seq_ $n >] <I, $( [< O $i >] , )+ [< O $n >] , E, F>(
                $(
                    [< parser_ $i >] : impl FnMut(I) -> NomRes<I, [< O $i >] , E, F>,
                )+
                [< parser_ $n >] : impl FnMut(I) -> NomRes<I, [< O $n >] , E, F>,
            ) -> impl FnMut(I) -> NomRes<I, ($( [< O $i >], )+ [< O $n >] ), E, F> {
                map(
                    seq_2( [< seq_ $m >] ($( [< parser_ $i >] ),+), [< parser_ $n >] ),
                    |(($( [< r $i >] ),+), [< r $n >] )| ($( [< r $i >] ,)+ [< r $n >] )
                )
            }
        }
    };
}

seq_n!(3; 2: 1, 2);
seq_n!(4; 3: 1, 2, 3);
seq_n!(5; 4: 1, 2, 3, 4);
seq_n!(6; 5: 1, 2, 3, 4, 5);
seq_n!(7; 6: 1, 2, 3, 4, 5, 6);
seq_n!(8; 7: 1, 2, 3, 4, 5, 6, 7);
seq_n!(9; 8: 1, 2, 3, 4, 5, 6, 7, 8);
seq_n!(10; 9: 1, 2, 3, 4, 5, 6, 7, 8, 9);
seq_n!(11; 10: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
seq_n!(12; 11: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
seq_n!(13; 12: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
seq_n!(14; 13: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
seq_n!(15; 14: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);

pub fn alt_2<I: Clone, O, E, F, X1>(
    mut parser_1: impl FnMut(I) -> NomRes<I, O, X1, F>,
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>,
) -> impl FnMut(I) -> NomRes<I, O, E, F> {
    move |input: I| parser_from_result(match result_from_parser(parser_1(input.clone())) {
        Ok(r) => Ok(r),
        Err(NomErr::Failure(f)) => Err(NomErr::Failure(f)),
        Err(NomErr::Error(_)) => result_from_parser(parser(input)),
    })
}

macro_rules! alt_n {
    (
        $n:literal; $m:literal: $($i:literal),+
    ) => {
        paste! {
            pub fn [< alt_ $n >] <I: Clone, O, E, F, $( [< X $i >]),+>(
                $(
                    [< parser_ $i >] : impl FnMut(I) -> NomRes<I, O, [< X $i >], F>,
                )+
                parser: impl FnMut(I) -> NomRes<I, O, E, F>,
            ) -> impl FnMut(I) -> NomRes<I, O, E, F> {
                alt_2( [< alt_ $m >] ($( [< parser_ $i >] ),+), parser)
            }
        }
    };
}

alt_n!(3; 2: 1, 2);
alt_n!(4; 3: 1, 2, 3);
alt_n!(5; 4: 1, 2, 3, 4);
alt_n!(6; 5: 1, 2, 3, 4, 5);
alt_n!(7; 6: 1, 2, 3, 4, 5, 6);
alt_n!(8; 7: 1, 2, 3, 4, 5, 6, 7);
alt_n!(9; 8: 1, 2, 3, 4, 5, 6, 7, 8);
alt_n!(10; 9: 1, 2, 3, 4, 5, 6, 7, 8, 9);
alt_n!(11; 10: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
alt_n!(12; 11: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
alt_n!(13; 12: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
alt_n!(14; 13: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
alt_n!(15; 14: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);

pub fn many0<I: Clone + InputLength, O, E, F>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>
) -> impl FnMut(I) -> NomRes<I, Vec<O>, !, F> {
    move |mut input: I| parser_from_result({
        let mut r = Vec::new();
        loop {
            if input.input_len() == 0 { break Ok(()); }
            match result_from_parser(parser(input.clone())) {
                Ok((i, o)) => {
                    assert_ne!(i.input_len(), input.input_len(), "invalid many0 parser");
                    input = i;
                    r.push(o);
                },
                Err(NomErr::Failure(f)) => break Err(NomErr::Failure(f)),
                Err(NomErr::Error(_)) => break Ok(()),
            }
        }.map(|()| (input, r))
    })
}

pub fn map<I, O, E, F, X>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>,
    mut f: impl FnMut(O) -> X
) -> impl FnMut(I) -> NomRes<I, X, E, F> {
    move |input: I| parser_from_result(result_from_parser(parser(input)).map(|(i, r)| (i, f(r))))
}

pub fn map_res<I, O, E, F, X>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>,
    mut f: impl FnMut(O) -> Result<X, E>
) -> impl FnMut(I) -> NomRes<I, X, E, F> {
    move |input: I| parser_from_result(result_from_parser(parser(input)).and_then(|(i, r)|
        f(r).map_err(NomErr::Error).map(|r| (i, r))
    ))
}

pub fn all_consuming<I: InputLength, O, E, F>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>,
    mut f: impl FnMut(I) -> NomErr<E, F>,
) -> impl FnMut(I) -> NomRes<I, O, E, F> {
    move |input: I| parser_from_result(result_from_parser(parser(input)).and_then(|(i, r)|
        if i.input_len() == 0 { Ok((i, r)) } else { Err(f(i)) }
    ))
}

pub fn flat_map<I, O1, O2, E, F, P: FnMut(I) -> NomRes<I, O2, E, F>>(
    mut parser: impl FnMut(I) -> NomRes<I, O1, E, F>,
    mut f: impl FnMut(O1) -> P,
) -> impl FnMut(I) -> NomRes<I, O2, E, F> {
    move |input: I| parser_from_result(match result_from_parser(parser(input)) {
        Err(e) => Err(e),
        Ok((i, r1)) => result_from_parser(f(r1)(i))
    })
}

pub fn count<I: Clone + PartialEq, O, E, F>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>,
    count: usize
) -> impl FnMut(I) -> NomRes<I, Vec<O>, E, F> {
    move |mut input: I| parser_from_result((|| {
        let mut r = Vec::new();
        for _ in 0 .. count {
            let (i, o) = result_from_parser(parser(input.clone()))?;
            input = i;
            r.push(o);
        }
        Ok((input, r))
    })())
}

pub mod bytes {
    use super::*;
    use nom::{Compare, InputIter, InputLength, InputTake, Slice};
    use std::ops::RangeFrom;

    pub fn le_u8<I: Slice<RangeFrom<usize>> + InputIter<Item=u8> + InputLength>() -> impl FnMut(I) -> NomRes<I, u8, (), !> {
        uni_err_no_fail(nom::number::complete::le_u8)
    }

    pub fn le_u16<I: Slice<RangeFrom<usize>> + InputIter<Item=u8> + InputLength>() -> impl FnMut(I) -> NomRes<I, u16, (), !> {
        uni_err_no_fail(nom::number::complete::le_u16)
    }

    pub fn le_u32<I: Slice<RangeFrom<usize>> + InputIter<Item=u8> + InputLength>() -> impl FnMut(I) -> NomRes<I, u32, (), !> {
        uni_err_no_fail(nom::number::complete::le_u32)
    }

    pub fn le_i8<I: Slice<RangeFrom<usize>> + InputIter<Item=u8> + InputLength>() -> impl FnMut(I) -> NomRes<I, i8, (), !> {
        uni_err_no_fail(nom::number::complete::le_i8)
    }

    pub fn le_i16<I: Slice<RangeFrom<usize>> + InputIter<Item=u8> + InputLength>() -> impl FnMut(I) -> NomRes<I, i16, (), !> {
        uni_err_no_fail(nom::number::complete::le_i16)
    }

    pub fn le_i32<I: Slice<RangeFrom<usize>> + InputIter<Item=u8> + InputLength>() -> impl FnMut(I) -> NomRes<I, i32, (), !> {
        uni_err_no_fail(nom::number::complete::le_i32)
    }

    pub fn tag<T: Clone + InputLength, I: InputTake + Compare<T>>(
        tag: T
    ) -> impl FnMut(I) -> NomRes<I, I, (), !> {
        uni_err_no_fail(nom::bytes::complete::tag(tag))
    }

    pub fn take<I: InputIter + InputTake>(
        count: usize
    ) -> impl FnMut(I) -> NomRes<I, I, (), !> {
        uni_err_no_fail(nom::bytes::complete::take(count))
    }

    pub fn take_all<I: InputLength + InputTake>() -> impl FnMut(I) -> NomRes<I, I, !, !> {
        move |input: I| {
            let input_len = input.input_len();
            Ok(input.take_split(input_len))
        }
    }
}
