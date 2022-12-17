#![feature(never_type)]

use nom::{self, IResult, InputLength};
use nom::error::ParseError;

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

pub fn alt_2<I: Clone, O, E, F, X1>(
    mut a: impl FnMut(I) -> NomRes<I, O, X1, F>,
    mut b: impl FnMut(I) -> NomRes<I, O, E, F>,
) -> impl FnMut(I) -> NomRes<I, O, E, F> {
    move |input: I| parser_from_result(match result_from_parser(a(input.clone())) {
        Ok(r) => Ok(r),
        Err(NomErr::Failure(f)) => Err(NomErr::Failure(f)),
        Err(NomErr::Error(_)) => result_from_parser(b(input)),
    })
}

pub fn many0<I: Clone + InputLength, O, E, F>(
    mut parser: impl FnMut(I) -> NomRes<I, O, E, F>
) -> impl FnMut(I) -> NomRes<I, Vec<O>, !, F> {
    move |mut input: I| parser_from_result({
        let mut r = Vec::new();
        loop {
            match result_from_parser(parser(input.clone())) {
                Ok((i, o)) => {
                    assert!(i.input_len() != input.input_len(), "invalid many0 parser");
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

pub mod bytes {
    use super::*;
    use nom::{Compare, InputIter, InputLength, InputTake};

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
            let (r, i) = input.take_split(input_len);
            Ok((i, r))
        }
    }
}
