#[derive(Clone, Copy)]
pub enum Error {
    Invalid,
}

#[derive(Clone, Copy)]
enum Kind {
    Data,
}

trait TryFromPrimitive: Sized {
    type Primitive: Copy;
    type Error;
}

struct ParseError<T: TryFromPrimitive> {
    number: T::Primitive,
}

impl TryFromPrimitive for Kind {
    type Primitive = u8;
    type Error = ParseError<Self>;
}

impl TryFrom<u8> for Kind {
    type Error = ParseError<Self>;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value == 0 {
            Ok(Self::Data)
        } else {
            Err(ParseError { number: value })
        }
    }
}

trait HasSize {
    const SIZE: usize;
}

trait IsReady {
    fn is_ready(&self) -> bool;
}

trait BaseState: HasSize + IsReady {}

struct State;

impl HasSize for State {
    const SIZE: usize = 1;
}

impl IsReady for State {
    fn is_ready(&self) -> bool {
        true
    }
}

impl BaseState for State {}

fn indices<S: BaseState>(input: &[u8]) -> Result<Option<(usize, usize)>, Error> {
    if input.len() > S::SIZE {
        Ok(Some((0, S::SIZE)))
    } else {
        Ok(None)
    }
}

fn split_with_check<S, F>(
    input: &mut [u8],
    check: F,
) -> Result<(&mut [u8], &mut [u8]), Error>
where
    S: BaseState,
    F: Fn(Kind) -> Result<(), Error>,
{
    if let Some((kind_index, data_index)) = indices::<S>(input)? {
        let kind = Kind::try_from(input[kind_index]).map_err(|error| {
            let _ = error.number;
            Error::Invalid
        })?;
        check(kind)?;
        let (kind, data) = input.split_at_mut(data_index);
        Ok((&mut kind[kind_index..data_index], data))
    } else {
        Ok((&mut [], &mut []))
    }
}

pub fn split(input: &mut [u8]) -> Result<(&mut [u8], &mut [u8]), Error> {
    if !State.is_ready() {
        return Err(Error::Invalid);
    }
    split_with_check::<State, _>(input, |_| Ok(()))
}
