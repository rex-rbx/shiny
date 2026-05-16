use enum_as_inner::EnumAsInner;
use nom::{
    bytes::complete::take,
    error::{Error, ErrorKind, ParseError},
    multi::count,
    number::complete::{le_f64, le_u32, le_u64, le_u8},
    Err, IResult,
};

#[derive(Debug, EnumAsInner)]
pub enum Value<'a> {
    Nil,
    Boolean(bool),
    Number(f64),
    String(&'a [u8]),
}

impl<'a> Value<'a> {
    pub fn parse(input: &'a [u8], size_t_width: u8) -> IResult<&'a [u8], Self> {
        let (input, kind) = le_u8(input)?;
        match kind {
            0 => Ok((input, Self::Nil)),
            1 => {
                let (input, value) = le_u8(input)?;
                Ok((input, Self::Boolean(value != 0)))
            }
            3 => {
                let (input, value) = le_f64(input)?;
                Ok((input, Self::Number(value)))
            }
            4 => {
                let (input, value) = parse_string(input, size_t_width)?;
                assert!(!value.is_empty());
                Ok((input, Self::String(&value[..value.len() - 1])))
            }
            _ => Err(Err::Failure(Error::from_error_kind(
                input,
                ErrorKind::Switch,
            ))),
        }
    }
}

pub fn parse_string<'a>(input: &'a [u8], size_t_width: u8) -> IResult<&'a [u8], &'a [u8]> {
    if size_t_width == 8 {
        let (input, string_length) = le_u64(input)?;
        take(string_length as usize)(input)
    } else {
        let (input, string_length) = le_u32(input)?;
        take(string_length as usize)(input)
    }
}

pub fn parse_strings<'a>(input: &'a [u8], size_t_width: u8) -> IResult<&'a [u8], Vec<&'a [u8]>> {
    let (input, string_count) = le_u32(input)?;
    let (input, strings) = count(
        |i| parse_string(i, size_t_width),
        string_count as usize,
    )(input)?;
    Ok((input, strings))
}