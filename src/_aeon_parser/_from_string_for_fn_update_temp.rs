use crate::_aeon_parser::FnUpdateTemp;
use crate::_aeon_parser::FnUpdateTemp::*;
use crate::BinaryOp::*;
use std::convert::TryFrom;
use std::iter::Peekable;
use std::str::Chars;

impl TryFrom<&str> for FnUpdateTemp {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let tokens = tokenize_function_group(&mut value.chars().peekable(), true)?;
        Ok(*(parse_update_function(&tokens)?))
    }
}

/// **(internal)** An enum of possible tokens occurring in a string representation of
/// a `FnUpdate`.
#[derive(Debug, Eq, PartialEq)]
enum Token {
    Not,                // '!'
    And,                // '&'
    Or,                 // '|'
    Xor,                // '^'
    Imp,                // '=>'
    Iff,                // '<=>'
    Comma,              // ','
    Name(String),       // 'name'
    Tokens(Vec<Token>), // A block of tokens inside parentheses
}

/// **(internal)** Process a peekable iterator of characters into a vector of `Token`s.
///
/// The outer method always consumes the opening parenthesis and the recursive call consumes the
/// closing parenthesis. Use `top_level` to indicate that there will be no closing parenthesis.
fn tokenize_function_group(
    data: &mut Peekable<Chars>,
    top_level: bool,
) -> Result<Vec<Token>, String> {
    let mut output = Vec::new();
    while let Some(c) = data.next() {
        match c {
            c if c.is_whitespace() => { /* Skip whitespace */ }
            // single char tokens
            '!' => output.push(Token::Not),
            ',' => output.push(Token::Comma),
            '&' => output.push(Token::And),
            '|' => output.push(Token::Or),
            '^' => output.push(Token::Xor),
            '=' => {
                if Some('>') == data.next() {
                    output.push(Token::Imp);
                } else {
                    return Err("Expected '>' after '='.".to_string());
                }
            }
            '<' => {
                if Some('=') == data.next() {
                    if Some('>') == data.next() {
                        output.push(Token::Iff)
                    } else {
                        return Err("Expected '>' after '='.".to_string());
                    }
                } else {
                    return Err("Expected '=' after '<'.".to_string());
                }
            }
            // '>' is invalid as a start of a token
            '>' => return Err("Unexpected '>'.".to_string()),
            ')' => {
                return if !top_level {
                    Ok(output)
                } else {
                    Err("Unexpected ')'.".to_string())
                };
            }
            '(' => {
                // start a nested token group
                let tokens = tokenize_function_group(data, false)?;
                output.push(Token::Tokens(tokens));
            }
            c if is_valid_in_name(c) => {
                // start of a variable name
                let mut name = vec![c];
                while let Some(c) = data.peek() {
                    if c.is_whitespace() || !is_valid_in_name(*c) {
                        break;
                    } else {
                        name.push(*c);
                        data.next(); // advance iterator
                    }
                }
                output.push(Token::Name(name.into_iter().collect()));
            }
            _ => return Err(format!("Unexpected '{}'.", c)),
        }
    }
    if top_level {
        Ok(output)
    } else {
        Err("Expected ')'.".to_string())
    }
}

/// **(internal)** Check if given char can appear in a name.
fn is_valid_in_name(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '{' || c == '}'
}

/// **(internal)** Parse a `FnUpdateTemp` using the recursive steps.
fn parse_update_function(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    iff(data)
}

/// **(internal)** Utility method to find first occurrence of a specific token in the token tree.
fn index_of_first(data: &[Token], token: Token) -> Option<usize> {
    data.iter().position(|t| *t == token)
}

/// **(internal)** Recursive parsing step 1: extract `<=>` operators.
fn iff(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    let iff_token = index_of_first(data, Token::Iff);
    Ok(if let Some(i) = iff_token {
        Box::new(Binary(Iff, imp(&data[..i])?, iff(&data[(i + 1)..])?))
    } else {
        imp(data)?
    })
}

/// **(internal)** Recursive parsing step 2: extract `=>` operators.
fn imp(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    let imp_token = index_of_first(data, Token::Imp);
    Ok(if let Some(i) = imp_token {
        Box::new(Binary(Imp, or(&data[..i])?, imp(&data[(i + 1)..])?))
    } else {
        or(data)?
    })
}

/// **(internal)** Recursive parsing step 3: extract `|` operators.
fn or(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    let or_token = index_of_first(data, Token::Or);
    Ok(if let Some(i) = or_token {
        Box::new(Binary(Or, and(&data[..i])?, or(&data[(i + 1)..])?))
    } else {
        and(data)?
    })
}

/// **(internal)** Recursive parsing step 4: extract `&` operators.
fn and(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    let and_token = index_of_first(data, Token::And);
    Ok(if let Some(i) = and_token {
        Box::new(Binary(And, xor(&data[..i])?, and(&data[(i + 1)..])?))
    } else {
        xor(data)?
    })
}

/// **(internal)** Recursive parsing step 5: extract `^` operators.
fn xor(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    let xor_token = index_of_first(data, Token::Xor);
    Ok(if let Some(i) = xor_token {
        Box::new(Binary(Xor, terminal(&data[..i])?, xor(&data[(i + 1)..])?))
    } else {
        terminal(data)?
    })
}

/// **(internal)** Recursive parsing step 6: extract terminals and negations.
fn terminal(data: &[Token]) -> Result<Box<FnUpdateTemp>, String> {
    if data.is_empty() {
        Err("Expected formula, found nothing.".to_string())
    } else {
        if data[0] == Token::Not {
            return Ok(Box::new(Not(terminal(&data[1..])?)));
        } else if data.len() == 1 {
            // This should be either a name or a parenthesis group, anything else does not make sense.
            match &data[0] {
                Token::Name(name) => {
                    return if name == "true" || name == "1" {
                        Ok(Box::new(Const(true)))
                    } else if name == "false" || name == "0" {
                        Ok(Box::new(Const(false)))
                    } else {
                        Ok(Box::new(Var(name.clone())))
                    };
                }
                Token::Tokens(inner) => return parse_update_function(inner),
                _ => {} // otherwise, fall through to the error at the end.
            }
        } else if data.len() == 2 {
            // If more tokens remain, it means this should be a parameter (function call).
            // Anything else is invalid.
            if let Token::Name(name) = &data[0] {
                if let Token::Tokens(args) = &data[1] {
                    let args = read_args(args)?;
                    return Ok(Box::new(Param(name.clone(), args)));
                }
            }
        }
        Err(format!("Unexpected: {:?}. Expecting formula.", data))
    }
}

/// **(internal)** Parse a list of function arguments. All arguments must be expressions separated
/// by commas.
///
/// Note that commas *have to* separate individual arguments, because any comma which is a part
/// of a "lower level" function call has to be enclosed in parentheses.
fn read_args(data: &[Token]) -> Result<Vec<FnUpdateTemp>, String> {
    if data.is_empty() {
        return Ok(Vec::new());
    }
    let mut result = Vec::new();
    for arg in data.split(|it| *it == Token::Comma) {
        if arg.is_empty() {
            return Err("Found empty function argument.".to_string());
        }
        let arg = parse_update_function(arg)?;
        result.push(*arg);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::_aeon_parser::FnUpdateTemp;
    use crate::BinaryOp;
    use std::convert::TryFrom;

    #[test]
    fn parse_update_function_basic() {
        let inputs = vec![
            "var",
            "var1(a, b, c)",
            "!foo(a)",
            "(var(a, b) | x)",
            "(xyz123 & abc)",
            "(a ^ b)",
            "(a => b)",
            "(a <=> b)",
            "(a <=> !(f(a, b) => (c ^ d)))",
            "f(a, f(b), c)",
            "f((a & c))",
        ];
        for str in inputs {
            assert_eq!(str, format!("{}", FnUpdateTemp::try_from(str).unwrap()))
        }
    }

    #[test]
    fn update_function_constants() {
        assert_eq!(
            FnUpdateTemp::try_from("0").unwrap(),
            FnUpdateTemp::Const(false)
        );
        assert_eq!(
            FnUpdateTemp::try_from("1").unwrap(),
            FnUpdateTemp::Const(true)
        );
        assert_eq!(
            FnUpdateTemp::try_from("false").unwrap(),
            FnUpdateTemp::Const(false)
        );
        assert_eq!(
            FnUpdateTemp::try_from("true").unwrap(),
            FnUpdateTemp::Const(true)
        );
        assert_eq!(
            FnUpdateTemp::try_from("0 | f(0,1)").unwrap(),
            FnUpdateTemp::Binary(
                BinaryOp::Or,
                Box::new(FnUpdateTemp::Const(false)),
                Box::new(FnUpdateTemp::Param(
                    "f".to_string(),
                    vec![FnUpdateTemp::Const(false), FnUpdateTemp::Const(true),]
                ))
            )
        )
    }

    #[test]
    fn test_invalid_tokens() {
        assert!(FnUpdateTemp::try_from("a = b").is_err());
        assert!(FnUpdateTemp::try_from("a > b").is_err());
        assert!(FnUpdateTemp::try_from("a <= b").is_err());
        assert!(FnUpdateTemp::try_from("a <- b").is_err());
        assert!(FnUpdateTemp::try_from("a ? b").is_err());
    }

    #[test]
    fn test_invalid_parentheses() {
        assert!(FnUpdateTemp::try_from("a & (b <=> c").is_err());
        assert!(FnUpdateTemp::try_from("(f => g))").is_err());
        assert!(FnUpdateTemp::try_from("a <=> (f(a,b ^ g)").is_err());
        assert!(FnUpdateTemp::try_from("a | (f(a,b)) ^ g)").is_err());
    }

    #[test]
    fn test_malformed_args() {
        assert!(FnUpdateTemp::try_from("f(a b c)").is_err());
        assert!(FnUpdateTemp::try_from("f(a, b, c,)").is_err());
        assert!(FnUpdateTemp::try_from("f(a, & c)").is_err());
    }

    #[test]
    fn test_missing_formula() {
        assert!(FnUpdateTemp::try_from("a & | g").is_err());
        assert!(FnUpdateTemp::try_from("a &").is_err());
        assert!(FnUpdateTemp::try_from("a & !").is_err());
        assert!(FnUpdateTemp::try_from("a & | g").is_err());
        assert!(FnUpdateTemp::try_from("a & a b c").is_err());
        assert!(FnUpdateTemp::try_from("a & ^x").is_err());
        assert!(FnUpdateTemp::try_from("a & x^").is_err());
        assert!(FnUpdateTemp::try_from(",").is_err());
        assert!(FnUpdateTemp::try_from(",hello").is_err());
        assert!(FnUpdateTemp::try_from("hello,").is_err());
    }

    #[test]
    fn operator_priority_test() {
        let formula = "a & b | c => d ^ e <=> f";
        let expected = "((((a & b) | c) => (d ^ e)) <=> f)".to_string();
        assert_eq!(
            expected,
            FnUpdateTemp::try_from(formula).unwrap().to_string()
        );
    }
}
