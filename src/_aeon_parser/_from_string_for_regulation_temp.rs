use crate::Monotonicity;
use crate::_aeon_parser::RegulationTemp;
use regex::Regex;
use std::convert::TryFrom;

impl TryFrom<&str> for RegulationTemp {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let re = Regex::new(r"^\s*(?P<regulator>[a-zA-Z0-9_]+)\s*-(?P<monotonicity>[|>?])(?P<observable>\??)\s*(?P<target>[a-zA-Z0-9_]+)\s*$").unwrap();
        return if let Some(captures) = re.captures(value) {
            Ok(RegulationTemp {
                regulator: captures["regulator"].to_string(),
                target: captures["target"].to_string(),
                observable: captures["observable"].is_empty(),
                monotonicity: match &captures["monotonicity"] {
                    "?" => None,
                    "|" => Some(Monotonicity::Inhibition),
                    ">" => Some(Monotonicity::Activation),
                    _ => unreachable!("Nothing else matches this group."),
                },
            })
        } else {
            Err(format!(
                "String \"{}\" does not describe a regulation.",
                value
            ))
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::Monotonicity::{Activation, Inhibition};
    use crate::_aeon_parser::RegulationTemp;
    use std::convert::TryFrom;

    #[test]
    fn parse_regulation_valid() {
        assert_eq!(
            RegulationTemp {
                regulator: "abc".to_string(),
                target: "123".to_string(),
                observable: true,
                monotonicity: Some(Activation)
            },
            RegulationTemp::try_from("  abc -> 123 ").unwrap()
        );

        assert_eq!(
            RegulationTemp {
                regulator: "abc".to_string(),
                target: "123".to_string(),
                observable: false,
                monotonicity: Some(Activation)
            },
            RegulationTemp::try_from("  abc ->? 123 ").unwrap()
        );

        assert_eq!(
            RegulationTemp {
                regulator: "hello_world".to_string(),
                target: "world_hello_123".to_string(),
                observable: true,
                monotonicity: Some(Inhibition)
            },
            RegulationTemp::try_from("hello_world -| world_hello_123").unwrap()
        );

        assert_eq!(
            RegulationTemp {
                regulator: "hello_world".to_string(),
                target: "world_hello_123".to_string(),
                observable: false,
                monotonicity: Some(Inhibition)
            },
            RegulationTemp::try_from("hello_world -|? world_hello_123").unwrap()
        );

        assert_eq!(
            RegulationTemp {
                regulator: "abc".to_string(),
                target: "abc".to_string(),
                observable: true,
                monotonicity: None
            },
            RegulationTemp::try_from("abc -? abc").unwrap()
        );

        assert_eq!(
            RegulationTemp {
                regulator: "abc".to_string(),
                target: "abc".to_string(),
                observable: false,
                monotonicity: None
            },
            RegulationTemp::try_from("abc -?? abc").unwrap()
        );
    }

    #[test]
    fn parse_regulation_invalid() {
        assert!(RegulationTemp::try_from("").is_err());
        assert!(RegulationTemp::try_from("var1 var2 -> var3").is_err());
        assert!(RegulationTemp::try_from("var -| v?r").is_err());
        assert!(RegulationTemp::try_from(" -? foo").is_err());
        assert!(RegulationTemp::try_from("hello -?> there").is_err());
        assert!(RegulationTemp::try_from("world -??? is").is_err());
        assert!(RegulationTemp::try_from("   te - ? st").is_err());
    }
}
