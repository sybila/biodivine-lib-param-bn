use crate::sbml::Layout;
use crate::{BinaryOp, BooleanNetwork, FnUpdate, Monotonicity};
use std::collections::HashMap;
use std::io::{Error, Write};

impl BooleanNetwork {
    /// Convert this network to an SBML string with an optional `Layout`.
    pub fn to_sbml(&self, layout: Option<&Layout>) -> String {
        let mut buffer: Vec<u8> = Vec::new();
        self.write_as_sbml(layout, &mut buffer)
            .expect("Cannot write model to SBML.");
        String::from_utf8(buffer).expect("Invalid UTF formatting in string.")
    }

    /// Write an SBML string representation (with an optional `Layout`) of this network
    /// to the given `out` writer.
    pub fn write_as_sbml(&self, layout: Option<&Layout>, out: &mut dyn Write) -> Result<(), Error> {
        write!(
            out,
            "<?xml version='1.0' encoding='UTF-8' standalone='no'?>"
        )?;
        write!(out, "<sbml xmlns=\"http://www.sbml.org/sbml/level3/version1/core\" layout:required=\"false\" level=\"3\" qual:required=\"true\" xmlns:layout=\"http://www.sbml.org/sbml/level3/version1/layout/version1\" version=\"1\" xmlns:qual=\"http://www.sbml.org/sbml/level3/version1/qual/version1\">")?;
        write!(out, "<model>")?;
        if let Some(layout) = layout {
            if !layout.is_empty() {
                write_layout(out, layout)?;
            }
        }
        self.write_species(out)?;
        self.write_transitions(out)?;
        write!(out, "</model>")?;
        write!(out, "</sbml>")?;
        Ok(())
    }

    fn write_species(&self, out: &mut dyn Write) -> Result<(), Error> {
        write!(out, "<qual:listOfQualitativeSpecies xmlns:qual=\"http://www.sbml.org/sbml/level3/version1/qual/version1\">")?;
        for v in self.variables() {
            write!(out, "<qual:qualitativeSpecies qual:maxLevel=\"1\" qual:constant=\"false\" qual:name=\"{}\" qual:id=\"{}\"/>", self[v].get_name(), self[v].get_name())?;
        }
        write!(out, "</qual:listOfQualitativeSpecies>")?;
        Ok(())
    }

    fn write_transitions(&self, out: &mut dyn Write) -> Result<(), Error> {
        write!(out, "<qual:listOfTransitions xmlns:qual=\"http://www.sbml.org/sbml/level3/version1/qual/version1\">")?;
        for id in self.variables() {
            let var_name = self[id].get_name();
            write!(out, "<qual:transition qual:id=\"tr_{}\">", var_name)?;

            // output inputs (regulators)
            write!(out, "<qual:listOfInputs>")?;
            for r in self.regulators(id) {
                let r_var_name = self[r].get_name();
                let regulation = self.graph.find_regulation(r, id);
                let monotonicity = regulation.and_then(|r| r.monotonicity);
                let observability = regulation.map(|r| r.is_observable());
                let sign = match monotonicity {
                    None => "unknown",
                    Some(Monotonicity::Activation) => "positive",
                    Some(Monotonicity::Inhibition) => "negative",
                };
                let essential = if let Some(true) = observability {
                    "true"
                } else {
                    "false"
                };
                write!(out, "<qual:input qual:qualitativeSpecies=\"{}\" qual:transitionEffect=\"none\" qual:sign=\"{}\" qual:id=\"tr_{}_in_{}\" essential=\"{}\"/>", r_var_name, sign, var_name, r_var_name, essential)?;
            }
            write!(out, "</qual:listOfInputs>")?;

            // output outputs (self)
            write!(out, "<qual:listOfOutputs>")?;
            write!(out, "<qual:output qual:qualitativeSpecies=\"{}\" qual:transitionEffect=\"assignmentLevel\" qual:id=\"tr_{}_out\"/>", var_name, var_name)?;
            write!(out, "</qual:listOfOutputs>")?;
            if let Some(update_function) = self.get_update_function(id) {
                write!(out, "<qual:listOfFunctionTerms>")?;
                if let FnUpdate::Const(value) = update_function {
                    // Constants are encoded into the default term:
                    let value = if *value { "1" } else { "0" };
                    write!(out, "<qual:defaultTerm qual:resultLevel=\"{}\"/>", value)?;
                } else {
                    // set default value to 0
                    write!(out, "<qual:defaultTerm qual:resultLevel=\"0\"/>")?;
                    write!(out, "<qual:functionTerm qual:resultLevel=\"1\">")?;
                    write!(out, "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">")?;
                    self.write_update_function(out, update_function)?;
                    write!(out, "</math>")?;
                    write!(out, "</qual:functionTerm>")?;
                }
                write!(out, "</qual:listOfFunctionTerms>")?;
            }
            write!(out, "</qual:transition>")?;
        }
        write!(out, "</qual:listOfTransitions>")?;
        Ok(())
    }

    fn write_update_function(&self, out: &mut dyn Write, function: &FnUpdate) -> Result<(), Error> {
        match function {
            FnUpdate::Const(true) => write!(out, "<true/>")?,
            FnUpdate::Const(false) => write!(out, "<false/>")?,
            FnUpdate::Var(id) => {
                write!(
                    out,
                    "<apply><eq/><ci>{}</ci><cn type=\"integer\">1</cn></apply>",
                    self.get_variable_name(*id)
                )?;
            }
            FnUpdate::Not(inner) => {
                write!(out, "<apply><not/>")?;
                self.write_update_function(out, inner)?;
                write!(out, "</apply>")?;
            }
            FnUpdate::Binary(op, l, r) => {
                let op = match op {
                    BinaryOp::Imp => "implies",
                    BinaryOp::And => "and",
                    BinaryOp::Or => "or",
                    BinaryOp::Xor => "xor",
                    BinaryOp::Iff => "eq",
                };
                write!(out, "<apply><{}/>", op)?;
                self.write_update_function(out, l)?;
                self.write_update_function(out, r)?;
                write!(out, "</apply>")?;
            }
            FnUpdate::Param(id, args) => {
                write!(out, "<apply><csymbol>{}</csymbol>", self[*id].get_name())?;
                for arg in args {
                    self.write_update_function(out, arg)?;
                }
                write!(out, "</apply>")?;
            }
        }
        Ok(())
    }
}

fn write_layout(out: &mut dyn Write, layout: &HashMap<String, (f64, f64)>) -> Result<(), Error> {
    write!(out, "<layout:listOfLayouts xmlns:layout=\"http://www.sbml.org/sbml/level3/version1/layout/version1\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">")?;
    write!(out, "<layout:layout layout:id=\"__layout__\">")?;
    write!(out, "<layout:listOfAdditionalGraphicalObjects>")?;
    for (name, (x, y)) in layout {
        write!(
            out,
            "<layout:generalGlyph layout:id=\"_ly_{}\" layout:reference=\"{}\">",
            name, name
        )?;
        write!(out, "<layout:boundingBox>")?;
        write!(
            out,
            "<layout:position layout:x=\"{}\" layout:y=\"{}\"/>",
            x, y
        )?;
        write!(
            out,
            "<layout:dimensions layout:height=\"25\" layout:width=\"45\"/>"
        )?;
        write!(out, "</layout:boundingBox>")?;
        write!(out, "</layout:generalGlyph>")?;
    }
    write!(out, "</layout:listOfAdditionalGraphicalObjects>")?;
    write!(out, "</layout:layout>")?;
    write!(out, "</layout:listOfLayouts>")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::BooleanNetwork;
    use pretty_assertions::assert_eq;
    use std::collections::HashMap;
    use std::convert::TryFrom;

    #[test]
    fn test_sbml_export() {
        let model = BooleanNetwork::try_from(
            "
            a -? a
            c -? a
            # This regulation is used in the function and therefore must
            # use our custom `essential` attribute in order to preserved
            # that it is in fact not essential.
            a ->? b
            a ->? c
            b -| c
            # Also some comments are allowed
            c -| d
            $a: a & (p(c) => (c | c))
            $b: p(a) <=> q(a, a)
            # Notice that a regulates c but does not appear in the function!
            $c: q(b, b) => !(b ^ r)
        ",
        )
        .unwrap();
        let mut expected_layout = HashMap::new();
        expected_layout.insert("a".to_string(), (1.0, 2.0));
        expected_layout.insert("b".to_string(), (1.5, 2.8));
        expected_layout.insert("c".to_string(), (1542.123, -4.333));
        expected_layout.insert("d".to_string(), (121.776, 2.0));
        let sbml = model.to_sbml(Some(&expected_layout));
        let (actual, layout) = BooleanNetwork::try_from_sbml(&sbml).unwrap();
        assert_eq!(model, actual);
        assert_eq!(expected_layout, layout);
    }
}
