//! Used for reading SBML layout specifications.

use crate::sbml::import::{SBML_LAYOUT, child_tags, read_unique_child};
use roxmltree::Node;
use std::collections::HashMap;

/// A very simple representation of the SBML layout XML object.
///
/// If contains dimensions of the layout and a mapping
/// from SBML ids to coordinates in such layout.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SbmlLayout {
    pub dimensions: (f64, f64),
    pub glyphs: HashMap<String, (f64, f64)>,
}

pub fn read_sbml_layout(model: Node) -> Result<SbmlLayout, String> {
    let layout_list = read_unique_child(model, (SBML_LAYOUT, "listOfLayouts"))?;

    let layouts = child_tags(layout_list, (SBML_LAYOUT, "layout"));

    if layouts.is_empty() {
        return Err("No layout found.".to_string());
    }

    // If there are multiple layouts, just pick the first one.

    let mut result = SbmlLayout {
        dimensions: (0.0, 0.0),
        glyphs: HashMap::new(),
    };

    let layout = layouts[0];

    let dimensions = read_unique_child(layout, (SBML_LAYOUT, "dimensions")).ok();

    if let Some(dimensions) = dimensions {
        if let Some(width) = dimensions.attribute((SBML_LAYOUT, "width")) {
            result.dimensions.0 = str_to_f64(width)?;
        }
        if let Some(height) = dimensions.attribute((SBML_LAYOUT, "height")) {
            result.dimensions.1 = str_to_f64(height)?;
        }
    }

    let glyph_list =
        read_unique_child(layout, (SBML_LAYOUT, "listOfAdditionalGraphicalObjects")).ok();
    if let Some(glyph_list) = glyph_list {
        let glyphs = child_tags(glyph_list, (SBML_LAYOUT, "generalGlyph"));
        for glyph in glyphs {
            if let Some(reference) = glyph.attribute((SBML_LAYOUT, "reference")) {
                let bounding_box = read_unique_child(glyph, (SBML_LAYOUT, "boundingBox")).ok();

                if let Some(bounding_box) = bounding_box {
                    let position = read_unique_child(bounding_box, (SBML_LAYOUT, "position")).ok();

                    if let Some(position) = position {
                        let mut coordinates = (0.0, 0.0);
                        if let Some(x) = position.attribute((SBML_LAYOUT, "x")) {
                            coordinates.0 = str_to_f64(x)?;
                        }
                        if let Some(y) = position.attribute((SBML_LAYOUT, "y")) {
                            coordinates.1 = str_to_f64(y)?;
                        }

                        result.glyphs.insert(reference.to_string(), coordinates);
                    }
                }
            }
        }
    }

    Ok(result)
}

fn str_to_f64(str: &str) -> Result<f64, String> {
    if let Ok(value) = str.parse::<f64>() {
        Ok(value)
    } else {
        Err(format!("Invalid numeric value: {}.", str))
    }
}
