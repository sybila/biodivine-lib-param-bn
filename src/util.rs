use std::collections::HashMap;
use std::hash::Hash;

/// Build a mapping from elements of the given vector to their respective indices.
///
/// TODO: Move to std-lib
/// **Warning:** Duplicates are not detected or handled in any way, they are just overwritten.
pub fn build_index_map<T, F, R>(keys: &Vec<T>, transform_index: F) -> HashMap<T, R>
where
    F: Fn(&T, usize) -> R,
    T: Clone + Hash + PartialEq + Eq,
{
    let mut result = HashMap::new();
    for i in 0..keys.len() {
        let item = &keys[i];
        result.insert(item.clone(), transform_index(item, i));
    }
    return result;
}
