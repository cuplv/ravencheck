/// This is like cross-product, but missing some values. While
/// cross-product includes (A,A), (A,B), and (B,A), this only includes
/// (A,B) or (B,A).
pub fn unordered_cross<T: Clone>(mut vs: Vec<T>) -> Vec<(T,T)>
{
    let mut pairs = Vec::new();
    while let Some(v1) = vs.pop() {
        for v2 in &vs {
            pairs.push((v1.clone(),v2.clone()));
        }
    }
    pairs
}
