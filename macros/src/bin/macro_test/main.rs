use ravencheck_macros::verify;
use ravenlang::CheckedSig;

fn main() {
    let mut sig = CheckedSig::empty();
    sig.add_sort("Nat");

    verify!(&sig, forall(|a:Nat| a == a));
}
