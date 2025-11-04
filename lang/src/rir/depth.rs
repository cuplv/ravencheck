use crate::{
    Comp,
};

impl Comp {
    pub fn binder_depth(mut self) -> (usize, usize) {
        let mut all_depth: usize = 0;
        let mut b1_depth: usize = 0;
        loop {
            match self {
                Self::Bind1(_b, _x, m) => {
                    all_depth = all_depth + 1;
                    b1_depth = b1_depth + 1;
                    self = *m;
                }
                Self::BindN(_b, _ps, m) => {
                    all_depth = all_depth + 1;
                    self = *m;
                }
                Self::Ite(_, tb, eb) => {
                    let (t_all, t_bin) = tb.binder_depth();
                    let (e_all, e_bin) = eb.binder_depth();
                    return (
                        t_all.max(e_all) + all_depth,
                        t_bin.max(e_bin) + b1_depth,
                    )
                }
                Self::Return(_vs) => return (all_depth, b1_depth),
                m => panic!("no binder_depth for {:?}", m),
            }
        }
    }
}
