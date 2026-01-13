use crate::{
    Binder1,
    BType,
    Comp,
    Ident,
    LogOpN,
    Quantifier,
    Sig,
    Val,
};

use graph_cycles::Cycles;
use petgraph::graph::Graph;

use std::collections::HashMap;
use std::collections::HashSet;

pub struct SortIndex(pub Vec<BType>);

pub type Cycle = Vec<BType>;

pub fn render_cycle(c: &Cycle) -> String {
    if c.len() == 1 {
        format!("self-loop ⤷ {} ⤴", c[0])
    } else {
        // Normalize the starting-point of the cycle so that we can
        // test based on error message matches.
        let c = normalize_cycle(c.clone());
        let mut s = String::new();
        let mut first = true;
        s.push_str("⤷ ");
        for b in c {
            if first {
                s.push_str(&format!("{} ", b));
            } else {
                s.push_str(&format!("→ {} ", b));
            }
            first = false;
        }
        s.push_str(&format!("⤴"));
        s
    }
}

// Rotate the cycle to start with the alphabetically-first sort.
fn normalize_cycle(c: Cycle) -> Cycle {
    if c.len() <= 1 {
        c
    } else {
        let mut idxs: Vec<(usize, &BType)> = c.iter().enumerate().collect();
        // Sort by comparing the string renderings.
        idxs.sort_by(|b1,b2| b1.1.render().cmp(&b2.1.render()));
        // Get the index of the first item.
        let head = idxs[0].0;

        let mut out = Vec::with_capacity(c.len());
        for i in 0..(c.len()) {
            out.push(c[(head + i) % c.len()].clone());
        }
        out
    }
}

impl SortIndex {
    fn to_index(&self, s: &BType) -> usize {
        for (i,s1) in self.0.iter().enumerate() {
            if s1 == s {
                return i
            }
        }
        panic!("No index found for base type {}", s)
    }
    fn from_index(&self, i: usize) -> BType {
        self.0[i].clone()
    }
}

#[derive(Clone, PartialEq, Eq)]
enum QNode {
    Exists(Vec<BType>, QTree),
    Forall(Vec<BType>, QTree),
}

impl QNode {
    fn negate(&self) -> Self {
        match self {
            Self::Exists(bs, t) =>
                Self::Forall(bs.clone(), t.negate()),
            Self::Forall(bs, t) =>
                Self::Exists(bs.clone(), t.negate()),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
struct QTree(Vec<QNode>);

impl QTree {
    fn new() -> Self { Self(Vec::new()) }
    fn merge(&mut self, mut other: Self) {
        self.0.append(&mut other.0);
    }
    fn negate(&self) -> Self {
        Self(self.0.iter().map(|n| n.negate()).collect())
    }
    fn wrap_with(self, q: Quantifier, bs: Vec<BType>) -> Self {
        let n = match q {
            Quantifier::Exists => QNode::Exists(bs, self),
            Quantifier::Forall => QNode::Forall(bs, self),
        };
        QTree(vec![n])
    }
    fn merge_vals<'a,I: Iterator<Item=&'a Val>>(
        &mut self,
        ctx: &HashMap<Ident, Option<Self>>,
        vs: I,
        also_negate: bool,
    ) {
        for v in vs {
            match v {
                Val::Literal(_) => {},
                Val::OpCode(..) => {},
                Val::Var(x, _, _, _) => match ctx.get(x) {
                    // This is a proposition
                    Some(Some(qt)) => {
                        self.merge(qt.clone());
                        if also_negate {
                            self.merge(qt.negate());
                        }
                    }
                    // This is a quantified value
                    Some(None) => {}
                    // Assume this is a constructor
                    None => {}
                }
                v => panic!("epr_check found unexpected val form in an equation: {:?}", v),
            }
        }
    }

    /// Record the tree's Forall->Exists alternations in a sort graph.
    fn sort_graph(&self) -> SortGraph {
        let mut graph = SortGraph::new();
        self.sort_graph_r(&mut graph, HashSet::new());
        graph
    }

    fn sort_graph_r(
        &self,
        graph: &mut SortGraph,
        within_foralls: HashSet<BType>,
    ) {
        for n in &self.0 {
            match n {
                QNode::Exists(bs, t) => {
                    for b1 in &within_foralls {
                        for b2 in bs {
                            graph.add_edge(b1.clone(), b2.clone());
                        }
                    }
                    t.sort_graph_r(graph, within_foralls.clone());
                }
                QNode::Forall(bs, t) => {
                    let mut fs = within_foralls.clone();
                    for b in bs {
                        fs.insert(b.clone());
                    }
                    t.sort_graph_r(graph, fs);
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct SortGraph(HashSet<(BType,BType)>);

impl SortGraph {
    pub fn new() -> Self { SortGraph(HashSet::new()) }
    fn add_edge(&mut self, s1: BType, s2: BType) {
        assert!(
            s1 != BType::prop() && s2 != BType::prop(),
            "sort graph edges should not be on 'bool'",
        );
        self.0.insert((s1,s2));
    }
    pub fn get_cycles(&self) -> Vec<Vec<BType>> {
        let index = self.get_index();
        let mut i_graph = Vec::new();
        for (s1,s2) in self.0.iter() {
            let i1 = index.to_index(s1);
            let i2 = index.to_index(s2);
            i_graph.push((i1 as u32,i2 as u32));
        }
        let g = Graph::<(), ()>::from_edges(i_graph);
        let mut cycles = Vec::new();
        g.visit_all_cycles(|_g, c| {
            let mut c_s = Vec::new();
            for i in c.iter() {
                c_s.push(index.from_index(i.index()));
            }
            cycles.push(c_s);
        });
        cycles
    }
    fn get_index(&self) -> SortIndex {
        let mut sorts = HashSet::new();
        for (s1,s2) in self.0.iter() {
            sorts.insert(s1.clone());
            sorts.insert(s2.clone());
        }
        SortIndex(sorts.into_iter().collect())
    }
    pub fn append(&mut self, other: Self) {
        self.0.extend(other.0);
    }
}

pub fn test() -> Graph<(), ()> {
    let g = Graph::<(), ()>::from_edges([
        (1, 2),
        (2, 3),
        (3, 4),
        (3, 2),
    ]);
    g.visit_all_cycles(|_g, c| {
        println!("Cycle: {c:?}");
    });
    g
}

impl Comp {
    pub fn sort_graph(&self) -> SortGraph {
        // self.sort_graph_r(HashSet::new())
        let t = self.qtree();
        t.sort_graph()
    }

    fn qtree(&self) -> QTree {
        self.qtree_r(HashMap::new())
    }

    fn qtree_r(&self, mut ctx: HashMap<Ident, Option<QTree>>) -> QTree {
        // In the context, x := Some(t) means that x is a proposition
        // with qtree t.  x := None means that x is a quantified
        // value, which has no qtree.  If x is not present, it means
        // that x is unbound, or a constructor.
        match self {
            Comp::Bind1(Binder1::LogQuantifier(q, xs, body), x, m) => {
                let mut bs = Vec::new();
                let mut body_ctx = ctx.clone();
                for (qx,qt) in xs {
                    // Record qx as a quantified value, shadowing any
                    // proposition that was already in the context
                    // under that name.
                    body_ctx.insert(qx.clone(), None);
                    // Collect the quantified base types, which will
                    // define the qnode for this quantifier.
                    for s in qt.clone().flatten() {
                        bs.push(s.unwrap_base().unwrap())
                    }
                }
                // Get the qtree of the body, and wrap it in a qnode
                // that describes this quantifier.
                let t = body.qtree_r(body_ctx).wrap_with(*q, bs);
                // Record x as a proposition, described by the qtree.
                ctx.insert(x.clone(), Some(t));
                // Process the rest of the computation.
                m.qtree_r(ctx)
            }
            Comp::Bind1(Binder1::Eq(_pol, left_vs, right_vs), x, m) => {
                // The polarity (whether this is is_eq or is_not_eq)
                // doesn't make a difference for the qtree.

                let mut t = QTree::new();
                // For each proposition we find among the equated
                // values, we add its qtree twice (positive and
                // negative) to x's qtree.
                t.merge_vals(&ctx, left_vs.iter().chain(right_vs), true);

                ctx.insert(x.clone(), Some(t));
                m.qtree_r(ctx)
            }
            Comp::Bind1(Binder1::LogOpN(op, vs), x, m) => {
                let mut t = QTree::new();
                match op {
                    LogOpN::Pred(..) => {
                        t.merge_vals(&ctx, vs.iter(), true);
                    }
                    LogOpN::Or | LogOpN::And => {
                        t.merge_vals(&ctx, vs.iter(), false);
                    }
                }
                ctx.insert(x.clone(), Some(t));
                m.qtree_r(ctx)
            }
            Comp::Ite(v, m1, m2) => {
                let mut t = QTree::new();
                t.merge_vals(&ctx, std::iter::once(v), true);
                t.merge(m1.qtree_r(ctx.clone()));
                t.merge(m2.qtree_r(ctx));
                t
            }
            Comp::Return(vs) => {
                let mut t = QTree::new();
                t.merge_vals(&ctx, vs.iter(), false);
                t
            }
            
            c => panic!("qtree_r can't handle {:?}", c)
        }
    }
}

impl Sig {
    pub fn sort_graph_combined(&self, term: &Comp) -> SortGraph {
        let (_, axioms) = self.relevant_with_axioms(term);

        let mut graph = SortGraph::new();

        for a in &axioms {
            graph.append(a.sort_graph());
        }

        graph.append(term.sort_graph());

        graph
    }

    // pub fn sort_graph(&self) -> SortGraph {
    //     // Operator axioms are counted when they are spliced into the
    //     // main assertion, so we only look at the axioms here.
    //     let mut graph = SortGraph::new();
    //     for a in self.axioms.iter() {
    //         graph.append(a.sort_graph());
    //     }
    //     graph
    // }
}
