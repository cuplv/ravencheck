use crate::{
    Binder1,
    Comp,
    Quantifier,
    Sig,
};

use graph_cycles::Cycles;
use petgraph::graph::Graph;

use std::collections::HashSet;

pub struct SortIndex(pub Vec<String>);

impl SortIndex {
    fn to_index(&self, s: &str) -> usize {
        for (i,s1) in self.0.iter().enumerate() {
            if s1 == s {
                return i
            }
        }
        panic!("No index found for sort {}", s)
    }
    fn from_index(&self, i: usize) -> String {
        self.0[i].clone()
    }
}

#[derive(Clone)]
pub struct SortGraph(HashSet<(String,String)>);

impl SortGraph {
    pub fn new() -> Self { SortGraph(HashSet::new()) }
    fn add_edge(&mut self, s1: String, s2: String) {
        self.0.insert((s1,s2));
    }
    pub fn get_cycles(&self) -> Vec<Vec<String>> {
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
        self.sort_graph_r(HashSet::new())
    }
    fn sort_graph_r(&self, foralls: HashSet<String>) -> SortGraph {
        match self {
            Comp::Bind1(Binder1::LogQuantifier(q, xs, body), _x, m) => {
                let mut q_sorts = Vec::new();
                for (_x,t) in xs {
                    for s in t.clone().flatten() {
                        q_sorts.push(s.unwrap_atom().unwrap().unwrap_ui())
                    }
                }
                match q {
                    Quantifier::Exists => {
                        // If we encounter an Exists quantifier, then
                        // edges to the newly-quantified sorts are
                        // recorded from every Forall-quantified sort that
                        // we are under.
                        let mut graph = body.sort_graph_r(foralls.clone());
                        for f_s in foralls.iter() {
                            for e_s in q_sorts.iter() {
                                graph.add_edge(f_s.clone(), e_s.clone());
                            }
                        }
                        graph.append(m.sort_graph_r(foralls));
                        graph
                    }
                    Quantifier::Forall => {
                        // If we encounter an Forall quantifier, we record
                        // its sorts before descending into the body.
                        //
                        // We *don't* use those sorts when descending on
                        // the continuation, which is outside the
                        // quantifier scope.
                        let mut body_foralls = foralls.clone();
                        for s in q_sorts {
                            body_foralls.insert(s);
                        }
                        let mut graph = body.sort_graph_r(body_foralls);
                        graph.append(m.sort_graph_r(foralls));
                        graph
                    }
                }
            }
            Comp::Bind1(b, _x, m) => match b {
                Binder1::Eq(..) |
                Binder1::LogNot(..) |
                Binder1::LogOpN(..) => {
                    m.sort_graph_r(foralls)
                }
                b => panic!(
                    "Unexpected {:?} encounterd during sort_graph",
                    b
                ),
            }
            Comp::Ite(_v, m1, m2) => {
                let mut graph = m1.sort_graph_r(foralls.clone());
                graph.append(m2.sort_graph_r(foralls));
                graph
            }
            Comp::Return(_vs) => SortGraph::new(),
            m => todo!("sort_graph_r for {:?}", m),
        }
    }
}

impl Sig {
    pub fn sort_graph(&self) -> SortGraph {
        // Operator axioms are counted when they are spliced into the
        // main assertion, so we only look at the axioms here.
        let mut graph = SortGraph::new();
        for a in self.axioms.iter() {
            graph.append(a.sort_graph());
        }
        graph
    }
}
