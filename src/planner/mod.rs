use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashSet},
    sync::Arc,
};
use {
    crate::arena::{Id, IdSet},
    graph::{Effect, Fact, Intents},
};

mod graph;
mod relevant_actions;

pub use graph::Graph;
pub use relevant_actions::relevant_actions;

/// A node in the search space, along with its heuristic weight.
#[derive(Debug, PartialOrd)]
struct Node {
    /// The effect applied in this state. If the id is invalid, this is the init state.
    effect: Id<Effect>,

    /// The heuristic value for this node in the graph.
    distance: usize,

    /// The previous node that was applied, empty if this was a node from the init state.
    parent: Option<SearchNode>,

    state: IdSet<graph::Fact>,

    intents: Intents,
}

#[derive(Clone, Debug)]
struct SearchNode {
    node: Arc<Node>,
}

impl PartialEq for SearchNode {
    fn eq(&self, other: &Self) -> bool {
        self.node.distance == other.node.distance
    }
}

impl Eq for SearchNode {}

impl PartialOrd for SearchNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SearchNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.node.distance.cmp(&other.node.distance)
    }
}

struct Planner<'a> {
    seen: HashSet<IdSet<Fact>>,
    work: BinaryHeap<Reverse<SearchNode>>,
    graph: Graph<'a>,
    goal: IdSet<Fact>,
}

impl<'a> Planner<'a> {
    fn new(graph: Graph<'a>, init: IdSet<Fact>, goal: IdSet<Fact>) -> Self {
        let mut p = Self {
            seen: HashSet::new(),
            work: BinaryHeap::new(),
            graph,
            goal,
        };

        p.push(Id::none(), init, None, Intents::new());

        p
    }

    /// Compute how far the current state is from the goal state.
    fn heuristic(&mut self, state: &IdSet<Fact>) -> usize {
        usize::MAX
    }

    /// Add a node to the search space for the given state.
    fn push(
        &mut self,
        effect: Id<Effect>,
        state: IdSet<Fact>,
        parent: Option<SearchNode>,
        intents: Intents,
    ) {
        if self.seen.insert(state.clone()) {
            let distance = self.heuristic(&state);
            self.work.push(Reverse(SearchNode {
                node: Arc::new(Node {
                    effect,
                    distance,
                    parent,
                    state,
                    intents,
                }),
            }))
        }
    }

    fn pop(&mut self) -> Option<SearchNode> {
        self.work.pop().map(|r| r.0)
    }
}

pub fn plan(graph: Graph<'_>, init: IdSet<Fact>, goal: IdSet<Fact>) -> Option<Vec<Id<Effect>>> {
    let mut p = Planner::new(graph, init, goal);

    while let Some(node) = p.pop() {
        println!("node: {:?}", node.node);
    }

    None
}
