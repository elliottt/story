
use crate::storage::{Index,Storage};

use std::collections::BTreeSet;

pub(crate) type Level = u32;

/// The plan graph, similar in structure to the graph of the fast-forward planner.
pub(crate) struct Graph {
    pub(crate) facts: Storage<Fact>,
    pub(crate) effects: Storage<Effect>,
}

#[derive(Default)]
pub(crate) struct Fact {
    /// Present when this fact ws marked true at a given level of the relaxed graph.
    pub(crate) is_true: Option<Level>,

    /// True when this fact is part of the relaxed goal state.
    pub(crate) is_goal: bool,

    /// All effects that this fact is a precondition for.
    pub(crate) pre_cond: BTreeSet<Index<Effect>>,
}

pub(crate) struct Effect {
    /// The facts that this effect requires for activation.
    pub(crate) pre_conds: BTreeSet<Index<Fact>>,

    /// The number of preconditions remaining to activate. This value is seeded with the size of
    /// the `pre_conds` set, and is decremented each time a precondition activates. Once this
    /// number reaches zero, the effect activates on the next level of the plan.
    pub(crate) num_pre_conds: u32,

    /// The facts that this effect will add to the current state.
    pub(crate) adds: BTreeSet<Index<Fact>>,

    /// The facts that this effect will remove from the current state.
    pub(crate) dels: BTreeSet<Index<Fact>>,

    /// The level in which this effect was made active. `None` indicates that the plan doesn't
    /// include this effect.
    pub(crate) level: Option<Level>,
}
