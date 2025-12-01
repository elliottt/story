use crate::{
    arena::{Arena, Id},
    ir::{self, Action, Context, Expr},
};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct Graph<'a> {
    c: &'a Context,
    facts: Arena<Fact>,
    effects: Arena<Effect>,
}

#[derive(Debug)]
pub struct Stats {
    pub facts: usize,
    pub effects: usize,
}

impl<'a> Graph<'a> {
    pub fn build(c: &'a mut Context) -> Self {
        let mut builder = GraphBuilder {
            atom_map: AtomMap::new(),
            facts: Arena::new(),
            effects: Arena::new(),
        };

        builder.effects.reserve(c.actions.len());

        for (id, action) in c.actions.iter_with_id() {
            builder.add_action(c, id, action);
        }

        // TODO: process init and goal to ensure that those atoms make it into the graph

        builder.build(c)
    }

    pub fn stats(&self) -> Stats {
        Stats {
            facts: self.facts.len(),
            effects: self.effects.len(),
        }
    }

    pub fn reset(&mut self) {
        for fact in self.facts.iter_mut() {
            fact.level = Level::INVALID;
            fact.enabled = false;
            fact.dirty = false;
        }

        for eff in self.effects.iter_mut() {
            eff.level = Level::INVALID;
            eff.enabled = false;
            eff.dirty = false;
            eff.active_pre = 0;
        }
    }
}

/// The level that an action or fact was enabled at.
#[derive(Debug)]
struct Level {
    level: u16,
}

impl Level {
    const INVALID: Self = Level { level: u16::MAX };
}

type AtomMap<T> = HashMap<Id<ir::Predicate>, HashMap<Vec<Id<ir::Constant>>, T>>;

#[derive(Debug)]
struct GroundedAtom {
    pred: Id<ir::Predicate>,
    args: Vec<Id<ir::Constant>>,
}

#[derive(Debug)]
struct Fact {
    atom: GroundedAtom,
    level: Level,
    enabled: bool,
    dirty: bool,

    required_by: HashSet<Id<Effect>>,
    added_by: HashSet<Id<Effect>>,
    deleted_by: HashSet<Id<Effect>>,
}

#[derive(Debug)]
struct Effect {
    action: Id<ir::Action>,
    level: Level,
    enabled: bool,
    dirty: bool,

    /// The number of preconditions this effect has.
    total_pre: u16,

    /// The number of active preconditions this effect has.
    active_pre: u16,

    /// When this is an effect that requires character motivation, the actor parameter specifies
    /// the character that must be acting intentionally.
    actor: Id<ir::Constant>,

    adds: HashSet<Id<Fact>>,
    dels: HashSet<Id<Fact>>,

    intents: HashSet<(Id<ir::Constant>, Id<Fact>)>,
}

struct GraphBuilder {
    atom_map: AtomMap<Id<Fact>>,
    facts: Arena<Fact>,
    effects: Arena<Effect>,
}

impl GraphBuilder {
    fn build(self, c: &Context) -> Graph<'_> {
        Graph {
            c,
            facts: self.facts,
            effects: self.effects,
        }
    }

    fn add_fact(&mut self, atom: &ir::Atom) -> Id<Fact> {
        let args = Vec::from_iter(atom.args.iter().map(|var| var.kind.unwrap_const()));
        let preds = self.atom_map.entry(atom.pred).or_default();
        if let Some(id) = preds.get(&args) {
            *id
        } else {
            let id = self.facts.add(Fact {
                atom: GroundedAtom {
                    pred: atom.pred,
                    args: args.clone(),
                },
                level: Level::INVALID,
                enabled: false,
                dirty: false,
                required_by: HashSet::new(),
                added_by: HashSet::new(),
                deleted_by: HashSet::new(),
            });
            preds.insert(args, id);
            id
        }
    }

    fn add_action(&mut self, c: &Context, id: Id<Action>, action: &Action) -> Id<Effect> {
        let mut actor = Id::none();
        for (ix, p) in action.params.iter().enumerate() {
            if p.name == "?actor" {
                actor = action.inst[ix];
                break;
            }
        }

        let mut preconds = HashSet::new();
        self.process_pre(&mut preconds, c, action.pre);

        let mut adds = HashSet::new();
        let mut dels = HashSet::new();
        let mut intents = HashSet::new();
        self.process_adds_dels_intents(&mut adds, &mut dels, &mut intents, c, action.effect);

        let eid = self.effects.add(Effect {
            action: id,
            level: Level::INVALID,
            enabled: false,
            dirty: false,
            total_pre: u16::try_from(preconds.len()).unwrap(),
            active_pre: 0,
            actor,
            adds,
            dels,
            intents,
        });

        for id in &preconds {
            self.facts[*id].required_by.insert(eid);
        }
        for id in &self.effects[eid].adds {
            self.facts[*id].added_by.insert(eid);
        }
        for id in &self.effects[eid].dels {
            self.facts[*id].deleted_by.insert(eid);
        }

        eid
    }

    fn process_pre(&mut self, preconds: &mut HashSet<Id<Fact>>, c: &Context, e: Id<Expr>) {
        match &c.exprs[e] {
            Expr::Atom { atom, .. } => {
                preconds.insert(self.add_fact(&c.atoms[*atom]));
            }
            Expr::Eq { .. } => {
                panic!("Equality should have been eliminated before graph building");
            }
            Expr::And { exprs } => {
                for e in exprs {
                    self.process_pre(preconds, c, *e);
                }
            }
            Expr::True | Expr::False => {}
        }
    }

    fn process_adds_dels_intents(
        &mut self,
        adds: &mut HashSet<Id<Fact>>,
        dels: &mut HashSet<Id<Fact>>,
        intents: &mut HashSet<(Id<ir::Constant>, Id<Fact>)>,
        c: &Context,
        id: Id<ir::Effect>,
    ) {
        match &c.effects[id] {
            ir::Effect::Atom { neg, atom } => {
                let fact = self.add_fact(&c.atoms[*atom]);
                if *neg {
                    dels.insert(fact);
                } else {
                    adds.insert(fact);
                }
            }
            ir::Effect::Intends { actor, neg, atom } => {
                assert!(
                    !*neg,
                    "Negation should have been removed from intents before graph construction"
                );
                let fact = self.add_fact(&c.atoms[*atom]);
                intents.insert((actor.kind.unwrap_const(), fact));
            }
            ir::Effect::And { effects } => {
                for id in effects {
                    self.process_adds_dels_intents(adds, dels, intents, c, *id);
                }
            }
            ir::Effect::True => {}
        }
    }
}
