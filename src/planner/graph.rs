use crate::{
    arena::{Arena, Id, IdSet},
    ir::{self, Action, Context, Expr},
    printing,
};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct Graph<'a> {
    pub c: &'a Context,
    facts: Arena<Fact>,
    effects: Arena<Effect>,
}

#[derive(Debug)]
pub struct Stats {
    pub facts: usize,
    pub effects: usize,
}

impl<'a> Graph<'a> {
    pub fn build(c: &'a mut Context) -> (Self, IdSet<Fact>, IdSet<Fact>) {
        let num_effects = c.actions.len();

        let mut builder = GraphBuilder {
            num_effects,
            atom_map: HashMap::new(),
            facts: Arena::new(),
            effects: Arena::new(),
        };

        builder.effects.reserve(num_effects);

        // pre-populate the facts and effects, so that we can precisely allocate the bitsets.
        let mut eff_ids = Vec::with_capacity(num_effects);
        for (id, action) in c.actions.iter_with_id() {
            eff_ids.push(builder.enter_effect(c, id, action));
        }

        for (id, action) in eff_ids.into_iter().zip(c.actions.iter()) {
            builder.update_action(c, id, action);
        }

        builder.enter_adds_dels_intents(c, c.init);
        builder.enter_pre(c, c.goal);

        // It's fine for deletions to exist in the initial state, as they can be safely ignored
        // after negative preconditions have been translated away.
        let mut dels = IdSet::with_capacity(builder.facts.len());

        // Only defined to reuse process_adds_dels_intents.
        let mut intents = Vec::new();

        let mut init = IdSet::with_capacity(builder.facts.len());
        builder.process_adds_dels_intents(&mut init, &mut dels, &mut intents, c, c.init);
        assert!(
            intents.is_empty(),
            "Intents aren't supported in the init state"
        );

        let mut goal = IdSet::with_capacity(builder.facts.len());
        builder.process_pre(&mut goal, c, c.goal);

        (builder.build(c), init, goal)
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

#[derive(Debug)]
struct GroundedAtom {
    pred: Id<ir::Predicate>,
    args: Vec<Id<ir::Constant>>,
}

#[derive(Debug)]
pub struct Fact {
    atom: GroundedAtom,
    level: Level,
    enabled: bool,
    dirty: bool,

    required_by: IdSet<Effect>,
    added_by: IdSet<Effect>,
    deleted_by: IdSet<Effect>,
}

#[derive(Debug)]
pub struct Intent {
    pub actor: Id<ir::Constant>,
    pub fact: Id<Fact>,
}

impl Intent {
    pub fn new(actor: Id<ir::Constant>, fact: Id<Fact>) -> Self {
        Self { actor, fact }
    }
}

pub type Intents = Vec<Intent>;

#[derive(Debug)]
pub struct Effect {
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

    adds: IdSet<Fact>,
    dels: IdSet<Fact>,

    intents: Intents,
}

struct GraphBuilder {
    num_effects: usize,
    atom_map: HashMap<Id<ir::Atom>, Id<Fact>>,
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

    fn get_fact(&self, atom: Id<ir::Atom>) -> Id<Fact> {
        *self.atom_map.get(&atom).unwrap()
    }

    fn enter_fact(&mut self, id: Id<ir::Atom>, atom: &ir::Atom) -> Id<Fact> {
        *self.atom_map.entry(id).or_insert_with(|| {
            let args = Vec::from_iter(atom.args.iter().map(|var| var.kind.unwrap_const()));
            self.facts.add(Fact {
                atom: GroundedAtom {
                    pred: atom.pred,
                    args: args,
                },
                level: Level::INVALID,
                enabled: false,
                dirty: false,
                required_by: IdSet::with_capacity(self.num_effects),
                added_by: IdSet::with_capacity(self.num_effects),
                deleted_by: IdSet::with_capacity(self.num_effects),
            })
        })
    }

    fn enter_effect(&mut self, c: &Context, id: Id<Action>, action: &Action) -> Id<Effect> {
        self.enter_pre(c, action.pre);
        self.enter_adds_dels_intents(c, action.effect);

        self.effects.add(Effect {
            action: id,
            level: Level::INVALID,
            enabled: false,
            dirty: false,
            total_pre: 0,
            active_pre: 0,
            actor: Id::none(),
            adds: IdSet::new(),
            dels: IdSet::new(),
            intents: Vec::new(),
        })
    }

    fn enter_pre(&mut self, c: &Context, e: Id<Expr>) {
        match &c.exprs[e] {
            Expr::Atom { atom, .. } => {
                self.enter_fact(*atom, &c.atoms[*atom]);
            }
            Expr::Eq { .. } => {
                panic!("Equality should have been eliminated before graph building");
            }
            Expr::And { exprs } => {
                for e in exprs {
                    self.enter_pre(c, *e);
                }
            }
            Expr::True | Expr::False => {}
        }
    }

    fn enter_adds_dels_intents(&mut self, c: &Context, id: Id<ir::Effect>) {
        match &c.effects[id] {
            &ir::Effect::Atom { atom, .. } => {
                self.enter_fact(atom, &c.atoms[atom]);
            }
            &ir::Effect::Intends { neg, atom, .. } => {
                assert!(
                    !neg,
                    "Negation should have been removed from intents before graph construction"
                );
                self.enter_fact(atom, &c.atoms[atom]);
            }
            ir::Effect::And { effects } => {
                for id in effects {
                    self.enter_adds_dels_intents(c, *id);
                }
            }
            ir::Effect::True => {}
        }
    }

    fn update_action(&mut self, c: &Context, eid: Id<Effect>, action: &Action) {
        let mut preconds = IdSet::with_capacity(self.facts.len());
        self.process_pre(&mut preconds, c, action.pre);

        let mut adds = IdSet::with_capacity(self.facts.len());
        let mut dels = IdSet::with_capacity(self.facts.len());
        let mut intents = Vec::new();
        self.process_adds_dels_intents(&mut adds, &mut dels, &mut intents, c, action.effect);

        for id in preconds.iter() {
            self.facts[id].required_by.insert(eid);
        }
        for id in adds.iter() {
            self.facts[id].added_by.insert(eid);
        }
        for id in dels.iter() {
            self.facts[id].deleted_by.insert(eid);
        }

        let eff = &mut self.effects[eid];

        eff.total_pre = u16::try_from(preconds.len()).unwrap();
        eff.adds = adds;
        eff.dels = dels;
        eff.intents = intents;

        for (ix, p) in action.params.iter().enumerate() {
            if p.name == "?actor" {
                eff.actor = action.inst[ix];
                break;
            }
        }
    }

    fn process_pre(&mut self, preconds: &mut IdSet<Fact>, c: &Context, e: Id<Expr>) {
        match &c.exprs[e] {
            Expr::Atom { neg, atom } => {
                assert!(
                    !*neg,
                    "Negation should have been removed from intents before graph construction {}",
                    printing::show(c, &c.exprs[e])
                );
                preconds.insert(self.get_fact(*atom));
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
        adds: &mut IdSet<Fact>,
        dels: &mut IdSet<Fact>,
        intents: &mut Intents,
        c: &Context,
        id: Id<ir::Effect>,
    ) {
        match &c.effects[id] {
            ir::Effect::Atom { neg, atom } => {
                let fact = self.get_fact(*atom);
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
                let fact = self.get_fact(*atom);
                intents.push(Intent::new(actor.kind.unwrap_const(), fact));
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
