import .lovelib


/-! # LoVe Homework 7: Metaprogramming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (9 points): A `mindless` Tactic

We develop a tactic that automates some of the mindless `intro`/`apply`
proofs that formed the core of lecture 2.

We proceed in three steps.

1.1 (6 points). Develop a `mindless_safe` tactic that applies the
introduction rules for `true`, `∧`, and `↔`, that invokes `tactic.intro` (or
`tactic.intro1`) for `→`/`∀`, and that invokes `tactic.assumption`, repeatedly
on all goals. The tactic generalizes `intro_ands` from the exercise.

Hint: You can use the `<|>` operator between the rules/tactics used for
different symbols. -/

#check tactic.repeat
#check tactic.applyc
#check tactic.intro
#check tactic.intro1

meta def mindless_safe : tactic unit :=
tactic.repeat
  (tactic.applyc `true.intro
   <|> tactic.applyc `and.intro
   <|> tactic.applyc `iff.intro
   <|> (do tactic.intro1, pure ())
   <|> tactic.assumption)

lemma abcd (a b c d : Prop) (hc : c) :
  a → ¬ b ∧ (c ↔ d) :=
begin
  mindless_safe,
  /- The proof state should be roughly as follows:

  a b c d : Prop,
  hc : c,
  a_1 : a,
  a_2 : b
  ⊢ false

  a b c d : Prop,
  hc : c,
  a_1 : a,
  a_2 : c
  ⊢ d -/
  repeat { sorry }
end

/-! 1.2 (3 points). Develop a `mindless_unsafe` tactic that works on the current
goal. For each hypothesis in turn:

1. It first tries to apply the hypothesis in turn using `tactic.apply`.

2. If this does not fail, it invokes some `continue` tactic, which is passed as
   argument.

3. If this does not fail, it invokes `tactic.done`, which succeeds only if there
   are no goals left.

Once a hypothesis has been found for which steps 1 to 3 succeed,
`mindless_unsafe` succeeds. -/

meta def mindless_unsafe (continue : tactic unit) : tactic unit :=
do
  hs ← tactic.local_context,
  list.mfirst (λh, do tactic.apply h, continue, tactic.done) hs

/-! A few tests follow. -/

lemma modus_ponens (a b : Prop) (ha : a) (hab : a → b) :
  b :=
by mindless_unsafe tactic.assumption

lemma junky_modus_ponens (a b c d : Prop) (ha : a) (hcb : c → b) (hab : a → b)
    (hdb : d → b) :
  b :=
by mindless_unsafe tactic.assumption

lemma refl_modus_ponens (n : ℕ) (b : Prop) (hnnb : n = n → b) :
  b :=
by mindless_unsafe tactic.reflexivity

/-! Finally, everything comes together with the `mindless` tactic below. The
tactic performs a depth-bounded search for a proof, applying `mindless_safe`
and `mindless_unsafe` on all goals in alternation. The bound is necessary to
eventually backtrack. -/

meta def mindless : ℕ → tactic unit
| 0           := mindless_safe
| (depth + 1) :=
  do
    mindless_safe,
    tactic.all_goals (tactic.try (mindless_unsafe (mindless depth))),
    pure ()

/-! Some tests are provided below. All should succeed. -/

lemma I (a : Prop) :
  a → a :=
by mindless 0

lemma K (a b : Prop) :
  a → b → b :=
by mindless 0

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
by mindless 1

lemma proj_1st (a : Prop) :
  a → a → a :=
by mindless 0

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
by mindless 1

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
by mindless 2

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
by mindless 2

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
by mindless 2

lemma more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
by mindless 1

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
by mindless 1

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
by mindless 3

lemma one_for_the_road (a c : Prop) (ha : a) (hccc : c → c → c) (hac : a → c) :
  c :=
by mindless 1


/-! ## Question 2 (2 bonus points): An `auto` Tactic

2.1 (1 bonus point). Develop an Isabelle-style `auto` tactic.

This tactic would apply all harmless introduction and elimination rules. In
addition, it would try potentially harmful rules (such as `or.intro_left` and
`false.elim`) but backtrack at some point (or try several possibilities in
parallel). Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also attempt to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

See also "Automatic Proof and Disproof in Isabelle/HOL"
(https://www.cs.vu.nl/~jbe248/frocos2011-dis-proof.pdf) by Blanchette, Bulwahn,
and Nipkow, and the references they give.

2.2 (1 bonus point). Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise 2
and homework 2. Please include these below. -/

end LoVe
