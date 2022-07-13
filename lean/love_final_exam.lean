import .lovelib


/-! # LoVe Final Exam

## Proof Guidelines

We expect detailed, rigorous, mathematical proofs, but we do not ask you to
write Lean proofs. You are welcome to use standard mathematical notation or Lean
structured commands (e.g., `assume`, `have`, `show`, `calc`). You can even use
tactical proofs (e.g., `intro`, `apply`), but then please indicate some of the
intermediate goals, so that we can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Unless specified otherwise, minor proof steps corresponding to
`refl`, `simp`, or `linarith` need not be justified if you think they are
obvious, but you should say which key lemmas they depend on.

You should be explicit whenever you use a function definition or an introduction
rule for an inductive predicate, especially for functions and predicates that
are specific to an exam question.

## In Case of Ambiguities or Errors in an Exam Question

The staff present at the exam has the lecturer's phone number, in case of
questions or issues concerning a specific exam question. Nevertheless, we
strongly recommend that you work things out yourselves, stating explicitly any
ambiguity or error and explaining how you interpret or repair the question. The
more explicit you are, the easier it will be for the lecturers to grade the
question afterwards.  -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (15 points): Connectives and quantifiers

The following two subquestions are about basic mastery of logic. Please provide
highly detailed proofs.

1a (6 points). Give a detailed proof of the following lemma about universal
quantification and disjunction. Make sure to emphasize and clearly label every
step corresponding to the introduction or elimination of connective. -/

lemma about_forall_and_or {α : Type} (p q : α → Prop) :
  (∀x, p x) → (∀x, q x) → (∀x, p x ∨ q x) :=
--sol sorry
begin
  intro hpx,
  intro hqx,
  intro a,
  apply or.intro_left,
  apply hpx a
end

/-! Assume `∀x, p x` and `∀x, q x`. Fix `a`. To prove `p a ∨ q a`, by the left
introduction rule of `∨`, it suffices to prove `p a`. This corresponds to
`∀x, p x` instantiated with `a`. -/
--los

/-! 1b (9 points). Prove the following one-point rule for existential
quantification. In your proof, identify clearly which witness is supplied for
the quantifier. -/

lemma exists.one_point_rule {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t ∧ p x) ↔ p t :=
--sol sorry
iff.intro
  (assume hex : ∃x : α, x = t ∧ p x,
   show p t,
     begin
       cases hex,
       cases hex_h,
       rw hex_h_left at hex_h_right,
       exact hex_h_right
     end)
  (assume hp : p t,
   show ∃x : α, x = t ∧ p x,
     begin
       apply exists.intro t,
       apply and.intro,
       { refl },
       { exact hp }
     end)

/-! By `↔`-introduction, it suffices to show
(1) (∃x : α, x = t ∧ p x) → p t
and
(2) p t → (∃x : α, x = t ∧ p x)

Let's start with (2). Assume `p t`. With the `∃`-introduction rule, instantiate
`x` with `t`, and then we must prove `t = t ∧ p t`. By `∧`-introduction, it
suffices to prove `t = t` and `p t`. The first formula is an instance of
reflexivity of `=` and the second formula corresponds to an assumption.

For (1), we assume `∃x : α, x = t ∧ p x` and show `p t`. From the
assumption, by `∃`-elimination there exists a witness `y` such that
`y = t` and `p y`. Using `y = t`, we rewrite `p y` into `p t`, as desired. -/
--los


/-! ## Question 2 (17 points): Lambda-terms

Consider the following inductive type representing untyped `λ`-terms, where
* `lam.var x` represents the variable `x`;
* `lam.abs x t` represents the `λ`-abstraction `λx, t`;
* `lam.app t t'` represents the application `t t'`. -/

inductive lam : Type
| var : string → lam
| abs : string → lam → lam
| app : lam → lam → lam

/-! 2a (5 points). Implement the following Lean function that returns the set of
all variables that occur freely or bound within a `λ`-term. For example:

`vars (lam.var x) = {x}`
`vars (lam.abs x (lam.var y)) = {x, y}`

You may assume that the type constructor `set` supports the familiar set
operations. -/

def vars : lam → set string
--sol
| (lam.var x)    := {x}
| (lam.abs x t)  := {x} ∪ vars t
| (lam.app t t') := vars t ∪ vars t'
--los

/-! 2b (5 points). Implement the following Lean function that returns the set of
all __free__ variables within a `λ`-term. A variable is free if it occurs
outside the scope of any binder ranging over it. For example:

`free_vars (lam.var x) = {x}`
`free_vars (lam.abs x (lam.var y)) = {y}`
`free_vars (lam.abs x (lam.app (lam.var x) (lam.var y))) = {y}` -/

def free_vars : lam → set string
--sol
| (lam.var x)    := {x}
| (lam.abs x t)  := free_vars t \ {x}
| (lam.app t t') := free_vars t ∪ free_vars t'
--los

/-! 2c (7 points). Prove that `free_vars` is a subset of `vars`. Note that
`A ⊆ B` is defined as `∀a, a ∈ A → a ∈ B`. -/

lemma free_vars_subset_vars (t : lam) :
  free_vars t ⊆ vars t :=
--sol
begin
  induction' t,
  case var {
    simp [vars, free_vars] },
  case abs : x t ih {
    simp [vars, free_vars],
    simp [(⊆), set.subset] at *,
    intros y h,
    specialize ih h,
    apply or.intro_right,
    apply ih },
  case app : t u ih_t ih_u {
    simp [vars, free_vars],
    simp [(⊆), set.subset] at *,
    apply and.intro,
    { intros y h,
      specialize ih_t h,
      apply or.intro_left,
      apply ih_t },
    { intros y h,
      specialize ih_u h,
      apply or.intro_right,
      apply ih_u } }
end
--los


/-! ## Question 3 (16 points): A loopy language

Consider the LOOPY programming language, which comprises three kinds of
statements:

* `output s` prints the string `s`;
* `choice S T` nondeterministically executes either `S` or `T`;
* `repeat S` executes `S` a nondeterministic number of times, printing the
  concatenation (`++`) of zero or more strings.

In Lean, we can model the language's abstract syntax as follows: -/

inductive stmt : Type
| output : string → stmt
| choice : stmt → stmt → stmt
| repeat : stmt → stmt

/-! 3a (8 points). The big-step semantics for the LOOPY language relates
programs `S : stmt` to possible outputs `s : string`.

Complete the following specification of a big-step semantics for the
language by giving the missing derivation rules for `choice` and `repeat`.

    ––––––––––––––––––––––––––––––––––––– output
    output s ⟹ s
-/

--sol
/-!
    S ⟹ s
    ––––––––––––––––––––––––––––––––––––– choice_left
    choice S T ⟹ s

    T ⟹ s
    ––––––––––––––––––––––––––––––––––––– choice_right
    choice S T ⟹ s

    ––––––––––––––––––––––––––––––––––––– repeat_base
    repeat S ⟹ ""

    S ⟹ s    repeat S ⟹ t
    ––––––––––––––––––––––––––––––––––––– repeat_step
    repeat S ⟹ s ++ t
-/
--los

/-! 3b (8 points). Specify the same big-step semantics as an inductive
predicate by completing the following Lean definition. -/

inductive big_step : stmt → string → Prop
| output {s} : big_step (stmt.output s) s
--sol
| choice_left {S T s} : big_step S s → big_step (stmt.choice S T) s
| choice_right {S T s} : big_step T s → big_step (stmt.choice S T) s
| repeat_base {S} : big_step (stmt.repeat S) ""
| repeat_step {S s s'} :
  big_step S s → big_step (stmt.repeat S) s' →
  big_step (stmt.repeat S) (s ++ s')
--los


/-! ## Question 4 (15 points): The list monad

The list monad is a monad that stores a list of values of type `α`. It
corresponds to the Lean type constructor `list`.

4a (6 points). Complete the Lean definitions of the `pure` and `bind`
operations. `pure` should create a singleton list. `bind` should apply its
second argument to all the elements of the first argument and concatenate the
resulting lists. Examples:

    list.pure 7 = [7]
    list.bind [1, 2, 3] (λx, [x, 10 * x]) = [1, 10, 2, 20, 3, 30]

You may assume the following operator and functions are available, among others:

  * `++` concatenates two lists;

  * `list.map` applies its first argument elementwise to its second argument;

  * `list.flatten` transforms a list of list into a flattened list formed by
    concatenating all the lists together. -/

def list.flatten {α : Type} : list (list α) → list α
| []          := []
| (as :: ass) := as ++ list.flatten ass

def list.pure {α : Type} : α → list α :=
--sol
λa, [a]
--los

def list.bind {α β : Type} : list α → (α → list β) → list β :=
--sol
λas f, list.flatten (list.map f as)
--los

#eval list.bind [1, 2, 3] (λx, [x, 10 * x])

namespace alternative

def list.bind {α β : Type} : list α → (α → list β) → list β
| []        _ := []
| (a :: as) f := f a ++ list.bind as f

#eval list.bind [1, 2, 3] (λx, [x, 10 * x])

end alternative

infixl ` >>= `:54 := list.bind

/- 4b (9 points). Assume `ma >>= f` is syntactic sugar for `list.bind ma f`.
Prove the three monad laws. Your proofs should be step by step, with at most
one rewrite rule or definition expansion per step, so that we can clearly see
what happens.

You may assume reasonable lemmas about `list.map` and `list.flatten`. Please
state them. -/

lemma list.pure_bind {α β : Type} (a : α) (f : α → list β) :
  (list.pure a >>= f) = f a :=
calc  (list.pure a >>= f)
    = ([a] >>= f) :
  by refl
... = f a :
  by simp [list.bind, list.flatten]

lemma list.bind_pure {α : Type} (ma : list α) :
  (ma >>= list.pure) = ma :=
calc  (ma >>= list.pure)
    = list.flatten (list.map list.pure ma) :
  by refl
... = ma :
  begin
    induction' ma,
    case nil {
      refl },
    case cons {
      simp [list.pure, list.map, list.flatten] at *,
      apply ih }
  end


/-! ## Question 5 (10 points): The loopy language revisited

5a (4 points). Implement the following `replicate` function in Lean. It takes a
number `n` and a string `s` and returns the string obtained by concatenating
`n` copies of `s`. -/

def replicate : ℕ → string → string
--sol
| 0       _ := ""
| (n + 1) s := s ++ replicate n s
--los

/-! 5b (4 points). In mathematics, the Kleene star operator takes a string set
`A` and returns the set of all the strings that are obtained by concatenating
strings from `A` zero or more times. A natural way to model this in Lean is
using an inductive predicate. Complete the following definition with the
necessary introduction rules so that `kleene_star A s` is true if and only if
string `s` is in the Kleene star of set `A`: -/

inductive kleene_star (A : set string) : string → Prop
--sol
| empty : kleene_star ""
| step {s t} : s ∈ A → kleene_star t → kleene_star (s ++ t)
--los

/-! 5c (6 points). Use the Kleene star to complete the following definition of
the denotational semantics of the LOOPY language from question 3. The
denotation of a LOOPY program should be the set of all strings it can output. -/

def denote : stmt → set string
| (stmt.output s)   := {s}
--sol
| (stmt.choice S T) := denote S ∪ denote T
| (stmt.repeat S)   := {s | kleene_star (denote S) s}
--los

/-! Recall that the Lean syntax for set comprehensions is `{x | φ x}`, where
`φ x` is some condition on `x`. -/


/-! ## Question 6 (13 points): Types and type classes

6a (4 points). What are the types of the following expressions? -/

#check [1, 2, (3 : ℤ)]
#check list ℕ
#check list
#check Sort 1

/-! 6b (5 points). The type class monoid is defined as follows in Lean: -/

#print monoid

class monoid (α : Type) :=
(mul : α → α → α)
(one : α)
(mul_assoc : ∀a b c : α, mul (mul a b) c = mul a (mul b c))
(one_mul : ∀a : α, mul one a = a)
(mul_one : ∀a : α, mul a one = a)

/-! A list can be viewed as a monoid, with the empty list `[]` as `one` and list
concatenation `++` as `mul`. Complete the following instantiation of `list α` as
a monoid by providing a suitable definition of the five fields of the monoid.
For each of the three properties, state the property to prove and very briefly
explain why it holds. -/

instance string.monoid {α : Type} : monoid (list α) :=
--sol
{ mul := (++),
  one := [],
  mul_assoc := by simp,
  mul_one := by simp,
  one_mul := by simp}
--los

/-! 6c (4 points). The type class group is defined as follows in Lean: -/

#print group

class group (α : Type) :=
(mul : α → α → α)
(one : α)
(mul_assoc : ∀a b c : α, mul (mul a b) c = mul a (mul b c))
(one_mul : ∀a : α, mul one a = a)
(mul_one : ∀a : α, mul a one = a)
(inv : α → α)
(mul_left_inv : ∀a : α, mul (inv a) a = one)

/-! Can the type `list α` be instantiated as a group, using the same definition
for `mul` and `one` as in question 6b? Briefly explain your answer. -/

--sol
/-! No, this cannot be done, because there is no inverse for `[a]` such that
`[a] ++ ... = []`. -/
--los

end LoVe
