import .lovelib


/-! # LoVe Demo 4: Functional Programming

We take a closer look at the basics of typed functional programming: inductive
types, proofs by induction, recursive functions, pattern matching, structures
(records), and type classes. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Inductive Types

Recall the definition of type `nat` (= `ℕ`): -/

#print nat

/-! Mottos:

* **No junk**: The type contains no values beyond those expressible using the
  constructors.

* **No confusion**: Values built in a different ways are different.

For `nat` (= `ℕ`):

* "No junk" means that there are no special values, say, `–1` or `ε`, that
  cannot be expressed using a finite combination of `zero` and `succ`.

* "No confusion" is what ensures that `zero` ≠ `succ x`.

In addition, inductive types are always finite. `succ (succ (succ …))` is not a
value.


## Structural Induction

__Structural induction__ is a generalization of mathematical induction to
inductive types. To prove a property `P[n]` for all natural numbers `n`, it
suffices to prove the base case

    `P[0]`

and the induction step

    `∀k, P[k] → P[k + 1]`

For lists, the base case is

    `P[[]]`

and the induction step is

    `∀y ys, P[ys] → P[y :: ys]`

In general, there is one subgoal per constructor, and induction hypotheses are
available for all constructor arguments of the type we are doing the induction
on. -/

--quo nat.succ_neq_self
lemma nat.succ_neq_self (n : ℕ) :
  nat.succ n ≠ n :=
begin
  induction' n,
  { simp },
  { simp [ih] }
end
--ouq

/-! The `case` tactic can be used to supply custom names, and potentially
reorder the cases. -/

--quo nat.succ_neq_self₂
lemma nat.succ_neq_self₂ (n : ℕ) :
  nat.succ n ≠ n :=
begin
  induction' n,
  case succ : m IH {
    simp [IH] },
  case zero {
    simp }
end
--ouq


/-! ## Structural Recursion

__Structural recursion__ is a form of recursion that allows us to peel off
one or more constructors from the value on which we recurse. Such functions are
guaranteed to call themselves only finitely many times before the recursion
stops. This is a prerequisite for establishing that the function terminates. -/

--quo fact
def fact : ℕ → ℕ
| 0       := 1
| (n + 1) := (n + 1) * fact n
--ouq

--quo fact₂
def fact₂ : ℕ → ℕ
| 0       := 1
| 1       := 1
| (n + 1) := (n + 1) * fact₂ n
--ouq

/-! For structurally recursive functions, Lean can automatically prove
termination. For more general recursive schemes, the termination check may fail.
Sometimes it does so for a good reason, as in the following example: -/

/-fails
--quo illegal
-- fails
def illegal : ℕ → ℕ
| n := illegal n + 1
--ouq
sliaf-/

--quo immoral
constant immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
  immoral n = immoral n + 1

lemma proof_of_false :
  false :=
have immoral 0 = immoral 0 + 1 :=
  immoral_eq 0,
have immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 :=
  by cc,
have 0 = 1 :=
  by simp [*] at *,
show false, from
  by cc
--ouq


/-! ## Pattern Matching Expressions

    `match` _term₁_, …, _termM_ `with`
    | _pattern₁₁_, …, _pattern₁M_ := _result₁_
        ⋮
    | _patternN₁_, …, _patternNM_ := _resultN_
    `end`

`match` allows nonrecursive pattern matching within terms.

In contrast to pattern matching after `lemma` or `def`, the patterns are
separated by commas, so parentheses are optional. -/

--quo bcount
def bcount {α : Type} (p : α → bool) : list α → ℕ
| []        := 0
| (x :: xs) :=
  match p x with
  | tt := bcount xs + 1
  | ff := bcount xs
  end
--ouq

--quo min
def min (a b : ℕ) : ℕ :=
if a ≤ b then a else b
--ouq


/-! ## Structures

Lean provides a convenient syntax for defining records, or structures. These are
essentially nonrecursive, single-constructor inductive types. -/

--quo rgb_def
structure rgb :=
(red green blue : ℕ)
--ouq

#check rgb.mk
#check rgb.red
#check rgb.green
#check rgb.blue

namespace rgb_as_inductive

--quo rgb_as_inductive
inductive rgb : Type
| mk : ℕ → ℕ → ℕ → rgb

def rgb.red : rgb → ℕ
| (rgb.mk r _ _) := r

def rgb.green : rgb → ℕ
| (rgb.mk _ g _) := g

def rgb.blue : rgb → ℕ
| (rgb.mk _ _ b) := b
--ouq

end rgb_as_inductive

--quo rgba_def
structure rgba extends rgb :=
(alpha : ℕ)
--ouq

#print rgba

--quo pure_red_etc_def
def pure_red : rgb :=
{ red   := 0xff,
  green := 0x00,
  blue  := 0x00 }

def semitransparent_red : rgba :=
{ alpha := 0x7f,
  ..pure_red }
--ouq

#print pure_red
#print semitransparent_red

--quo shuffle_def
def shuffle (c : rgb) : rgb :=
{ red   := rgb.green c,
  green := rgb.blue c,
  blue  := rgb.red c }
--ouq

/-! `cases'` performs a case distinction on the specified term. This gives rise
to as many subgoals as there are constructors in the definition of the term's
type. The tactic behaves the same as `induction'` except that it does not
produce induction hypotheses. -/

--quo shuffle_shuffle_shuffle
lemma shuffle_shuffle_shuffle (c : rgb) :
  shuffle (shuffle (shuffle c)) = c :=
begin
  cases' c,
  refl
end
--ouq

--quo shuffle_shuffle_shuffle₂
lemma shuffle_shuffle_shuffle₂ (c : rgb) :
  shuffle (shuffle (shuffle c)) = c :=
match c with
| rgb.mk _ _ _ := eq.refl _
end
--ouq


/-! ## Type Classes

A __type class__ is a structure type combining abstract constants and their
properties. A type can be declared an instance of a type class by providing
concrete definitions for the constants and proving that the properties hold.
Based on the type, Lean retrieves the relevant instance. -/

#print inhabited

--quo inhabited_nat
@[instance] def nat.inhabited : inhabited ℕ :=
{ default := 0 }
--ouq

--quo inhabited_list
@[instance] def list.inhabited {α : Type} :
  inhabited (list α) :=
{ default := [] }
--ouq

#eval inhabited.default ℕ          -- result: 0
#eval inhabited.default (list ℤ)   -- result: []

--quo head
def head {α : Type} [inhabited α] : list α → α
| []       := inhabited.default α
| (x :: _) := x
--ouq

--quo head_head
lemma head_head {α : Type} [inhabited α] (xs : list α) :
  head [head xs] = head xs
--ouq
:=
begin
  cases' xs,
  { refl },
  { refl }
end

--quo head_eval
#eval head ([] : list ℕ)   -- result: 0
--ouq

#check list.head

--quo fun.inhabited_1
@[instance] def fun.inhabited {α β : Type} [inhabited β] :
  inhabited (α → β) :=
{ default := λa : α, inhabited.default β }
--ouq

--quo fun.inhabited_2
inductive empty : Type

@[instance] def fun_empty.inhabited {β : Type} :
  inhabited (empty → β) :=
{ default := λa : empty, match a with end }
--ouq

--quo prod.inhabited
@[instance] def prod.inhabited {α β : Type}
    [inhabited α] [inhabited β] :
  inhabited (α × β) :=
{ default := (inhabited.default α, inhabited.default β) }
--ouq

/-! Here are other type classes without properties: -/

#check has_zero
#check has_neg
#check has_add
#check has_one
#check has_inv
#check has_mul

#check (1 : ℕ)
#check (1 : ℤ)
#check (1 : ℝ)

/-! We encountered these type classes in lecture 2: -/

#print is_commutative
#print is_associative


/-! ## Lists

`list` is an inductive polymorphic type constructed from `nil` and `cons`: -/

#print list

/-! `cases'` can also be used on a hypothesis of the form `l = r`. It matches `r`
against `l` and replaces all occurrences of the variables occurring in `r` with
the corresponding terms in `l` everywhere in the goal. -/

--quo injection_example
lemma injection_example {α : Type} (x y : α) (xs ys : list α)
    (h : x :: xs = y :: ys) :
  x = y ∧ xs = ys :=
begin
  cases' h,
  cc
end
--ouq

/-! If `r` fails to match `l`, no subgoals emerge; the proof is complete. -/

--quo distinctness_example
lemma distinctness_example {α : Type} (y : α) (ys : list α)
    (h : [] = y :: ys) :
  false :=
by cases' h
--ouq

--quo map
def map {α β : Type} (f : α → β) : list α → list β
| []        := []
| (x :: xs) := f x :: map xs
--ouq

--quo map₂
def map₂ {α β : Type} : (α → β) → list α → list β
| _ []        := []
| f (x :: xs) := f x :: map₂ f xs
--ouq

#check list.map

--quo map_ident
lemma map_ident {α : Type} (xs : list α) :
  map (λx, x) xs = xs :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end
--ouq

--quo map_comp
lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ)
    (xs : list α) :
  map g (map f xs) = map (λx, g (f x)) xs :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end
--ouq

--quo map_append
lemma map_append {α β : Type} (f : α → β) (xs ys : list α) :
  map f (xs ++ ys) = map f xs ++ map f ys :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : y ys {
    simp [map, ih] }
end
--ouq

--quo tail
def tail {α : Type} : list α → list α
| []        := []
| (_ :: xs) := xs
--ouq

#check list.tail

--quo head_opt
def head_opt {α : Type} : list α → option α
| []       := option.none
| (x :: _) := option.some x
--ouq

--quo head_pre
def head_pre {α : Type} : ∀xs : list α, xs ≠ [] → α
| []       hxs := by cc
| (x :: _) _   := x
--ouq

#eval head_opt [3, 1, 4]
--quo head_pre_eval
#eval head_pre [3, 1, 4] (by simp)
--ouq
/-fails
-- fails
#eval head_pre ([] : list ℕ) sorry
sliaf-/

--quo zip
def zip {α β : Type} : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys
| []        _         := []
| (_ :: _)  []        := []
--ouq

#check list.zip

--quo length
def length {α : Type} : list α → ℕ
| []        := 0
| (x :: xs) := length xs + 1
--ouq

#check list.length

/-! `cases'` can also be used to perform a case distinction on a proposition, in
conjunction with `classical.em`. Two cases emerge: one in which the proposition
is true and one in which it is false. -/

#check classical.em

--quo min_add_add
lemma min_add_add (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
begin
  cases' classical.em (m ≤ n),
  case inl {
    simp [min, h] },
  case inr {
    simp [min, h] }
end
--ouq

--quo min_add_add₂
lemma min_add_add₂ (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
match classical.em (m ≤ n) with
| or.inl h := by simp [min, h]
| or.inr h := by simp [min, h]
end
--ouq

--quo min_add_add₃
lemma min_add_add₃ (l m n : ℕ) :
  min (m + l) (n + l) = min m n + l :=
if h : m ≤ n then
  by simp [min, h]
else
  by simp [min, h]
--ouq

--quo length_zip
lemma length_zip {α β : Type} (xs : list α) (ys : list β) :
  length (zip xs ys) = min (length xs) (length ys) :=
begin
  induction' xs,
  case nil {
    refl },
  case cons : x xs' {
    cases' ys,
    case nil {
      refl },
    case cons : y ys' {
      simp [zip, length, ih ys', min_add_add] } }
end
--ouq

--quo map_zip
lemma map_zip {α α' β β' : Type} (f : α → α') (g : β → β') :
  ∀xs ys,
    map (λab : α × β, (f (prod.fst ab), g (prod.snd ab)))
      (zip xs ys) =
    zip (map f xs) (map g ys)
| (x :: xs) (y :: ys) := by simp [zip, map, map_zip xs ys]
| []        _         := by refl
| (_ :: _)  []        := by refl
--ouq


/-! ## Binary Trees

Inductive types with constructors taking several recursive arguments define
tree-like objects. __Binary trees__ have nodes with at most two children. -/

--quo btree
inductive btree (α : Type) : Type
| empty : btree
| node  : α → btree → btree → btree
--ouq

/-! The type `aexp` of arithmetic expressions was also an example of a tree data
structure.

The nodes of a tree, whether inner nodes or leaf nodes, often carry labels or
other annotations.

Inductive trees contain no infinite branches, not even cycles. This is less
expressive than pointer- or reference-based data structures (in imperative
languages) but easier to reason about.

Recursive definitions (and proofs by induction) work roughly as for lists, but
we may need to recurse (or invoke the induction hypothesis) on several child
nodes. -/

--quo mirror
def mirror {α : Type} : btree α → btree α
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node a (mirror r) (mirror l)
--ouq

--quo mirror_mirror
lemma mirror_mirror {α : Type} (t : btree α) :
  mirror (mirror t) = t :=
begin
  induction' t,
  case empty {
    refl },
  case node : a l r ih_l ih_r {
    simp [mirror, ih_l, ih_r] }
end
--ouq

--quo mirror_mirror₂
lemma mirror_mirror₂ {α : Type} :
  ∀t : btree α, mirror (mirror t) = t
| btree.empty        := by refl
| (btree.node a l r) :=
  calc  mirror (mirror (btree.node a l r))
      = mirror (btree.node a (mirror r) (mirror l)) :
    by refl
  ... = btree.node a (mirror (mirror l)) (mirror (mirror r)) :
    by refl
  ... = btree.node a l (mirror (mirror r)) :
    by rw mirror_mirror₂ l
  ... = btree.node a l r :
    by rw mirror_mirror₂ r
--ouq

--quo mirror_eq_empty_iff
lemma mirror_eq_empty_iff {α : Type} :
  ∀t : btree α, mirror t = btree.empty ↔ t = btree.empty
| btree.empty        := by refl
| (btree.node _ _ _) := by simp [mirror]
--ouq


/-! ## Dependent Inductive Types (**optional**) -/

#check vector

--quo vec
inductive vec (α : Type) : ℕ → Type
| nil                              : vec 0
| cons (a : α) {n : ℕ} (v : vec n) : vec (n + 1)
--ouq

#check vec.nil
#check vec.cons

--quo list_of_vec
def list_of_vec {α : Type} : ∀{n : ℕ}, vec α n → list α
| _ vec.nil        := []
| _ (vec.cons a v) := a :: list_of_vec v
--ouq

--quo vec_of_list
def vec_of_list {α : Type} :
  ∀xs : list α, vec α (list.length xs)
| []        := vec.nil
| (x :: xs) := vec.cons x (vec_of_list xs)
--ouq

--quo length_list_of_vec
lemma length_list_of_vec {α : Type} :
  ∀{n : ℕ} (v : vec α n), list.length (list_of_vec v) = n
| _ vec.nil        := by refl
| _ (vec.cons a v) :=
  by simp [list_of_vec, length_list_of_vec v]
--ouq

end LoVe
