import .love04_functional_programming_demo


/-! # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (2 points): Maps

1.1 (1 point). Complete the following definition. The `map_btree` function
should apply its argument `f` to all values of type `α` stored in the tree and
otherwise preserve the tree's structure. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node (f a) (map_btree l) (map_btree r)

/-! 1.2 (1 point). Prove the following lemma about your `map_btree` function. -/

lemma map_btree_iden {α : Type} :
  ∀t : btree α, map_btree (λa, a) t = t
| btree.empty        := by refl
| (btree.node a l r) := by simp [map_btree, map_btree_iden l, map_btree_iden r]


/-! ## Question 2 (4 points): Tail-Recursive Factorials

Recall the definition of the factorial functions: -/

#check fact

/-! 2.1 (2 points). Experienced functional programmers tend to avoid definitions
such as the above, because they lead to a deep call stack. Tail recursion can be
used to avoid this. Results are accumulated in an argument and returned. This
can be optimized by compilers. For factorials, this gives the following
definition: -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

/-! Prove that, given 1 as the accumulator `a`, `accufact` computes `fact`.

Hint: You will need to prove a generalized version of the statement as a
separate lemma or `have`, because the desired property fixes `a` to 1, which
yields a too weak induction hypothesis. -/

lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = fact n :=
have accufact_eq_fact_mul : ∀m a, accufact a m = fact m * a :=
  begin
    intros m a,
    induction' m,
    case zero {
      simp [fact, accufact] },
    case succ {
      simp [fact, accufact, ih],
      cc }
  end,
by simp [accufact_eq_fact_mul n 1]

/-! 2.2 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

/-! The generalized lemma we prove is `∀n a, accufact a n = fact n * a`.

We perform the proof by structural (mathematical) induction on `n`,
generalizing `a`.

Case 0: The goal is `accufact a 0 = fact 0 * a`. The left-hand side is `a` by
definition of `accufact`. The right-hand side is `a` by definition of `fact` and
`*`.

Case `m + 1`: The goal is `accufact a (m + 1) = fact (m + 1) * a`. The induction
hypothesis is `∀a, accufact a m = fact m * a`.

Let us simplify the goal's left-hand side:

      accufact a (m + 1)
    = accufact ((m + 1) * a) m   -- by definition of `accufact`
    = fact m * ((m + 1) * a)     -- by the induction hypothesis
    = fact m * (m + 1) * a       -- by associativity of `*`

Now let us massage the right-hand side so that it matches the simplified
left-hand side:

      fact (m + 1) * a
    = (m + 1) * fact m * a       -- by definition of `fact`
    = fact m * (m + 1) * a       -- by commutativity of `*`

The two sides are equal.

The desired property follows from the generalized lemma by setting `a` to be `1`
and by simplifying away `* 1`. QED -/


/-! ## Question 3 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/-! 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1)
| 0       := by refl
| (m + 1) :=
  begin
    simp [sum_upto, sum_upto_eq m, add_mul, mul_add],
    linarith
  end

/-! 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n
| 0       := by refl
| (n + 1) :=
  begin
    simp [sum_upto, sum_upto_mul n],
    cc
  end

end LoVe
