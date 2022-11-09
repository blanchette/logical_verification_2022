import .love01_definitions_and_statements_demo


/-! # LoVe Homework 1: Definitions and Statements

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (1 point): Fibonacci Numbers

1.1 (1 point). Define the function `fib` that computes the Fibonacci
numbers. -/

def fib : ℕ → ℕ
| 0                       := 0
| 1                       := 1
| (nat.succ (nat.succ n)) := fib n + fib (nat.succ n)

/-! Alternative solution: -/

def fib₂ : ℕ → ℕ
| 0       := 0
| 1       := 1
| (n + 2) := fib n + fib (n + 1)

/-! 1.2 (0 points). Check that your function works as expected. -/

#eval fib 0   -- expected: 0
#eval fib 1   -- expected: 1
#eval fib 2   -- expected: 1
#eval fib 3   -- expected: 2
#eval fib 4   -- expected: 3
#eval fib 5   -- expected: 5
#eval fib 6   -- expected: 8
#eval fib 7   -- expected: 13
#eval fib 8   -- expected: 21


/-! ## Question 2 (3 points): Lists

Consider the type `list` described in the lecture and the `append₂` and
`reverse` functions from the lecture's demo. The `list` type is part of Lean's
core libraries. You will find the definition of `append₂` and `reverse` in
`love01_definitions_and_statements_demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `list`, `append₂`, or `reverse`;
3. click the identifier. -/

#print list
#check append₂
#check reverse

/-! 2.1 (1 point). Test that `reverse` behaves as expected on a few examples.

In the first example, the type annotation `: list ℕ` is needed to guide Lean's
type inference. -/

#eval reverse ([] : list ℕ)   -- expected: []
#eval reverse [1, 3, 5]       -- expected: [5, 3, 1]
#eval reverse [3]             -- expected: [3]
#eval reverse [3, 2]          -- expected: [2, 3]
#eval reverse [3, 2, 5]       -- expected: [5, 2, 3]
#eval reverse [7, 2, 9, 8]    -- expected: [8, 9, 2, 7]
#eval reverse ["b", "c"]      -- expected: ["c, "b"]

/-! 2.2 (2 points). State (without proving them) the following properties of
`append₂` and `reverse`. Schematically:

    `append₂ (append₂ xs ys) zs = append₂ xs (append₂ ys zs)`
    `reverse (append₂ xs ys) = append₂ (reverse ys) (reverse xs)`

for all lists `xs`, `ys`, `zs`. Try to give meaningful names to your lemmas. If
you wonder how to enter the symbol `₂`, have a look at the table at the end of
the preface in the Hitchhiker's Guide.

Hint: Take a look at `reverse_reverse` from the demonstration file. -/

#check sorry_lemmas.reverse_reverse

lemma append₂_assoc {α : Type} (xs ys zs : list α) :
  append₂ (append₂ xs ys) zs = append₂ xs (append₂ ys zs) :=
sorry

lemma reverse_append₂ {α : Type} (xs ys : list α) :
  reverse (append₂ xs ys) = append₂ (reverse ys) (reverse xs) :=
sorry


/-! ## Question 3 (5 points): λ-Terms

3.1 (2 points). Complete the following definitions, by replacing the `sorry`
placeholders by terms of the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def B : (α → β) → (γ → α) → γ → β :=
λg f c, g (f c)

def S : (α → β → γ) → (α → β) → α → γ :=
λg f a, g a (f a)

def more_nonsense : (γ → (α → β) → α) → γ → β → α :=
λh c b, h c (λx, b)

def even_more_nonsense : (α → α → β) → (β → γ) → α → β → γ :=
λf g a b, g (f a a)

/-! 3.2 (1 point). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weak_peirce : ((((α → β) → α) → α) → β) → β :=
λf, f (λg, g (λa, f (λh, a)))

/-! 3.3 (2 points). Show the typing derivation for your definition of `S` above,
using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

/-! Let `C` := `g : α → β → γ, f : α → β, a : α`. We have

    –––––––––––––– Var  –––––––––– Var  –––––––––––––– Var  –––––––––– Var
    C ⊢ g : α → β       C ⊢ a : α       C ⊢ f : α → β       C ⊢ a : α
    –––––––––––––––––––––––––––––– App  –––––––––––––––––––––––––––––– App
    C ⊢ g a : β → γ                     C ⊢ f a : β
    –––––––––––––––––––––––––––––––––––––––––––––––– App
    C ⊢ g a (f a) : γ
    ––––––––––––––––––––––––––––––––––––––––––––––––––– Lam
    g : α → β → γ, f : α → β ⊢ (λa, g a (f a)) : α → γ
    –––––––––––––––––––––––––––––––––––––––––––––––––––– Lam
    g : α → β → γ ⊢ (λf a, g a (f a)) : (α → β) → α → γ
    ––––––––––––––––––––––––––––––––––––––––––––––––––––– Lam
    ⊢ (λg f a, g a (f a)) ⊢ (α → β → γ) → (α → β) → α → γ -/

end LoVe
