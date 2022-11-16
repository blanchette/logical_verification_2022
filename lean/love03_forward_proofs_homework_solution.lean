import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
assume h : double_negation,
show peirce, from
  peirce_of_em (sorry_lemmas.em_of_dn h)

lemma em_of_peirce :
  peirce → excluded_middle :=
assume h : peirce,
show excluded_middle, from
  sorry_lemmas.em_of_dn (dn_of_peirce h)

lemma dn_of_em :
  excluded_middle → double_negation :=
assume h : excluded_middle,
show double_negation, from
  dn_of_peirce (peirce_of_em h)

end backward_proofs

/-! 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
iff.intro
  (assume hex : ∃x, p x ∧ q x,
   show ∃x, q x ∧ p x, from
     exists.elim hex
       (fix a,
        assume hpq : p a ∧ q a,
        have hp : p a :=
          and.elim_left hpq,
        have hq : q a :=
          and.elim_right hpq,
        show ∃x, q x ∧ p x, from
          exists.intro a (and.intro hq hp)))
  (assume hex : ∃x, q x ∧ p x,
   show ∃x, p x ∧ q x, from
     exists.elim hex
       (fix a,
        assume hqp : q a ∧ p a,
        have hq : q a :=
          and.elim_left hqp,
        have hp : p a :=
          and.elim_right hqp,
        show ∃x, p x ∧ q x, from
          exists.intro a (and.intro hp hq)))


/-! ## Question 2 (3 points): Fokkink Logic Puzzles

If you have studied Logic and Sets with Prof. Fokkink, you will know he is fond
of logic puzzles. This question is a tribute.

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/-! 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
λ(a b : Prop) (habaab : (((a → b) → a) → a) → b),
  habaab (λhabaa : (a → b) → a,
    habaa (λha : a,
      habaab (λhaba : (a → b) → a,
        ha)))

/-! There are in fact three easy ways:

* Copy-paste the result of `#print weak_peirce`.

* Simply enter `weak_peirce` as the proof term for `weak_peirce₂`.

* Reuse the answer to question 3.2 of homework 1. -/

/-! 2.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
fix a b,
assume habaab : (((a → b) → a) → a) → b,
show b, from
  habaab
    (assume habaa : (a → b) → a,
     show a, from
       habaa
         (assume ha : a,
          show b, from
            habaab
              (assume haba : (a → b) → a,
                show a, from
                  ha)))

end LoVe
