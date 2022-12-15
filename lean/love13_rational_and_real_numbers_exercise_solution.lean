import .love05_inductive_predicates_demo
import .love13_rational_and_real_numbers_demo


/-! # LoVe Exercise 13: Rational and Real Numbers -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Rationals

1.1. Prove the following lemma.

Hint: The lemma `fraction.mk.inj_eq` might be useful. -/

#check fraction.mk.inj_eq

lemma fraction.ext (a b : fraction) (hnum : fraction.num a = fraction.num b)
    (hdenom : fraction.denom a = fraction.denom b) :
  a = b :=
begin
  cases' a,
  cases' b,
  rw fraction.mk.inj_eq,
  exact and.intro hnum hdenom
end

/-! 1.2. Extending the `fraction.has_mul` instance from the lecture, declare
`fraction` as an instance of `semigroup`.

Hint: Use the lemma `fraction.ext` above, and possibly `fraction.mul_num`, and
`fraction.mul_denom`. -/

#check fraction.ext
#check fraction.mul_num
#check fraction.mul_denom

@[instance] def fraction.semigroup : semigroup fraction :=
{ mul_assoc :=
    begin
      intros,
      apply fraction.ext,
      repeat {
        simp [fraction.mul_num, fraction.mul_denom],
        cc }
    end,
  ..fraction.has_mul }

/-! 1.3. Extending the `rat.has_mul` instance from the lecture, declare `rat` as
an instance of `semigroup`. -/

@[instance] def rat.semigroup : semigroup rat :=
{ mul_assoc :=
    begin
      intros x y z,
      apply quotient.induction_on x,
      apply quotient.induction_on y,
      apply quotient.induction_on z,
      intros a b c,
      apply quotient.sound,
      rw mul_assoc
    end,
  ..rat.has_mul }

end LoVe
