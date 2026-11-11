module

public import Mathlib.RingTheory.Kaehler.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# The module of differentials as `J / J²`

Stacks 00RW: for a ring map `R → S`, with `J = Ker(S ⊗[R] S → S)` the kernel of the
multiplication map, there is a canonical isomorphism of `S`-modules `Ω_{S/R} → J / J²`,
`a d b ↦ a ⊗ b - ab ⊗ 1`.

Here `Ω_{S/R}` is the module of Stacks 07BK, defined by generators and relations: the free
`S`-module on symbols `d b` (`b : S`) modulo `d(a + b) - d a - d b`, `d(ab) - a d b - b d a`
and `d r` for `r` in the image of `R`. In Mathlib this quotient is
`(S →₀ S) ⧸ KaehlerDifferential.kerTotal R S`, the symbol `a d b` being the class of
`Finsupp.single b a`, and `J / J²` is `(KaehlerDifferential.ideal R S).Cotangent`, an
`S`-module through `s ↦ s ⊗ 1`.

Mathlib *defines* `Ω[S⁄R]` to be `J / J²`, so the isomorphism is Mathlib's
`KaehlerDifferential.quotKerTotalEquiv`. `quotKerTotalEquivCotangent` states it with the
target written as `J / J²`, and `quotKerTotalEquivCotangent_mk_single` is the formula.
-/

@[expose] public section

namespace KaehlerDifferential

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- **Stacks 00RW.** The canonical `S`-linear isomorphism from the module of differentials
`Ω_{S/R}`, presented by generators and relations as `(S →₀ S) ⧸ kerTotal R S`, to `J / J²`,
where `J` is the kernel of the multiplication map `S ⊗[R] S → S`. Its formula is
`quotKerTotalEquivCotangent_mk_single`. -/
@[stacks 00RW "the isomorphism `Ω_{S/R} ≃ J / J²`"]
noncomputable def quotKerTotalEquivCotangent :
    ((S →₀ S) ⧸ kerTotal R S) ≃ₗ[S] (ideal R S).Cotangent :=
  quotKerTotalEquiv R S

/-- For `a, b : S`, the element `a ⊗ b - ab ⊗ 1` of `S ⊗[R] S` lies in the kernel `J` of the
multiplication map. -/
theorem tmul_sub_mul_tmul_one_mem_ideal (a b : S) :
    a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S) ∈ ideal R S := by
  simp [RingHom.mem_ker]

/-- **Stacks 00RW**, the formula: the isomorphism `Ω_{S/R} ≃ J / J²` sends `a d b` to the
class of `a ⊗ b - ab ⊗ 1`. -/
@[stacks 00RW "the formula `a d b ↦ a ⊗ b - ab ⊗ 1`"]
theorem quotKerTotalEquivCotangent_mk_single (a b : S) :
    quotKerTotalEquivCotangent R S ((kerTotal R S).mkQ (Finsupp.single b a)) =
      (ideal R S).toCotangent
        ⟨a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S), tmul_sub_mul_tmul_one_mem_ideal R S a b⟩ := by
  have h1 : quotKerTotalEquiv R S ((kerTotal R S).mkQ (Finsupp.single b a)) = a • D R S b := by
    change (kerTotal R S).liftQ (Finsupp.linearCombination S (D R S)) (kerTotal_eq R S).ge
      ((kerTotal R S).mkQ (Finsupp.single b a)) = _
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, Finsupp.linearCombination_single]
  have h2 : (a • D R S b : Ω[S⁄R]) = (ideal R S).toCotangent
      ⟨a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S), tmul_sub_mul_tmul_one_mem_ideal R S a b⟩ := by
    change a • ((fromIdeal R S).restrictScalars S)
        ⟨1 ⊗ₜ[R] b - b ⊗ₜ[R] 1, one_smul_sub_smul_one_mem_ideal R b⟩ =
      ((fromIdeal R S).restrictScalars S)
        ⟨a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S), tmul_sub_mul_tmul_one_mem_ideal R S a b⟩
    rw [← map_smul]
    congr 1
    ext
    simp only [Submodule.coe_smul_of_tower, smul_sub, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
  exact h1.trans h2

end KaehlerDifferential

add_to_stacks 00RW "the isomorphism, with target `Ω[S⁄R]` (Mathlib's `J / J²`)"
  KaehlerDifferential.quotKerTotalEquiv

end
