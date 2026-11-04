module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.RigSmoothBaseChange

/-!
# Rig-smoothness of the completed base change `(B₁ ⊗_{A₁} A₂)^` (Stacks 0GAM)

Let `A₁ → A₂` be a map of Noetherian rings and let `I₁ ⊆ A₁`, `I₂ ⊆ A₂` be ideals with
`V(I₁ A₂) = V(I₂)`.  For `B₁` an `I₁`-adically complete `A₁`-algebra of finite type modulo `I₁`,
Stacks Remark 0AL5 makes the `I₂`-adic completion `B₂ = (B₁ ⊗_{A₁} A₂)^` an `I₂`-adically
complete `A₂`-algebra of finite type modulo `I₂`.  This file constructs that object directly
from the hypothesis `V(I₁ A₂) = V(I₂)` and proves Stacks 0GAM for it: if `B₁` is rig-smooth over
`(A₁, I₁)` then `B₂` is rig-smooth over `(A₂, I₂)`.

## Main results

* `Rig.isAdicComplete_and_finiteType_completedBaseChangedAlgebra`: under `V(I₁ A₂) = V(I₂)` over
  Noetherian rings, the completion `(B₁ ⊗_{A₁} A₂)^` is `I₂`-adically complete and of finite
  type modulo `I₂` (the part of Stacks Remark 0AL5 that makes it an object of the category).
* `Rig.isRigSmooth_completedBaseChangedAlgebra`: **Stacks 0GAM**, stated for the object
  `(B₁ ⊗_{A₁} A₂)^` itself.

## Implementation notes

The condition `V(I₁ A₂) = V(I₂)` is expressed as the equality of radicals
`(I₁ A₂)^rad = I₂^rad`, equivalent by `PrimeSpectrum.zeroLocus_eq_iff`.  Over the Noetherian
ring `A₂` the inclusion `I₁ A₂ ≤ I₂^rad` yields `c ≥ 1` with `I₁^c A₂ ≤ I₂`, which is the
hypothesis of Remark 0AL5 under which the base-change functor `Rig.completedBaseChange` of the
category file is built; the object constructed here is, definitionally, the value of that
functor at `B₁`, with the `A₂`-algebra structure of `B₁ ⊗_{A₁} A₂` through the right factor.

## References

* [Stacks Project, Tag 0GAM](https://stacks.math.columbia.edu/tag/0GAM)
* [Stacks Project, Tag 0AL5](https://stacks.math.columbia.edu/tag/0AL5)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u₁ u₂ v

variable {A₁ : Type u₁} [CommRing A₁] [IsNoetherianRing A₁]
  {A₂ : Type u₂} [CommRing A₂] [IsNoetherianRing A₂] [Algebra A₁ A₂]
  {I₁ : Ideal A₁} {I₂ : Ideal A₂}

omit [IsNoetherianRing A₁] in
/-- Over a Noetherian `A₂`, the equality `V(I₁ A₂) = V(I₂)` gives a positive power of `I₁`
whose extension to `A₂` lies in `I₂`. -/
theorem exists_pos_pow_map_le_of_radical_eq
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical) :
    ∃ c : ℕ, 0 < c ∧ (I₁ ^ c).map (algebraMap A₁ A₂) ≤ I₂ := by
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (Ideal.le_radical.trans hV.le) (Ideal.fg_of_isNoetherianRing _)
  refine ⟨m + 1, m.succ_pos, ?_⟩
  rw [Ideal.map_pow]
  exact (Ideal.pow_le_pow_right m.le_succ).trans hm

omit [IsNoetherianRing A₁] in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks Remark 0AL5**, the object part, under `V(I₁ A₂) = V(I₂)` over Noetherian rings:
the `I₂`-adic completion of `B₁ ⊗_{A₁} A₂` is `I₂`-adically complete and its reduction modulo
`I₂` is of finite type over `A₂ ⧸ I₂`. -/
theorem isAdicComplete_and_finiteType_completedBaseChangedAlgebra
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical)
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) :
    IsAdicComplete (I₂.map (algebraMap A₂ (completedBaseChangedAlgebra (I₂ := I₂) B₁)))
        (completedBaseChangedAlgebra (I₂ := I₂) B₁) ∧
      Algebra.FiniteType (A₂ ⧸ I₂)
        (completedBaseChangedAlgebra (I₂ := I₂) B₁ ⧸
          I₂.map (algebraMap A₂ (completedBaseChangedAlgebra (I₂ := I₂) B₁))) :=
  let hc := exists_pos_pow_map_le_of_radical_eq hV
  (completedBaseChangeObj I₁ I₂ hc.choose hc.choose_spec.1 hc.choose_spec.2
    (Ideal.fg_of_isNoetherianRing I₂) B₁).property

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks Project, Tag 0GAM.** Let `A₁ → A₂` be a map of Noetherian rings and let
`I₁ ⊆ A₁`, `I₂ ⊆ A₂` be ideals with `V(I₁ A₂) = V(I₂)`.  If `B₁` is rig-smooth over
`(A₁, I₁)`, then its base change `B₂ = (B₁ ⊗_{A₁} A₂)^`, the `I₂`-adic completion of Remark
0AL5, is rig-smooth over `(A₂, I₂)`. -/
@[stacks 0GAM]
public theorem isRigSmooth_completedBaseChangedAlgebra
    (hV : (I₁.map (algebraMap A₁ A₂)).radical = I₂.radical)
    (B₁ : AdicFiniteTypeAlgebra.{u₁, v} A₁ I₁) (hB₁ : IsRigSmooth B₁) :
    IsRigSmooth (I := I₂)
      (⟨CommAlgCat.of A₂ (completedBaseChangedAlgebra (I₂ := I₂) B₁),
        isAdicComplete_and_finiteType_completedBaseChangedAlgebra hV B₁⟩ :
        AdicFiniteTypeAlgebra.{u₂, max v u₂} A₂ I₂) := by
  obtain ⟨c, hc, hmap⟩ := exists_pos_pow_map_le_of_radical_eq hV
  exact isRigSmooth_completedBaseChange hV
    (completedBaseChange I₁ I₂ c hc hmap (Ideal.fg_of_isNoetherianRing I₂)) B₁ hB₁

end Rig

end
