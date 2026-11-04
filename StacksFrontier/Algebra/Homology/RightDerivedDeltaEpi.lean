module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# Surjectivity of `RⁿQ X₂ ⟶ RⁿQ X₃` from the long exact sequence

Let `Q : B ⥤ D` be an additive functor between abelian categories, `B` having enough
injectives, and let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence in `B`.  Exactness of the
long exact sequence of right derived functors at `RⁿQ X₃` makes `RⁿQ X₂ ⟶ RⁿQ X₃` an
epimorphism as soon as `Rⁿ⁺¹Q X₁` vanishes, the outgoing connecting morphism then landing in
zero.  In degree zero and for a left exact `Q`, which is identified with `R⁰Q`, this says that
`Q X₂ ⟶ Q X₃` is an epimorphism when `R¹Q X₁ = 0`.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.Horseshoe.epi_rightDerived_map_g` and
  `Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_map_g`: `RⁿQ X₂ ⟶ RⁿQ X₃` is an
  epimorphism when `Rⁿ⁺¹Q X₁` vanishes, read through a chosen horseshoe resolution and with no
  resolution mentioned.
* `Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one`: for a left exact
  `Q`, the vanishing `R¹Q X₁ = 0` makes `Q X₂ ⟶ Q X₃` an epimorphism.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedDelta

variable {B : Type u₁} [Category.{v₁} B] [Abelian B]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace Horseshoe

variable {S : ShortComplex B} (H : Horseshoe S) (Q : B ⥤ D) [Q.Additive]
  [HasInjectiveResolutions B]

include H in
/-- **`RⁿQ X₂ ⟶ RⁿQ X₃` is an epimorphism when `Rⁿ⁺¹Q X₁` vanishes.** Exactness of the long
exact sequence at `RⁿQ X₃` makes the map an epimorphism, because the connecting morphism out of
`RⁿQ X₃` lands in the vanishing `Rⁿ⁺¹Q X₁`. -/
theorem epi_rightDerived_map_g (n : ℕ) (h' : IsZero ((Q.rightDerived (n + 1)).obj S.X₁)) :
    Epi ((Q.rightDerived n).map S.g) := by
  have hepi : Epi (HomologicalComplex.homologyMap (H.mapSequence Q).g n) :=
    (ShortComplex.exact_iff_epi _
      ((h'.of_iso (H.J₁.isoRightDerivedObj' Q (n + 1)).symm).eq_of_tgt _ 0)).1
      ((H.shortExact_mapSequence Q).homology_exact₃ n (n + 1) (ComplexShape.up_rel_succ n))
  rw [H.rightDerived_map_g Q n]
  infer_instance

end Horseshoe

section Existence

variable [EnoughInjectives B] {S : ShortComplex B} (hS : S.ShortExact) (Q : B ⥤ D) [Q.Additive]

include hS in
/-- **`RⁿQ X₂ ⟶ RⁿQ X₃` is an epimorphism when `Rⁿ⁺¹Q X₁` vanishes.** This is the half of the
long exact sequence that right exactness of `Q` at a short exact sequence amounts to: in degree
`n = 0`, with `Q` left exact, it says `Q X₂ ⟶ Q X₃` is surjective as soon as `R¹Q X₁ = 0`. -/
theorem epi_rightDerived_map_g (n : ℕ) (h' : IsZero ((Q.rightDerived (n + 1)).obj S.X₁)) :
    Epi ((Q.rightDerived n).map S.g) :=
  (horseshoe hS).epi_rightDerived_map_g Q n h'

include hS in
/-- **A left exact `Q` is right exact at a short exact sequence whose sub-object has vanishing
first right derived functor**: if `R¹Q X₁ = 0` then `Q X₂ ⟶ Q X₃` is an epimorphism.

This is `Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_map_g` in degree zero, read
through `CategoryTheory.Functor.rightDerivedZeroIsoSelf`, which identifies `R⁰Q` with `Q` for a
left exact `Q`. -/
theorem epi_map_g_of_isZero_rightDerived_one [PreservesFiniteLimits Q]
    (h : IsZero ((Q.rightDerived 1).obj S.X₁)) : Epi (Q.map S.g) := by
  have := epi_rightDerived_map_g hS Q 0 h
  have hepi : Epi (Q.rightDerivedZeroIsoSelf.hom.app S.X₂ ≫ Q.map S.g) := by
    rw [← Q.rightDerivedZeroIsoSelf.hom.naturality S.g]
    infer_instance
  exact epi_of_epi (Q.rightDerivedZeroIsoSelf.hom.app S.X₂) (Q.map S.g)

end Existence

end Stacks.Cohomology.RightDerivedDelta

end
