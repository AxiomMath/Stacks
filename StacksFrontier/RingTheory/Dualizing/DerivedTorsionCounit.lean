module

public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion

/-!
# The derived torsion adjunction as a value, and its normalized counit

Let `I` be a finitely generated ideal of a commutative ring `A`. Tag 0A6L asserts that local
cohomology `RΓ_I = Dualizing.derivedPowerTorsion` is right adjoint to the derived inclusion of
the `I`-power-torsion modules into `D(A)`, by an adjunction whose counit is normalized by the
underived torsion-submodule inclusion. This file names that adjunction and that counit.

## Main definitions

* `Dualizing.derivedPowerTorsionAdjunction` — the Tag 0A6L adjunction as a value.
* `Dualizing.derivedPowerTorsionCounit` — its counit `RΓ_I ⋙ ι ⟶ 𝟭 (D(A))`.

## Main results

* `Dualizing.derivedPowerTorsionCounit_isCanonical` — that counit is the one induced by the
  underived torsion-submodule inclusion.

## Implementation notes

*What "normalized" means here.* `Dualizing.IsCanonicalDerivedPowerTorsionCounit` asks of a
natural transformation `RΓ_I ⋙ ι ⟶ 𝟭 (D(A))` that its composite with the total right derived
unit of `RΓ_I` be the degreewise inclusion `Γ_I M ↪ M` of the `I`-power-torsion submodule,
read through the comparison map of the derived inclusion. On a K-injective resolution the
derived unit is invertible, so the condition determines the transformation. Tag 0A6L supplies
an adjunction whose counit satisfies it; this file chooses one such adjunction, so its counit
is not merely *a* counit of *an* adjunction between these functors but the one induced by the
underived inclusion.

## References

* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- **Stacks 0A6L, as a value.** The adjunction between the derived inclusion of the
`I`-power-torsion modules into `D(A)` and local cohomology `RΓ_I`, chosen so that its counit
is normalized by the underived torsion-submodule inclusion. -/
@[no_expose] noncomputable def derivedPowerTorsionAdjunction
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    P.ι.mapDerivedCategory ⊣ derivedPowerTorsion.{u, v} A I hI :=
  (derivedInclusion_adj_derivedPowerTorsion.{u, v} A I hI).choose

/-- **The normalized counit of the Tag 0A6L adjunction.** The counit
`RΓ_I ⋙ ι ⟶ 𝟭 (D(A))` of `Dualizing.derivedPowerTorsionAdjunction`, hence the natural
transformation obtained by descending the underived torsion-submodule inclusion
`Γ_I M ↪ M` along the two derived functors. -/
noncomputable def derivedPowerTorsionCounit (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    derivedPowerTorsion.{u, v} A I hI ⋙ P.ι.mapDerivedCategory ⟶
      𝟭 (DerivedCategory (ModuleCat.{max u v} A)) :=
  (derivedPowerTorsionAdjunction.{u, v} A I hI).counit

/-- The derived counit is induced by the degreewise torsion-submodule inclusion. -/
theorem derivedPowerTorsionCounit_isCanonical (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    IsCanonicalDerivedPowerTorsionCounit.{u, v} A I hI
      (derivedPowerTorsionCounit.{u, v} A I hI) :=
  (derivedInclusion_adj_derivedPowerTorsion.{u, v} A I hI).choose_spec

end Dualizing

end
