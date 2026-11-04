module

public import StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Comparison of derived torsion and local cohomology

For a finitely generated ideal `I` of a commutative ring `A`, the derived power-torsion
functor `RΓ_I`, followed by the comparison to the power-torsion part of `D(A)`, carries a
canonical natural transformation to local cohomology with support in `V(I)`.

## Main definitions

* `Dualizing.compareTorsionFunctorsData` — the comparison together with its characterization.
* `Dualizing.compareTorsionFunctors` — the comparison natural transformation.

## Main results

* `Dualizing.compareTorsionFunctorsData_nonempty` — the canonical derived torsion counit
  factors uniquely through the local cohomology counit.

## Implementation notes

The comparison is characterized componentwise as the unique factorization of the canonical
derived torsion map `RΓ_I → id` through the local cohomology counit. That derived torsion map
is `Dualizing.derivedPowerTorsionCounit`, the normalized counit of Tag 0A6L, whose
normalization is induced by the underived torsion-submodule inclusion. The module universe is
enlarged to `max u v` to match that construction.

## References

* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The canonical derived torsion counit factors uniquely through the local cohomology
counit. -/
theorem compareTorsionFunctorsData_nonempty
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Nonempty (Σ' α : (derivedPowerTorsion.{u, v} A I hI ⋙
        powerTorsionComparison.{u, max u v} A I hI) ⟶
        localCohomologyFunctor.{u, max u v} A I hI,
      ∀ K,
        let factors := fun f ↦
          (derivedPowerTorsionProperty A I hI).ι.map f ≫
              (localCohomologyAdjunction.{u, max u v} A I hI).counit.app K =
            (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
                ((derivedPowerTorsion.{u, v} A I hI).obj K) ≫
              (derivedPowerTorsionCounit.{u, v} A I hI).app K
        factors (α.app K) ∧ ∀ f, factors f → f = α.app K) := by
  refine ⟨?_⟩
  let adj := localCohomologyAdjunction.{u, max u v} A I hI
  let α :
      (derivedPowerTorsion.{u, v} A I hI ⋙
        powerTorsionComparison.{u, max u v} A I hI) ⟶
        localCohomologyFunctor.{u, max u v} A I hI := by
    refine
      { app := fun K => (adj.homEquiv _ K)
            ((powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
                ((derivedPowerTorsion.{u, v} A I hI).obj K) ≫
              (derivedPowerTorsionCounit.{u, v} A I hI).app K)
        naturality := ?_ }
    intro K K' f
    change
      ((derivedPowerTorsion.{u, v} A I hI ⋙
        powerTorsionComparison.{u, max u v} A I hI).map f ≫
          (adj.homEquiv _ K')
            ((powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
                ((derivedPowerTorsion.{u, v} A I hI).obj K') ≫
              (derivedPowerTorsionCounit.{u, v} A I hI).app K')) =
        ((adj.homEquiv _ K)
            ((powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
                ((derivedPowerTorsion.{u, v} A I hI).obj K) ≫
              (derivedPowerTorsionCounit.{u, v} A I hI).app K) ≫
          (localCohomologyRightAdjoint.{u, max u v} A I hI).1.map f)
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    change
      (adj.homEquiv
        ((derivedPowerTorsion.{u, v} A I hI ⋙
          powerTorsionComparison.{u, max u v} A I hI).obj K) K') _ =
      (adj.homEquiv
        ((derivedPowerTorsion.{u, v} A I hI ⋙
          powerTorsionComparison.{u, max u v} A I hI).obj K) K') _
    apply congrArg (adj.homEquiv
      ((derivedPowerTorsion.{u, v} A I hI ⋙
        powerTorsionComparison.{u, max u v} A I hI).obj K) K')
    let P : ObjectProperty (ModuleCat.{max u v} A) :=
      fun M => IsIPowerTorsion A M I
    let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    let : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    let : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    have hmap :
        (derivedPowerTorsionProperty A I hI).ι.map
            ((derivedPowerTorsion.{u, v} A I hI ⋙
              powerTorsionComparison.{u, max u v} A I hI).map f) =
          (P.ι.mapDerivedCategory).map
            ((derivedPowerTorsion.{u, v} A I hI).map f) := by
      rfl
    simp only [powerTorsionComparisonCompInclusionIso,
      ObjectProperty.liftCompιIso, Iso.refl_hom]
    rw [hmap]
    change
      ((P.ι.mapDerivedCategory).map
          ((derivedPowerTorsion.{u, v} A I hI).map f) ≫
        𝟙 ((derivedPowerTorsion.{u, v} A I hI ⋙
          P.ι.mapDerivedCategory).obj K') ≫
        (derivedPowerTorsionCounit.{u, v} A I hI).app K') =
      (𝟙 ((derivedPowerTorsion.{u, v} A I hI ⋙
          P.ι.mapDerivedCategory).obj K) ≫
        (derivedPowerTorsionCounit.{u, v} A I hI).app K) ≫ f
    calc
      _ = (P.ι.mapDerivedCategory.map
            ((derivedPowerTorsion.{u, v} A I hI).map f) ≫
          (derivedPowerTorsionCounit.{u, v} A I hI).app K') := by cat_disch
      _ = (derivedPowerTorsionCounit.{u, v} A I hI).app K ≫ f :=
        (derivedPowerTorsionCounit.{u, v} A I hI).naturality f
      _ = _ := by cat_disch
  refine ⟨α, ?_⟩
  intro K
  dsimp [α]
  constructor
  · exact (adj.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  · exact fun f hf ↦ (adj.homEquiv _ K).symm.injective <|
      (adj.homEquiv_counit _ _ _).trans (hf.trans (Equiv.symm_apply_apply _ _).symm)

/-- The natural transformation and its characterization as the unique factorization of the
canonical derived torsion counit. -/
noncomputable def compareTorsionFunctorsData
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Σ' α : (derivedPowerTorsion.{u, v} A I hI ⋙
        powerTorsionComparison.{u, max u v} A I hI) ⟶
        localCohomologyFunctor.{u, max u v} A I hI,
      ∀ K,
        let factors := fun f ↦
          (derivedPowerTorsionProperty A I hI).ι.map f ≫
              (localCohomologyAdjunction.{u, max u v} A I hI).counit.app K =
            (powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI).hom.app
                ((derivedPowerTorsion.{u, v} A I hI).obj K) ≫
              (derivedPowerTorsionCounit.{u, v} A I hI).app K
        factors (α.app K) ∧ ∀ f, factors f → f = α.app K :=
  Classical.choice (compareTorsionFunctorsData_nonempty A I hI)

/-- **Stacks 0A6U.** The canonical natural transformation from derived power torsion followed
by the comparison functor to local cohomology with support in `V(I)`. -/
@[stacks 0A6U]
noncomputable def compareTorsionFunctors
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (derivedPowerTorsion.{u, v} A I hI ⋙
      powerTorsionComparison.{u, max u v} A I hI) ⟶
      localCohomologyFunctor.{u, max u v} A I hI :=
  (compareTorsionFunctorsData.{u, v} A I hI).1

end Dualizing
