module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally
public import StacksCore.Tactic.StacksAttribute

/-!
# Normalized base change over a Dedekind domain

For a finite extension of the fraction field of a Dedekind domain, the normalized base change
of a flat finite-type scheme is the normalization of its pullback to the integral closure. Its
structure morphism to the integral closure is the composite of normalization and the pullback
projection.

## Main definitions

* `AlgebraicGeometry.normalizedBaseChange` is the normalization of the pullback, as a scheme
  over the pullback.
* `AlgebraicGeometry.normalizedBaseChangeOverIntegralClosure` is the same scheme over the
  integral closure.

## Implementation notes

The integral closure is represented abstractly by `IsIntegralClosure B A L`. The finite
extension supplies its Dedekind and hence Noetherian property. The two morphisms out of the
normalized scheme are the normalization morphism and its composite with the pullback
projection. The displayed triangle commutes by construction.

## References

* [Stacks Project, Tag 09IK](https://stacks.math.columbia.edu/tag/09IK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The normalized pullback of a finite-type scheme over a Dedekind domain along the
integral closure in a finite fraction-field extension, as a scheme over the pullback. -/
@[stacks 09IK "the normalization morphism to the base change"]
noncomputable def normalizedBaseChange
    (A K L B : Type u)
    [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A))
    [Flat p] [LocallyOfFiniteType p] [QuasiCompact p] :
    let g : Spec (.of B) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    Over (pullback p g) := by
  have : IsDedekindDomain B :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A K L B).1
  intro g
  let XB := pullback p g
  have hXB : ∀ U : XB.Opens, IsCompact (U : Set XB) →
      (irreducibleComponents U).Finite := by
    have : IsLocallyNoetherian XB :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p g)
    intro U hU
    have : CompactSpace U := isCompact_iff_compactSpace.mp hU
    have : NoetherianSpace U := noetherianSpace_of_isLocallyNoetherianSpace U
      ((isLocallyNoetherianSpace_of_isLocallyNoetherian XB).subtype U)
    exact NoetherianSpace.finite_irreducibleComponents
  exact Over.mk (Stacks.AlgebraicGeometry.Normalization.normalization XB hXB)

/-- The structure morphism to the integral closure in the normalized base-change diagram. -/
@[stacks 09IK "the morphism to the integral closure"]
noncomputable def normalizedBaseChangeOverIntegralClosure
    (A K L B : Type u)
    [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A))
    [Flat p] [LocallyOfFiniteType p] [QuasiCompact p] :
    Over (Spec (.of B)) :=
  Over.mk ((normalizedBaseChange A K L B X p).hom ≫ pullback.snd p _)

end AlgebraicGeometry
