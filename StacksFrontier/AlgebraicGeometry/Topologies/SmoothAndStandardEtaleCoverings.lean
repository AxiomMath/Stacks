module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings
import StacksCore.Tactic.StacksAttribute

/-!
# Smooth coverings and standard étale coverings

A smooth covering of a scheme `T` is a family of smooth morphisms with target `T` whose images
cover `T`, and a standard étale covering of an affine scheme `T` is a finite family of étale
morphisms from affine schemes to `T` whose images cover `T`. This file defines the precoverage of
smooth coverings and the standard étale coverings, and records that every Zariski covering is an
étale covering.

## Main definitions

* `AlgebraicGeometry.Scheme.smoothPrecoverage` is the precoverage of smooth coverings.
* `AlgebraicGeometry.IsStandardEtaleCovering` is the predicate singling out the standard étale
  coverings of an affine scheme.

## Main results

* `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_etalePrecoverage`: every Zariski covering is
  an étale covering.
* `AlgebraicGeometry.isStandardEtaleCovering_iff` unfolds a standard étale covering into its
  four conditions.

## References

* [Stacks Project, Tag 0216](https://stacks.math.columbia.edu/tag/0216)
* [Stacks Project, Tag 0219](https://stacks.math.columbia.edu/tag/0219)
* [Stacks Project, Tag 021Z](https://stacks.math.columbia.edu/tag/021Z)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A standard étale covering of an affine scheme `T`: a finite family of étale morphisms
`f i : U i ⟶ T` with affine sources whose images cover `T`, that is, the étale case of
`AlgebraicGeometry.IsStandardCovering`. -/
@[stacks 0219]
public abbrev IsStandardEtaleCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T) : Prop :=
  IsStandardCovering .etale U f

/-- A family is a standard étale covering of an affine scheme exactly when it is finite, has
affine sources, is jointly surjective and consists of étale morphisms. -/
public theorem isStandardEtaleCovering_iff {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {U : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} :
    IsStandardEtaleCovering U f ↔
      Finite I ∧ (∀ i, IsAffine (U i)) ∧ (⋃ i, Set.range (f i)) = Set.univ ∧
        ∀ i, Etale (f i) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3, h.4⟩, fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

namespace Scheme

/-- Every Zariski covering is an étale covering. -/
@[stacks 0216]
public theorem zariskiPrecoverage_le_etalePrecoverage :
    zariskiPrecoverage.{u} ≤ etalePrecoverage :=
  precoverage_mono fun _ _ _ _ ↦ inferInstance

/-- The smooth precoverage on the category of schemes: its covering families are the jointly
surjective families of smooth morphisms. -/
@[stacks 021Z]
public def smoothPrecoverage : Precoverage Scheme.{u} :=
  precoverage @Smooth

/-- Smooth coverings are stable under base change. -/
public instance : smoothPrecoverage.IsStableUnderBaseChange :=
  @instIsStableUnderBaseChangePrecoverageOfIsJointlySurjectivePreservingOfIsStableUnderBaseChange
    _ (isJointlySurjectivePreserving _) _

/-- Smooth coverings are stable under composition. -/
public instance : smoothPrecoverage.IsStableUnderComposition :=
  instIsStableUnderCompositionPrecoverageOfIsStableUnderComposition _

end Scheme

end AlgebraicGeometry
