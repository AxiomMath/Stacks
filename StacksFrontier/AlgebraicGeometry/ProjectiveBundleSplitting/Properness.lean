module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Proper
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.ProjectiveBundleTwists

/-!
# The projection of the graded-algebra presentation of a projective bundle is proper

Properness of the projection of a projective bundle is proved for one of this repository's two
presentations of `𝐏(ℰ)`, the one built from a `Stacks.RelativeProj.Situation`, as
`Stacks.RelativeProj.isProper_projectiveBundleToBase`. The twists `𝒪_{𝐏(ℰ)}(n)` live on the
other, the one built from a `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`,
as `Stacks.SymGraded.schemeProjectiveBundle`. This file carries properness across.

The crossing is free: `AlgebraicGeometry.projectiveBundlePresentationsAgree` is proved, and it
provides an isomorphism of the two bundles commuting with the two projections. An isomorphism is
proper and properness is stable under composition, so the projection of the graded-algebra
presentation is proper too.

## Main results

* `Stacks.ProjectiveBundleSplitting.isQuasicoherentPieces_of_isFiniteLocallyFree`: a finite
  locally free module satisfies `Stacks.SymGraded.IsQuasicoherentPieces`.
* `Stacks.ProjectiveBundleSplitting.isProper_schemeProjectiveBundleToBase`: **the projection
  `𝐏(ℰ) ⟶ X` of the graded-algebra presentation of the projective bundle of a finite locally
  free module is proper.**

## References

* [Stacks Project, Tag 0800](https://stacks.math.columbia.edu/tag/0800)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleSplitting

variable {X : Scheme.{u}} (E : X.Modules)

/-- A finite locally free module is quasi-coherent, so every homogeneous piece of its symmetric
algebra is, which is `Stacks.SymGraded.IsQuasicoherentPieces`. -/
public theorem isQuasicoherentPieces_of_isFiniteLocallyFree
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsQuasicoherentPieces E :=
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  isQuasicoherentPieces_of_isQuasicoherent E

/-- **The projection of the graded-algebra presentation of the projective bundle of a finite
locally free module is proper.**

`Stacks.RelativeProj.isProper_projectiveBundleToBase` is properness for the presentation built
from the relative `Proj` situation of `Sym(ℰ)`, and
`AlgebraicGeometry.projectiveBundlePresentationsAgree` identifies the two presentations over the
base. Properness transports because an isomorphism is proper and properness is stable under
composition. -/
public theorem isProper_schemeProjectiveBundleToBase [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hqc : IsQuasicoherentPieces E) :
    IsProper (schemeProjectiveBundleToBase E hqc) := by
  obtain ⟨b, hb⟩ := AlgebraicGeometry.projectiveBundlePresentationsAgree E hqc
  have hprop : IsProper (Stacks.RelativeProj.projectiveBundleToBase X E) :=
    Stacks.RelativeProj.isProper_projectiveBundleToBase X E
  have : IsProper b.hom := inferInstance
  have : IsProper (b.hom ≫ Stacks.RelativeProj.projectiveBundleToBase X E) := inferInstance
  rwa [hb] at this

end Stacks.ProjectiveBundleSplitting

end
