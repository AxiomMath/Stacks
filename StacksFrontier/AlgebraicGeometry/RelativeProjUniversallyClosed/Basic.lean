module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.DegreeZeroConditions

/-!
# Universal closedness of the relative homogeneous spectrum of sheaf-level graded algebra data

Let `S` be a scheme and `A` a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra,
given as `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. If `𝒪_S → A₀` is
integral and `A` is of finite type over `A₀`, the structure morphism of `Proj_S(A)` is
universally closed. This is Stacks 07ZZ on the substrate on which Stacks 084B presents the
base changes of the relative Proj of an algebraic space.

Over an affine open `U` of the base the chart square identifies the restriction of the structure
morphism with `Proj Γ(U, A) ⟶ Spec Γ(U, A)₀ ⟶ Spec Γ(S, U) ≅ U`. The first leg is proper, by
Mathlib's `AlgebraicGeometry.Proj.toSpecZero` instance, since `Γ(U, A)` is of finite type over
`Γ(U, A)₀`; the second is integral, hence universally closed. Universal closedness is local on
the target.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed.universallyClosed_toBase`.

## References

* [Stacks Project, Tag 07ZZ](https://stacks.math.columbia.edu/tag/07ZZ)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- Over an affine open on which `Γ(U, A)` is of finite type over `Γ(U, A)₀` and
`Γ(S, U) → Γ(U, A)₀` is integral, the chart structure morphism `Proj Γ(U, A) ⟶ U` is universally
closed. -/
theorem universallyClosed_projInclusionToOpen (U : S.Opens) (hU : IsAffineOpen U)
    (hint : ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)).IsIntegral)
    (hft : Algebra.FiniteType (A.grading U 0) (A.sectionRing U)) :
    UniversallyClosed (projInclusionToOpen A U hU) := by
  let φ := (GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) :=
    IsIntegralHom.SpecMap_iff.mpr hint
  have hdef : projInclusionToOpen A U hU =
      Proj.toSpecZero (A.grading U) ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv := rfl
  rw [hdef]
  infer_instance

/-- **Stacks 07ZZ**, for sheaf-level graded algebra data. If `𝒪_S → A₀` is integral and `A` is of
finite type as an `A₀`-algebra, the structure morphism of the relative homogeneous spectrum
`Proj_S(A) ⟶ S` is universally closed. -/
theorem universallyClosed_toBase (hint : A.IsIntegralInDegreeZero)
    (hft : A.IsFiniteTypeOverDegreeZero) :
    UniversallyClosed (relativeProj A).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @UniversallyClosed)
    (fun V : S.affineOpens => (V : S.Opens)) (iSup_affineOpens_eq_top S)]
  intro V
  have hchart := (relativeProj A).chart_isPullback (V : S.Opens) V.2
  have hrestrict := (isPullback_morphismRestrict (relativeProj A).toBase (V : S.Opens)).flip
  have he : (hchart.isoIsPullback _ _ hrestrict).inv ≫
      projInclusionToOpen A (V : S.Opens) V.2 = (relativeProj A).toBase ∣_ (V : S.Opens) :=
    hchart.isoIsPullback_inv_snd _ _ hrestrict
  have := hft (V : S.Opens) V.2
  have := universallyClosed_projInclusionToOpen A (V : S.Opens) V.2 (hint _ V.2) this
  rw [← he]
  infer_instance

end Stacks.AlgebraicGeometry.RelativeProjUniversallyClosed

end
