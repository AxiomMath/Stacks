module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.Conic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafRank

/-!
# A Gorenstein genus-zero curve is a plane conic

Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`. If `X` is Gorenstein and has
genus `0`, then `X` is isomorphic to a plane curve of degree `2`: this is [Stacks, Tag 0C6N].

On a Gorenstein curve the dualizing sheaf `ω_X` of [Stacks, Tag 0BS2] is invertible of degree
`2g - 2 = -2` ([Stacks, Tag 0C19]), so `ω_X^{⊗ -1}` has degree `2`, and a genus-zero curve with an
invertible module of degree two is a plane conic
(`AlgebraicGeometry.exists_planeCurveData_deg_two_of_invertibleCurveDegree_eq_two`).

## Main results

* `AlgebraicGeometry.exists_planeCurveData_deg_two_of_isGorenstein`: a Gorenstein proper curve
  of genus `0` with `H⁰(X, 𝒪_X) = k` is isomorphic over `k` to a plane curve of degree `2`.

## References

* [Stacks Project, Tag 0C6N](https://stacks.math.columbia.edu/tag/0C6N)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`. If `X` is Gorenstein and
has genus `0`, then `X` is isomorphic over `k` to a plane curve of degree `2`. -/
@[stacks 0C6N]
theorem exists_planeCurveData_deg_two_of_isGorenstein [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] [IsGorenstein X]
    (hgenus : genus f = 0) :
    ∃ C : ProjectiveSpectrum.Proj.PlaneCurveData k, C.deg = 2 ∧
      ∃ e : X ≅ C.Z, e.hom ≫ C.toSpec = f := by
  have hdim : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)
  let := connectedSpace_of_isIso_globalSections k f
  let hω := isInvertible_dualizingSheafOverField_of_connectedSpace k f hdim
  have hωdeg := invertibleCurveDegree_dualizingSheafOverField k f hdim
  rw [hgenus] at hωdeg
  let := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2
    (Stacks.Duality.dualizingSheafOverField f) (-1)
  refine exists_planeCurveData_deg_two_of_invertibleCurveDegree_eq_two f hdim hgenus
    (tensorPower X.presheaf X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField f) (-1)) ?_
  rw [invertibleCurveDegree_tensorPower k f hdim.le _ (-1), hωdeg]
  norm_num

end AlgebraicGeometry

end
