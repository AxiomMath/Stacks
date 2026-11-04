module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.DualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DualizingDegree
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of a curve without rational tails or bridges is ample

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, whose
singularities are at worst nodal, which has neither a rational tail nor a rational bridge, and
whose genus is at least two. Then `ω_X` is invertible and ample ([Stacks, Tag 0E3P]).

## Main results

* `AlgebraicGeometry.isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities`: the
  dualizing sheaf of such a curve is invertible and ample.

## References

* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ComponentDegrees

/-- Let `k` be a field and let `X` be a proper scheme over `k` of dimension one with
`H⁰(X, 𝒪_X) = k`. If the singularities of `X` are at worst nodal, `X` has no rational tail and no
rational bridge, and the genus of `X` is at least two, then `ω_X` is an invertible `𝒪_X`-module
and it is ample. -/
@[stacks 0E3P]
theorem isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C)
    (hg : 2 ≤ genus (X ↘ Spec (.of k))) :
    ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))),
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) := by
  let f := X ↘ Spec (.of k)
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hXeq : TopologicalSpace.Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k f hdim
  have : IsGorenstein X :=
    Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities k X hXeq hdim hnodal
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  have hω : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
    isInvertible_dualizingSheafOverField_of_connectedSpace k f hdim
  refine ⟨hω, (isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos k f hdim.le
    (Stacks.Duality.dualizingSheafOverField f)).mpr fun ζ => ?_⟩
  let Z : TopologicalSpace.Closeds X := ⟨closure ({ζ.1} : Set X), isClosed_closure⟩
  let C := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsIntegral C.subscheme := isIntegral_reducedComponent X ζ
  have hCdim : topologicalKrullDim C.subscheme = 1 := topologicalKrullDim_reducedComponent X ζ
  have hCeq : TopologicalSpace.Equidimensional C.subscheme :=
    TopologicalSpace.Equidimensional.of_preirreducibleSpace C.subscheme
  have hωC : let := isIntegral_reducedComponent X ζ
      let : Field Γ(reducedComponent X ζ, ⊤) :=
        (isField_of_universallyClosed k (reducedComponentι X ζ ≫ f)).toField
      have : IsProper (reducedComponent X ζ).toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ (reducedComponentι X ζ ≫ f)
      SheafOfModules.IsInvertible (reducedComponent X ζ).presheaf
        (reducedComponent X ζ).ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (reducedComponent X ζ).toSpecΓ) := by
    intro _ _ _
    have : IsGorenstein (reducedComponent X ζ) :=
      isGorenstein_reducedComponent_of_hasAtWorstNodalSingularities k X hXeq hdim hnodal ζ
    exact isInvertible_dualizingSheafOverField_of_connectedSpace Γ(reducedComponent X ζ, ⊤)
      (reducedComponent X ζ).toSpecΓ hCdim
  have hseq := (Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible f hXeq hdim
    C hCeq hCdim).2.2.2.2.2.2.2.2.1
  exact invertibleCurveDegree_pullback_reducedComponent_dualizingSheafOverField_pos k X hdim
    htail hbridge hg ζ hωC hseq

end AlgebraicGeometry

end
