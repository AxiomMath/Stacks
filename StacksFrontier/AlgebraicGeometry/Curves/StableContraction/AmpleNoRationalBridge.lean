module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.TricanonicalVeryAmple

/-!
# Stable curves over a field: no rational tails or bridges, or ample dualizing sheaf

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, at-worst-nodal
singularities and genus `g ≥ 2`. Then `X` has no rational tail and no rational bridge exactly when
its dualizing sheaf `ω_X` is ample. This is the comparison of conditions (b) and (c) of part (2)
of Stacks 0E76 and Stacks 0E78, and the fibrewise content of Stacks 0E74.

## Main results

* `AlgebraicGeometry.forall_not_isRationalBridge_of_isAmple_dualizingSheafOverField`: if `ω_X` is
  ample, `X` has no rational bridge, since `deg(ω_X|_C) = 0` on a rational bridge `C`
  ([Stacks, Tag 0E64]) while the pullback of an ample invertible module along the affine morphism
  `C ⟶ X` has positive degree.
* `AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`: the
  equivalence. One direction is [Stacks, Tag 0E3P]; the other is
  `AlgebraicGeometry.forall_not_isRationalTail_of_isAmple_dualizingSheafOverField` (from
  [Stacks, Tag 0E63]) together with the previous result.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E64](https://stacks.math.columbia.edu/tag/0E64)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A nodal curve with ample dualizing sheaf has no rational bridge.** Let `X` be a proper
scheme of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities whose
dualizing sheaf `ω_X` is ample. On a rational bridge `C` the degree of `ω_X|_C` is zero
([Stacks, Tag 0E64]), while the pullback of an ample invertible module along the affine morphism
`C ⟶ X` has positive degree. -/
theorem forall_not_isRationalBridge_of_isAmple_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (C : X.IdealSheafData) : ¬ IsRationalBridge k X C := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  intro hC
  have : IsIntegral C.subscheme := hC.isIntegral
  have hpos := invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k
    (C.subschemeι ≫ (X ↘ Spec (.of k)))
    (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalBridge k X hdim hC)
    C.subschemeι _ hω
  exact hpos.ne' <|
    invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hdim hnodal
      C hC

/-- **No rational tails or bridges, or ample dualizing sheaf.** Let `X` be a proper scheme of
dimension one over `k` with `H⁰(X, 𝒪_X) = k`, at-worst-nodal singularities and genus `g ≥ 2`.
Then `X` has no rational tail and no rational bridge exactly when `ω_X` is ample. -/
theorem forall_not_isRationalTail_and_isRationalBridge_iff_isAmple
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hg : 2 ≤ genus (X ↘ Spec (.of k))) :
    ((∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ∧
        ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) ↔
      haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) := by
  refine ⟨fun h => ?_, fun hω =>
    ⟨forall_not_isRationalTail_of_isAmple_dualizingSheafOverField hdim hnodal hω,
      forall_not_isRationalBridge_of_isAmple_dualizingSheafOverField hdim hnodal hω⟩⟩
  obtain ⟨_, hample⟩ := isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
    hnodal h.1 h.2 hg
  exact hample

end AlgebraicGeometry

end
