module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiSummands

/-!
# The category of Chow motives is additive

Stacks 0FGF: the category `M_k` of Chow motives over a field `k` is additive. It is preadditive,
being `ℚ`-linear (Stacks 0FGA); what has to be shown is that it has finite direct sums.

A zero object is any motive `(X, 0, m)` with zero projector. For two motives `(Y, p, m)` and
`(Z, q, m)` with the same twist a direct sum is `(Y ⨿ Z, p + q, m)`, "with obvious notation": the
projector is `[Γ_iᵗ] ∘ p ∘ [Γ_i] + [Γ_jᵗ] ∘ q ∘ [Γ_j]` for the coprojections `i`, `j` of the
disjoint union, by the relations between graphs and transposed graphs of the coprojections of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences`.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.coprodSummandData`: `Y` and `Z` as direct summands of
  `Y ⨿ Z` in the category of correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.biproductDataOfTwistEq`: the direct sum
  `(Y ⨿ Z, p + q, m)` of two motives with the same twist.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.isZero_zeroMotive`: `(Spec k, 0, 0)` is a zero object.
* `Stacks.WeilCohomology.ChowMotiveCat.hasBinaryBiproduct_of_twist_eq`: two motives with the same
  twist have a direct sum.

## References

* [Stacks Project, Tag 0FGF](https://stacks.math.columbia.edu/tag/0FGF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GradedCategory AlgebraicGeometry
  MonoidalCategory

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k]

/-! ### A zero object -/

/-- The zero motive `(Spec k, 0, 0)`. -/
def zeroMotive : ChowMotiveCat k where
  X := GradedCompositionData.Obj.mk (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))
  p := 0
  p_mem := Submodule.zero_mem _
  idem := Limits.zero_comp
  twist := 0

/-- The zero motive is a zero object of `M_k`. -/
theorem isZero_zeroMotive : IsZero (zeroMotive : ChowMotiveCat k) :=
  TwistedKaroubi.isZero_of_p_eq_zero _ rfl

/-- The category `M_k` of Chow motives has a zero object. -/
instance hasZeroObject : HasZeroObject (ChowMotiveCat k) :=
  ⟨⟨zeroMotive, isZero_zeroMotive⟩⟩

/-! ### Direct sums of motives with the same twist -/

/-- `Y` and `Z` are direct summands of the disjoint union `Y ⨿ Z` in the category of
correspondences, through the transposed graphs and the graphs of the coprojections. -/
def coprodSummandData (Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    TwistedKaroubi.SummandData (R := ℚ)
      (GradedCompositionData.Obj.mk Y : (canonicalCorrespondenceCompositionData k).Obj)
      (GradedCompositionData.Obj.mk Z)
      (GradedCompositionData.Obj.mk (SmoothProjectiveScheme.coprodObj Y Z)) where
  ιX := cographHom (SmoothProjectiveScheme.coprodInl Y Z)
  πX := homOf 0 (graphCorrespondenceSP (SmoothProjectiveScheme.coprodInl Y Z))
  ιY := cographHom (SmoothProjectiveScheme.coprodInr Y Z)
  πY := homOf 0 (graphCorrespondenceSP (SmoothProjectiveScheme.coprodInr Y Z))
  ιX_mem := cographHom_mem_grade _
  πX_mem := homOf_mem_grade _
  ιY_mem := cographHom_mem_grade _
  πY_mem := homOf_mem_grade _
  ιX_πX := by
    have : IsOpenImmersion (SmoothProjectiveScheme.coprodInl Y Z).hom.left :=
      SmoothProjectiveScheme.isOpenImmersion_inl
          (SmoothProjectiveScheme.isColimitCoprodCofan Y Z)
    exact cographHom_comp_graph_self _
  ιX_πY := cographHom_comp_graph_of_disjoint _ _
    (SmoothProjectiveScheme.isCompl_range_inl_inr
      (SmoothProjectiveScheme.isColimitCoprodCofan Y Z)).disjoint
  ιY_πX := cographHom_comp_graph_of_disjoint _ _
    (SmoothProjectiveScheme.isCompl_range_inl_inr
      (SmoothProjectiveScheme.isColimitCoprodCofan Y Z)).disjoint.symm
  ιY_πY := by
    have : IsOpenImmersion (SmoothProjectiveScheme.coprodInr Y Z).hom.left :=
      SmoothProjectiveScheme.isOpenImmersion_inr
          (SmoothProjectiveScheme.isColimitCoprodCofan Y Z)
    exact cographHom_comp_graph_self _

/-- **Stacks Project, Tag 0FGF, equal twists.** Two motives `M = (Y, p, m)` and `N = (Z, q, m)`
with the same twist have the direct sum `(Y ⨿ Z, p + q, m)`, whose projector is
`[Γ_iᵗ] ∘ p ∘ [Γ_i] + [Γ_jᵗ] ∘ q ∘ [Γ_j]` for the coprojections `i`, `j` of `Y ⨿ Z`. -/
def biproductDataOfTwistEq (M N : ChowMotiveCat k) (h : M.twist = N.twist) :
    BinaryBiproductData M N :=
  TwistedKaroubi.SummandData.biproductDataOfSummands (coprodSummandData M.scheme N.scheme) h

/-- Two motives with the same twist have a direct sum. -/
theorem hasBinaryBiproduct_of_twist_eq (M N : ChowMotiveCat k) (h : M.twist = N.twist) :
    HasBinaryBiproduct M N :=
  HasBinaryBiproduct.mk (biproductDataOfTwistEq M N h)

end Stacks.WeilCohomology.ChowMotiveCat

end
