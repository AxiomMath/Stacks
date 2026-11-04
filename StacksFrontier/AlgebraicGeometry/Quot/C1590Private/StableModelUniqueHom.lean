module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelExistsHom
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelUnique

/-!
# Uniqueness of the stable model

Two stable models `c₁ : X ⟶ Y₁` and `c₂ : X ⟶ Y₂` of a prestable family of curves of genus
`g ≥ 2` are related by a unique morphism of families `Y₁ ⟶ Y₂` compatible with them: they
contract the fibres alike (Stacks 0E7Q uniqueness), hence are isomorphic étale locally near every
point (Stacks 0E89), and the local isomorphisms glue.

## Main results

* `AlgebraicGeometry.C1590Private.IsStableModel.exists_hom`: the comparison morphism.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Uniqueness of the stable model.** Two stable models `c₁ : X ⟶ Y₁` over `b₁` and
`c₂ : X ⟶ Y₂` over `b₂` of a prestable family `X` of genus `g ≥ 2` are related by a morphism of
families `e : Y₁ ⟶ Y₂` with `b₁ ≫ e.baseMap = b₂` and `c₁ ≫ e.totalMap = c₂`. -/
theorem IsStableModel.exists_hom (h0E6F : HasEtaleLocalSchemeCharts B hZ) {g : ℕ}
    {X Y₁ Y₂ : CurveFamily B hZ} (hX : IsPrestableCurveFamily B hZ X) (hg : 2 ≤ g)
    {b₁ : X.base ⟶ Y₁.base} {c₁ : X.total ⟶ Y₁.total} {b₂ : X.base ⟶ Y₂.base}
    {c₂ : X.total ⟶ Y₂.total} (h₁ : IsStableModel B hZ g b₁ c₁)
    (h₂ : IsStableModel B hZ g b₂ c₂) :
    ∃ e : Y₁ ⟶ Y₂, b₁ ≫ e.baseMap = b₂ ∧ c₁ ≫ e.totalMap = c₂ := by
  have := h₁.isIso_base
  have := h₂.isIso_base
  refine h₁.exists_hom_of_locallyIso' h₂ fun s => ?_
  obtain ⟨U, e, he, hs, hiso⟩ := exists_etale_iso_of_fibre_contraction h0E6F b₁ b₂ c₁ c₂
    h₁.comp_toBase h₂.comp_toBase s (fibresContractedAlike_of_isStableModel hX hg h₁ h₂ s)
  exact ⟨U, e, he, hs, hiso⟩

end AlgebraicGeometry.C1590Private

end
