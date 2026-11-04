module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilization
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso

/-!
# Two stabilizations of a prestable family have isomorphic fibres

Let `X ⟶ S` be a prestable family of curves whose fibres have genus `g ≥ 2`, and let
`cᵢ : X ⟶ Yᵢ`, `i = 1, 2`, be morphisms to families of curves over `S` satisfying condition (2) of
Stacks 0E8A: on every fibre, `cᵢ` is the contraction to a stable curve of Algebraic Curves,
Section 0E7N. Then over every field-valued point `p` of `S` the fibres `Y₁,p` and `Y₂,p` are
related by a unique isomorphism under `X_p`: the fibre `X_p` satisfies the standing hypotheses of
Stacks 0E7Q (`AlgebraicGeometry.CurveFamily.fibre_standing_of_isPrestableCurveFamily`), which
characterizes the contraction up to unique isomorphism.

This is the isomorphism of fibres that Stacks 0E89 extends to a neighbourhood of the point, in the
proof of the uniqueness in Stacks 0E8A.

## Main results

* `AlgebraicGeometry.CurveFamily.existsUnique_fibreIso_of_hasStableContractionFibres`

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The fibres of two stabilizations are related by a unique isomorphism.** Let `X` be a
prestable family whose fibres have genus `g ≥ 2` and `cᵢ : X ⟶ Yᵢ` two morphisms over the base
satisfying condition (2) of Stacks 0E8A. For presentations `V_X`, `V₁`, `V₂` of the fibres over a
field-valued point `p` and the fibres `aᵢ : V_X ⟶ Vᵢ` of the `cᵢ`, there is exactly one isomorphism
`φ : V₁ ≅ V₂` of the site with `a₁ ≫ φ = a₂`, and it lies over `p`. -/
theorem existsUnique_fibreIso_of_hasStableContractionFibres {X Y₁ Y₂ : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g) (hgen : X.HasFibresOfGenus g)
    {hb₁ : Y₁.base = X.base} {hb₂ : Y₂.base = X.base} {c₁ : X.total ⟶ Y₁.total}
    {c₂ : X.total ⟶ Y₂.total}
    (h₁ : X.HasStableContractionFibres B hZ Y₁ hb₁ c₁)
    (h₂ : X.HasStableContractionFibres B hZ Y₂ hb₂ c₂)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {VX V₁ V₂ : BigFppfOver B integerBase hZ} {vX : VX ⟶ p.siteObject}
    {v₁ : V₁ ⟶ p.siteObject} {v₂ : V₂ ⟶ p.siteObject} {qX : yoneda.obj VX ⟶ X.total.obj}
    {q₁ : yoneda.obj V₁ ⟶ Y₁.total.obj} {q₂ : yoneda.obj V₂ ⟶ Y₂.total.obj}
    (hqX : IsPullback qX (yoneda.map vX) X.toBase.hom (yonedaEquiv.symm p.value))
    (hq₁ : IsPullback q₁ (yoneda.map v₁) (Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁)).hom
      (yonedaEquiv.symm p.value))
    (hq₂ : IsPullback q₂ (yoneda.map v₂) (Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂)).hom
      (yonedaEquiv.symm p.value))
    {a₁ : VX ⟶ V₁} {a₂ : VX ⟶ V₂} (ha₁ : a₁ ≫ v₁ = vX) (ha₂ : a₂ ≫ v₂ = vX)
    (hqa₁ : qX ≫ c₁.hom = yoneda.map a₁ ≫ q₁) (hqa₂ : qX ≫ c₂.hom = yoneda.map a₂ ≫ q₂) :
    ∃ φ : V₁ ≅ V₂, a₁ ≫ φ.hom = a₂ ∧ φ.hom ≫ v₂ = v₁ ∧
      ∀ φ' : V₁ ≅ V₂, a₁ ≫ φ'.hom = a₂ → φ' = φ := by
  obtain ⟨hprop, hH0, hdim, hnodal⟩ := fibre_standing_of_isPrestableCurveFamily hX hqX
  have hst₁ := h₁ p VX V₁ vX v₁ qX q₁ a₁ hqX hq₁ ha₁ hqa₁
  have hst₂ := h₂ p VX V₂ vX v₂ qX q₂ a₂ hqX hq₂ ha₂ hqa₂
  have hgenus : 2 ≤ genus ((𝒯).map vX) := ((hgen p).genus_eq vX qX hqX).symm ▸ hg
  obtain ⟨e, he, heu⟩ := Stacks.Curves.StableModel.existsUnique_iso_of_isStableContraction
    ((𝒯).map vX) hdim hgenus hnodal hst₁ hst₂
  let F := BigFppfOver.fullyFaithfulToScheme B integerBase hZ specULiftZIsTerminal
  refine ⟨F.preimageIso e, ?_, ?_, fun φ' hφ' => ?_⟩
  · apply F.map_injective
    rw [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom, F.map_preimage, he]
  · apply F.map_injective
    rw [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom, F.map_preimage]
    refine hst₁.ext (gY' := 𝟙 _) ?_
    rw [← Category.assoc, he, ← Functor.map_comp, ← Functor.map_comp, ha₁, ha₂]
  · apply Iso.ext
    apply F.map_injective
    rw [Functor.FullyFaithful.preimageIso_hom, F.map_preimage]
    have := heu ((𝒯).mapIso φ') (by dsimp only; rw [Functor.mapIso_hom, ← Functor.map_comp, hφ'])
    exact congrArg Iso.hom this

end CurveFamily

end AlgebraicGeometry

end
