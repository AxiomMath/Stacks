/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialAmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType

/-!
# A relatively ample module over an affine base gives an immersion into `ℙⁿ`

Let `f : W ⟶ h_T` be a morphism of finite presentation of algebraic spaces over `Spec ℤ` to the
algebraic space of an affine scheme `T`, and `M` an invertible `𝒪_W`-module ample on `W/T`
(Stacks 0D31).  Then `W` is the algebraic space of a scheme `U`, the reading `M_U` of `M` on `U`
is invertible and ample, and some power `M_U^{⊗ d}`, `d ≥ 1`, is the inverse image of `𝒪(1)`
along an immersion `U ⟶ ℙⁿ_T` over `T` (Stacks 01VS); the immersion is a closed immersion into a
quasi-compact open `V ⊆ ℙⁿ_T`.

This is the embedding of the proof of Stacks 0DPD and 0DPR over an affine base.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.exists_immersionData_of_isRelativelyAmple`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace Stacks.AmpleProjectiveImmersion

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **The projective embedding over an affine base, with a quasi-compact open.**  For
`f : W ⟶ h_T` of finite presentation with `T` affine and `M` ample on `W/T`, there are a scheme
`U` with `h_U ≅ W` over `h_T`, an integer `d ≥ 1`, a quasi-compact open `V` of `ℙⁿ_T`, a closed
immersion `c : U ⟶ V` and the open immersion `o : V ⟶ ℙⁿ_T`, with `M_U^{⊗ d} ≅ (c ≫ o)^*𝒪(1)`. -/
theorem exists_immersionData_of_isRelativelyAmple (T : BigFppfOver B integerBase ℤS)
    [hT : IsAffine ((𝒯).obj T)] {W : AlgebraicSpaces B integerBase ℤS} (f : W ⟶ schemeSpace T)
    (hf : IsFinitePresentation B integerBase ℤS f.hom)
    (M : Modules.{u, u} B integerBase ℤS W.1 W.2) (hM : IsRelativelyAmple B integerBase ℤS f M) :
    ∃ (U : BigFppfOver B integerBase ℤS) (p : yoneda.obj U ⟶ W.1) (q : U ⟶ T)
      (_ : IsPullback p (yoneda.map q) f.hom (yoneda.map (𝟙 T)))
      (_ : Stacks.Ample.IsInvertibleModule ((𝒯).obj U) (baseChangeModule B integerBase ℤS M U p))
      (n d : ℕ) (_ : 1 ≤ d) (V : BigFppfOver B integerBase ℤS) (c : U ⟶ V)
      (o : V ⟶ projectiveSite B n T),
      _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map c) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map o) ∧ CompactSpace ((𝒯).obj V) ∧
      c ≫ o ≫ projectiveSiteStructure B n T = q ∧
      Nonempty (Stacks.Ample.tensorPowModule ((𝒯).obj U) (baseChangeModule B integerBase ℤS M U p)
          (d : ℤ) ≅
        (Scheme.Modules.pullback ((𝒯).map (c ≫ o))).obj
          (projectiveSpaceTwistingSheaf n ((𝒯).obj T))) := by
  obtain ⟨U, q, p, hsq⟩ := hM.1 (yoneda.map (𝟙 T))
  obtain ⟨hinv, hamp⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hM T U hT _ p q hsq
  -- `U` is quasi-compact and `U ⟶ T` locally of finite type
  have hqcU : IsQuasiCompactSpace B integerBase ℤS (pullback (yoneda.map (𝟙 T)) f.hom) :=
    hf.2.1 _ (isAlgebraicSpace_yoneda B integerBase ℤS T)
      (isQuasiCompact_yoneda_of_compact B integerBase ℤS T inferInstance) _
  have hcU : CompactSpace ((𝒯).obj U) := compactSpace_of_isQuasiCompactSpace_yoneda_obj B
    integerBase ℤS (IsQuasiCompactSpace.of_iso B integerBase ℤS hqcU hsq.flip.isoPullback.symm)
  have : IsIso p := hsq.isIso_fst_of_isIso (inferInstanceAs (IsIso (yoneda.map (𝟙 T))))
  have hlft : IsLocallyOfFiniteType B integerBase ℤS (yoneda.map q) := by
    have h := (holdsOnEveryEtaleChart_precomp_iso B integerBase ℤS _ (asIso p) f.hom).1
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase ℤS hf.1)
    have hw : p ≫ f.hom = yoneda.map q :=
      hsq.w.trans (Category.comp_id (yoneda.map q))
    rwa [asIso_hom, hw] at h
  have : LocallyOfFiniteType ((𝒯).map q) :=
    (isLocallyOfFiniteType_yoneda_map_iff B integerBase ℤS q).1 hlft
  obtain ⟨d₀, hd₀, h⟩ := Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple
    ((𝒯).map q) _ hamp
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ := h d₀ le_rfl
  obtain ⟨V₀, c₀, hV₀, hc₀, hc₀i⟩ := exists_isCompact_opens_isClosedImmersion_of_isImmersion i
  have hV : B.Contains V₀.toScheme :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion V₀.ι)
      (Space.contains_projectiveSpaceOver B _ T.left.property n)
  let V : BigFppfOver B integerBase ℤS := CurveFamily.ofScheme V₀.toScheme hV
  let c : U ⟶ V := CurveFamily.homOfScheme c₀
  let o : V ⟶ projectiveSite B n T := CurveFamily.homOfScheme V₀.ι
  have hco : (𝒯).map (c ≫ o) = i := ((𝒯).map_comp c o).trans hc₀i
  refine ⟨U, p, q, hsq, hinv, n, d₀, hd₀, V, c, o, hc₀,
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V₀.ι),
    isCompact_iff_compactSpace.1 hV₀,
    ?_, ⟨e ≪≫ (Scheme.Modules.pullbackCongr hco.symm).app _⟩⟩
  apply (𝒯).map_injective
  rw [← Category.assoc, Functor.map_comp, hco]
  exact hover

end AlgebraicGeometry.Space.QuotSituation

end
