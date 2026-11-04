module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SchemeBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# Extending a section over an open by a dominating admissible blowup, over a scheme

Let `Y` be an algebraic space over `S`, `U ⊆ Y` a quasi-compact open subspace, `f : X ⟶ Y` a proper
morphism and `s : U ⟶ X` a section of `f` over `U`. Say that `Y` *dominates sections* when for all
such data there is a `U`-admissible blowup `b : Y' ⟶ Y` and a morphism `g : Y' ⟶ X` with
`f ∘ g = b` which extends `s`, that is, agrees with `s ∘ b` on `b⁻¹(U)`. This is the conclusion of
Stacks 0CPI for `W = Y`, and it implies Stacks 087G: if `f` is an isomorphism over `U` it has the
section `f⁻¹` there.

This file proves that every algebraic space isomorphic to a quasi-compact quasi-separated scheme
dominates sections. Following the proof of Stacks 0CPI, `X` is replaced by the scheme-theoretic
image `X̃` of `s`, which is proper over `Y` and an isomorphism over `U` (Stacks 0CP3,
`AlgebraicGeometry.Space.isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section`); then
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_qcqs_scheme` (Stacks 087G over a
scheme) dominates `X̃`, and the domination extends `s` because two morphisms to `X̃` over `Y`
agree over `U`.

## Main definitions

* `AlgebraicGeometry.Space.DominatesSections`.

## Main results

* `AlgebraicGeometry.Space.IsAdmissibleBlowup.comp_inv`: admissible blowups transport along an
  isomorphism of the base.
* `AlgebraicGeometry.Space.dominatesSections_schemeSpace`: a quasi-compact quasi-separated scheme
  of the site dominates sections.
* `AlgebraicGeometry.Space.DominatesSections.of_iso`: so does any algebraic space isomorphic to
  it.

## References

* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An algebraic space `Y` **dominates sections** when, for every quasi-compact open subspace
`U ⊆ Y`, every proper morphism `f : X ⟶ Y` and every section `s : U ⟶ X` of `f` over `U`, there
are a `U`-admissible blowup `b : Y' ⟶ Y` and a morphism `g : Y' ⟶ X` with `g ≫ f = b` whose
restriction to `b⁻¹(U)` is `s` composed with the restriction of `b`. -/
def DominatesSections (Y : AlgebraicSpaces B S hS) : Prop :=
  ∀ (U : OpenSubspaces B S hS Y.1), IsQuasiCompactSpace B S hS U.1.toFunctor →
    ∀ (X : AlgebraicSpaces B S hS) (f : X ⟶ Y), IsProper B S hS f.hom →
      ∀ s : U.1.toFunctor ⟶ X.1, s ≫ f.hom = U.1.ι →
        ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y), IsAdmissibleBlowup B S hS U b ∧
          ∃ g : Y' ⟶ X, g ≫ f = b ∧
            (U.1.preimage b.hom).ι ≫ g.hom = U.1.fromPreimage b.hom ≫ s

/-- **Admissible blowups transport along an isomorphism of the base.** If `b : Y' ⟶ Y₂` is a
`U₂`-admissible blowup and `e : Y₁ ≅ Y₂`, then `b ≫ e⁻¹` is an `e⁻¹(U₂)`-admissible blowup
of `Y₁`. -/
theorem IsAdmissibleBlowup.comp_inv {Y₁ Y₂ Y' : AlgebraicSpaces B S hS} (e : Y₁ ≅ Y₂)
    (U₂ : OpenSubspaces B S hS Y₂.1) {b : Y' ⟶ Y₂} (hb : IsAdmissibleBlowup B S hS U₂ b) :
    IsAdmissibleBlowup B S hS
      ⟨U₂.1.preimage e.hom.hom, isOpenSubspace_preimage B S hS e.hom.hom U₂.1 Y₂.2 Y₁.2 U₂.2⟩
      (b ≫ e.inv) := by
  obtain ⟨Z, hZfp, hZdisj, hZb⟩ := hb
  have hsq : IsPullback (b ≫ e.inv) (𝟙 Y') e.hom b :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hflat : IsFlat B S hS e.hom.hom := by
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map e.hom))
    exact isFlat_of_isIso e.hom.hom Y₂.2
  refine ⟨preimageClosedSubspace e.hom Z, ?_, ?_,
    isBlowupAlong_preimage_of_isPullback_of_isFlat hflat hZb hsq⟩
  · exact isFinitePresentation_of_isPullback B S hS
      (preimageClosedSubspace e.hom Z).2.1 Z.2.1 Y₁.2 Y₂.2
      (Subfunctor.isPullback_preimage e.hom.hom Z.1) hZfp
  · show Disjoint (subspacePointSet B S hS Y₁.1 (U₂.1.preimage e.hom.hom))
      (subspacePointSet B S hS Y₁.1 (Z.1.preimage e.hom.hom))
    rw [subspacePointSet_preimage B S hS, subspacePointSet_preimage B S hS]
    exact hZdisj.preimage _

/-- **A scheme dominates sections over an open cut out by a quasi-compact open of the scheme.** -/
theorem dominatesSections_schemeSpace_aux (hZ : B.Contains (⊤_ Scheme.{u})) (R : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj R)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj R)]
    (U₀ : ((BigFppfOver.toScheme B S hS).obj R).Opens)
    (hU₀ : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj R)))
    (U : OpenSubspaces B S hS (schemeSpace R).1)
    (hUeq : U.1 = openSubspaceOfPoints B S hS (yoneda.obj R)
      (pointsToScheme B S hS R ⁻¹' (U₀ : Set _)))
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace R) (hf : IsProper B S hS f.hom)
    (s : U.1.toFunctor ⟶ X.1) (hs : s ≫ f.hom = U.1.ι) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ schemeSpace R), IsAdmissibleBlowup B S hS U b ∧
      ∃ g : Y' ⟶ X, g ≫ f = b ∧
        (U.1.preimage b.hom).ι ≫ g.hom = U.1.fromPreimage b.hom ≫ s := by
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R
  have hUι : IsQuasiCompact B S hS U.1.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hQ
      (isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ R inferInstance) hUqc U.1.ι
  have hXtcl : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS s) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS s X.2
  have hiso : IsIso (pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom) U.1.ι) :=
    isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS X.2 hQ f.hom hf.1
      U.1 U.2 hUι s hs
  have hft : IsProper B S hS ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom) :=
    isProper_comp B S hS hXtcl.1 X.2 hQ _ _ (isProper_of_isClosedImmersion B S hS hXtcl.1 X.2 _
      hXtcl.2) hf
  have hiso' : IsIso (pullback.snd (Over.mk ((schemeTheoreticImageSubfunctor B S hS s).ι ≫
      f.hom)).hom (openSubspaceOfPoints B S hS (yoneda.obj R)
        (pointsToScheme B S hS R ⁻¹' (U₀ : Set _))).ι) := by
    rwa [← hUeq]
  obtain ⟨Y', b, hb, -, -, g, hg⟩ :=
    exists_isAdmissibleBlowup_dominating_of_qcqs_scheme R U₀ hU₀
      (Over.mk ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom)) hXtcl.1 hiso' hft
  have hUU : U = ⟨openSubspaceOfPoints B S hS (yoneda.obj R)
      (pointsToScheme B S hS R ⁻¹' (U₀ : Set _)),
        isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme R U₀⟩ := Subtype.ext hUeq
  refine ⟨Y', b, hUU ▸ hb, ObjectProperty.homMk (g ≫ (schemeTheoreticImageSubfunctor B S hS s).ι),
    ?_, ?_⟩
  · refine ObjectProperty.hom_ext _ ?_
    show (g ≫ (schemeTheoreticImageSubfunctor B S hS s).ι) ≫ f.hom = b.hom
    exact (Category.assoc _ _ _).trans hg
  · let st : U.1.toFunctor ⟶ (schemeTheoreticImageSubfunctor B S hS s).toFunctor :=
      Subfunctor.lift s (range_le_schemeTheoreticImageSubfunctor B S hS s)
    have hst : st ≫ (schemeTheoreticImageSubfunctor B S hS s).ι = s := Subfunctor.lift_ι _ _
    have h := eq_of_comp_eq_of_isIso_pullback_snd
      ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f.hom) U.1
      (p := (U.1.preimage b.hom).ι ≫ g) (q := U.1.fromPreimage b.hom ≫ st) (U.1.fromPreimage b.hom)
      (by
        rw [Category.assoc]
        show (U.1.preimage b.hom).ι ≫ g ≫ (Over.mk ((schemeTheoreticImageSubfunctor B S hS s).ι ≫
          f.hom)).hom = _
        exact (congrArg ((U.1.preimage b.hom).ι ≫ ·) hg).trans
          (Subfunctor.fromPreimage_ι _ _).symm)
      (by rw [Category.assoc, ← Category.assoc st, hst, hs])
    show (U.1.preimage b.hom).ι ≫ g ≫ (schemeTheoreticImageSubfunctor B S hS s).ι = _
    rw [← Category.assoc, h, Category.assoc, hst]

/-- **A quasi-compact quasi-separated scheme of the site dominates sections.** -/
theorem dominatesSections_schemeSpace (hZ : B.Contains (⊤_ Scheme.{u})) (R : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj R)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj R)] :
    DominatesSections (schemeSpace R) := by
  intro U hUqc X f hf s hs
  have hAc : IsCompact (Set.range (pointsMap B S hS U.1.toFunctor U.1.ι)) := by
    have := compactSpace_points_of_isQuasiCompactSpace B S hS U.2.1 hUqc
    exact isCompact_range (continuous_pointsMap B S hS U.1.ι)
  let U₀ : ((BigFppfOver.toScheme B S hS).obj R).Opens :=
    ⟨schemePointsHomeomorph B S hS R '' Set.range (pointsMap B S hS U.1.toFunctor U.1.ι),
      (schemePointsHomeomorph B S hS R).isOpenMap _
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS U.1.ι U.2.2)⟩
  have hU₀c : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj R)) :=
    hAc.image (schemePointsHomeomorph B S hS R).continuous
  have hUeq : U.1 = openSubspaceOfPoints B S hS (yoneda.obj R)
      (pointsToScheme B S hS R ⁻¹' (U₀ : Set _)) := by
    rw [show pointsToScheme B S hS R ⁻¹' (U₀ : Set _) = _ from
      (schemePointsHomeomorph B S hS R).preimage_image _]
    exact eq_openSubspaceOfPoints_range_pointsMap B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R) U.1 U.2
  exact dominatesSections_schemeSpace_aux hZ R U₀ hU₀c U hUeq hUqc X f hf s hs

/-- **Dominating sections transports along an isomorphism of algebraic spaces.** -/
theorem DominatesSections.of_iso {Y₁ Y₂ : AlgebraicSpaces B S hS} (e : Y₁ ≅ Y₂)
    (h : DominatesSections Y₂) : DominatesSections Y₁ := by
  intro U hUqc X f hf s hs
  have hinv : e.inv.hom ≫ e.hom.hom = 𝟙 Y₂.1 := congrArg (fun m => m.hom) e.inv_hom_id
  have hhom : e.hom.hom ≫ e.inv.hom = 𝟙 Y₁.1 := congrArg (fun m => m.hom) e.hom_inv_id
  have : IsIso e.inv.hom := ⟨e.hom.hom, hinv, hhom⟩
  have : IsIso e.hom.hom := ⟨e.inv.hom, hhom, hinv⟩
  let U' : OpenSubspaces B S hS Y₂.1 :=
    ⟨U.1.preimage e.inv.hom, isOpenSubspace_preimage B S hS e.inv.hom U.1 Y₁.2 Y₂.2 U.2⟩
  have : IsIso (U.1.fromPreimage e.inv.hom) :=
    (Subfunctor.isPullback_preimage e.inv.hom U.1).isIso_fst_of_isIso
  have hU'qc : IsQuasiCompactSpace B S hS U'.1.toFunctor :=
    IsQuasiCompactSpace.of_iso B S hS hUqc (asIso (U.1.fromPreimage e.inv.hom)).symm
  have hf' : IsProper B S hS (f ≫ e.hom).hom :=
    isProper_comp B S hS X.2 Y₁.2 Y₂.2 _ _ hf (isProper_of_isIso B S hS e.hom.hom)
  have hs' : (U.1.fromPreimage e.inv.hom ≫ s) ≫ (f ≫ e.hom).hom = U'.1.ι := by
    show (U.1.fromPreimage e.inv.hom ≫ s) ≫ f.hom ≫ e.hom.hom = U'.1.ι
    rw [Category.assoc, ← Category.assoc s, hs, ← Category.assoc, Subfunctor.fromPreimage_ι,
      Category.assoc, hinv, Category.comp_id]
  obtain ⟨Y', b, hb, g, hg, hext⟩ := h U' hU'qc X (f ≫ e.hom) hf' _ hs'
  have hUU : (⟨U'.1.preimage e.hom.hom,
      isOpenSubspace_preimage B S hS e.hom.hom U'.1 Y₂.2 Y₁.2 U'.2⟩ : OpenSubspaces B S hS Y₁.1) =
      U := by
    refine Subtype.ext ?_
    show (U.1.preimage e.inv.hom).preimage e.hom.hom = U.1
    rw [← Subfunctor.preimage_comp, hhom, Subfunctor.preimage_id]
  refine ⟨Y', b ≫ e.inv, hUU ▸ IsAdmissibleBlowup.comp_inv e U' hb, g, ?_, hext⟩
  rw [← hg, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Space

end
