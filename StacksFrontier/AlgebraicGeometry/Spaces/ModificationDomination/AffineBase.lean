module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.LocalRing
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic

/-!
# A proper modification of a Noetherian affine scheme is dominated by a scheme blowup

Let `V` be an object of the big fppf site over `S` whose underlying scheme is affine and
Noetherian, let `W` be an open of that scheme and let `f : Y ⟶ h_V` be a proper morphism of
algebraic spaces which is an isomorphism over the open subspace of `h_V` given by `W`. Then there
is a finitely presented quasi-coherent sheaf of ideals `K` on `V` cutting out exactly `V ∖ W`
such that the scheme blowup `Bl_K V ⟶ V`, read as a morphism of algebraic spaces, factors
through `f`. This is Stacks 087G over such a base, with the dominating `W`-admissible blowup
named as a blowup of schemes.

The blowup `Bl_K V ⟶ V` is proper, it is an isomorphism over `W` (whose inverse image is the
complement of the exceptional divisor, so scheme-theoretically dense and dense), and it is
birational as soon as `W` is dense in `V`.

## Main results

* `AlgebraicGeometry.Space.exists_supportSet_eq_compl_blowUpObj_dominating`: the centre `K`,
  with support `V ∖ W`, and the factorisation of `Bl_K V ⟶ V` through `f`.
* `AlgebraicGeometry.Space.exists_isProper_isIso_morphismRestrict_dominating`: a site object `P`
  over `V`, proper over `V`, an isomorphism over `W`, with `W` pulling back to a
  scheme-theoretically dense (hence dense) open, birational over `V` when `W` is dense, and
  whose algebraic space dominates `Y` over `h_V`.

## References

* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 0GUW](https://stacks.math.columbia.edu/tag/0GUW)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 087G over a Noetherian affine scheme, with the centre named.** Let `V` be an object
of the site whose underlying scheme is affine and Noetherian, let `W` be an open of it and let
`f : Y ⟶ h_V` be a proper morphism of algebraic spaces which is an isomorphism over the open
subspace of the points over `W`. Then there is a finitely presented centre `K` on `V` with
support `V ∖ W` such that the blowup `Bl_K V ⟶ V` factors through `f`. -/
theorem exists_supportSet_eq_compl_blowUpObj_dominating (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (hiso : IsIso (pullback.snd f.hom (openSubspaceOfPoints B S hS (yoneda.obj V)
      (pointsToScheme B S hS V ⁻¹' (W : Set _))).ι)) :
    ∃ K : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData,
      FinitePresentation K.subschemeι ∧ K.supportSet = (W : Set _)ᶜ ∧
        ∃ h : schemeSpace (blowUpObj V K) ⟶ Y, h ≫ f = schemeSpaceMap (blowUpObjHom V K) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.obj ⟶ yoneda.obj V, φ = f.hom := ⟨_, rfl⟩
  have : IsIso (pullback.snd φ (openSubspaceOfPoints B S hS (yoneda.obj V)
      (pointsToScheme B S hS V ⁻¹' (W : Set _))).ι) := hφ ▸ hiso
  have hφp : IsProper B S hS φ := hφ ▸ hf
  obtain ⟨U, hUdef⟩ : ∃ U : Subfunctor (yoneda.obj V),
      U = openSubspaceOfPoints B S hS (yoneda.obj V) (pointsToScheme B S hS V ⁻¹' (W : Set _)) :=
    ⟨_, rfl⟩
  have hU : IsOpenSubspace B S hS U :=
    hUdef ▸ isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme V W
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V
  have hX : IsAlgebraicSpace B S hS Y.obj := Y.property
  have hqcX : IsQuasiCompactSpace B S hS Y.obj :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS V inferInstance hX hQ φ
      hφp.2.2
  obtain ⟨C, u, hCaff, husp, hue⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.obj hX).1 hqcX
  have hus : IsSurjective B S hS u :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y.obj hX C u).1 husp
  obtain ⟨g, hg⟩ : ∃ g : C ⟶ V, u ≫ φ = yoneda.map g :=
    ⟨yoneda.preimage (u ≫ φ), (yoneda.map_preimage _).symm⟩
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := by
    refine (isLocallyOfFiniteType_yoneda_map_iff B S hS g).1 ?_
    rw [← hg]
    exact isLocallyOfFiniteType_comp' B S hS u φ hX hQ
      (isLocallyOfFiniteType_of_isEtale' B S hS u hue) hφp.2.1.1
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj C) := inferInstance
  have : Flat ((BigFppfOver.toScheme B S hS).map g ∣_ W) :=
    flat_morphismRestrict_of_isEtale W φ u hue g hg
  obtain ⟨K, hKfp, hKsupp, hKflat⟩ :=
    exists_supportSet_eq_compl_flat_strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g)
      W (TopologicalSpace.NoetherianSpace.isCompact _)
  refine ⟨K, hKfp, hKsupp, ?_⟩
  have hbl := isBlowupAlong_schemeSpaceMap_blowUpObjHom V K hKfp
  have hZpts : subspacePointSet B S hS (yoneda.obj V) (closedSubspaceOfIdeal V K).1 =
      (subspacePointSet B S hS (yoneda.obj V) U)ᶜ := by
    rw [hUdef, subspacePointSet_closedSubspaceOfIdeal, subspacePointSet,
      range_pointsMap_ι_openSubspaceOfPoints, ← Set.preimage_compl]
    congr 1
  have hP := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (blowUpObj V K)
  have hdense : IsSchemeTheoreticallyDense B S hS
      (U.preimage (yoneda.map (blowUpObjHom V K))) :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong (X := schemeSpace V) ⟨U, hU⟩
      (closedSubspaceOfIdeal V K) hbl hZpts
  have hUqc : IsQuasiCompact B S hS U.ι := by
    have hUr : U = Subfunctor.range (yoneda.map (openSubHom V W)) :=
      hUdef.trans (openSubspaceOfPoints_preimage_pointsToScheme V W)
    have : Mono (yoneda.map (openSubHom V W)) := by
      have : Mono (openSubHom V W) := (BigFppfOver.toScheme B S hS).mono_of_mono_map (by
        rw [toScheme_map_openSubHom B S hS]
        exact inferInstanceAs (Mono W.ι))
      exact Functor.map_mono yoneda _
    have hι : (Subfunctor.range (yoneda.map (openSubHom V W))).ι =
        inv (Subfunctor.toRange (yoneda.map (openSubHom V W))) ≫ yoneda.map (openSubHom V W) :=
      (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι _).symm
    rw [hUr, hι]
    refine isQuasiCompact_isIso_comp B S hS _
      (Space.isQuasiCompact_yoneda_map_of_quasiCompact B S hS _ ?_)
    rw [toScheme_map_openSubHom B S hS]
    exact inferInstanceAs (QuasiCompact W.ι)
  have hqc : IsQuasiCompact B S hS (U.preimage (yoneda.map (blowUpObjHom V K))).ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage _ _) hUqc
  subst hUdef
  obtain ⟨h, hh⟩ := exists_comp_eq_of_isFlat hQ hP hX φ hφp _ hU _ hqc hdense
    (isFlat_modificationSection_of_flat_strictTransformToBlowUp W hX φ u hue hus g hg K
      hKsupp hKflat hqc)
  subst hφ
  exact ⟨ObjectProperty.homMk h, ObjectProperty.hom_ext _ hh⟩

/-- **A proper modification of an algebraic space over a Noetherian affine scheme is dominated by
a proper modification of the scheme.** Let `V` be an object of the site whose underlying scheme
is affine and Noetherian, let `W` be an open of it and let `f : Y ⟶ h_V` be a proper morphism of
algebraic spaces which is an isomorphism over the open subspace of the points over `W`. Then
there are a site object `P` and a morphism `q : P ⟶ V` such that `h_q` factors through `f`, the
morphism of schemes underlying `q` is proper and an isomorphism over `W`, the inverse image of
`W` is scheme-theoretically dense and dense, and `q` is birational when `W` is dense in `V`.

In fact `q` is the blowup of `V` in a finitely presented centre with support `V ∖ W`, by
`AlgebraicGeometry.Space.exists_supportSet_eq_compl_blowUpObj_dominating`. -/
theorem exists_isProper_isIso_morphismRestrict_dominating (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (hiso : IsIso (pullback.snd f.hom (openSubspaceOfPoints B S hS (yoneda.obj V)
      (pointsToScheme B S hS V ⁻¹' (W : Set _))).ι)) :
    ∃ (P : BigFppfOver B S hS) (q : P ⟶ V) (h : schemeSpace P ⟶ Y),
      h ≫ f = schemeSpaceMap q ∧
        AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q) ∧
        IsIso ((BigFppfOver.toScheme B S hS).map q ∣_ W) ∧
        Scheme.Opens.IsSchemeTheoreticallyDense ((BigFppfOver.toScheme B S hS).map q ⁻¹ᵁ W) ∧
        Dense (((BigFppfOver.toScheme B S hS).map q ⁻¹ᵁ W :
          ((BigFppfOver.toScheme B S hS).obj P).Opens) :
            Set ((BigFppfOver.toScheme B S hS).obj P)) ∧
        (Dense (W : Set ((BigFppfOver.toScheme B S hS).obj V)) →
          IsBirational ((BigFppfOver.toScheme B S hS).map q)) := by
  obtain ⟨K, -, hK, h, hh⟩ := exists_supportSet_eq_compl_blowUpObj_dominating V W f hf hiso
  have hmap : (BigFppfOver.toScheme B S hS).map (blowUpObjHom V K) =
      _root_.AlgebraicGeometry.blowUpToBase K :=
    toScheme_map_blowUpObjHom V K
  have hpre := _root_.AlgebraicGeometry.preimage_eq_compl_support_exceptionalIdeal K W hK
  have hstd : Scheme.Opens.IsSchemeTheoreticallyDense
      (_root_.AlgebraicGeometry.blowUpToBase K ⁻¹ᵁ W) := by
    rw [hpre]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
      (_root_.AlgebraicGeometry.exceptionalIdeal K) inferInstance
  have hWsub : (W : Set ((BigFppfOver.toScheme B S hS).obj V)) ⊆
      (K.support : Set ((BigFppfOver.toScheme B S hS).obj V))ᶜ := by
    change (W : Set ((BigFppfOver.toScheme B S hS).obj V)) ⊆ K.supportSetᶜ
    rw [hK, compl_compl]
  have hWiso := _root_.AlgebraicGeometry.isIso_blowUpToBase_restrict_of_subset_compl_support K W
    hWsub
  refine ⟨blowUpObj V K, blowUpObjHom V K, h, hh, ?_⟩
  rw [hmap]
  refine ⟨_root_.AlgebraicGeometry.isProper_blowUpToBase K, hWiso, hstd,
    _root_.AlgebraicGeometry.dense_of_isSchemeTheoreticallyDense _ hstd, fun hWd => ?_⟩
  refine isBirational_of_isIso_morphismRestrict _ W hWiso (fun x hx => ?_)
    (fun y hy => _root_.AlgebraicGeometry.genericPoints_mem_of_dense W hWd ⟨y, hy⟩)
  have h1 := (_root_.AlgebraicGeometry.bijOn_genericPoints_blowUpToBase K).mapsTo hx
  have h2 : _root_.AlgebraicGeometry.blowUpToBase K x ∉ K.supportSet := h1.2
  rw [hK] at h2
  exact not_not.mp h2

end AlgebraicGeometry.Space

end
