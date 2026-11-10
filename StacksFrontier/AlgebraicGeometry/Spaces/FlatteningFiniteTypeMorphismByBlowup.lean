module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineOverBaseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective

/-!
# Flattening a morphism of finite type by blowing up

Let `S` be a scheme, let `f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A`
be an open subspace.  Assume that `A` is quasi-compact and quasi-separated, that `U` is
quasi-compact, that `f` is of finite type and quasi-separated and that `f⁻¹(U) ⟶ U` is flat and
locally of finite presentation.  Then there is a `U`-admissible blowup `A' ⟶ A` such that the
strict transform of `X` is flat and of finite presentation over `A'`.  This is the content of
Stacks 087E.

## Main results

* `exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp_of_isFiniteType`:
  a `U`-admissible blowup flattens a quasi-separated morphism of finite type.

## Implementation notes

The statement is deduced from
`exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`, whose two
hypotheses are Stacks 07VR, which is
`exists_integralFiniteSystem_isClosedImmersion_of_isFinite`, and an embedding of an affine étale
chart `V` of `X` as a closed subspace of an algebraic space of finite presentation over `A`. The
chart `V` is chosen étale over `X ×_A W` for an affine étale chart `W ⟶ A`; then `V ⟶ A` is the
composite of the morphism `V ⟶ W` of affine schemes, which is affine, and of `W ⟶ A`, which is
étale, quasi-compact (the base being quasi-separated) and separated (its source being a scheme),
hence quasi-finite and separated, hence quasi-affine (Stacks 082J). So `V ⟶ A` is quasi-affine
(Stacks 03WN) and locally of finite type, and Stacks 0871, which is
`exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_qcqs`, gives the
embedding.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0871](https://stacks.math.columbia.edu/tag/0871)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flattening a morphism of finite type by blowing up (the content of Stacks 087E).**  Let
`f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open subspace.
Assume that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is of
finite type and quasi-separated, and that `f⁻¹(U) ⟶ U` (read on `X ×_A U ⟶ U`) is flat and
locally of finite presentation.  Then there is a `U`-admissible blowup `b : A' ⟶ A`, with
finitely presented centre `Z` whose points avoid those of `U`, such that the strict transform of
`X` is flat and of finite presentation over `A'`.

See the module documentation for the argument. -/
theorem
    exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp_of_isFiniteType
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {A X : AlgebraicSpaces B S hS} (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hft : IsFiniteType B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (hflat : IsFlat B S hS (pullback.snd f.hom U.1.ι))
    (hlfp : IsLocallyOfFinitePresentation B S hS (pullback.snd f.hom U.1.ι)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom ∧
              IsFinitePresentation B S hS
                (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom := by
  -- an affine étale chart `w : W ⟶ A` and an affine étale chart `v : V ⟶ X ×_A W`
  obtain ⟨W₀, w, hW₀, hws, hwe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS A.1 A.2).1 hAqc
  have hWqc : IsQuasiCompactSpace B S hS (yoneda.obj W₀) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS W₀ hW₀
  have hWsp : IsAlgebraicSpace B S hS (yoneda.obj W₀) := isAlgebraicSpace_yoneda B S hS W₀
  have hXW : IsAlgebraicSpace B S hS (pullback f.hom w) :=
    isAlgebraicSpace_pullback B S hS f.hom w X.2 hWsp A.2
  have hXWqc : IsQuasiCompactSpace B S hS (pullback f.hom w) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hWsp hWqc
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f.hom w) hft.2)
  obtain ⟨V₀, v, hV₀, hvs, hve⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hXW).1 hXWqc
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V₀) := isAlgebraicSpace_yoneda B S hS V₀
  -- `a : V ⟶ X` is surjective and étale
  let a : yoneda.obj V₀ ⟶ X.1 := v ≫ pullback.fst f.hom w
  have hae : IsEtale B S hS a :=
    isEtale_comp B S hS hve (isEtale_pullback_fst B S hS X.2 A.2 hWsp f.hom w hwe)
  have has : IsSurjective B S hS a :=
    isSurjective_comp B S hS ((presheafSurjective_iff_isSurjective_yoneda B S hS _ hXW V₀ v).1 hvs)
      (isSurjective_pullback_fst B S hS X.2 A.2 hWsp f.hom w
        ((presheafSurjective_iff_isSurjective_yoneda B S hS A.1 A.2 W₀ w).1 hws))
  -- `V ⟶ A` is locally of finite type and quasi-affine: it is `V ⟶ W ⟶ A`, with `V ⟶ W` a
  -- morphism of affine schemes and `W ⟶ A` quasi-finite and separated (Stacks 082J)
  have hvlft : IsLocallyOfFiniteType B S hS (a ≫ f.hom) :=
    isLocallyOfFiniteType_comp B S hS hV X.2 A.2 a f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (isLocallyOfFinitePresentation_of_isEtale B S hS hae)) hft.1
  have hwqa : IsQuasiAffineHom B S hS w := by
    have := hW₀
    exact isQuasiAffineHom_of_isQuasiFinite_isSeparated hWsp A.2
      ⟨isLocallyQuasiFinite_of_isEtale B S hS A.2 hwe,
        isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hWqc w⟩
      (isSeparated_of_scheme_isSeparated B S hS inferInstance w)
  have hvqa : IsQuasiAffineHom B S hS (v ≫ pullback.snd f.hom w) :=
    isQuasiAffineHom_of_isAffineHom
      (isAffineHom_of_isAffineSpace_source B S hS (isAffineSpace_yoneda B S hS V₀ hV₀) hW₀ _)
  have hqa : IsQuasiAffineHom B S hS (a ≫ f.hom) := by
    have h := IsQuasiAffineHom.comp hV hWsp A.2 hvqa hwqa
    rwa [Category.assoc, ← pullback.condition, ← Category.assoc] at h
  -- Stacks 0871: a closed immersion `i : V ⟶ Y` with `Y ⟶ A` of finite presentation
  obtain ⟨Y₀, g₀, i, hY₀, hgfp, hi, hig⟩ :=
    exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_qcqs B S hS (a ≫ f.hom)
      hV A.2 hvlft hqa hAqc hAqs
  let Y : AlgebraicSpaces B S hS := ⟨Y₀, hY₀⟩
  let g : Y ⟶ A := ObjectProperty.homMk g₀
  -- the image `W ⊆ Y` of `i`, isomorphic to `V`
  let W : ClosedSubspaces B S hS Y₀ :=
    ⟨Subfunctor.range i, isClosedSubspace_range_of_isClosedImmersion B S hS i hV hi⟩
  have : Mono i := mono_of_isClosedImmersion B S hS i hi
  let e : yoneda.obj V₀ ≅ W.1.toFunctor := asIso (Subfunctor.toRange i)
  have he : e.inv ≫ i = W.1.ι := by
    rw [Iso.inv_comp_eq]
    exact (Subfunctor.toRange_ι i).symm
  let u : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk (e.inv ≫ a)
  have hue : IsEtale B S hS u.hom := isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv) hae
  have hus : IsSurjective B S hS u.hom :=
    isSurjective_comp B S hS (isSurjective_of_isIso B S hS e.inv)
      has
  have hcomm : u ≫ f = subspaceInclusion B S hS Y W ≫ g := by
    refine ObjectProperty.hom_ext _ ?_
    change (e.inv ≫ a) ≫ f.hom = W.1.ι ≫ g₀
    rw [Category.assoc, ← hig, ← Category.assoc, he]
  -- `W_U ⟶ U` is flat and locally of finite presentation: it is étale over `X_U ⟶ U`
  have hWU := (preimageClosedSubspace (restrictOverι g U) W).2.1
  have hsqg := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g U.toSpaceι)
  have hu : u.hom ≫ f.hom = W.1.ι ≫ g.hom := congrArg (fun k => k.hom) hcomm
  have hXU : IsAlgebraicSpace B S hS (pullback f.hom U.1.ι) :=
    isAlgebraicSpace_pullback B S hS f.hom U.1.ι X.2 U.2.1 A.2
  let t : (W.1.preimage (restrictOverι g U).hom).toFunctor ⟶ pullback f.hom U.1.ι :=
    pullback.lift (W.1.fromPreimage (restrictOverι g U).hom ≫ u.hom)
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) (by
        rw [Category.assoc, hu, ← Category.assoc,
          Subfunctor.fromPreimage_ι W.1 (restrictOverι g U).hom, Category.assoc, hsqg.w,
          Category.assoc]
        rfl)
  have ht_snd : t ≫ pullback.snd f.hom U.1.ι =
      (W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom :=
    pullback.lift_snd _ _ _
  have hsqt : IsPullback t (W.1.fromPreimage (restrictOverι g U).hom)
      (pullback.fst f.hom U.1.ι) u.hom := by
    have houter : IsPullback (t ≫ pullback.snd f.hom U.1.ι)
        (W.1.fromPreimage (restrictOverι g U).hom) U.1.ι (u.hom ≫ f.hom) := by
      rw [ht_snd, hu]
      exact (Subfunctor.isPullback_preimage (restrictOverι g U).hom W.1).flip.paste_horiz
        hsqg.flip
    exact IsPullback.of_right houter (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback f.hom U.1.ι).flip
  have ht : IsEtale B S hS t :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsqt hWU hXU W.2.1 X.2 hue
  have hWflat :
      IsFlat B S hS ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) := by
    rw [← ht_snd]
    exact isFlat_comp B S hS hWU hXU U.2.1 _ _ (isFlat_of_isEtale B S hS ht) hflat
  have hWlfp : IsLocallyOfFinitePresentation B S hS
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) := by
    rw [← ht_snd]
    exact isLocallyOfFinitePresentation_comp B S hS hWU hXU U.2.1 _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS ht) hlfp
  -- the case of the closed subspace `W ⊆ Y`
  obtain ⟨A', b, Z, hZfp, hUZ, hb, hW'flat, hW'lfp⟩ :=
    exists_isBlowupAlong_isFlat_strictTransformSpaceToBlowUp_of_closedSubspace hZ
      (fun φ hX hY hf hqc hqs => exists_integralFiniteSystem_isClosedImmersion_of_isFinite φ hX hY
        hf hqc hqs)
      g hgfp hAqc hAqs U hUqc W hWflat hWlfp
  rw [← hcomm] at hW'flat hW'lfp
  -- Stacks 0863, part (2): the strict transform of `X` is flat and locally of finite presentation
  obtain ⟨hXflat, hXlfp⟩ :=
    isFlat_and_isLocallyOfFinitePresentation_strictTransformSpaceToBlowUp_of_comp hb f u hue hus
      hW'flat hW'lfp
  -- the strict transform is closed in `X ×_A A'`, which is quasi-compact and quasi-separated
  -- over `A'`
  have hcl := strictTransformSubfunctor_isClosedSubspace B S hS f b (Z.1.preimage b.hom)
  have hsqb := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  refine ⟨A', b, Z, hZfp, hUZ, hb, hXflat, hXlfp, ?_, ?_⟩
  · exact isQuasiCompact_comp B S hS (strictTransformPullback B S hS f b).2 A'.2 _ _
      (isQuasiCompact_of_isClosedImmersion' B S hS hcl.2)
      (isQuasiCompact_of_isPullback B S hS hsqb hft.2)
  · exact isQuasiSeparated_comp B S hS hcl.1 (strictTransformPullback B S hS f b).2 _ _
      (isQuasiSeparated_of_isClosedImmersion B S hS hcl.2)
      (isQuasiSeparated_of_isPullback B S hS hsqb hqs)

end AlgebraicGeometry.Space

end
