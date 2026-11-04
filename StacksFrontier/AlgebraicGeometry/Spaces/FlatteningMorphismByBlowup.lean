module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyStructureSheafDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafPushforwardDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningByBlowupAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceFlatEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# Flattening a morphism by blowing up

Let `S` be a scheme, let `f : X ⟶ B` be a morphism of algebraic spaces over `S` and let `U ⊆ B`
be an open subspace.  Assume that `B` is quasi-compact and quasi-separated, that `U` is
quasi-compact, that `f` is of finite type and quasi-separated and that `f⁻¹(U) ⟶ U` is flat and
locally of finite presentation.  Then there is a `U`-admissible blowup `B' ⟶ B` such that the
strict transform `X'` of `X` is flat and of finite presentation over `B'`.  This is
[Stacks, Tag 087E].

The proof is the source's.  The strict transform of `X` is a closed subspace of `X ×_B B'`, so it
is quasi-compact and quasi-separated over `B'`, and only flatness and local finite presentation
need an argument.  Choose an affine scheme `V` with a surjective étale morphism `V ⟶ X`; the
strict transform commutes with étale localization (Stacks 0863, part (2)), so it suffices to
treat `V ⟶ B`, which is separated and of finite type.  Then `V` is a closed subspace of an
algebraic space `Y` separated and of finite presentation over `B` (Stacks 0873).  Flattening by
blowing up (Stacks 087C), applied to `i_*𝒪_V` on `Y/B`, gives a `U`-admissible blowup over which
the strict transform of `i_*𝒪_V` is flat and of finite presentation.  The strict transform of
`i_*𝒪_V` is `i'_*𝒪_{V'}`, where `V'` is the strict transform of `V` and `i' : V' ⟶ Y ×_B B'` the
induced closed immersion (Stacks 0866, together with the identification of the strict transform
of `𝒪_V` with `𝒪_{V'}`), and flatness and finite presentation of `i'_*𝒪_{V'}` are flatness and
local finite presentation of `V' ⟶ B'`.

## Main results

* `nonempty_modulePullback_restrictOverι_pushforwardStructureSheaf_iso`:
  the restriction of `i_*𝒪_W` over an open subspace of the base is `i_*𝒪_{W_U}`.
* `exists_isBlowupAlong_isFlat_strictTransformSpaceToBlowUp_of_closedSubspace`:
  the case of a closed subspace of an algebraic space of finite presentation over the base.
* `exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp`:
  Stacks 087E, over Stacks 0873 and the held inputs of Stacks 087C (Stacks 07VR).

## Implementation notes

The base is written `A` in the statements, `B` naming the big fppf site.  A `U`-admissible
blowup is the blowup in a finitely presented closed subspace `Z` whose points avoid those of `U`;
the strict transform depends on the centre, so the conclusion names `Z`.
Quasi-separatedness of `B` is absolute quasi-separatedness, and the hypothesis on `f⁻¹(U) ⟶ U`
is read on the fibre product `X ×_B U ⟶ U`.

The closed immersion `V ⟶ Y` of Stacks 0873 is replaced by the inclusion of its image, a closed
subspace `W ⊆ Y` isomorphic to `V`, so that the direct image `i_*𝒪_W` is the quotient of `𝒪_Y`
by the defining ideal sheaf of a closed subspace.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0866](https://stacks.math.columbia.edu/tag/0866)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The restriction of `i_*𝒪_W` over an open subspace of the base.**  For `g : Y ⟶ A`, an open
subspace `U ⊆ A` and a closed subspace `W ⊆ Y`, the pullback of `i_*𝒪_W` to `Y_U = Y ×_A U` is
`i_*𝒪_{W_U}` for the closed subspace `W_U = W ×_Y Y_U` of `Y_U`.  This is affine base change
(the base-change clause of Stacks 07U8) along the inclusion of `W`, which is affine. -/
theorem nonempty_modulePullback_restrictOverι_pushforwardStructureSheaf_iso
    {A Y : AlgebraicSpaces B S hS} (g : Y ⟶ A) (U : OpenSubspaces B S hS A.1)
    (W : ClosedSubspaces B S hS Y.1) :
    Nonempty ((modulePullback B S hS (restrictOverι g U)).obj
        (pushforwardStructureSheaf B S hS Y W) ≅
      pushforwardStructureSheaf B S hS (restrictOver g U)
        (preimageClosedSubspace (restrictOverι g U) W)) := by
  let W' := preimageClosedSubspace (restrictOverι g U) W
  let gW : (⟨W'.1.toFunctor, W'.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W.1.toFunctor, W.2.1⟩ :=
    ObjectProperty.homMk (W.1.fromPreimage (restrictOverι g U).hom)
  have sq : IsPullback gW (subspaceInclusion B S hS (restrictOver g U) W')
      (subspaceInclusion B S hS Y W) (restrictOverι g U) :=
    IsPullback.of_map (ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι W.1 (restrictOverι g U).hom))
      (Subfunctor.isPullback_preimage (restrictOverι g U).hom W.1)
  have h1 := isIso_moduleBaseChangeMap_app_of_isAffineHom sq
    (isAffineHom_of_isClosedImmersion B S hS _ W.2.2)
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨W.1.toFunctor, W.2.1⟩))
    (SheafOfModules.isQuasicoherentOnSite_unit _)
  let e₁ := @asIso _ _ _ _ _ h1
  let e₂ := (modulePushforward B S hS (subspaceInclusion B S hS (restrictOver g U) W')).mapIso
    (modulePullbackUnitIso B S hS gW)
  exact ⟨e₁ ≪≫ e₂⟩

/-- The second projection of a fibre product is locally of finite presentation if the first
morphism is. -/
private theorem isLocallyOfFinitePresentation_snd_fiberProduct {A Y C : AlgebraicSpaces B S hS}
    (g : Y ⟶ A) (c : C ⟶ A) (hg : IsLocallyOfFinitePresentation B S hS g.hom) :
    IsLocallyOfFinitePresentation B S hS (pullback.snd g.hom c.hom) :=
  (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g c) hg

/-- **Stacks 087E for a closed subspace of an algebraic space of finite presentation over the
base, over the held inputs of Stacks 087C (`h07VR`).**  Let `A` be a quasi-compact
and quasi-separated algebraic space, let `U ⊆ A` be a quasi-compact open subspace, let
`g : Y ⟶ A` be of finite presentation and let `W ⊆ Y` be a closed subspace such that
`W_U ⟶ U` is flat and locally of finite presentation.  Then there is a `U`-admissible blowup
`b : A' ⟶ A`, with centre `Z`, such that the strict transform of `W` is flat and locally of
finite presentation over `A'`.

Flattening by blowing up (Stacks 087C) applied to `i_*𝒪_W` on `Y/A` gives the blowup; by Stacks
0866 (`AlgebraicGeometry.Space.exists_modulePushforward_strictTransformSheaf_iso_unconditional`)
and `AlgebraicGeometry.Space.nonempty_strictTransformSheaf_unit_iso` the strict
transform of `i_*𝒪_W` is `k_*𝒪_{W'}` for the closed immersion `k : W' ⟶ Y ×_A A'` of the strict
transform `W'` of `W`; and flatness and finite presentation of `k_*𝒪_{W'}` are flatness and local
finite presentation of `W' ⟶ A'`. -/
theorem exists_isBlowupAlong_isFlat_strictTransformSpaceToBlowUp_of_closedSubspace
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {A Y : AlgebraicSpaces B S hS} (g : Y ⟶ A) (hg : IsFinitePresentation B S hS g.hom)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (U : OpenSubspaces B S hS A.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (W : ClosedSubspaces B S hS Y.1)
    (hWflat : IsFlat B S hS
      ((preimageClosedSubspace (restrictOverι g U) W).1.ι ≫ (restrictOverHom g U).hom))
    (hWlfp : IsLocallyOfFinitePresentation B S hS
      ((preimageClosedSubspace (restrictOverι g U) W).1.ι ≫ (restrictOverHom g U).hom)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsFlat B S hS (strictTransformSpaceToBlowUp B S hS
              (subspaceInclusion B S hS Y W ≫ g) b (Z.1.preimage b.hom)).hom ∧
              IsLocallyOfFinitePresentation B S hS (strictTransformSpaceToBlowUp B S hS
                (subspaceInclusion B S hS Y W ≫ g) b (Z.1.preimage b.hom)).hom := by
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS A.2 hAqc hg.2.1
  -- the module `F = i_*𝒪_W` on `Y`
  have hFqc : (pushforwardStructureSheaf B S hS Y W).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_pushforwardStructureSheaf B S hS Y W
  have hFft : (pushforwardStructureSheaf B S hS Y W).IsFiniteTypeOnSite := by
    exact @isFiniteTypeOnSite_of_epi B S hS Y.1 Y.2 _ _ (structureProjection B S hS Y W)
      (epi_structureProjection B S hS Y W) (isFiniteTypeOnSite_unit_structureRingSheaf B S hS Y)
  -- its restriction over `U` is `i_*𝒪_{W_U}`, of finite presentation and flat over `U`
  obtain ⟨eU⟩ := nonempty_modulePullback_restrictOverι_pushforwardStructureSheaf_iso g U W
  set WU := preimageClosedSubspace (restrictOverι g U) W with hWU
  have hsnd : IsLocallyOfFinitePresentation B S hS (restrictOverHom g U).hom :=
    isLocallyOfFinitePresentation_snd_fiberProduct g U.toSpaceι hg.1
  have hincl : IsLocallyOfFinitePresentation B S hS WU.1.ι :=
    isLocallyOfFinitePresentation_of_comp B S hS WU.2.1 (restrictOver g U).2 U.2.1 _ _ hWlfp
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hsnd)
  have hker := (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
    (subspaceInclusion B S hS (restrictOver g U) WU) WU.2.2).1
    ((isFinitePresentation_iff_isLocallyOfFinitePresentation B S hS
      (subspaceInclusion B S hS (restrictOver g U) WU) WU.2.2).2 hincl)
  rw [kernelIdealSheaf_eq_definingIdealSheaf] at hker
  have hFUfp : ((modulePullback B S hS (restrictOverι g U)).obj
      (pushforwardStructureSheaf B S hS Y W)).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso eU.symm
      (isFinitePresentationOnSite_pushforwardStructureSheaf B S hS _ WU hker)
  have hFUflat : IsFlatOver B S hS (restrictOver g U).2 (restrictOverHom g U).hom
      ((modulePullback B S hS (restrictOverι g U)).obj
        (pushforwardStructureSheaf B S hS Y W)) :=
    IsFlatOver.of_iso B S hS _ eU.symm
      (isFlatOver_pushforwardStructureSheaf_of_isFlat B S hS WU (restrictOverHom g U) hWflat)
  -- flattening by blowing up, Stacks 087C
  obtain ⟨Z, A', b, hZfp, hUZ, hb, hFfp, hFflat⟩ :=
    exists_isFlatteningBlowup hZ hAqc hAqs U hUqc h07VR g hYqc hg.1
      (pushforwardStructureSheaf B S hS Y W) hFqc hFft hFUfp hFUflat
  -- the strict transform of `i_*𝒪_W` is `k_*𝒪_{W'}`, by Stacks 0866
  obtain ⟨-, e, -⟩ := exists_modulePushforward_strictTransformSheaf_iso_unconditional B S hS
    (subspaceInclusion B S hS Y W) g b Z
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨W.1.toFunctor, W.2.1⟩))
    (SheafOfModules.isQuasicoherentOnSite_unit _) hb
    (isAffineHom_of_isClosedImmersion B S hS _ W.2.2)
  obtain ⟨e₀⟩ := nonempty_strictTransformSheaf_unit_iso (subspaceInclusion B S hS Y W ≫ g) b hb
  set i' := strictTransformPullbackMap B S hS (subspaceInclusion B S hS Y W) g b with hi'
  set W' := strictTransform B S hS (subspaceInclusion B S hS Y W ≫ g) b (Z.1.preimage b.hom)
    with hW'
  have hk : IsClosedImmersion B S hS
      (subspaceInclusion B S hS (strictTransformPullback B S hS
        (subspaceInclusion B S hS Y W ≫ g) b) W' ≫ i').hom :=
    isClosedImmersion_comp B S hS _ _ W'.2.2
      (isClosedImmersion_of_isPullback B S hS
        (isPullback_strictTransformPullbackMap B S hS (subspaceInclusion B S hS Y W) g b) W.2.2)
  let eM : structureSheafPushforward B S hS
        (subspaceInclusion B S hS (strictTransformPullback B S hS
          (subspaceInclusion B S hS Y W ≫ g) b) W' ≫ i') ≅
      strictTransformSheaf B S hS g b (Z.1.preimage b.hom)
        (pushforwardStructureSheaf B S hS Y W) :=
    ((modulePushforwardCompIso B S hS _ i').app _).symm ≪≫
      (modulePushforward B S hS i').mapIso e₀.symm ≪≫ e
  have hkfp := isFinitePresentation_of_isFinitePresentationOnSite_structureSheafPushforward B S hS
    _ hk (SheafOfModules.IsFinitePresentationOnSite.of_iso eM.symm hFfp)
  have hkflat := isFlat_comp_of_isFlatOver_structureSheafPushforward B S hS _ hk
    (strictTransformPullbackToBlowUp B S hS g b) (IsFlatOver.of_iso B S hS _ eM.symm hFflat)
  have hp : IsLocallyOfFinitePresentation B S hS (strictTransformPullbackToBlowUp B S hS g b).hom :=
    isLocallyOfFinitePresentation_snd_fiberProduct g b hg.1
  have hkeq : (subspaceInclusion B S hS (strictTransformPullback B S hS
        (subspaceInclusion B S hS Y W ≫ g) b) W' ≫ i') ≫
          strictTransformPullbackToBlowUp B S hS g b =
      strictTransformSpaceToBlowUp B S hS (subspaceInclusion B S hS Y W ≫ g) b
        (Z.1.preimage b.hom) := by
    rw [Category.assoc, hi', strictTransformPullbackMap_toBlowUp]
  refine ⟨A', b, Z, hZfp, hUZ, hb, ?_, ?_⟩
  · rw [← hkeq]
    exact hkflat
  · rw [← hkeq]
    exact isLocallyOfFinitePresentation_comp B S hS W'.2.1 (strictTransformPullback B S hS g b).2
      A'.2 _ _ hkfp.1 hp

/- Stacks 087E is stated below relative to two hypotheses.  `h0873` states Stacks 0873, which is
proved in `exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType`; `h07VR`
states Stacks 07VR in the shape it has in `exists_isFlatteningBlowup`, where it is the assumed
input of Stacks 087C. The tag 087E is attached to the form proved under the source's hypotheses
alone,
`exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp_of_isFiniteType`.
-/

/-- **Stacks 087E, flattening a morphism by blowing up, over Stacks 0873 (`h0873`) and the held
inputs of Stacks 087C (`h07VR`).**  Let
`f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open subspace.
Assume that `A` is quasi-compact and quasi-separated, that `U` is quasi-compact, that `f` is of
finite type and quasi-separated, and that `f⁻¹(U) ⟶ U` is flat and locally of finite
presentation.  Then there is a `U`-admissible blowup `b : A' ⟶ A`, with centre `Z`, such that the
strict transform of `X` is flat and of finite presentation over `A'`.

See the module documentation for the argument. -/
theorem exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    (h0873 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
      IsFiniteType B S hS f → IsSeparated B S hS f →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS hZ Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
        IsAlgebraicSpace B S hS X' ∧ IsSeparated B S hS f' ∧
          IsFinitePresentation B S hS f' ∧ IsClosedImmersion B S hS i ∧ i ≫ f' = f)
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
  -- an affine scheme `V` with a surjective étale `a : V ⟶ X`
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS A.2 hAqc hft.2
  obtain ⟨V₀, a, hV₀, has, hae⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hXqc
  have hVqc : IsQuasiCompactSpace B S hS (yoneda.obj V₀) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V₀) := isAlgebraicSpace_yoneda B S hS V₀
  -- `V ⟶ A` is separated and of finite type
  have hsep : IsSeparated B S hS (a ≫ f.hom) := by
    have := hV₀
    exact isSeparated_of_scheme_isSeparated B S hS inferInstance _
  have hvft : IsFiniteType B S hS (a ≫ f.hom) :=
    ⟨isLocallyOfFiniteType_comp B S hS hV X.2 A.2 a f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
          (isLocallyOfFinitePresentation_of_isEtale B S hS hae)) hft.1,
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hVqc _⟩
  -- Stacks 0873: a closed immersion `i : V ⟶ Y` with `Y ⟶ A` separated of finite presentation
  obtain ⟨Y₀, g₀, i, hY₀, -, hgfp, hi, hig⟩ := h0873 (a ≫ f.hom) hV A.2 hvft hsep hAqc hAqs
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
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 V₀ a).1 has)
  have hcomm : u ≫ f = subspaceInclusion B S hS Y W ≫ g := by
    refine ObjectProperty.hom_ext _ ?_
    show (e.inv ≫ a) ≫ f.hom = W.1.ι ≫ g₀
    rw [Category.assoc, ← hig, ← Category.assoc, he]
  -- `W_U ⟶ U` is flat and locally of finite presentation: it is étale over `X_U ⟶ U`
  have hWU := (preimageClosedSubspace (restrictOverι g U) W).2.1
  have hsqg := AlgebraicSpaces.isPullback_hom B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g U.toSpaceι)
  have hfst : (W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverι g U).hom =
      W.1.fromPreimage (restrictOverι g U).hom ≫ W.1.ι :=
    (Subfunctor.fromPreimage_ι W.1 (restrictOverι g U).hom).symm
  have hu : u.hom ≫ f.hom = W.1.ι ≫ g.hom := congrArg (fun k => k.hom) hcomm
  have hXU : IsAlgebraicSpace B S hS (pullback f.hom U.1.ι) :=
    isAlgebraicSpace_pullback B S hS f.hom U.1.ι X.2 U.2.1 A.2
  let t : (W.1.preimage (restrictOverι g U).hom).toFunctor ⟶ pullback f.hom U.1.ι :=
    pullback.lift (W.1.fromPreimage (restrictOverι g U).hom ≫ u.hom)
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) (by
        rw [Category.assoc, hu, ← Category.assoc, ← hfst, Category.assoc, hsqg.w,
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
  have hWflat : IsFlat B S hS
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) := by
    rw [← ht_snd]
    exact isFlat_comp B S hS hWU hXU U.2.1 _ _ (isFlat_of_isEtale B S hS ht) hflat
  have hWlfp : IsLocallyOfFinitePresentation B S hS
      ((W.1.preimage (restrictOverι g U).hom).ι ≫ (restrictOverHom g U).hom) := by
    rw [← ht_snd]
    exact isLocallyOfFinitePresentation_comp B S hS hWU hXU U.2.1 _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS ht) hlfp
  -- the case of the closed subspace `W ⊆ Y`
  obtain ⟨A', b, Z, hZfp, hUZ, hb, hW'flat, hW'lfp⟩ :=
    exists_isBlowupAlong_isFlat_strictTransformSpaceToBlowUp_of_closedSubspace hZ h07VR
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
