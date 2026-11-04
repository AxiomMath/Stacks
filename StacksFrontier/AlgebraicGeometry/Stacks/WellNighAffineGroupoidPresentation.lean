module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentSizeBound
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
import all StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoid

/-!
# Well-nigh affine stacks are the quotients of affine finite locally free groupoids (Stacks 0DUM)

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site. **Stacks 0DUM** says that
`𝒳` is well-nigh affine (Stacks 0DUL) exactly when `𝒳 = [U/R]` for a groupoid scheme
`(U, R, s, t, c)` with `U` and `R` affine and `s, t` finite locally free, and that `𝒳` is then
quasi-compact, quasi-DM and separated. The condition (2) and the quasi-compactness and quasi-DM
assertions are in `StacksFrontier/AlgebraicGeometry/Stacks/WellNighAffineGroupoid.lean`; this file
proves the two implications and the separatedness assertion in the absolute sense of Stacks 050D,
part (7), and registers the whole statement.

## Main results

* `AlgebraicGeometry.Stack.hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine`:
  (1) ⇒ (2).
* `AlgebraicGeometry.Stack.isWellNighAffine_of_hasAffineFiniteLocallyFreeGroupoidPresentation`:
  (2) ⇒ (1).
* `AlgebraicGeometry.Stack.isAbsolutelySeparated_of_isWellNighAffine`: a well-nigh affine
  algebraic stack is separated over `Spec ℤ`.
* `AlgebraicGeometry.Stack.isWellNighAffine_iff_and_isQuasiCompact_isQuasiDM_isSeparated`:
  **Stacks 0DUM**.

## Implementation notes

**(1) ⇒ (2)** is the source's argument. The presentation `f : U ⟶ 𝒳` has a self-intersection
`U ×_𝒳 U` represented by an algebraic space `R` (Stacks 04T4 (1)); its two projections are base
changes of `f`, so the source and target `s, t : R ⟶ U` of the groupoid of Stacks 04T4 (4) are
finite, flat and locally of finite presentation (Stacks 045C), and since `f` is surjective, flat
and locally of finite presentation the canonical 1-morphism `[U/R] ⟶ 𝒳` is an equivalence
(Stacks 04WY). Finiteness of `t` over the affine scheme `U`, tested against the identity of `U`,
makes `R` the algebraic space of an affine scheme of the site, and then `s` and `t` are Yoneda
images of finite locally free morphisms of schemes (Stacks 02KB). The groupoid in algebraic spaces
of Stacks 04T4 (4) is then literally `AlgebraicGeometry.Stack.representedGroupoid` of a groupoid
scheme, by `exists_representedGroupoid_eq_ofComposable`.

**(2) ⇒ (1)** reads the atlas `U ⟶ [U/R] ≃ 𝒳` of Stacks 044R on the model `𝒳`
(`AlgebraicGeometry.Stack.quotientStackModelProjection`). It is surjective, flat and locally of
finite presentation by Stacks 06FH; it is finite because its self-intersection is `R` with first
projection `s` (Stacks 04M9), so every relative property of `s` which is stable under base change
and fppf local on the target passes to it (Stacks 04XD), and finiteness is (Stacks 0426). Finite
presentation is local finite presentation together with quasi-compactness and
quasi-separatedness, the last two coming from finiteness. The source's own appeal to Stacks 06FI
(algebraicity of `[U/R]`) is not needed: `𝒳` is an algebraic stack by hypothesis.

**Separatedness.** The library's `IsAbsolutelySeparated` is separatedness over `Spec ℤ` of `𝒳`
viewed over `Spec ℤ` by Construction A of Stacks 04X5. Separatedness over `S`, which Stacks 0DTY
(6) gives directly, is weaker when `S` is not separated, so the argument is run over `Spec ℤ`
instead: the presentation viewed over `Spec ℤ` (with source the affine scheme `U` viewed over
`Spec ℤ`, through `AlgebraicGeometry.Stack.factorSliceInverse`) is surjective, flat, locally of
finite presentation and proper, because these four relative properties are unchanged by
Construction A (`hasRelativeProperty_surjective_changeBaseHom_iff`,
`hasRelativeProperty_smooth_changeBaseHom_iff`, `isProper_changeBaseHom_iff`); Stacks 04WY over
`Spec ℤ` presents `𝒳` by its self-intersection groupoid, whose source and target are then flat,
locally of finite presentation and proper, over an affine object space; and Stacks 0DTY (6) over
`Spec ℤ` concludes.

## References

* [Stacks Project, Tag 0DUM](https://stacks.math.columbia.edu/tag/0DUM)
* [Stacks Project, Tag 0DUL](https://stacks.math.columbia.edu/tag/0DUL)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The terminal scheme lies in every big fppf site.** It is isomorphic to `Spec (ULift ℤ)`,
which lies in every big fppf site, and an isomorphism is flat and surjective. So the hypothesis
`B.Contains (⊤_ Scheme)` under which the absolute separation properties of Stacks 050D are
stated is always met. -/
alias contains_terminalScheme := BigFppfSite.contains_terminal

/-- A morphism of the site whose Yoneda image is a finite, flat and locally finitely presented
morphism of algebraic spaces is a finite locally free morphism of schemes (Stacks 02KB). -/
theorem isFiniteLocallyFree_of_yonedaMap {U R : BigFppfOver B S hS} (s : R ⟶ U)
    (hfin : Space.IsFinite B S hS (yoneda.map s)) (hflat : Space.IsFlat B S hS (yoneda.map s))
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (yoneda.map s)) :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) :=
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).2
    ⟨Space.finite_of_isFinite_yoneda_map B S hS s hfin,
      (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget s).1
        hflat,
      (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget s).1 hlfp⟩

/-- Variant of `isFiniteLocallyFree_of_yonedaMap` for a morphism of presheaves known to equal
the Yoneda image of `s`. -/
private theorem isFiniteLocallyFree_of_eq_yonedaMap {U R : BigFppfOver B S hS} (s : R ⟶ U)
    {σ : yoneda.obj R ⟶ yoneda.obj U} (hσ : yoneda.map s = σ) (hfin : Space.IsFinite B S hS σ)
    (hflat : Space.IsFlat B S hS σ) (hlfp : Space.IsLocallyOfFinitePresentation B S hS σ) :
    Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) := by
  subst hσ
  exact isFiniteLocallyFree_of_yonedaMap B S hS s hfin hflat hlfp

/-- A groupoid in algebraic spaces built by `GroupoidInAlgebraicSpaces.ofComposable` on the
represented algebraic spaces of two objects of the site is the represented groupoid of a groupoid
scheme of the site: its source and target are Yoneda images by full faithfulness. -/
theorem exists_representedGroupoid_eq_ofComposable {U R : BigFppfOver B S hS}
    (σ τ : yoneda.obj R ⟶ yoneda.obj U)
    (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R) σ τ ⟶ yoneda.obj R)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (σ.app T) (τ.app T)
      fun p => c.app T p)) :
    ∃ (s t : R ⟶ U) (c' : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
        (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
      (hG' : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
        ((yoneda.map t).app T) fun p => c'.app T p)),
      yoneda.map s = σ ∧ yoneda.map t = τ ∧
        representedGroupoid B S hS s t c' hG' =
          GroupoidInAlgebraicSpaces.ofComposable
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
            ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩
            (ObjectProperty.homMk σ) (ObjectProperty.homMk τ) c hG := by
  obtain ⟨s, rfl⟩ : ∃ s, yoneda.map s = σ := ⟨yoneda.preimage σ, yoneda.map_preimage σ⟩
  obtain ⟨t, rfl⟩ : ∃ t, yoneda.map t = τ := ⟨yoneda.preimage τ, yoneda.map_preimage τ⟩
  exact ⟨s, t, c, hG, rfl, rfl, rfl⟩

/-- A flat surjective presentation of an algebraic stack by a scheme is relatively flat and
relatively surjective. -/
private theorem hasRelativeProperty_flat_and_surjective_of_presentation {U : BigFppfOver B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) f.hom hrep ∧
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      f.hom hrep := by
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  exact ⟨(hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (schemeStack.{u, w} B S hS U).property
      𝒳.property f.hom hrep).1 hflat,
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).1 hsurj⟩

/-- A morphism of algebraic spaces which is finite is proper and locally quasi-finite. -/
private theorem isProper_and_isLocallyQuasiFinite_of_isFinite_hom
    {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y) (hfa : Space.IsFinite B S hS a.hom) :
    Space.IsProper B S hS a.hom ∧ Space.IsLocallyQuasiFinite B S hS a.hom :=
  Space.isProper_and_isLocallyQuasiFinite_of_isFinite B S hS
    (ObjectProperty.FullSubcategory.property _) (ObjectProperty.FullSubcategory.property _)
    a.hom hfa

/-- **(1) ⇒ (2) of Stacks 0DUM.** A well-nigh affine algebraic stack is the quotient stack of a
groupoid scheme with affine object and arrow schemes and finite locally free source and target. -/
theorem hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    HasAffineFiniteLocallyFreeGroupoidPresentation.{u, w} B S hS 𝒳 := by
  classical
  obtain ⟨U, hU, f, hsurj, hflat, ⟨hrep, hfin⟩, ⟨-, hfp⟩⟩ := h𝒳
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS U
  let F : 𝒰 ⟶ 𝒳.val := f.hom
  let Uₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let eU : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (Uₛ.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳.val F.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  let R₀ : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR₀' : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (R₀.obj ⋙ typeToCat)).p := eR₀
  -- the relative properties of the presentation
  have hfinP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.finiteMorphismProperty B S hS) F hrep := hfin
  obtain ⟨hflatP, hsurjP⟩ :=
    hasRelativeProperty_flat_and_surjective_of_presentation B S hS f hrep hsurj hflat
  have hlfpP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) F hrep :=
    fun V y hy G hG he => (hfp V y hy G hG he).1
  -- the self-intersection is an affine scheme, finite over `U`
  have ht₀ : Space.IsFinite B S hS (SelfIntersection.relationTarget eU eR₀').hom :=
    SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ R₀ eU eR₀'
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨V, p, i, hV, -, hpb⟩ := ht₀ U hU (𝟙 _)
  have hi : IsIso i := hpb.flip.isIso_snd_of_isIso
  let iV : yoneda.obj V ≅ Robj := asIso i
  let Rₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (Rₛ.obj ⋙ typeToCat)).p :=
    eR₀'.trans (PresheafOfCategories.equivalenceOverOfIso iV.symm)
  -- Stacks 04WY: the canonical 1-morphism out of `[U/R]` is an equivalence
  obtain ⟨E⟩ := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eU eR 𝒳.property
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)
  let e := StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).canonicalMap.w E
  -- the source and target of the groupoid
  have hsF := SelfIntersection.prop_relationSource B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  have htF := SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget
    B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR hrep hflatP
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget
      B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR hrep hlfpP
  obtain ⟨s, t, c', hG', hs, ht, hGeq⟩ := exists_representedGroupoid_eq_ofComposable B S hS
    (SelfIntersection.relationSourceMap eU eR) (SelfIntersection.relationTargetMap eU eR)
    (SelfIntersection.compositionLaw eU eR (SelfIntersection.isFiberedInSetoids_source eU))
    (SelfIntersection.nonempty_pointwiseGroupoid eU eR
      (SelfIntersection.isFiberedInSetoids_source eU))
  refine ⟨U, V, s, t, c', hG', hU, hV, ?_, ?_, ⟨?_⟩⟩
  · exact isFiniteLocallyFree_of_eq_yonedaMap B S hS s hs hsF hsFl hsL
  · exact isFiniteLocallyFree_of_eq_yonedaMap B S hS t ht htF htFl htL
  · rw [hGeq]
    exact e

/-- **(2) ⇒ (1) of Stacks 0DUM.** The quotient stack of a groupoid scheme with affine object
scheme and finite locally free source and target is well-nigh affine. -/
theorem isWellNighAffine_of_hasAffineFiniteLocallyFreeGroupoidPresentation
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h : HasAffineFiniteLocallyFreeGroupoidPresentation.{u, w} B S hS 𝒳) :
    IsWellNighAffine.{u, w} B S hS 𝒳 := by
  classical
  obtain ⟨U, R, s, t, c, hG, hU, -, hs, ht, ⟨e⟩⟩ := h
  let G := representedGroupoid B S hS s t c hG
  let A := Space.terminalSpace B S hS
  let p := quotientStackModelProjection.{u, w} B S hS A G 𝒳 e
  have hrep : IsRepresentableByAlgebraicSpaces B S hS p.hom.hom :=
    isRepresentableByAlgebraicSpaces_quotientStackModelProjection G 𝒳 e
  -- the relative properties of the atlas, from those of `s`
  have hsFin : Space.finiteMorphismProperty B S hS G.source :=
    Space.isFinite_of_isProper_of_isLocallyQuasiFinite B S hS (isAlgebraicSpace_yoneda B S hS R)
      (isAlgebraicSpace_yoneda B S hS U) _ (isProper_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
      (isLocallyQuasiFinite_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
  have hpfin := hasRelativeProperty_quotientStackModelProjection G 𝒳 e
    (Space.finiteMorphismProperty B S hS) hsFin
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hplfp := hasRelativeProperty_quotientStackModelProjection G 𝒳 e
    (spaceProperty B S hS (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h))
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
  obtain ⟨-, hpsurj, hpflat, -⟩ := quotientModelAtlasFppf G 𝒳 e
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
  -- the algebraic stack of `U` is the algebraic stack of its represented algebraic space
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let k : schemeStack.{u, w} B S hS U ⟶
      algebraicSpaceStack.{u, w} B S hS G.objects.obj G.objects.property :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (⟨eU.hom.functor, eU.hom.w⟩ : (schemeStack.{u, w} B S hS U).val.val ⥤ᵇ
        (algebraicSpaceStack.{u, w} B S hS G.objects.obj G.objects.property).val.val))
  have hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom) :=
    eU.isEquivalence_hom_functor
  have hid𝒳 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have hrepk : IsRepresentableByAlgebraicSpaces B S hS (k ≫ p).hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (k ≫ p).hom.hom p.hom.hom
      k.hom.hom (BasedFunctor.id 𝒳.val.val) (Iso.refl _)).1 hrep
  refine ⟨U, hU, k ≫ p, isSurjective_comp_of_isEquivalence B S hS k p hk hpsurj,
    AlgebraicStacks.isFlat_comp_of_isEquivalence B S hS k p hk hpflat, ⟨hrepk, ?_⟩,
    ⟨hrepk, ?_⟩⟩
  · exact relativeProperty_of_equivalences B S hS
      (fun _ _ m => Space.IsFinite B S hS m.hom) (k ≫ p).hom.hom p.hom.hom k.hom.hom
      (BasedFunctor.id 𝒳.val.val) (Iso.refl _) hpfin
  · refine relativeProperty_of_equivalences B S hS
      (fun _ _ m => Space.IsFinitePresentation B S hS m.hom) (k ≫ p).hom.hom p.hom.hom
      k.hom.hom (BasedFunctor.id 𝒳.val.val) (Iso.refl _) ?_
    intro V y hy F hF he
    obtain ⟨⟨hsep, ⟨-, hqc⟩, -⟩, -⟩ :=
      isProper_and_isLocallyQuasiFinite_of_isFinite_hom B S hS _ (hpfin V y hy F hF he)
    exact ⟨hplfp V y hy F hF he, hqc, Space.isQuasiSeparated_of_isSeparated B S hS hsep⟩

/-- **Stacks 0DUM, the separatedness assertion, in the absolute sense of Stacks 050D (7).** A
well-nigh affine algebraic stack over `S` is separated over `Spec ℤ`, with no hypothesis on `S`.

The affine scheme `U` presenting `𝒳`, viewed over `Spec ℤ` by Construction A (Stacks 04X5),
presents `𝒳` viewed over `Spec ℤ` by a surjective, flat, locally finitely presented and proper
1-morphism: surjectivity, flatness and local finite presentation of a 1-morphism are unchanged by
Construction A, and so is properness (a finite morphism of algebraic spaces being proper). Stacks
04WY over `Spec ℤ` makes `𝒳` the quotient stack of the self-intersection groupoid of that
presentation, whose source and target inherit the four properties and whose object space is the
affine scheme `U`, separated over `Spec ℤ`; Stacks 0DTY (6) over `Spec ℤ` concludes. -/
theorem isAbsolutelySeparated_of_isWellNighAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 := by
  classical
  obtain ⟨U, hU, f, hsurj, hflat, ⟨hrep, hfin⟩, ⟨-, hfp⟩⟩ := h𝒳
  -- the relative properties of the presentation over `S`
  obtain ⟨hflatP, hsurjP⟩ :=
    hasRelativeProperty_flat_and_surjective_of_presentation B S hS f hrep hsurj hflat
  have hproperP : IsProper B S hS f.hom := fun V y hy F hF he =>
    (isProper_and_isLocallyQuasiFinite_of_isFinite_hom B S hS _ (hfin V y hy F hF he)).1
  -- Construction A along `S ⟶ Spec ℤ`
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let 𝒳Z : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ :=
    AlgebraicStacks.viewOverIntegers B S hS hZ 𝒳
  let UZ : BigFppfOver B (⊤_ Scheme.{u}) hZ := (Over.map g).obj U
  let 𝒰Z := schemeFibredCategory B (⊤_ Scheme.{u}) hZ UZ
  let fC := changeBaseHom B S (⊤_ Scheme.{u}) hS hZ g f.hom
  let k := factorSliceInverse B S (⊤_ Scheme.{u}) hS hZ g U
  let 𝒳C := changeBaseFiberedInGroupoids B S (⊤_ Scheme.{u}) hS hZ g 𝒳.val
  have h𝒳C : IsAlgebraicStack.{u, w} B (⊤_ Scheme.{u}) hZ 𝒳C.val := 𝒳Z.property
  let FZ : 𝒰Z ⟶ 𝒳C := Bicategory.InducedBicategory.mkHom k ≫ fC
  have hrepZ : IsRepresentableByAlgebraicSpaces B (⊤_ Scheme.{u}) hZ FZ.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B (⊤_ Scheme.{u}) hZ h𝒳C
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B (⊤_ Scheme.{u}) hZ UZ) FZ
  have hid : Functor.IsEquivalence (BasedFunctor.id 𝒳C.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳C.val.obj))
  have hrepC := (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S (⊤_ Scheme.{u}) hS hZ
    g f.hom.hom).2 hrep
  -- a relative property of `fC` is one of `FZ`, as `k` is an equivalence
  have hZtrans : ∀ (P : MorphismProperty (AlgebraicSpaces B (⊤_ Scheme.{u}) hZ))
      [P.IsStableUnderBaseChange] [P.IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B (⊤_ Scheme.{u}) hZ)],
      HasRelativeProperty.{u, u, u + 1, u} B (⊤_ Scheme.{u}) hZ P fC hrepC →
        HasRelativeProperty.{u, u, u + 1, u} B (⊤_ Scheme.{u}) hZ P FZ hrepZ :=
    fun P _ _ h => relativeProperty_of_equivalences B (⊤_ Scheme.{u}) hZ P FZ.hom fC.hom k
      (BasedFunctor.id 𝒳C.val) (Iso.refl _) h
  have hsurjZ : HasRelativeProperty.{u, u, u + 1, u} B (⊤_ Scheme.{u}) hZ
      (Space.surjectiveMorphismProperty B (⊤_ Scheme.{u}) hZ) FZ hrepZ :=
    hZtrans _
      ((hasRelativeProperty_surjective_changeBaseHom_iff.{u, u, u + 1, u} B S (⊤_ Scheme.{u}) hS
        hZ g f.hom hrep).2 hsurjP)
  have hflatBCZ : (spaceProperty B (⊤_ Scheme.{u}) hZ
      (fun _ _ h => Space.IsFlat B (⊤_ Scheme.{u}) hZ h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B (⊤_ Scheme.{u}) hZ
  have hflatLTZ : (spaceProperty B (⊤_ Scheme.{u}) hZ
      (fun _ _ h => Space.IsFlat B (⊤_ Scheme.{u}) hZ h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B (⊤_ Scheme.{u}) hZ) :=
    Space.isFlat_isLocalAtTarget_fppf B (⊤_ Scheme.{u}) hZ
  have hflatZ : HasRelativeProperty.{u, u, u + 1, u} B (⊤_ Scheme.{u}) hZ
      (spaceProperty B (⊤_ Scheme.{u}) hZ
        (fun _ _ h => Space.IsFlat B (⊤_ Scheme.{u}) hZ h)) FZ hrepZ :=
    hZtrans _
      ((hasRelativeProperty_smooth_changeBaseHom_iff B S (⊤_ Scheme.{u}) hS hZ g
        (@Flat.{u}) f.hom hrep).2 hflatP)
  have hlfpZ : HasRelativeProperty.{u, u, u + 1, u} B (⊤_ Scheme.{u}) hZ
      (fun ⦃X Y : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (m : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ m.hom) FZ hrepZ :=
    hZtrans _
      ((hasRelativeProperty_smooth_changeBaseHom_iff B S (⊤_ Scheme.{u}) hS hZ g
        (@LocallyOfFinitePresentation.{u}) f.hom hrep).2
        (fun V y hy F hF he => (hfp V y hy F hF he).1))
  have hpropBCZ : (Space.properProperty B (⊤_ Scheme.{u}) hZ).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B (⊤_ Scheme.{u}) hZ
  have hpropLTZ : (Space.properProperty B (⊤_ Scheme.{u}) hZ).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B (⊤_ Scheme.{u}) hZ) :=
    Space.proper_isLocalAtTarget_fppf B (⊤_ Scheme.{u}) hZ
  have hpropZ : HasRelativeProperty.{u, u, u + 1, u} B (⊤_ Scheme.{u}) hZ
      (Space.properProperty B (⊤_ Scheme.{u}) hZ) FZ hrepZ :=
    hZtrans _
      ((isProper_changeBaseHom_iff B S (⊤_ Scheme.{u}) hS hZ g f.hom).2 hproperP)
  -- Stacks 04WY over `Spec ℤ`
  let UZs : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    ⟨yoneda.obj UZ, isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ UZ⟩
  let eUZ : StacksRepresentableCFG.EquivalenceOver
      𝒰Z.val.p (presheafOfCategories (UZs.obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver UZ
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B (⊤_ Scheme.{u}) hZ 𝒰Z 𝒳C FZ.hom 𝒳Z.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B (⊤_ Scheme.{u}) hZ UZ)
  let Rs : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨Robj, hRobj⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B (⊤_ Scheme.{u}) hZ 𝒰Z 𝒳C FZ.hom).val.p
      (presheafOfCategories (Rs.obj ⋙ typeToCat)).p := eR₀
  obtain ⟨E⟩ := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eUZ eR h𝒳C
    (fun T y hy G hG he => ⟨hsurjZ T y hy G hG he, hflatZ T y hy G hG he,
      hlfpZ T y hy G hG he⟩)
  let e := StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (SelfIntersection.selfIntersectionPresentation eUZ eR h𝒳C).canonicalMap.w E
  -- the source and target of the groupoid over `Spec ℤ`
  have hsP := SelfIntersection.prop_relationSource B (⊤_ Scheme.{u}) hZ 𝒰Z 𝒳C FZ UZs Rs
    eUZ eR (Space.properProperty B (⊤_ Scheme.{u}) hZ) hrepZ hpropZ
  have htP := SelfIntersection.prop_relationTarget B (⊤_ Scheme.{u}) hZ 𝒰Z 𝒳C FZ UZs Rs
    eUZ eR (Space.properProperty B (⊤_ Scheme.{u}) hZ) hrepZ hpropZ
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget
    B (⊤_ Scheme.{u}) hZ 𝒰Z 𝒳C FZ UZs Rs eUZ eR hrepZ hflatZ
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget
      B (⊤_ Scheme.{u}) hZ 𝒰Z 𝒳C FZ UZs Rs eUZ eR hrepZ hlfpZ
  exact isSeparatedOver_of_isProper_source_target.{u, w}
    (SelfIntersection.selfIntersectionPresentation eUZ eR h𝒳C).groupoid 𝒳Z ⟨e⟩
    hsFl htFl hsL htL hsP htP
    (isSeparated_toTerminalSpace_of_isAffine B (⊤_ Scheme.{u}) hZ UZ hU _)

/-- **Stacks 0DUM.** Let `𝒳` be an algebraic stack over `S`. The following are equivalent:

1. `𝒳` is well-nigh affine (Stacks 0DUL);
2. there is a groupoid scheme `(U, R, s, t, c)` with `U` and `R` affine and `s, t : R ⟶ U`
   finite locally free such that `𝒳 = [U/R]`.

If they hold, then `𝒳` is quasi-compact, quasi-DM and separated, the last two in the absolute
sense of Stacks 050D, parts (6) and (7), that is over `Spec ℤ`.

The equivalence is `hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine` and
`isWellNighAffine_of_hasAffineFiniteLocallyFreeGroupoidPresentation`; quasi-compactness is
`isQuasiCompactStack_of_isWellNighAffine`, quasi-DM is Stacks 0DTY (4) applied to the
presentation of (2), and separatedness is `isAbsolutelySeparated_of_isWellNighAffine`. -/
@[stacks 0DUM]
theorem isWellNighAffine_iff_and_isQuasiCompact_isQuasiDM_isSeparated
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (IsWellNighAffine.{u, w} B S hS 𝒳 ↔
        HasAffineFiniteLocallyFreeGroupoidPresentation.{u, w} B S hS 𝒳) ∧
      (IsWellNighAffine.{u, w} B S hS 𝒳 →
        IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property ∧
          AlgebraicStacks.IsAbsolutelyQuasiDM.{u, w} B S hS (contains_terminalScheme B) 𝒳 ∧
            AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS (contains_terminalScheme B) 𝒳) := by
  refine ⟨⟨hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine B S hS 𝒳,
    isWellNighAffine_of_hasAffineFiniteLocallyFreeGroupoidPresentation B S hS 𝒳⟩, fun h => ⟨
      isQuasiCompactStack_of_isWellNighAffine B S hS 𝒳 h, ?_,
      isAbsolutelySeparated_of_isWellNighAffine B S hS _ 𝒳 h⟩⟩
  obtain ⟨U, R, s, t, c, hG, -, -, hs, ht, hequiv⟩ :=
    hasAffineFiniteLocallyFreeGroupoidPresentation_of_isWellNighAffine B S hS 𝒳 h
  exact isAbsolutelyQuasiDM_of_representedGroupoid_isFiniteLocallyFree B S hS 𝒳 s t c hG _ hs ht
    hequiv

end AlgebraicGeometry.Stack

end
