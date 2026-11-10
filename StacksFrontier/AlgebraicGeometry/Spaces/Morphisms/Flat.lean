module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Flat morphisms of algebraic spaces: the nine criteria

Flatness of a morphism of algebraic spaces over a scheme `S` is by definition the condition
of Stacks 03MJ that the morphism of schemes underlying every commuting square of étale
charts be flat (`AlgebraicGeometry.Space.IsFlat`, part (1) of Stacks 03ML). This file proves
the nine equivalent characterisations of that condition listed in Stacks 03MM.

The last seven of the nine hold for any property of scheme morphisms which is étale local on
the source and target, stable under composition and base change, and implied by étaleness, and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae` states them in that generality. The
pointwise criterion is specific to flatness: it is phrased with the germ-level predicate of
Stacks 04ND rather than with the property of scheme morphisms itself.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae`: the nine criteria for an arbitrary
  property of scheme morphisms with the four properties above, with the pointwise criterion
  in its open-neighbourhood form.
* `AlgebraicGeometry.Space.isFlat_iff_forall_isFlatAt`: the equivalence of conditions (1) and
  (2) of Stacks 03MM, with flatness at a point in the germ sense of Stacks 03ML.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_zariskiCover_target`: the leg (9) implies
  (1) of those criteria on its own, that the every-chart condition is Zariski local on the
  target, with `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_openSubspace_cover_target`
  its form for a family of open subspaces covering the target on points.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_pullback_snd_comp_iff`: the every-chart
  condition does not distinguish the base change along a composite from the iterated base
  change.
* `AlgebraicGeometry.Space.isFlat_tfae`: the nine criteria for flatness.
* `AlgebraicGeometry.Space.universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation`: a flat
  morphism locally of finite presentation is universally open.
* `AlgebraicGeometry.Space.universallyOpen_of_isSyntomic`: a syntomic morphism is universally
  open.

## References

* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
* [Stacks Project, Tag 01UL](https://stacks.math.columbia.edu/tag/01UL)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 03Z5](https://stacks.math.columbia.edu/tag/03Z5)
* [Stacks Project, Tag 0410](https://stacks.math.columbia.edu/tag/0410)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
* [Stacks Project, Tag 0DF0](https://stacks.math.columbia.edu/tag/0DF0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_flat :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_flat
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_flat B S hS).has_limit _

local instance (priority := high) hasLimitsOfShape_discrete_presheaf_flat (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-! ### Auxiliary facts about open immersions and base changes of presheaves -/

/-- The second projection of a fibre product of presheaves on the big fppf site of `S` is
étale when the morphism it is the base change of is. -/
public theorem isEtale_pullback_snd {F G Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hZ : IsAlgebraicSpace B S hS Z) (g : Z ⟶ G) (f : F ⟶ G) (hg : IsEtale B S hS g) :
    IsEtale B S hS (pullback.snd g f) := by
  let F' : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let G' : AlgebraicSpaces B S hS := ⟨G, hG⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let g' : Z' ⟶ G' := ObjectProperty.homMk g
  let f' : F' ⟶ G' := ObjectProperty.homMk f
  let W : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS g' f'
  let fstHom : W ⟶ Z' := ObjectProperty.homMk (pullback.fst g f)
  let sndHom : W ⟶ F' := ObjectProperty.homMk (pullback.snd g f)
  have hsq : IsPullback fstHom sndHom g' f' :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS g' f'
  exact isEtale_of_isPullback B S hS fstHom sndHom g' f' hsq hg

/-- Surjectivity of the morphism of schemes underlying a morphism of the big fppf site of `S`
is stable under composition, and hence so is the corresponding property of represented
morphisms of presheaves. -/
private theorem presheaf_surjective_isStableUnderComposition :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderComposition :=
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    ⟨fun u v hu hv ↦ by
      have h₁ : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map u) := hu
      have h₂ : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map v) := hv
      change AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map (u ≫ v))
      rw [Functor.map_comp]
      infer_instance⟩
  MorphismProperty.relative_isStableUnderComposition _

/-! ### The nine criteria for a property of scheme morphisms -/

variable (P : MorphismProperty Scheme.{u})

/-- A property of morphisms of schemes implied by étaleness holds on every étale chart of an
isomorphism into an algebraic space. -/
private theorem holdsOnEveryEtaleChart_of_isIso
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    [IsIso f] : HoldsOnEveryEtaleChart B S hS P f :=
  holdsOnEveryEtaleChart_of_isEtale_hom B S hS P hPetale hG (isEtale_of_isIso B S hS f)

/-- A property of morphisms of schemes implied by étaleness holds on every étale chart of a
morphism from a representable presheaf whose underlying scheme morphism is étale. -/
private theorem holdsOnEveryEtaleChart_of_presheaf_etale
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {U : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (p : yoneda.obj U ⟶ G)
    (hp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    HoldsOnEveryEtaleChart B S hS P p :=
  holdsOnEveryEtaleChart_of_isEtale_hom B S hS P hPetale hG
    ((isEtale_iff_presheaf_of_yoneda B S hS p).2 hp)

/-- If `P` holds on every étale chart of `g`, it holds on every étale chart of the composite of
`g` with the identity inclusion of the open subspace `⊤` of its source. -/
private theorem holdsOnEveryEtaleChart_top_ι_comp
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPcomp : P.IsStableUnderComposition)
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) {g : Z ⟶ Y} (hg : HoldsOnEveryEtaleChart B S hS P g) :
    HoldsOnEveryEtaleChart B S hS P ((⊤ : Subfunctor Z).ι ≫ g) :=
  have := hPcomp
  holdsOnEveryEtaleChart_comp B S hS P hP (isOpenSubspace_top hZ).1 hZ hY _ _
    (holdsOnEveryEtaleChart_of_isIso B S hS P hPetale hZ _) hg

/-- A property of morphisms of schemes which is étale local on the source and target, stable
under base change and implied by étaleness holds on every étale chart of the first projection
of `Z ×[Y] X` as soon as it holds on every étale chart of `f : X ⟶ Y`, for an arbitrary
morphism `g : Z ⟶ Y` of algebraic spaces over `S`. -/
theorem holdsOnEveryEtaleChart_pullback_fst_of_isAlgebraicSpace
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPbc : P.IsStableUnderBaseChange)
    {F G Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hZ : IsAlgebraicSpace B S hS Z) (g : Z ⟶ G) (f : F ⟶ G)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P (pullback.fst g f) := by
  have := hPbc
  let F' : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let G' : AlgebraicSpaces B S hS := ⟨G, hG⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let g' : Z' ⟶ G' := ObjectProperty.homMk g
  let f' : F' ⟶ G' := ObjectProperty.homMk f
  have hf' : HoldsOnEveryEtaleChart B S hS P f'.hom := hf
  have hbc := (holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS P hP).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g' f').flip hf'
  simpa [F', G', Z', g', f', AlgebraicSpaces.fiberProduct] using hbc

/-- The second-projection form of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_pullback_fst_of_isAlgebraicSpace`. -/
theorem holdsOnEveryEtaleChart_pullback_snd_of_isAlgebraicSpace
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPbc : P.IsStableUnderBaseChange)
    {F G Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hZ : IsAlgebraicSpace B S hS Z) (f : F ⟶ G) (g : Z ⟶ G)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P (pullback.snd f g) := by
  have := hPbc
  let F' : AlgebraicSpaces B S hS := ⟨F, hF⟩
  let G' : AlgebraicSpaces B S hS := ⟨G, hG⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let g' : Z' ⟶ G' := ObjectProperty.homMk g
  let f' : F' ⟶ G' := ObjectProperty.homMk f
  have hf' : HoldsOnEveryEtaleChart B S hS P f'.hom := hf
  have hbc := (holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS P hP).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f' g') hf'
  simpa [F', G', Z', g', f', AlgebraicSpaces.fiberProduct] using hbc

/-- Condition (6) of Stacks 03MM implies condition (1): if `P` holds on every étale chart of
the composite of `f` with one surjective étale chart of its source, then it holds on every
étale chart of `f`. -/
theorem holdsOnEveryEtaleChart_of_surjectiveEtale_source
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
    (hpSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpf : HoldsOnEveryEtaleChart B S hS P (p ≫ f)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  have hsurjcomp := presheaf_surjective_isStableUnderComposition B S hS
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hG.exists_atlas
  obtain ⟨W, r, α, hcomm, hrSurj, hrEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS
      (isAlgebraicSpace_yoneda B S hS U) hG (p ≫ f) V q hqSurj hqEtale
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hF hG f).2
    ⟨W, V, r ≫ p, q, α,
      MorphismProperty.comp_mem _ r p hrEtale hpEtale, hqEtale,
      MorphismProperty.comp_mem _ r p hrSurj hpSurj, ?_,
      hpf W V r q α hrEtale hqEtale hcomm.symm⟩
  rw [Category.assoc, ← hcomm]

/-- Condition (4) of Stacks 03MM implies condition (1): if `P` holds on every étale chart of
every base change of `f` to an affine scheme over its target, then it holds on every étale
chart of `f`. -/
theorem holdsOnEveryEtaleChart_of_affine_baseChange
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPcomp : P.IsStableUnderComposition)
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ G),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        HoldsOnEveryEtaleChart B S hS P (pullback.fst g f)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  have := hPcomp
  intro U V p q a hp hq ha
  set T := BigFppfOver.toScheme B S hS with hT
  set aS := T.map a with haSdef
  have hqEtale : IsEtale B S hS q := (isEtale_iff_presheaf_of_yoneda B S hS q).2 hq
  have hpChart : HoldsOnEveryEtaleChart B S hS P p :=
    holdsOnEveryEtaleChart_of_presheaf_etale B S hS P hPetale hF p hp
  have hrestrict : ∀ W : (T.obj V).affineOpens, P (aS ∣_ W.1) := by
    intro W
    set Upre := aS ⁻¹ᵁ W.1 with hUpre
    let V' : BigFppfOver B S hS :=
      Over.mk (Y := B.obj (Scheme.size_lt_of_isOpenImmersion W.1.ι V.left.property))
        (ObjectProperty.homMk (W.1.ι ≫ V.hom.hom))
    let U' : BigFppfOver B S hS :=
      Over.mk (Y := B.obj (Scheme.size_lt_of_isOpenImmersion Upre.ι U.left.property))
        (ObjectProperty.homMk (Upre.ι ≫ U.hom.hom))
    let v : V' ⟶ V := Over.homMk (ObjectProperty.homMk W.1.ι)
    let i : U' ⟶ U := Over.homMk (ObjectProperty.homMk Upre.ι)
    have haS : aS ≫ V.hom.hom = U.hom.hom := congrArg (fun k ↦ k.hom) a.w
    let a' : U' ⟶ V' := Over.homMk (ObjectProperty.homMk (aS ∣_ W.1)) (by
      apply ObjectProperty.hom_ext
      change (aS ∣_ W.1) ≫ W.1.ι ≫ V.hom.hom = Upre.ι ≫ U.hom.hom
      rw [morphismRestrict_ι_assoc, haS])
    have hav : a' ≫ v = i ≫ a := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact morphismRestrict_ι aS W.1
    set g := yoneda.map v ≫ q with hg
    set p' := yoneda.map i ≫ p with hp'def
    have hw : yoneda.map a' ≫ g = p' ≫ f := by
      rw [hg, hp'def, ← Category.assoc, ← yoneda.map_comp, hav, yoneda.map_comp]
      simpa only [Category.assoc] using congrArg (fun k ↦ yoneda.map i ≫ k) ha
    set r : yoneda.obj U' ⟶ pullback g f := pullback.lift (yoneda.map a') p' hw with hr
    have hU' := isAlgebraicSpace_yoneda B S hS U'
    have hV' := isAlgebraicSpace_yoneda B S hS V'
    have hpb := isAlgebraicSpace_pullback B S hS g f hV' hF hG
    have hiEtale : IsEtale B S hS (yoneda.map i) := by
      refine (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map i)).2
        ((presheaf_yoneda_map_etale_iff B S hS i).2 ?_)
      change AlgebraicGeometry.Etale Upre.ι
      infer_instance
    have hvEtale : IsEtale B S hS (yoneda.map v) := by
      refine (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map v)).2
        ((presheaf_yoneda_map_etale_iff B S hS v).2 ?_)
      change AlgebraicGeometry.Etale W.1.ι
      infer_instance
    have hgEtale : IsEtale B S hS g := isEtale_comp B S hS hvEtale hqEtale
    have hp'Etale : IsEtale B S hS p' :=
      isEtale_comp B S hS hiEtale ((isEtale_iff_presheaf_of_yoneda B S hS p).2 hp)
    have hsndEtale : IsEtale B S hS (pullback.snd g f) :=
      isEtale_pullback_snd B S hS hF hG hV' g f hgEtale
    have hrEtale : IsEtale B S hS r :=
      isEtale_of_isEtale_over B S hS hU' hpb hF r p' (pullback.snd g f) hp'Etale hsndEtale
        (pullback.lift_snd _ _ _)
    have hrChart : HoldsOnEveryEtaleChart B S hS P r :=
      holdsOnEveryEtaleChart_of_isEtale_hom B S hS P hPetale hpb hrEtale
    have hgf : HoldsOnEveryEtaleChart B S hS P (pullback.fst g f) :=
      hf V' g (by change IsAffine W.1.toScheme; exact W.2)
    have htop := holdsOnEveryEtaleChart_comp B S hS P hP hU' hpb hV' r (pullback.fst g f)
      hrChart hgf
    rw [show r ≫ pullback.fst g f = yoneda.map a' from pullback.lift_fst _ _ _] at htop
    exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP a').mp htop
  refine (hP.iff_forall_exists_etale_neighborhood aS).mpr fun x ↦ ?_
  have hx : aS x ∈ (⨆ W : (T.obj V).affineOpens, W.1) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨W, hxW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, _, (aS ⁻¹ᵁ W.1).ι, W.1.ι, aS ∣_ W.1, ⟨x, hxW⟩,
    inferInstance, inferInstance, rfl, morphismRestrict_ι aS W.1, hrestrict W⟩

/-- Let `P` be a property of morphisms of schemes which is étale local on the source and target,
stable under composition and base change, and implied by étaleness. Then, for a morphism `f`
of algebraic spaces over `S`, the condition of Stacks 03MJ that `P` hold on every étale chart
of `f` can equivalently be tested at every point of the source, after base change to every
scheme or to every affine scheme or to one surjective étale chart of the target, on the
composite with one surjective étale chart of the source, in every — or in one surjective —
commuting square of étale charts, or over a pair of Zariski coverings. -/
theorem holdsOnEveryEtaleChart_tfae
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPcomp : P.IsStableUnderComposition)
    (hPbc : P.IsStableUnderBaseChange)
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      HoldsOnEveryEtaleChart B S hS P f,
      ∀ x : points B S hS X, ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
        ∃ x' : points B S hS U.toFunctor,
          pointsMap B S hS U.toFunctor U.ι x' = x ∧
            HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        HoldsOnEveryEtaleChart B S hS P (pullback.fst g f),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          HoldsOnEveryEtaleChart B S hS P (pullback.fst g f),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          HoldsOnEveryEtaleChart B S hS P (pullback.fst g f),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          HoldsOnEveryEtaleChart B S hS P (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          HoldsOnEveryEtaleChart B S hS P (yoneda.map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ HoldsOnEveryEtaleChart B S hS P (yoneda.map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, HoldsOnEveryEtaleChart B S hS P
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] := by
  have := hPcomp
  have := hPbc
  have h1iff2 : HoldsOnEveryEtaleChart B S hS P f ↔
      ∀ x : points B S hS X, ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
        ∃ x' : points B S hS U.toFunctor,
          pointsMap B S hS U.toFunctor U.ι x' = x ∧
            HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f) := by
    rw [holdsOnEveryEtaleChart_iff_forall_atPoint B S hS P hP hX hY f]
    refine forall_congr' fun x => ?_
    rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS P hP hX hY f x]
    exact ⟨fun ⟨U, hU, ⟨y, hy⟩, hq⟩ ↦ ⟨U, hU, y, hy, hq⟩,
      fun ⟨U, hU, y, hy, hq⟩ ↦ ⟨U, hU, ⟨y, hy⟩, hq⟩⟩
  have h1iff7 : HoldsOnEveryEtaleChart B S hS P f ↔
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          HoldsOnEveryEtaleChart B S hS P (yoneda.map a) := by
    constructor
    · intro hf U V p q a hp hq hcomm
      exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP a).mpr
        (hf U V p q a ((isEtale_iff_presheaf_of_yoneda B S hS p).1 hp)
          ((isEtale_iff_presheaf_of_yoneda B S hS q).1 hq) hcomm.symm)
    · intro h U V p q a hp hq hcomm
      exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP a).mp
        (h U V p q a ((isEtale_iff_presheaf_of_yoneda B S hS p).2 hp)
          ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hq) hcomm.symm)
  have h1iff8 : HoldsOnEveryEtaleChart B S hS P f ↔
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧
            HoldsOnEveryEtaleChart B S hS P (yoneda.map a) := by
    constructor
    · intro hf
      obtain ⟨U, V, p, q, a, hp, hq, hs, hcomm, hPa⟩ :=
        (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f).mp hf
      exact ⟨U, V, p, q, a, (isEtale_iff_presheaf_of_yoneda B S hS p).2 hp,
        (isEtale_iff_presheaf_of_yoneda B S hS q).2 hq,
        (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hs, hcomm.symm,
        (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP a).mpr hPa⟩
    · rintro ⟨U, V, p, q, a, hp, hq, hs, hcomm, hPa⟩
      refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f).mpr
        ⟨U, V, p, q, a, (isEtale_iff_presheaf_of_yoneda B S hS p).1 hp,
          (isEtale_iff_presheaf_of_yoneda B S hS q).1 hq,
          (surjective_iff_surjective_pointsMap B S hS X hX U p).mpr hs, hcomm.symm,
          (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP a).mp hPa⟩
  have h1to3 : HoldsOnEveryEtaleChart B S hS P f →
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        HoldsOnEveryEtaleChart B S hS P (pullback.fst g f) := fun hf Z g ↦
    holdsOnEveryEtaleChart_pullback_fst_of_isAlgebraicSpace B S hS P hP hPbc hX hY
      (isAlgebraicSpace_yoneda B S hS Z) g f hf
  have h3to5 : (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        HoldsOnEveryEtaleChart B S hS P (pullback.fst g f)) →
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          HoldsOnEveryEtaleChart B S hS P (pullback.fst g f) := by
    intro h
    obtain ⟨V, g, hs, he⟩ := hY.exists_atlas
    exact ⟨V, g, (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hs,
      (isEtale_iff_presheaf_of_yoneda B S hS g).2 he, h V g⟩
  have h5to8 : (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          HoldsOnEveryEtaleChart B S hS P (pullback.fst g f)) →
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧
            HoldsOnEveryEtaleChart B S hS P (yoneda.map a) := by
    rintro ⟨V, q, hqSurj, hqEtale, hbase⟩
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let V' : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
    let q' : V' ⟶ Y' := ObjectProperty.homMk q
    let f' : X' ⟶ Y' := ObjectProperty.homMk f
    let W : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS q' f'
    let fst : W ⟶ V' := ObjectProperty.homMk (pullback.fst q f)
    let snd : W ⟶ X' := ObjectProperty.homMk (pullback.snd q f)
    have hsq : IsPullback fst snd q' f' :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS q' f'
    obtain ⟨U, t, htSurj, htEtale⟩ := W.property.exists_atlas
    have htChart := holdsOnEveryEtaleChart_of_presheaf_etale B S hS P hPetale W.property t htEtale
    have hsndEtale : IsEtale B S hS snd.hom :=
      isEtale_of_isPullback B S hS fst snd q' f' hsq hqEtale
    set a : U ⟶ V := yoneda.preimage (t ≫ fst.hom) with hadef
    have ha : yoneda.map a = t ≫ fst.hom := yoneda.map_preimage _
    have htop : HoldsOnEveryEtaleChart B S hS P (yoneda.map a) := by
      rw [ha]
      exact holdsOnEveryEtaleChart_comp B S hS P hP (isAlgebraicSpace_yoneda B S hS U)
        W.property (isAlgebraicSpace_yoneda B S hS V) t fst.hom htChart hbase
    have hQsurj := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hsndSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) snd.hom := by
      refine hQsurj.of_isPullback (IsPullback.of_hasPullback q f) ?_
      exact (surjective_iff_surjective_pointsMap B S hS Y hY V q).mpr hqSurj
    have hQsurjcomp := presheaf_surjective_isStableUnderComposition B S hS
    have hsourceSurj : IsSurjective B S hS (t ≫ snd.hom) := by
      refine (surjective_iff_surjective_pointsMap B S hS X hX U (t ≫ snd.hom)).mp ?_
      exact MorphismProperty.comp_mem _ t snd.hom htSurj hsndSurj
    have hsourceEtale : IsEtale B S hS (t ≫ snd.hom) :=
      isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS t).2 htEtale) hsndEtale
    refine ⟨U, V, t ≫ snd.hom, q, a, hsourceEtale,
      hqEtale, hsourceSurj, ?_, htop⟩
    have hw : snd.hom ≫ f = fst.hom ≫ q := by
      simpa [q', f', Y'] using congrArg (fun k ↦ k.hom) hsq.w.symm
    rw [ha, Category.assoc, hw, Category.assoc]
  have h1to6 : HoldsOnEveryEtaleChart B S hS P f →
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          HoldsOnEveryEtaleChart B S hS P (p ≫ f) := by
    intro hf
    obtain ⟨U, p, hpSurj, hpEtale⟩ := hX.exists_atlas
    have hpChart := holdsOnEveryEtaleChart_of_presheaf_etale B S hS P hPetale hX p hpEtale
    exact ⟨U, p, (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hpSurj,
      (isEtale_iff_presheaf_of_yoneda B S hS p).2 hpEtale,
      holdsOnEveryEtaleChart_comp B S hS P hP (isAlgebraicSpace_yoneda B S hS U) hX hY p f
        hpChart hf⟩
  have h6to1 : (∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          HoldsOnEveryEtaleChart B S hS P (p ≫ f)) →
      HoldsOnEveryEtaleChart B S hS P f := by
    rintro ⟨U, p, hpSurj, hpEtale, hpf⟩
    exact holdsOnEveryEtaleChart_of_surjectiveEtale_source B S hS P hP hX hY f p
      ((surjective_iff_surjective_pointsMap B S hS X hX U p).mpr hpSurj)
      ((isEtale_iff_presheaf_of_yoneda B S hS p).1 hpEtale) hpf
  have h1to9 : HoldsOnEveryEtaleChart B S hS P f →
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, HoldsOnEveryEtaleChart B S hS P
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι) := by
    intro hf
    have hYtop := isOpenSubspace_top (B := B) (S := S) (hS := hS) (F := Y) hY
    have hPpull : IsAlgebraicSpace B S hS (pullback f (⊤ : Subfunctor Y).ι) :=
      isAlgebraicSpace_pullback B S hS f (⊤ : Subfunctor Y).ι hX hYtop.1 hY
    have hbase := holdsOnEveryEtaleChart_pullback_snd_of_isAlgebraicSpace B S hS P hP hPbc
      hX hY hYtop.1 f (⊤ : Subfunctor Y).ι hf
    exact ⟨PUnit.{u + 1}, fun _ ↦ ⊤, fun _ ↦ PUnit.{u + 1}, fun _ _ ↦ ⊤,
      isZariskiCover_top hY, fun _ ↦ isZariskiCover_top hPpull, fun _ _ ↦
        holdsOnEveryEtaleChart_top_ι_comp B S hS P hP hPcomp hPetale hPpull hYtop.1 hbase⟩
  have h9to2 : (∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, HoldsOnEveryEtaleChart B S hS P
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)) →
      ∀ x : points B S hS X, ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
        ∃ x' : points B S hS U.toFunctor,
          pointsMap B S hS U.toFunctor U.ι x' = x ∧
            HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f) := by
    rintro ⟨I, Yopen, J, Xopen, hYcover, hXcover, hlocal⟩ x
    have hYopens : ∀ i, IsOpenSubspace B S hS (Yopen i) := hYcover.1
    have hYpoints :=
      (isZariskiCover_iff_iUnion_points B S hS Y hY I Yopen hYopens).mp hYcover
    have hyCover : pointsMap B S hS X f x ∈
        ⋃ i, Set.range (pointsMap B S hS (Yopen i).toFunctor (Yopen i).ι) := by
      rw [hYpoints]; trivial
    obtain ⟨i, yi, hyi⟩ := Set.mem_iUnion.mp hyCover
    have hPi : IsAlgebraicSpace B S hS (pullback f (Yopen i).ι) :=
      isAlgebraicSpace_pullback B S hS f (Yopen i).ι hX (hYopens i).1 hY
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Yi' : AlgebraicSpaces B S hS := ⟨(Yopen i).toFunctor, (hYopens i).1⟩
    let W' : AlgebraicSpaces B S hS := ⟨pullback f (Yopen i).ι, hPi⟩
    let f₀ : X' ⟶ Y' := ObjectProperty.homMk f
    let g₀ : Yi' ⟶ Y' := ObjectProperty.homMk (Yopen i).ι
    have hpb : IsPullback (ObjectProperty.homMk (pullback.fst f (Yopen i).ι) : W' ⟶ X')
        (ObjectProperty.homMk (pullback.snd f (Yopen i).ι) : W' ⟶ Yi') f₀ g₀ :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS f₀ g₀
    obtain ⟨w, hwp, -⟩ := exists_point_of_isPullback B S hS hpb x yi hyi.symm
    have hXicover := hXcover i
    have hXipoints := (isZariskiCover_iff_iUnion_points B S hS
      (pullback f (Yopen i).ι) hPi (J i) (Xopen i) hXicover.1).mp hXicover
    have hwCover : w ∈ ⋃ j, Set.range
        (pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι) := by
      rw [hXipoints]; trivial
    obtain ⟨j, w', hwj⟩ := Set.mem_iUnion.mp hwCover
    have hXi : IsOpenSubspace B S hS (Xopen i j) := hXicover.1 j
    set r : (Xopen i j).toFunctor ⟶ X := (Xopen i j).ι ≫ pullback.fst f (Yopen i).ι with hrdef
    have hQbc := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hQcomp := MorphismProperty.relative_isStableUnderComposition
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hfstOpen : IsOpenImmersion B S hS (pullback.fst f (Yopen i).ι) :=
      hQbc.of_isPullback (IsPullback.of_hasPullback f (Yopen i).ι).flip (hYopens i).2
    have hrOpen : IsOpenImmersion B S hS r :=
      MorphismProperty.comp_mem _ (Xopen i j).ι (pullback.fst f (Yopen i).ι) hXi.2 hfstOpen
    have _ : Mono r := mono_of_presheaf_isOpenImmersion hrOpen
    have hROpen : IsOpenSubspace B S hS (Subfunctor.range r) :=
      isOpenSubspace_range_of_open B S hS r hXi.1 hrOpen
    have hYiChart : HoldsOnEveryEtaleChart B S hS P (Yopen i).ι :=
      holdsOnEveryEtaleChart_of_isEtale_hom B S hS P hPetale hY
        (isEtale_ι_of_isOpenSubspace (hYopens i))
    have hXiTarget : HoldsOnEveryEtaleChart B S hS P
        ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι ≫ (Yopen i).ι) := by
      have hcomp := holdsOnEveryEtaleChart_comp B S hS P hP hXi.1 (hYopens i).1 hY
        ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι) (Yopen i).ι (hlocal i j) hYiChart
      simpa only [Category.assoc] using hcomp
    have hrTarget : r ≫ f =
        (Xopen i j).ι ≫ pullback.snd f (Yopen i).ι ≫ (Yopen i).ι := by
      rw [hrdef, Category.assoc, pullback.condition]
    have hgR : Subfunctor.toRange r ≫ (Subfunctor.range r).ι = r := Subfunctor.toRange_ι r
    have hinvR : (asIso (Subfunctor.toRange r)).inv ≫ r = (Subfunctor.range r).ι :=
      (Iso.inv_comp_eq _).2 hgR.symm
    have heChart := holdsOnEveryEtaleChart_of_isIso B S hS P hPetale hXi.1
      (asIso (Subfunctor.toRange r)).inv
    have hRlocal : HoldsOnEveryEtaleChart B S hS P ((Subfunctor.range r).ι ≫ f) := by
      have hcomp := holdsOnEveryEtaleChart_comp B S hS P hP hROpen.1 hXi.1 hY
        (asIso (Subfunctor.toRange r)).inv (r ≫ f) heChart (hrTarget ▸ hXiTarget)
      simpa only [← Category.assoc, hinvR] using hcomp
    refine ⟨Subfunctor.range r, hROpen,
      pointsMap B S hS (Xopen i j).toFunctor (Subfunctor.toRange r) w', ?_, hRlocal⟩
    calc pointsMap B S hS (Subfunctor.range r).toFunctor (Subfunctor.range r).ι
          (pointsMap B S hS (Xopen i j).toFunctor (Subfunctor.toRange r) w')
        = pointsMap B S hS (Xopen i j).toFunctor
            (Subfunctor.toRange r ≫ (Subfunctor.range r).ι) w' := by
          rw [pointsMap_comp]; rfl
      _ = pointsMap B S hS (Xopen i j).toFunctor r w' := by rw [hgR]
      _ = pointsMap B S hS (pullback f (Yopen i).ι) (pullback.fst f (Yopen i).ι)
            (pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι w') := by
          rw [hrdef, pointsMap_comp]; rfl
      _ = pointsMap B S hS (pullback f (Yopen i).ι) (pullback.fst f (Yopen i).ι) w := by
          rw [hwj]
      _ = x := hwp
  tfae_have 1 ↔ 2 := h1iff2
  tfae_have 1 → 3 := h1to3
  tfae_have 3 → 4 := fun h Z g _ ↦ h Z g
  tfae_have 4 → 1 :=
    holdsOnEveryEtaleChart_of_affine_baseChange B S hS P hP hPcomp hPetale hX hY f
  tfae_have 3 → 5 := h3to5
  tfae_have 5 → 8 := h5to8
  tfae_have 8 → 1 := h1iff8.mpr
  tfae_have 1 → 6 := h1to6
  tfae_have 6 → 1 := h6to1
  tfae_have 1 ↔ 7 := h1iff7
  tfae_have 1 → 8 := h1iff8.mp
  tfae_have 1 → 9 := h1to9
  tfae_have 9 → 2 := h9to2
  tfae_finish

/-! ### Zariski locality on the target of the every-chart condition -/

/-- The base change of `f` along a composite `n ≫ c` and the base change along `n` of the base
change of `f` along `c` are two fibre products of the same cospan, so the every-chart condition
holds of the one exactly when it holds of the other. -/
theorem holdsOnEveryEtaleChart_pullback_snd_comp_iff
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPcomp : P.IsStableUnderComposition)
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {X Y C A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hC : IsAlgebraicSpace B S hS C) (hA : IsAlgebraicSpace B S hS A)
    (f : X ⟶ Y) (c : C ⟶ Y) (n : A ⟶ C) :
    HoldsOnEveryEtaleChart B S hS P (pullback.snd f (n ≫ c)) ↔
      HoldsOnEveryEtaleChart B S hS P (pullback.snd (pullback.snd f c) n) := by
  have := hPcomp
  have hPbL : IsAlgebraicSpace B S hS (pullback f (n ≫ c)) :=
    isAlgebraicSpace_pullback B S hS f (n ≫ c) hX hA hY
  have hPbC : IsAlgebraicSpace B S hS (pullback f c) :=
    isAlgebraicSpace_pullback B S hS f c hX hC hY
  have hPbR : IsAlgebraicSpace B S hS (pullback (pullback.snd f c) n) :=
    isAlgebraicSpace_pullback B S hS (pullback.snd f c) n hPbC hA hC
  have hsq := (IsPullback.of_hasPullback f (n ≫ c)).of_right'
    (IsPullback.of_hasPullback f c)
  have he := hsq.isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback (pullback.snd f c) n)
  set e := hsq.isoIsPullback _ _ (IsPullback.of_hasPullback (pullback.snd f c) n) with hedef
  have hiso := holdsOnEveryEtaleChart_of_isIso B S hS P hPetale hPbR e.hom
  have hisoinv := holdsOnEveryEtaleChart_of_isIso B S hS P hPetale hPbL e.inv
  constructor
  · intro h
    have hcomp := holdsOnEveryEtaleChart_comp B S hS P hP hPbR hPbL hA e.inv _ hisoinv h
    rwa [← he, Iso.inv_hom_id_assoc] at hcomp
  · intro h
    have hcomp := holdsOnEveryEtaleChart_comp B S hS P hP hPbL hPbR hA e.hom _ hiso h
    rwa [he] at hcomp

/-- The every-chart condition is Zariski local on the target: if `P` holds on every étale chart
of the base change of `f : X ⟶ Y` over each member of a Zariski covering of `Y`, then `P` holds
on every étale chart of `f`. -/
theorem holdsOnEveryEtaleChart_of_zariskiCover_target
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPcomp : P.IsStableUnderComposition)
    (hPbc : P.IsStableUnderBaseChange)
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} {U : I → Subfunctor Y} (hcov : IsZariskiCover B S hS I U)
    (hlocal : ∀ i, HoldsOnEveryEtaleChart B S hS P (pullback.snd f (U i).ι)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  have := hPcomp
  refine ((holdsOnEveryEtaleChart_tfae B S hS P hP hPcomp hPbc hPetale hX hY f).out 9 1).mp ?_
  refine ⟨I, U, fun _ ↦ PUnit.{u + 1}, fun _ _ ↦ ⊤, hcov, ?_, ?_⟩
  · exact fun i ↦ isZariskiCover_top
      (isAlgebraicSpace_pullback B S hS f (U i).ι hX (hcov.1 i).1 hY)
  · intro i _
    exact holdsOnEveryEtaleChart_top_ι_comp B S hS P hP hPcomp hPetale
      (isAlgebraicSpace_pullback B S hS f (U i).ι hX (hcov.1 i).1 hY) (hcov.1 i).1 (hlocal i)

/-- If `P` holds on every étale chart of the base change of `f : X ⟶ Y` over each member of a
family of open subspaces of `Y` whose point sets cover `Y`, then `P` holds on every étale chart
of `f`. -/
theorem holdsOnEveryEtaleChart_of_openSubspace_cover_target
    (hP : IsEtaleLocalOnSourceAndTarget P) (hPcomp : P.IsStableUnderComposition)
    (hPbc : P.IsStableUnderBaseChange)
    (hPetale : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), AlgebraicGeometry.Etale g → P g)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {I : Type u} (U : I → Subfunctor Y) (hU : ∀ i, IsOpenSubspace B S hS (U i))
    (hcover : ∀ y : points B S hS Y, ∃ i,
      y ∈ Set.range (pointsMap B S hS (U i).toFunctor (U i).ι))
    (hlocal : ∀ i, HoldsOnEveryEtaleChart B S hS P (pullback.snd f (U i).ι)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  exact holdsOnEveryEtaleChart_of_zariskiCover_target B S hS P hP hPcomp hPbc hPetale hX hY f
    (U := U) ((isZariskiCover_iff_iUnion_points B S hS Y hY I U hU).mpr
      (Set.eq_univ_iff_forall.mpr fun y ↦ Set.mem_iUnion.mpr (hcover y))) hlocal

/-! ### The nine criteria for flatness -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves on the big fppf site of `S` is flat exactly when it is flat at
every point of its source, in the germ sense of part (2) of [Stacks Project, Tag 03ML]. -/
theorem isFlat_iff_forall_isFlatAt (f : X ⟶ Y) :
    IsFlat B S hS f ↔ ∀ x : points B S hS X, IsFlatAt B S hS f x := by
  constructor
  · intro hf x c
    have : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map c.h) :=
      hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
    exact MorphismOfGerms.isFlat_ofSchemeHom _ _
  · intro hp U V a b h ha hb hab
    refine _root_.AlgebraicGeometry.Flat.of_stalkMap
      ((BigFppfOver.toScheme B S hS).map h) fun z ↦ ?_
    set p := schemePointRepresentative B S hS U z with hpdef
    let c : EtaleChartAtPoint B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
      { U := U, V := V, a := a, b := b, h := h, a_etale := ha, b_etale := hb
        comm := hab, representative := p
        point := IsLocalRing.closedPoint p.carrier, maps_to := rfl }
    have hpoint : c.sourcePoint B S hS = z := schemePointRepresentative_point B S hS U z
    have hflatAt := flatAt_of_isFlat_germ
      ((BigFppfOver.toScheme B S hS).map h) _ (hp _ c)
    change _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom z
    simpa only [hpoint] using hflatAt

/-- Nine criteria for a morphism of algebraic spaces over `S` to be flat: pointwise flatness,
flatness of every base change to a scheme or to an affine scheme or to one surjective étale chart
of the target, flatness of the composite with one surjective étale chart of the source, flatness
of the morphism of schemes in every — or in one surjective — commuting square of étale charts, or
over a pair of Zariski coverings. -/
@[stacks 03MM, stacks 08EW "the equivalence of (1) and (2): flat iff flat at every point of |X|"]
theorem isFlat_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE [
      IsFlat B S hS f,
      ∀ x : points B S hS X, IsFlatAt B S hS f x,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsFlat B S hS (pullback.fst g f),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) → IsFlat B S hS (pullback.fst g f),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧ IsFlat B S hS (pullback.fst g f),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧ IsFlat B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          IsFlat B S hS (yoneda.map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsFlat B S hS (yoneda.map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsFlat B S hS ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] := by
  have hgen := holdsOnEveryEtaleChart_tfae B S hS (@_root_.AlgebraicGeometry.Flat.{u})
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget inferInstance inferInstance
    (fun _ hg ↦ have := hg; inferInstance) hX hY f
  tfae_have 1 ↔ 2 := isFlat_iff_forall_isFlatAt B S hS f
  tfae_have 1 ↔ 3 := hgen.out 1 3
  tfae_have 1 ↔ 4 := hgen.out 1 4
  tfae_have 1 ↔ 5 := hgen.out 1 5
  tfae_have 1 ↔ 6 := hgen.out 1 6
  tfae_have 1 ↔ 7 := hgen.out 1 7
  tfae_have 1 ↔ 8 := hgen.out 1 8
  tfae_have 1 ↔ 9 := hgen.out 1 9
  tfae_finish

/-! ### Flat morphisms locally of finite presentation are universally open -/

section UniversallyOpen

attribute [local instance] pointTopology

/-- A flat morphism of algebraic spaces over `S` which is locally of finite presentation is
universally open in the sense of Stacks 03Z2. -/
@[stacks 042S,
  ega "IV 2.4.6" "in particular clause",
  ega "IV 15.2.1" "flat+lfp ⇒ univ open",
  sga "3 XVI 2.1" "more general"]
theorem universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    UniversallyOpen B S hS f := by
  have hflatBC := ((isFlat_tfae B S hS hX hY f).out 1 3).mp hflat
  have hfpBC := ((holdsOnEveryEtaleChart_tfae B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    inferInstance inferInstance (fun _ hg ↦ have := hg; inferInstance)
    hX hY f).out 1 3).mp hfp
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  refine ((universallyOpen_tfae B S hS hX hY f).out 2 1).mp ?_
  intro T g
  have hQ : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
  obtain ⟨U, a, haSurj, haEtale⟩ := hQ.exists_atlas
  obtain ⟨h, hh⟩ : ∃ h : U ⟶ T, yoneda.map h = a ≫ pullback.fst g f :=
    ⟨yoneda.preimage (a ≫ pullback.fst g f), by simp⟩
  have hcomm : yoneda.map h ≫ 𝟙 (yoneda.obj T) = a ≫ pullback.fst g f := by
    rw [Category.comp_id, hh]
  have hidEtale := hmulEtale.id_mem (yoneda.obj T)
  have : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map h) :=
    hflatBC T g U T a (𝟙 (yoneda.obj T)) h haEtale hidEtale hcomm
  have : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map h) :=
    hfpBC T g U T a (𝟙 (yoneda.obj T)) h haEtale hidEtale hcomm
  have : _root_.AlgebraicGeometry.UniversallyOpen
      ((BigFppfOver.toScheme B S hS).map h) := inferInstance
  have hhOpen : IsOpenMap (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) :=
    (isOpenMap_pointsMap_yoneda_iff B S hS h).mpr
      (Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map h))
  have hfactor : pointsMap B S hS (pullback g f) (pullback.fst g f) ∘
      pointsMap B S hS (yoneda.obj U) a =
      pointsMap B S hS (yoneda.obj U) (yoneda.map h) := by
    rw [hh, pointsMap_comp]
  refine IsOpenMap.of_comp (continuous_pointsMap B S hS a)
    ((surjective_iff_surjective_pointsMap B S hS (pullback g f) hQ U a).mp haSurj) ?_
  rwa [hfactor]

/-- A syntomic morphism of algebraic spaces over `S` is universally open in the sense of
Stacks 03Z2. -/
@[stacks 0DF0]
theorem universallyOpen_of_isSyntomic
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsSyntomic B S hS f) : UniversallyOpen B S hS f :=
  universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS hX hY f
    (isFlat_of_isSyntomic B S hS hf) (isLocallyOfFinitePresentation_of_isSyntomic B S hS hf)

end UniversallyOpen

end AlgebraicGeometry.Space

end
