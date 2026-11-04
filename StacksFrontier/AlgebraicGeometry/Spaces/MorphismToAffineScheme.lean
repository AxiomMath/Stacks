module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction

/-!
# Morphisms from an algebraic space to an affine scheme

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, with `S`
terminal, and let `T` be an object of the site whose underlying scheme is affine.  A morphism
of algebraic spaces `X ⟶ T` is determined by, and may be built from, a single ring
homomorphism `Γ(T, 𝒪_T) ⟶ Γ(X, 𝒪_X)`, where the global functions of `X` are the compatible
families of regular functions on its étale scheme charts.

## Main results

* `AlgebraicGeometry.Space.morphismToAffineEquiv`: **Stacks 05Z1**, the bijection between
  morphisms of algebraic spaces `X ⟶ T` and ring homomorphisms
  `Γ(T, 𝒪_T) →+* Γ(X, 𝒪_X)`, together with the specification that its forward map is pullback
  of regular functions on every étale scheme chart of `X`.
* `AlgebraicGeometry.Space.pullbackToGlobalFunctions` is that forward map, and
  `AlgebraicGeometry.Space.affineMapOfGlobalHom` constructs the morphism of algebraic spaces
  attached to a ring homomorphism.
* `AlgebraicGeometry.Space.exists_atlasKernelPair`: an algebraic space has a surjective étale
  scheme atlas whose kernel pair is again representable, with étale projections.

## Implementation notes

The specification in `AlgebraicGeometry.Space.morphismToAffineEquiv` is what makes the
bijection *canonical* rather than an arbitrary one: it pins the forward map to be pullback of
functions on every chart.  Both directions are then determined, and the two round trips are
`AlgebraicGeometry.Space.affineMapOfPullback` and
`AlgebraicGeometry.Space.pullback_affineMapConstruction`.

A ring homomorphism `φ` is turned into a morphism of algebraic spaces by descent along a
surjective étale atlas.  On a single chart, `AlgebraicGeometry.Space.affineChartMap` is the
morphism of schemes with prescribed action on global functions supplied by the
`Γ`–`Spec` adjunction, and `AlgebraicGeometry.Space.affineChartMap_comp` says that these are
compatible with morphisms of charts; applied to the two projections of the kernel pair of the
atlas this is exactly the cocone condition that Stacks 0262, part (3) descends.  The
intermediate data is bundled in `AlgebraicGeometry.Space.AffineMapConstruction` so that the
descended morphism is produced together with the chart formula characterising it, which is
what `AlgebraicGeometry.Space.affineMapConstruction_chart` propagates to *every* chart — by
étale descent along the covering of a chart by its fibre product with the atlas.

The hypothesis that `S` is terminal is used to turn a morphism of the underlying schemes of
two objects of the site into a morphism *over* `S`, in
`AlgebraicGeometry.Space.overMapOfSchemeHom`.

## References

* [Stacks Project, Lemma 66.6.6 (Tag 05Z1)](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of a global regular function of a presheaf on the big fppf site of `S` to one
of its étale scheme charts. -/
def globalFunctionsChartRestriction (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) :
    globalFunctions B S hS X.1 →+*
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V), ⊤) := by
  let F := structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat RingCat
  change _ →+* ↑(F.obj (op V))
  exact (Pi.evalRingHom (fun j => ↑(F.obj j)) (op V)).comp (RingCat.sectionsSubring F).subtype

/-- Restriction of global functions to the étale charts is compatible with pullback along a
morphism of charts. -/
lemma globalFunctionsChartRestriction_naturality (X : AlgebraicSpaces B S hS)
    {V W : SmallEtale B S hS X.1} (g : V ⟶ W) :
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map g)))) ∘
      globalFunctionsChartRestriction B S hS X W =
        globalFunctionsChartRestriction B S hS X V := by
  funext s
  let F := structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat RingCat
  show F.map g.op (s.1 (op W)) = s.1 (op V)
  have hs : Functor.sections (F ⋙ forget RingCat) s.1 := s.2
  exact hs g.op

/-- The morphism of schemes from an étale chart of `X` to an affine object `T` of the site
whose action on global functions is the prescribed homomorphism `φ` followed by restriction to
the chart.  It exists and is unique by the `Γ`–`Spec` adjunction. -/
def affineChartMap (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (_hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V) ⟶
      (BigFppfOver.toScheme B S hS).obj T :=
  letI U := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)
  letI R := (BigFppfOver.toScheme B S hS).obj T
  ΓSpec.adjunction.homEquiv U (op (CommRingCat.of Γ(R, ⊤)))
      (CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp φ)).op ≫
    (Scheme.isoSpec R).inv

/-- The action of `AlgebraicGeometry.Space.affineChartMap` on global functions is the
prescribed homomorphism followed by restriction to the chart. -/
lemma affineChartMap_appTop (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (V : SmallEtale B S hS X.1) :
    Scheme.Hom.appTop (affineChartMap B S hS X T hterminal φ V) =
      CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp φ) := by
  let U := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)
  let R := (BigFppfOver.toScheme B S hS).obj T
  show Scheme.Hom.appTop
    (ΓSpec.adjunction.homEquiv U (op (CommRingCat.of Γ(R, ⊤)))
      (CommRingCat.ofHom ((globalFunctionsChartRestriction B S hS X V).comp φ)).op ≫
      (Scheme.isoSpec R).inv) = _
  rw [Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop,
    ΓSpec_adjunction_homEquiv_eq]
  show (Scheme.ΓSpecIso Γ(R, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(R, ⊤)).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

/-- A morphism of the underlying schemes of two objects of the big fppf site of `S`, read as a
morphism of the site.  The triangle over `S` commutes because `S` is terminal. -/
def overMapOfSchemeHom (hterminal : IsTerminal S) (U T : BigFppfOver B S hS)
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj T) : U ⟶ T :=
  Over.homMk (B.inclusion.preimage g)
    (B.inclusion.map_injective (hterminal.hom_ext _ _))

/-- The chart morphisms of `AlgebraicGeometry.Space.affineChartMap` are compatible with
morphisms of charts: both sides act on global functions by the prescribed homomorphism
followed by restriction, and a morphism into an affine scheme is determined by its action on
global functions. -/
lemma affineChartMap_comp (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    {V W : SmallEtale B S hS X.1} (g : V ⟶ W) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g) ≫
        affineChartMap B S hS X T hterminal φ W =
      affineChartMap B S hS X T hterminal φ V := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, affineChartMap_appTop, affineChartMap_appTop]
  apply CommRingCat.hom_ext
  ext s
  exact congrFun (globalFunctionsChartRestriction_naturality B S hS X g) (φ s)

/-- An étale chart of `X`, read as an object of the small étale site. -/
def chartFromEtaleHom (X : AlgebraicSpaces B S hS) (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ X.1)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f) :
    SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk f, hf⟩

/-- Precomposing an étale chart with an étale morphism of the site gives an étale chart. -/
theorem chart_preimage_etale (X : AlgebraicSpaces B S hS) {U V : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ X.1)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (g : V ⟶ U)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) g) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map g ≫ f) := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hbc : P.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have hsc : P.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have hcomp : (P.relative yoneda).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  exact (P.relative yoneda).comp_mem (yoneda.map g) f (MorphismProperty.relative_map hg) hf

/-- An algebraic space has a surjective étale scheme atlas whose kernel pair is again
representable by an object of the site, with étale projections. -/
theorem exists_atlasKernelPair (X : AlgebraicSpaces B S hS) :
    ∃ (U R : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X.1) (t s : R ⟶ U),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f ∧
      IsPullback (yoneda.map t) (yoneda.map s) f f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) t ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) s := by
  obtain ⟨U, f, hsurj, hetale⟩ := X.property.exists_atlas
  let hrep : yoneda.relativelyRepresentable f := hetale.1
  let t := hrep.fst' f
  let s := hrep.snd f
  have hpb : IsPullback (yoneda.map t) (yoneda.map s) f f := hrep.isPullback' f
  exact ⟨U, hrep.pullback f, f, t, s, hsurj, hetale, hpb,
    hetale.2 f (yoneda.map s) t hpb.flip, hetale.2 f (hrep.fst f) s (hrep.isPullback f)⟩

/-- A choice of surjective étale scheme atlas of an algebraic space together with its kernel
pair, bundled. -/
structure AtlasKernelPairData (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) where
  /-- The object of the site carrying the atlas. -/
  U : BigFppfOver B S hS
  /-- The object of the site representing the kernel pair. -/
  R : BigFppfOver B S hS
  /-- The atlas. -/
  f : yoneda.obj U ⟶ X.1
  /-- The first projection of the kernel pair. -/
  t : R ⟶ U
  /-- The second projection of the kernel pair. -/
  s : R ⟶ U
  /-- The atlas is surjective after every representable base change. -/
  surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  /-- The atlas is étale after every representable base change. -/
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  /-- The two projections exhibit `R` as the kernel pair of the atlas. -/
  pullback : IsPullback (yoneda.map t) (yoneda.map s) f f
  /-- The first projection is étale. -/
  tEtale : MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) t
  /-- The second projection is étale. -/
  sEtale : MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) s

/-- A chosen surjective étale atlas with its kernel pair, from
`AlgebraicGeometry.Space.exists_atlasKernelPair`. -/
def chosenAtlasKernelPair (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) : AtlasKernelPairData B S hS X := by
  choose U R f t s h using exists_atlasKernelPair B S hS X
  obtain ⟨hsurj, hetale, hpb, htEtale, hsEtale⟩ := h
  exact ⟨U, R, f, t, s, hsurj, hetale, hpb, htEtale, hsEtale⟩

/-- The morphism of algebraic spaces attached to a ring homomorphism on global functions,
together with the data witnessing that it is the descent of
`AlgebraicGeometry.Space.affineChartMap` along a chosen atlas. -/
structure AffineMapConstruction (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS) (hterminal : IsTerminal S)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1) where
  /-- The atlas along which the morphism is descended. -/
  atlas : AtlasKernelPairData B S hS X
  /-- The descended morphism of algebraic spaces. -/
  map : X ⟶ schemeSpace T
  /-- The morphism of the site from the atlas to `T`. -/
  chartMapOver : atlas.U ⟶ T
  /-- The underlying morphism of schemes. -/
  chartMapScheme : (BigFppfOver.toScheme B S hS).obj atlas.U ⟶
    (BigFppfOver.toScheme B S hS).obj T
  /-- The morphism of the site underlies the morphism of schemes. -/
  chartMapOver_spec : (BigFppfOver.toScheme B S hS).map chartMapOver = chartMapScheme
  /-- The morphism of schemes is the chart morphism prescribed by `φ`. -/
  chartMapScheme_spec : chartMapScheme = affineChartMap B S hS X T hterminal φ
    (chartFromEtaleHom B S hS X atlas.U atlas.f atlas.etale)
  /-- The descended morphism restricts on the atlas to the chart morphism. -/
  factor : atlas.f ≫ map.hom = yoneda.map chartMapOver

/-- Pullback of regular functions along a morphism from an algebraic space to an object of the
site: a global function on the target is sent to the family of its pullbacks on the étale
charts of the source. -/
def pullbackToGlobalFunctions (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace T) :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1 := by
  let chartMapToT := fun (V : SmallEtale B S hS X.1) => yoneda.preimage (V.1.hom ≫ f.hom)
  let P : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+*
      ∀ j : (SmallEtale B S hS X.1)ᵒᵖ,
        Γ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj j.unop), ⊤) :=
    RingHom.pi fun j => (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (chartMapToT j.unop)))).hom
  refine P.codRestrict (RingCat.sectionsSubring
    (structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat RingCat)) ?_
  intro r
  change Functor.sections
    (structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat RingCat ⋙ forget RingCat) (P r)
  intro j j' g
  let V := j'.unop
  let W := j.unop
  let gOver := (SmallEtale.toOver B S hS X.1).map g.unop
  have htriangle : yoneda.map gOver ≫ W.1.hom = V.1.hom := g.unop.hom.w
  have hp : gOver ≫ chartMapToT W = chartMapToT V := by
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda.map_preimage]
    change yoneda.map gOver ≫ (W.1.hom ≫ f.hom) = _
    rw [← Category.assoc, htriangle, yoneda.map_preimage]
    rfl
  have hscheme := congrArg (BigFppfOver.toScheme B S hS).map hp
  rw [Functor.map_comp] at hscheme
  change Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map gOver))
      ((Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (chartMapToT W)))).hom r) =
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (chartMapToT V)))).hom r
  have hschemeOp := congrArg Quiver.Hom.op hscheme
  rw [op_comp] at hschemeOp
  have hGamma := congrArg Scheme.Γ.map hschemeOp
  rw [Functor.map_comp] at hGamma
  exact congrArg (fun k => k.hom' r) hGamma

/-- The atlas of a presentation of an algebraic space, read as an object of its small étale
site. -/
abbrev atlasChart (X : AlgebraicSpaces B S hS) (D : AtlasKernelPairData B S hS X) :
    SmallEtale B S hS X.1 :=
  chartFromEtaleHom B S hS X D.U D.f D.etale

/-- The morphism of the site from the atlas of a presentation `D` to an affine object `T`
prescribed by a ring homomorphism `φ` on global functions. -/
def atlasMapOver (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (D : AtlasKernelPairData B S hS X) : D.U ⟶ T :=
  overMapOfSchemeHom B S hS hterminal D.U T
    (affineChartMap B S hS X T hterminal φ (atlasChart B S hS X D))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.atlasMapOver` is the chart
morphism prescribed by `φ`. -/
lemma toScheme_map_atlasMapOver (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (D : AtlasKernelPairData B S hS X) :
    (BigFppfOver.toScheme B S hS).map (atlasMapOver B S hS X T hterminal φ D) =
      affineChartMap B S hS X T hterminal φ (atlasChart B S hS X D) := by
  dsimp [atlasMapOver, overMapOfSchemeHom]
  exact B.inclusion.map_preimage _

/-- The cocone condition: the morphism of the site prescribed by `φ` on the atlas identifies
the two projections of the kernel pair.

Both projections are morphisms of étale charts of `X`, so this is
`AlgebraicGeometry.Space.affineChartMap_comp` for each of them. -/
lemma atlasMapOver_comp_eq (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (D : AtlasKernelPairData B S hS X) :
    D.t ≫ atlasMapOver B S hS X T hterminal φ D =
      D.s ≫ atlasMapOver B S hS X T hterminal φ D := by
  let A := atlasChart B S hS X D
  let AC : SmallEtale B S hS X.1 :=
    chartFromEtaleHom B S hS X D.R (yoneda.map D.t ≫ D.f)
      (chart_preimage_etale B S hS X D.f D.etale D.t D.tEtale)
  let tC : AC ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk D.t rfl)
  let sC : AC ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk D.s D.pullback.w.symm)
  apply Functor.map_injective (BigFppfOver.toScheme B S hS)
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_atlasMapOver]
  exact (affineChartMap_comp B S hS X T hterminal φ tC).trans
    (affineChartMap_comp B S hS X T hterminal φ sC).symm

/-- **Stacks 05Z1**, the construction half: a ring homomorphism `Γ(T, 𝒪_T) ⟶ Γ(X, 𝒪_X)` is the
action on global functions of a morphism of algebraic spaces `X ⟶ T`.

The morphism is obtained by descending the chart morphism of
`AlgebraicGeometry.Space.affineChartMap` on a chosen surjective étale atlas along the
coequalizer presentation of Stacks 0262, part (3). -/
def affineMapOfGlobalHom (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1) :
    AffineMapConstruction B S hS X T hterminal φ := by
  let D := chosenAtlasKernelPair B S hS X
  let gOver : D.U ⟶ T := atlasMapOver B S hS X T hterminal φ D
  let J := BigFppfOver.topology B S hS
  let TF : Sheaf J (Type u) := ⟨yoneda.obj T, (isAlgebraicSpace_yoneda B S hS T).isSheaf⟩
  choose hRsh hUsh hc using isCoequalizer_of_surjectiveEtale B S hS D.f D.t D.s D.pullback
    X.property D.surjective D.etale
  let hc := Classical.choice hc
  let RF : Sheaf J (Type u) := ⟨yoneda.obj D.R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj D.U, hUsh⟩
  let FF : Sheaf J (Type u) := ⟨X.1, X.property.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map D.t⟩
  let tf : RF ⟶ UF := ⟨yoneda.map D.s⟩
  let ff : UF ⟶ FF := ⟨D.f⟩
  let k : UF ⟶ TF := ⟨yoneda.map gOver⟩
  have hw : sf ≫ k = tf ≫ k := by
    apply Sheaf.hom_ext
    change yoneda.map D.t ≫ yoneda.map gOver = yoneda.map D.s ≫ yoneda.map gOver
    rw [← Functor.map_comp, ← Functor.map_comp,
      atlasMapOver_comp_eq B S hS X T hterminal φ D]
  let c : Cofork sf tf := Cofork.ofπ k hw
  let d := hc.desc c
  have hfac : ff ≫ d = k := by simpa [d, c] using hc.fac c WalkingParallelPair.one
  exact ⟨D, ObjectProperty.homMk d.hom, gOver,
    affineChartMap B S hS X T hterminal φ (atlasChart B S hS X D),
    toScheme_map_atlasMapOver B S hS X T hterminal φ D, rfl, congrArg (fun q => q.hom) hfac⟩

/-- The morphism of algebraic spaces descended in
`AlgebraicGeometry.Space.affineMapOfGlobalHom` restricts to the prescribed chart morphism on
*every* étale chart, not only on the atlas it was built from.

A chart is covered by its fibre product with the atlas, and the projection to the chart is
surjective and étale, hence an epimorphism of schemes; the two morphisms therefore agree. -/
lemma affineMapConstruction_chart (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (C : AffineMapConstruction B S hS X T hterminal φ) (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ C.map.hom)) =
      affineChartMap B S hS X T hterminal φ V := by
  let D := C.atlas
  let hrep := D.etale.1
  let i := hrep.fst' V.1.hom
  let j := hrep.snd V.1.hom
  let hp := hrep.isPullback' V.1.hom
  have hjEtale := D.etale.property V.1.hom (yoneda.map i) j hp
  let Wchart : SmallEtale B S hS X.1 :=
    chartFromEtaleHom B S hS X (hrep.pullback V.1.hom) (yoneda.map j ≫ V.1.hom)
      (chart_preimage_etale B S hS X V.1.hom V.2 j hjEtale)
  let A : SmallEtale B S hS X.1 := chartFromEtaleHom B S hS X D.U D.f D.etale
  let iC : Wchart ⟶ A := ObjectProperty.homMk (CostructuredArrow.homMk i hp.w)
  let jC : Wchart ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk j rfl)
  let vMap := yoneda.preimage (V.1.hom ≫ C.map.hom)
  have hlocal : j ≫ vMap = i ≫ C.chartMapOver := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, yoneda.map_preimage]
    show yoneda.map j ≫ V.1.hom ≫ C.map.hom = yoneda.map i ≫ yoneda.map C.chartMapOver
    rw [← Category.assoc, ← hp.w, Category.assoc]
    exact congrArg (yoneda.map i ≫ ·) C.factor
  have hi' : (BigFppfOver.toScheme B S hS).map i ≫ C.chartMapScheme =
      affineChartMap B S hS X T hterminal φ Wchart := by
    rw [C.chartMapScheme_spec]
    exact affineChartMap_comp B S hS X T hterminal φ iC
  have hcomp : (BigFppfOver.toScheme B S hS).map j ≫
      (BigFppfOver.toScheme B S hS).map vMap =
      (BigFppfOver.toScheme B S hS).map j ≫ affineChartMap B S hS X T hterminal φ V := by
    refine (?_ : _ = _).trans (hi'.trans (affineChartMap_comp B S hS X T hterminal φ jC).symm)
    simpa only [Functor.map_comp, C.chartMapOver_spec] using
      congrArg (BigFppfOver.toScheme B S hS).map hlocal
  have : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    D.surjective.property V.1.hom (yoneda.map i) j hp
  have : Etale ((BigFppfOver.toScheme B S hS).map j) := hjEtale
  have : Epi ((BigFppfOver.toScheme B S hS).map j) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  exact (cancel_epi ((BigFppfOver.toScheme B S hS).map j)).1 hcomp

/-- Pullback of a global function along a morphism to an object of the site, read on a single
étale chart. -/
lemma pullbackToGlobalFunctions_apply_chart (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (f : X ⟶ schemeSpace T) (V : SmallEtale B S hS X.1)
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    ((pullbackToGlobalFunctions B S hS X T f) s).1 (op V) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (V.1.hom ≫ f.hom)))) s := rfl

/-- For a morphism of algebraic spaces to an affine object of the site, the chart morphism
prescribed by the pullback homomorphism on global functions is the restriction of the
morphism to that chart. -/
lemma affineChartMap_eq_pullback (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (f : X ⟶ schemeSpace T) (V : SmallEtale B S hS X.1) :
    affineChartMap B S hS X T hterminal (pullbackToGlobalFunctions B S hS X T f) V =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ f.hom)) := by
  apply ext_of_isAffine
  rw [affineChartMap_appTop]
  apply CommRingCat.hom_ext
  ext s
  rfl

/-- The morphism constructed from a ring homomorphism pulls global functions back to that
homomorphism. -/
lemma pullback_affineMapConstruction (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1) :
    pullbackToGlobalFunctions B S hS X T
        (affineMapOfGlobalHom B S hS X T hterminal φ).map = φ := by
  refine RingHom.ext fun s ↦ Subtype.ext (funext fun V ↦ ?_)
  rw [pullbackToGlobalFunctions_apply_chart, affineMapConstruction_chart B S hS X T hterminal φ
    (affineMapOfGlobalHom B S hS X T hterminal φ) V.unop]
  have hmap : Scheme.Γ.map (affineChartMap B S hS X T hterminal φ V.unop).op =
      CommRingCat.ofHom
        ((globalFunctionsChartRestriction B S hS X V.unop).comp φ) := by
    rw [Scheme.Γ_map_op]
    simpa only [Scheme.Γ_obj_op, BigFppfOver.toScheme, BigFppfOver.forget,
      BigFppfSite.inclusion, schemeBelowInclusion, Functor.comp_obj, Over.forget_obj,
      ObjectProperty.ι_obj] using affineChartMap_appTop B S hS X T hterminal φ V.unop
  exact congrArg (fun k => k.hom s) hmap

/-- A morphism of algebraic spaces to an affine object of the site is recovered from its
pullback homomorphism on global functions. -/
lemma affineMapOfPullback (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (f : X ⟶ schemeSpace T) :
    (affineMapOfGlobalHom B S hS X T hterminal
      (pullbackToGlobalFunctions B S hS X T f)).map = f := by
  let C := affineMapOfGlobalHom B S hS X T hterminal (pullbackToGlobalFunctions B S hS X T f)
  let D := C.atlas
  let A := chartFromEtaleHom B S hS X D.U D.f D.etale
  have hchart := affineMapConstruction_chart B S hS X T hterminal
    (pullbackToGlobalFunctions B S hS X T f) C A
  have hactual := affineChartMap_eq_pullback B S hS X T hterminal f A
  have hbase : D.f ≫ C.map.hom = D.f ≫ f.hom := by
    have hpre : yoneda.preimage (D.f ≫ C.map.hom) = yoneda.preimage (D.f ≫ f.hom) :=
      Functor.map_injective (BigFppfOver.toScheme B S hS) (hchart.trans hactual)
    have h := congrArg yoneda.map hpre
    rw [yoneda.map_preimage, yoneda.map_preimage] at h
    simpa [A, chartFromEtaleHom, schemeSpace] using h
  let J := BigFppfOver.topology B S hS
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS D.f D.t D.s D.pullback
    X.property D.surjective D.etale
  let UF : Sheaf J (Type u) := ⟨yoneda.obj D.U, hUsh⟩
  let FF : Sheaf J (Type u) := ⟨X.1, X.property.isSheaf⟩
  let TF : Sheaf J (Type u) := ⟨yoneda.obj T, (isAlgebraicSpace_yoneda B S hS T).isSheaf⟩
  let ff : UF ⟶ FF := ⟨D.f⟩
  have : Epi ff := Cofork.IsColimit.epi (Classical.choice hc)
  have hsheaf : ff ≫ (⟨C.map.hom⟩ : FF ⟶ TF) = ff ≫ (⟨f.hom⟩ : FF ⟶ TF) :=
    Sheaf.hom_ext hbase
  exact ObjectProperty.hom_ext _ (congrArg (fun q => q.hom) ((cancel_epi ff).1 hsheaf))

/-- **Stacks 05Z1.** Pullback of regular functions is a bijection between morphisms of
algebraic spaces `X ⟶ T` into an affine object of the site and ring homomorphisms
`Γ(T, 𝒪_T) →+* Γ(X, 𝒪_X)`.

The bijection is specified, not merely asserted: its forward map restricts on every étale
scheme chart of `X` to pullback of regular functions along the induced morphism of schemes. -/
@[stacks 05Z1, ega "II 1.2.7" "absolute case S=Spec ℤ", ega "I 2.2.4"]
def morphismToAffineEquiv (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hterminal : IsTerminal S) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    { e : (X ⟶ schemeSpace T) ≃
        (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1) //
      ∀ (f : X ⟶ schemeSpace T) (U : SmallEtale B S hS X.1)
        (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
        ((e f) s).1 (op U) = Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (U.1.hom ≫ f.hom)))) s } :=
  ⟨{ toFun := pullbackToGlobalFunctions B S hS X T
     invFun := fun φ => (affineMapOfGlobalHom B S hS X T hterminal φ).map
     left_inv := fun f => affineMapOfPullback B S hS X T hterminal f
     right_inv := fun φ => pullback_affineMapConstruction B S hS X T hterminal φ },
    fun f U s => pullbackToGlobalFunctions_apply_chart B S hS X T f U s⟩

end AlgebraicGeometry.Space

end
