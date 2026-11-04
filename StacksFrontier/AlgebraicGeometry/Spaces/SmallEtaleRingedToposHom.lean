module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The morphism of small étale ringed topoi of a morphism of algebraic spaces

Stacks 03G8 attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` a morphism
of the small étale *ringed* topoi of `X` and `Y`, in the sense of Stacks 01D3.  This file
assembles it out of the two halves that were built separately.

The geometric half is
`AlgebraicGeometry.Space.smallToposMorphismTypeU`
(`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleEssentiallySmall.lean`): the morphism of small
étale topoi of Stacks 03G2, part (3), at `Type u`, the universe at which a ringed topos declares
its underlying topos.  The structure-map half is
`AlgebraicGeometry.Space.structureSharp`
(`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean`): the homomorphism
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of sheaves of *rings* on the small étale site of `Y`.

Two things have to be reconciled.  First, the direct image of the geometric morphism must be the
direct image the structure map takes values in; it is, *on the nose*:
`(smallToposMorphismTypeU B S hS f).pushforward` and
`AlgebraicGeometry.Space.smallEtaleDirectImage B S hS f` are the same functor, both being the
spaces-étale direct image conjugated by the comparison equivalences of Stacks 03G1.  Second, a
`AlgebraicGeometry.RingedTopos` carries its structure sheaf in `Sheaf J CommRingCat`, whereas
the structure map is stated in `Sheaf J RingCat`, because that is what `SheafOfModules` consumes.
The passage between the two is *not* a cast and *not* a new commutativity proof: the transported
multiplication on the sections of the direct image is commutative by
`Stacks.Sheaves.ToposPullback.commRingSheaf_mul_comm`, which is already what
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf` is built from, and forgetting commutativity
is fully faithful on sheaves
(`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf`).  So the `CommRingCat`-valued
structure map is the preimage of the `RingCat`-valued one under a fully faithful functor, and
`AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp` records that it has the `RingCat`-valued
structure map underneath — which is what makes the chart formula
`AlgebraicGeometry.Space.chartProjection_structureMapApp` compute it.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram` and `AlgebraicGeometry.Space.FMap` are Stacks 03G3: a
  commutative diagram of étale scheme charts over a morphism of algebraic spaces, and a map of
  sections along such a morphism.
* `AlgebraicGeometry.Space.smallEtaleRingedTopos` is the small étale ringed topos of an
  algebraic space.
* `AlgebraicGeometry.Space.structureSharpCommRing` is the structure map of a morphism of
  algebraic spaces as a homomorphism of sheaves of commutative rings, and
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is the morphism of ringed topoi it and the
  geometric morphism make up.
* `AlgebraicGeometry.Space.IsChartCorrespondence` is the sectionwise characterization, through
  the geometric comparison, of a bijection between `f`-maps and homomorphisms into the direct
  image.
* `AlgebraicGeometry.Space.IsCartesianComposition` is the corresponding characterization, again
  through the geometric comparison, of a comparison of the direct images of sheaves of
  commutative rings of a composite as the one induced by cartesian composition, and
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` is that comparison.
* `AlgebraicGeometry.Space.schemeChartToOver` presents the small étale site of a representable
  algebraic space as a site of schemes over the representing scheme.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward`: the underlying geometric
  direct image is the spaces-étale one, through the comparison equivalences of Stacks 03G1.
* `AlgebraicGeometry.Space.forgetCommRingSheaf_map_fSharp`: the structure map of the morphism of
  ringed topoi is `AlgebraicGeometry.Space.structureSharp` with commutativity forgotten.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` and
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing`: for a representable
  morphism the direct image of sheaves of sets, and of sheaves of commutative rings, is base
  change of étale scheme charts; the second is the first with the ring operations carried
  along, which is
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing_forget`.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso_isCartesianComposition`: the
  comparison of the direct images of sheaves of commutative rings of a composite is induced by
  cartesian composition.

## Implementation notes

`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU` and
`AlgebraicGeometry.Space.smallBaseChange_pushforward_comparisonTypeU` are the `Type u`
instantiations of two isomorphisms that
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleToposMorphism.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChange.lean` state at `Type (u + 1)`, the
universe of the sites.  The sheaf universe plays no role in either proof; the duplication is
only because those two files are universe-pinned and are not edited here.

The chart correspondence asserts that `f`-maps are exactly homomorphisms into the direct image.
`AlgebraicGeometry.Space.IsChartCorrespondence` states what such a bijection has to satisfy,
and the bijection itself is constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartCorrespondenceRingUniverse.lean` as
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse`, with
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_chart` showing that it satisfies
`IsChartCorrespondence`.  The construction identifies the index category of
`AlgebraicGeometry.Space.chartIsLimit` — the étale scheme charts of `X` above `X ×_Y V` — with
the chart diagrams over `V`, by the cartesian universal property
`(AlgebraicGeometry.Space.spacesBaseChange B S hS f).isPullback`; the pointwise-limit apparatus
it needs is already stated for an arbitrary sheaf, rather than only the structure sheaf, by
`AlgebraicGeometry.Space.ranProj`, `ranIsLimit` and `spacesEtale_section_ext` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`.

The *geometric* half of the composition law is here.
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` is Stacks 03G2, part (3), at the
universe of the structure rings, and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` carries it to sheaves of
commutative rings; it is induced by cartesian composition in the sense of
`AlgebraicGeometry.Space.IsCartesianComposition`.  The composition law for the structure map
itself, `(g ∘ f)♯` followed by that comparison versus `(g ≫ f)♯`, is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`.  It does not go through
the chart correspondence: rather than comparing chart projections and identifying an iterated
limit with a single one, it uses the injectivity of the unit of the adjunction, so it needs
neither the chart correspondence of Stacks 03G8 nor any refinement of charts.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

/-! ### Transporting the inverse image of sheaves of commutative rings along a transformation

`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans`
(`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean`) transports the inverse image of
a sheaf of *rings* along a natural transformation of the two finite-product-preserving functors
of sheaves of sets.  The three declarations below are the same for sheaves of *commutative*
rings, which is what a ringed topos in the sense of Stacks 01D3 carries; they belong with
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposCommRingImageAdjunction.lean`, and are here
only to keep that file — which has many consumers — untouched.
-/

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section Transport

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  (O : Sheaf K CommRingCat.{ww'})

/-- On underlying sheaves of sets, the isomorphism of inverse-image functors of sheaves of
commutative rings induced by a natural isomorphism of finite-product-preserving functors of
sheaves of sets *is* that natural isomorphism.

This is `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso_hom_app`
followed by `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIsoOfNatIso_hom_forget`, both
proved in `StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/CommRingPullback.lean`
together with the transport itself. -/
@[simp]
lemma underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom (θ : Φ ≅ Φ') :
    (sheafCompose J (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorIsoOfNatIso J θ).hom.app O) =
      θ.hom.app (Stacks.underlyingRingSheaf K O) :=
  (congrArg (fun m ↦ (sheafCompose J (forget CommRingCat.{ww})).map m)
      (pullbackCommRingSheafFunctorIsoOfNatIso_hom_app J θ O)).trans
    (pullbackCommRingSheafIsoOfNatIso_hom_forget J θ O)

end Transport

section Restriction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K]

/-- The isomorphism of functors is the identity on underlying sheaves of sets. -/
@[simp]
lemma underlyingRingSheaf_map_restrictionCommRingNatIso_hom
    [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J (forget CommRingCat.{ww})).map
        ((restrictionCommRingNatIso J K G).hom.app O) =
      𝟙 ((G.sheafPushforwardContinuous (Type ww) J K).obj
        (Stacks.underlyingRingSheaf K O)) :=
  restrictionCommRingIso_hom_forget J K G O

end Restriction

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Maps of sheaves along a morphism of algebraic spaces -/

section FMap

variable (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : F ⟶ G)

/-- A commutative diagram of étale scheme charts over a morphism of algebraic spaces, with an
arbitrary vertical scheme morphism. -/
structure ChartDiagram where
  /-- The étale scheme chart of the source. -/
  U : SmallEtale B S hS F
  /-- The étale scheme chart of the target. -/
  V : SmallEtale B S hS G
  /-- The vertical morphism of schemes. -/
  g : (SmallEtale.toOver B S hS F).obj U ⟶ (SmallEtale.toOver B S hS G).obj V
  /-- The diagram commutes. -/
  comm : U.1.hom ≫ f = yoneda.map g ≫ V.1.hom

/-- A map of sections along a morphism of algebraic spaces, natural under simultaneous étale
restriction of the source and target charts. -/
@[stacks 03G3]
structure FMap (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type v)
    (Q : (SmallEtale B S hS G)ᵒᵖ ⥤ Type w) where
  /-- The map of sections attached to a chart diagram. -/
  app : (d : ChartDiagram B S hS F G f) → Q.obj (op d.V) → P.obj (op d.U)
  /-- The maps of sections are compatible with étale restriction of both charts. -/
  naturality : ∀ (d d' : ChartDiagram B S hS F G f) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V),
      (SmallEtale.toOver B S hS F).map i ≫ d.g =
        d'.g ≫ (SmallEtale.toOver B S hS G).map j →
      ∀ s : Q.obj (op d.V), app d' (Q.map j.op s) = P.map i.op (app d s)

end FMap

/-- The small étale ringed topos of an algebraic space. -/
noncomputable abbrev smallEtaleRingedTopos (X : AlgebraicSpaces B S hS) :
    RingedTopos.{u, u + 1, u} :=
  { C := SmallEtale B S hS X.1
    J := SmallEtale.topology B S hS X.1
    O := structureSheaf B S hS X.1 X.2 }

variable {X Y : AlgebraicSpaces B S hS}

/-- The structure map of a morphism of algebraic spaces as a homomorphism of sheaves of
*commutative* rings. -/
noncomputable def structureSharpCommRing (f : X ⟶ Y) :
    (smallEtaleRingedTopos B S hS Y).O ⟶
      (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallToposMorphismTypeU B S hS f)).obj (smallEtaleRingedTopos B S hS X).O :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS Y.1)).preimage (structureSharp B S hS f)

/-- Forgetting commutativity in `AlgebraicGeometry.Space.structureSharpCommRing` gives back the
`RingCat`-valued structure map it was chosen over.  This is the defining property, and it is the
only thing anything needs of the definition.

`structureSharpCommRing` is a `Classical.choose`:
`CategoryTheory.Functor.FullyFaithful.preimage` is `Classical.choice` applied to the fullness
witness.  Left transparent, it lets the definitional unifier descend into choice while deciding
an unrelated equation — and there it does not terminate rather than merely run long; the small
étale structure map sits inside every ringed-topos morphism of a morphism of algebraic spaces,
so every defeq problem mentioning one is a candidate.  It is therefore marked irreducible just
below, and this lemma stands in for the transparency. -/
theorem map_structureSharpCommRing (f : X ⟶ Y) :
    (sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (structureSharpCommRing B S hS f) =
      structureSharp B S hS f :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS Y.1)).map_preimage _

attribute [irreducible] structureSharpCommRing

/-- The morphism of small étale ringed topoi induced by a morphism of algebraic spaces. -/
@[stacks 03G8 "canonical morphism of ringed topoi"]
noncomputable def smallEtaleRingedToposHom (f : X ⟶ Y) :
    RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) where
  toToposHom := smallToposMorphismTypeU B S hS f
  fSharp := structureSharpCommRing B S hS f

/-- The underlying geometric morphism of `smallEtaleRingedToposHom`. -/
@[stacks 03G8 "underlying geometric morphism"]
noncomputable def smallEtaleRingedToposHom_pushforward (f : X ⟶ Y) :
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward ≅
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  smallToposMorphismTypeU_comparison B S hS f

/-- Cartesian composition on spaces-étale direct images at the universe of the structure
rings. -/
noncomputable def spacesBaseChange_pushforward_compTypeU {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      ((spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)) ≅
      (spacesBaseChange B S hS (f ≫ g)).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X) :=
  Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS f g) (Type u)
    (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X)

/-- Direct-image comparison of the small and spaces-étale cartesian square, at the universe of
the structure rings. This is
`AlgebraicGeometry.Space.smallBaseChange_pushforward_comparison` with the sheaves of sets taken
in `Type u` rather than `Type (u + 1)`; the proof is the same, the sheaf universe playing no
role in it. -/
noncomputable def smallBaseChange_pushforward_comparisonTypeU (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) ⋙
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) ≅
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  letI := Functor.isContinuous_comp (smallBaseChange B S hS f hf) (comparisonFunctor B S hS X)
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  letI := Functor.isContinuous_comp (comparisonFunctor B S hS Y)
    (spacesBaseChange B S hS f).functor (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  Functor.sheafPushforwardContinuousComp (smallBaseChange B S hS f hf)
      (comparisonFunctor B S hS X) (Type u) (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ≪≫
    Functor.sheafPushforwardContinuousIso (smallBaseChange_comparison B S hS f hf)
      (Type u) (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) ≪≫
    (Functor.sheafPushforwardContinuousComp (comparisonFunctor B S hS Y)
      (spacesBaseChange B S hS f).functor (Type u) (SmallEtale.topology B S hS Y.1)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).symm

/-- **Stacks 03G8.** For a representable morphism of algebraic spaces the geometric direct
image of `smallEtaleRingedToposHom` is base change of étale scheme charts. -/
@[stacks 03G8 "agreement with scheme-chart base change"]
noncomputable def smallEtaleRingedToposHom_representable (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  ((Functor.whiskeringLeft _ _ _).obj
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))).preimageIso
    (smallToposMorphismTypeU_comparison B S hS f ≪≫
      (smallBaseChange_pushforward_comparisonTypeU B S hS f hf).symm)

/-- **Stacks 03G8.** The same comparison on sheaves of *commutative rings*: for a representable
morphism of algebraic spaces the direct image of sheaves of commutative rings along
`smallEtaleRingedToposHom` is base change of étale scheme charts.

The transported ring structure on the direct image is the one of the base-changed chart, by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, so this comparison is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` with the ring operations
carried along and nothing else; that is what
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing_forget` records. -/
noncomputable def smallEtaleRingedToposHom_representableRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1)
      (Φ := (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward)
      (Φ' := (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1))
      (smallEtaleRingedToposHom_representable B S hS f hf) ≪≫
    restrictionCommRingNatIso.{u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)

/-- Forgetting the ring operations in the comparison of direct images of sheaves of commutative
rings gives back the comparison of direct images of sheaves of sets. -/
theorem smallEtaleRingedToposHom_representableRing_forget (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
    (smallEtaleRingedTopos B S hS Y).forgetRing.map
        ((smallEtaleRingedToposHom_representableRing B S hS f hf).hom.app R) =
      (smallEtaleRingedToposHom_representable B S hS f hf).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R) := by
  have := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  simp only [smallEtaleRingedToposHom_representableRing, Iso.trans_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp,
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom,
    underlyingRingSheaf_map_restrictionCommRingNatIso_hom]
  exact Category.comp_id _

/-- Forgetting commutativity in the structure map of `smallEtaleRingedToposHom` gives back the
structure map of sheaves of rings. The chart formula
`AlgebraicGeometry.Space.chartProjection_structureMapApp` therefore computes it. -/
@[simp]
theorem forgetCommRingSheaf_map_fSharp (f : X ⟶ Y) :
    (sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharp =
      structureSharp B S hS f :=
  map_structureSharpCommRing B S hS f

/-! ### Monomorphisms of sheaves of rings are the sectionwise injective homomorphisms -/

/-- A morphism of sheaves with values in a concrete category whose forgetful functor preserves
pullbacks is a monomorphism exactly when it is injective on sections over every object. -/
private theorem mono_iff_app_injective_of_preservesPullback {C : Type*} [Category C]
    {A : Type*} [Category.{u} A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan (forget A)]
    (J : GrothendieckTopology C)
    [(sheafToPresheaf J A).PreservesMonomorphisms] {P Q : Sheaf J A} (φ : P ⟶ Q) :
    Mono φ ↔ ∀ Z, Function.Injective (ConcreteCategory.hom (φ.hom.app Z)) := by
  refine ⟨fun h Z => ?_, fun h => ⟨fun {Z} α β hab => ?_⟩⟩
  · exact (ConcreteCategory.mono_iff_injective_of_preservesPullback (φ.hom.app Z)).mp
      ((NatTrans.mono_iff_mono_app _).mp (Functor.map_mono (sheafToPresheaf J A) φ) Z)
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    refine ConcreteCategory.hom_ext _ _ fun x => h V ?_
    simpa using congrArg (fun t : Z ⟶ Q => ConcreteCategory.hom (t.hom.app V) x) hab

/-- A homomorphism of sheaves of rings is a monomorphism exactly when it is injective on
sections over every object of the site. -/
theorem mono_iff_app_injective_ringCat {C : Type*} [Category C]
    (J : GrothendieckTopology C) {P Q : Sheaf J RingCat.{u}} (φ : P ⟶ Q) :
    Mono φ ↔ ∀ Z, Function.Injective (φ.hom.app Z).hom :=
  mono_iff_app_injective_of_preservesPullback J φ

/-- A homomorphism of sheaves of commutative rings is a monomorphism exactly when it is
injective on sections over every object of the site. -/
theorem mono_iff_app_injective_commRingCat {C : Type*} [Category C]
    (J : GrothendieckTopology C) {P Q : Sheaf J CommRingCat.{u}} (φ : P ⟶ Q) :
    Mono φ ↔ ∀ Z, Function.Injective (φ.hom.app Z).hom :=
  mono_iff_app_injective_of_preservesPullback J φ

/-- The comparison between the two forms of the small étale direct image is, on the structure
sheaf of rings, a component of an isomorphism of functors. -/
private theorem mono_smallEtaleDirectImageRanIso_inv_app (f : X ⟶ Y) :
    Mono ((smallEtaleDirectImageRanIso B S hS f).inv.app
      (structureRingSheaf B S hS X).ringSheaf) := by
  have : IsIso ((smallEtaleDirectImageRanIso B S hS f).inv.app
      (structureRingSheaf B S hS X).ringSheaf) :=
    inferInstanceAs (IsIso (((smallEtaleDirectImageRanIso B S hS f).app
      (structureRingSheaf B S hS X).ringSheaf).symm.hom))
  exact IsIso.mono_of_iso _

/-- The comparison of the two forms of the direct image is a monomorphism of sheaves of rings:
on underlying sheaves of sets it is a component of an isomorphism of functors, and forgetting
the ring structure is faithful. -/
private theorem mono_pullbackRingSheafMapOfNatTrans_directImageRanIso (f : X ⟶ Y) :
    Mono (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv) := by
  have hmono : Mono ((sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget RingCat.{u})).map (pullbackRingSheafMapOfNatTrans
        (SmallEtale.topology B S hS Y.1) (structureRingSheaf B S hS X)
        (smallEtaleDirectImageRanIso B S hS f).inv)) := by
    rw [ringSheafMap_pullbackRingSheafMapOfNatTrans]
    exact mono_smallEtaleDirectImageRanIso_inv_app B S hS f
  exact (sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget RingCat.{u})).mono_of_mono_map hmono

/-- The structure map is its right Kan extension form followed by the comparison of the two
forms of the direct image. -/
private theorem structureSharp_eq_comp (f : X ⟶ Y) :
    structureSharp B S hS f = structureSharpRan B S hS f ≫
      pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
        (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv := rfl

/-- The structure map of a morphism of algebraic spaces is a monomorphism of sheaves of
commutative rings exactly when, over every étale scheme chart of the target, the map on
sections is injective. -/
theorem mono_fSharp_iff_injective_structureMapApp (f : X ⟶ Y) :
    Mono (smallEtaleRingedToposHom B S hS f).fSharp ↔
      ∀ V : SmallEtale B S hS Y.1, Function.Injective (structureMapApp B S hS f V) := by
  rw [mono_iff_app_injective_commRingCat]
  refine ⟨fun h V => ?_, fun h Z => ?_⟩
  · have : Mono (structureSharp B S hS f) := by
      rw [← forgetCommRingSheaf_map_fSharp B S hS f]
      exact (mono_iff_app_injective_ringCat _ _).mpr h
    rw [structureSharp_eq_comp] at this
    have h' : Mono (structureSharpRan B S hS f) :=
      mono_of_mono _ (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
        (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv)
    exact (mono_iff_app_injective_ringCat _ _).mp h' (op V)
  · have : Mono (structureSharpRan B S hS f) :=
      (mono_iff_app_injective_ringCat _ _).mpr fun Z => h Z.unop
    have := mono_pullbackRingSheafMapOfNatTrans_directImageRanIso B S hS f
    have h' : Mono (structureSharp B S hS f) := by
      rw [structureSharp_eq_comp]
      infer_instance
    rw [← forgetCommRingSheaf_map_fSharp B S hS f] at h'
    exact (mono_iff_app_injective_ringCat _ _).mp h' Z

/-- The underlying geometric morphism of `smallEtaleRingedToposHom` is the morphism of small
étale topoi of Stacks 03G2, part (3), at the universe of the structure rings. -/
theorem smallEtaleRingedToposHom_toToposHom (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toToposHom = smallToposMorphismTypeU B S hS f := rfl

/-! ### Composition -/

/-- **Stacks 03G2, part (3)** at the universe of the structure rings: the small étale direct
image is compatible with composition.  This is
`AlgebraicGeometry.Space.smallToposMorphism_comp` at `Type u`; the proof is the same, the sheaf
universe playing no role in it. -/
noncomputable def smallToposMorphismTypeU_comp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (MorphismOfTopoi.comp (smallToposMorphismTypeU B S hS g)
        (smallToposMorphismTypeU B S hS f)).pushforward ≅
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward :=
  MorphismOfTopoi.transport_comp_pushforward _ _ (smallEtaleToposEquivTypeU B S hS X)
      (smallEtaleToposEquivTypeU B S hS Y) (smallEtaleToposEquivTypeU B S hS Z) ≪≫
    Functor.isoWhiskerLeft (smallEtaleToposEquivTypeU B S hS X).inverse
      (Functor.isoWhiskerRight (spacesBaseChange_pushforward_compTypeU B S hS f g)
        (smallEtaleToposEquivTypeU B S hS Z).functor)

/-- **Stacks 03G2, part (3)** at the universe of the structure rings: the composition
isomorphism `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` is the transport of the
cartesian composition on the spaces-étale site through the comparison equivalences.  This is
`AlgebraicGeometry.Space.smallToposMorphism_comp_comparison` at `Type u`. -/
theorem smallToposMorphismTypeU_comp_comparison {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (F : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (smallToposMorphismTypeU B S hS g).pushforward.map
        ((smallToposMorphismTypeU_comparison B S hS f).hom.app F) ≫
      (smallToposMorphismTypeU_comparison B S hS g).hom.app
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj F) ≫
      (smallEtaleComparisonRestriction B S hS Z).map
        ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app F) =
    (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((smallEtaleComparisonRestriction B S hS X).obj F) ≫
      (smallToposMorphismTypeU_comparison B S hS (f ≫ g)).hom.app F :=
  MorphismOfTopoi.transport_comp_pushforward_comparison
    (spacesToposMorphismTypeU B S hS f) (spacesToposMorphismTypeU B S hS g)
    (spacesToposMorphismTypeU B S hS (f ≫ g))
    (spacesBaseChange_pushforward_compTypeU B S hS f g)
    (smallEtaleToposEquivTypeU B S hS X) (smallEtaleToposEquivTypeU B S hS Y)
    (smallEtaleToposEquivTypeU B S hS Z) F

/-- `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison` for an arbitrary sheaf
with a presentation on the spaces-étale site: the composite of the two geometric comparisons,
followed by cartesian composition, is the composition isomorphism followed by the geometric
comparison of the composite.  The passage from the presented sheaf to the sheaf itself is
naturality of `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`. -/
theorem smallToposMorphismTypeU_comp_presentation {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (e : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H) :
    (smallToposMorphismTypeU B S hS g).pushforward.map
        ((smallToposMorphismTypeU B S hS f).pushforward.map e.hom ≫
          (smallToposMorphismTypeU_comparison B S hS f).hom.app H) ≫
      (smallToposMorphismTypeU_comparison B S hS g).hom.app
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H) ≫
      (smallEtaleComparisonRestriction B S hS Z).map
        ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app H) =
    (smallToposMorphismTypeU_comp B S hS f g).hom.app P ≫
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.map e.hom ≫
      (smallToposMorphismTypeU_comparison B S hS (f ≫ g)).hom.app H := by
  have hnat : (smallToposMorphismTypeU B S hS g).pushforward.map
          ((smallToposMorphismTypeU B S hS f).pushforward.map e.hom) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((smallEtaleComparisonRestriction B S hS X).obj H) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app P ≫
        (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.map e.hom :=
    (smallToposMorphismTypeU_comp B S hS f g).hom.naturality e.hom
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    smallToposMorphismTypeU_comp_comparison B S hS f g H, ← Category.assoc]
  exact Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun m ↦ m ≫
      (smallToposMorphismTypeU_comparison B S hS (f ≫ g)).hom.app H) hnat)

/-- A comparison of the direct images of sheaves of commutative rings of `g ∘ f` and of the
composite morphism of ringed topoi is *induced by cartesian composition* when, on underlying
sheaves of sets, it is the transport of
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_compTypeU` through the geometric
comparison.  The condition is imposed for every sheaf of commutative rings and every
presentation of its underlying sheaf of sets on the spaces-étale site. -/
def IsCartesianComposition {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        ((smallEtaleRingedToposHom B S hS g).comp
          (smallEtaleRingedToposHom B S hS f)).toToposHom ≅
      pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom) : Prop :=
  ∀ (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (e : (smallEtaleRingedTopos B S hS X).forgetRing.obj R ≅
      (smallEtaleComparisonRestriction B S hS X).obj H),
    (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map e.hom ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H) ≫
      (smallEtaleRingedToposHom_pushforward B S hS g).hom.app
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H) ≫
      (smallEtaleComparisonRestriction B S hS Z).map
        ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app H) =
    (smallEtaleRingedTopos B S hS Z).forgetRing.map (i.hom.app R) ≫
      (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.pushforward.map e.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS (f ≫ g)).hom.app H

/-- The comparison of the direct images of sheaves of commutative rings of a composite of
morphisms of algebraic spaces, induced by cartesian composition: it is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` with the ring operations carried
along. -/
noncomputable def smallEtaleRingedToposHom_compRingIso {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        ((smallEtaleRingedToposHom B S hS g).comp
          (smallEtaleRingedToposHom B S hS f)).toToposHom ≅
      pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom :=
  pullbackCommRingSheafFunctorIsoOfNatIso.{u, u, u, u + 1, u, u + 1}
    (SmallEtale.topology B S hS Z.1)
    (Φ := ((smallEtaleRingedToposHom B S hS g).comp
      (smallEtaleRingedToposHom B S hS f)).toToposHom.pushforward)
    (Φ' := (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.pushforward)
    (smallToposMorphismTypeU_comp B S hS f g)

/-- The comparison `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` is induced by
cartesian composition: forgetting the ring operations it is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, whose transport through the geometric
comparison is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison`, and the
passage from a presentation of an arbitrary sheaf of commutative rings to the presented sheaf
is naturality of that isomorphism. -/
theorem smallEtaleRingedToposHom_compRingIso_isCartesianComposition
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsCartesianComposition B S hS f g (smallEtaleRingedToposHom_compRingIso B S hS f g) := by
  intro R H e
  have hforget : (smallEtaleRingedTopos B S hS Z).forgetRing.map
      ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app R) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj R) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) R (smallToposMorphismTypeU_comp B S hS f g)
  rw [hforget]
  exact smallToposMorphismTypeU_comp_presentation B S hS f g
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj R) H e

/-- The chart correspondence is specified using the geometric comparison: restriction along the
induced map to a cartesian spaces-étale chart computes its action on every section, after any
presentation of the source sheaf. -/
def IsChartCorrespondence (f : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (e : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj ≃
      (Q ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj P)) : Prop :=
  ∀ (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
    (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj d.V))
    (_hh : HEq
      (((SpacesEtale.toSpaces B S hS X).map h) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom
      (yoneda.map d.g))
    (s : Q.obj.obj (op d.V)),
    let ψ : Q ⟶ (smallEtaleComparisonRestriction B S hS Y).obj
        (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H) :=
      e ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H
    (((sheafToPresheaf (SmallEtale.topology B S hS X.1)
      (Type u)).map i.hom).app (op d.U)) (ξ.app d s) =
      H.obj.map h.op
        (((sheafToPresheaf (SmallEtale.topology B S hS Y.1)
          (Type u)).map ψ).app (op d.V) s)

/-- An étale chart of a representable algebraic space, as a scheme over the representing
scheme. This uses the Yoneda preimage of its structure map. -/
noncomputable def schemeChartToOver (T : BigFppfOver B S hS) :
    SmallEtale B S hS (yoneda.obj T) ⥤ Over ((BigFppfOver.toScheme B S hS).obj T) :=
  Functor.toOver
    (SmallEtale.toOver B S hS (yoneda.obj T) ⋙ BigFppfOver.toScheme B S hS)
    ((BigFppfOver.toScheme B S hS).obj T)
    (fun V => (BigFppfOver.toScheme B S hS).map (yoneda.preimage V.1.hom))
    (by
      intro V W k
      change (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj T)).map k) ≫ _ = _
      rw [← Functor.map_comp]
      congr 1
      apply yoneda.map_injective
      simp)

/-- The structure sheaf in the scheme-chart presentation has the sheaf property needed by the
construction of Stacks 070R. -/
theorem schemeChart_structure_isSheaf (T : BigFppfOver B S hS) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS (yoneda.obj T))
      (Stacks.Sites.structurePresheaf ((BigFppfOver.toScheme B S hS).obj T)
        (schemeChartToOver B S hS T)) :=
  ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj T))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (smallEtaleRingedTopos B S hS (schemeSpace T)).O).property

end AlgebraicGeometry.Space

add_to_stacks 03G8 "schemes regarded as algebraic spaces" AlgebraicGeometry.schemeSpace

end
