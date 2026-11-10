module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage

/-!
# The structure map of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03G8 attaches to `f` a morphism of the small étale *ringed topoi* of `X` and
`Y`.  This file constructs the part of that datum which does not need a morphism of topoi: the
structure map

`f♯ : 𝒪_Y ⟶ f_*𝒪_X`

as a homomorphism of sheaves of rings on the small étale site of `Y`, where `f_*` is
`AlgebraicGeometry.Space.smallEtaleDirectImage`, the direct image of sheaves of sets at the
universe of the structure rings.  No adjoint and no left exactness of an inverse image is
used, and that is the point: the direct image of modules of Stacks 03D6, part (1) consumes
exactly this map, so with it the direct image
`AlgebraicGeometry.Space.modulePushforward : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` becomes unconditional.

The construction is the one of Stacks 03G8: on an étale scheme chart `V` of `Y`, a regular
function on `V` is sent to the family of its pullbacks along the induced morphisms of schemes
`V' ⟶ V`, one for each étale scheme chart `V'` of `X` above the algebraic space `X ×_Y V`.
That family is a section of the direct image because the sections of the direct image over `V`
are exactly the limit of the sections of `𝒪_X` over those charts: the quasi-inverse of the
comparison equivalence of Stacks 03G1 is the right Kan extension along the comparison functor,
and that Kan extension is pointwise.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans` is the morphism of
  inverse-image sheaves of rings induced by a natural transformation of the two
  finite-product-preserving functors of sheaves of sets.
* `AlgebraicGeometry.Space.structureRingSheaf` is the structure sheaf of an algebraic space as
  a sheaf of (not necessarily commutative) rings, the ring sheaf in which its sheaves of
  modules are indexed, and `AlgebraicGeometry.Space.structureSetSheaf` is the sheaf of sets
  underlying it.
* `AlgebraicGeometry.Space.chartBaseChangeMap` is the morphism of schemes `V' ⟶ V` induced by
  a chart `V'` of `X` above `X ×_Y V`, and `AlgebraicGeometry.Space.chartPullback` is pullback
  of regular functions along it.
* `AlgebraicGeometry.Space.structureMapApp` is the structure map on sections over an étale
  chart of `Y`, and `AlgebraicGeometry.Space.structureSharp` is the structure map
  `f♯ : 𝒪_Y ⟶ f_*𝒪_X` itself.
* `AlgebraicGeometry.Space.modulePushforward` is the direct image of `𝒪_X`-modules along `f`,
  read as `𝒪_Y`-modules along `f♯`: Stacks 03D6, part (1) for the small étale sites, with no
  hypothesis.

## Main results

* `AlgebraicGeometry.Space.smallEtaleComparisonRanIso`: the quasi-inverse of the comparison
  equivalence of Stacks 03G1 is the right Kan extension along the comparison functor, both
  being right adjoint to the comparison restriction.  This is what makes the sections of the
  direct image a limit over the étale charts.
* `AlgebraicGeometry.Space.chartProjection_structureMapApp` pins the structure map down: its
  projection to the chart `V'` is pullback of functions along `V' ⟶ V`.  Together with
  `AlgebraicGeometry.Space.chartProjection_ext`, which says that a section of the direct image
  is determined by its chart projections, this characterizes `structureSharp` completely.

## Implementation notes

The sections of `f_*𝒪_X` over an étale chart `V` of `Y` carry the ring structure *transported*
along the direct image, in the sense of `CategoryTheory.Sheaf.ringObjRing`, so the four
homomorphism properties of the structure map are not formalities.  Each is proved by projecting
to the étale charts of `X` above `X ×_Y V`, where
`CategoryTheory.Sheaf.ringAddObj_naturality` and its siblings turn the transported operation
into the transported operation of the sections functor, which
`CategoryTheory.Sheaf.sectionsFunctor_map_ringAddHom` identifies with the honest one.  The
projection used for this is `AlgebraicGeometry.Space.chartProjection`, built as a natural
transformation of *sections functors* — restriction followed by the counit of the comparison
adjunction — rather than as the bare cone projection, precisely so that those naturality
lemmas apply to it; `AlgebraicGeometry.Space.chartProjection_app_apply` identifies it with the
cone projection.

`AlgebraicGeometry.Space.smallEtaleDirectImageRan` is the direct image of sheaves of sets with
the `CategoryTheory.Functor.asEquivalence` quasi-inverse of the comparison replaced by
`CategoryTheory.Functor.sheafPushforwardCocontinuous`.  The two are isomorphic, by uniqueness
of right adjoints, but not equal — the former is `CategoryTheory.Functor.inv`, extracted from
an `IsEquivalence` instance — so the structure map is built against the Kan extension form,
where the pointwise limit is available, and transported to
`AlgebraicGeometry.Space.structureRingSheafDirectImage` at the very end by
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans`.

What this file does not provide, but Stacks 03G8 asserts, is the morphism of ringed topoi
itself.  That is built in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHom.lean` as
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, out of
`AlgebraicGeometry.Space.smallToposMorphismTypeU`
(`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleEssentiallySmall.lean`), which is a
`MorphismOfTopoi` and whose `preservesFiniteLimits` field is exactly the left exactness of the
spaces-étale inverse image at the universe of the structure rings.

The composition law for the structure map alone, `(g ≫ f)♯` versus `f♯` followed by `f_*(g♯)`,
is `AlgebraicGeometry.Space.structureSharpRanSet_comp`, and its ringed-topoi form is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`; both are in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  (O : Sheaf K RingCat.{ww'})

/-- A natural transformation between finite-product-preserving functors of sheaves of sets
induces a morphism between the inverse images of a sheaf of rings along them. -/
noncomputable def pullbackRingSheafMapOfNatTrans (θ : Φ ⟶ Φ') :
    pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ' O where
  hom :=
    { app := fun Z ↦
        letI := ringObjRing O (Φ ⋙ sectionsFunctor J Z)
        letI := ringObjRing O (Φ' ⋙ sectionsFunctor J Z)
        RingCat.ofHom (ringObjHom O (Functor.whiskerRight θ (sectionsFunctor J Z)))
      naturality := fun Z₁ Z₂ g ↦ by
        refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        exact NatTrans.naturality_apply (θ.app (ringSheaf O)).hom g x }

/-- The morphism induced by a natural transformation is that transformation on underlying
sheaves of sets. -/
@[simp]
lemma ringSheafMap_pullbackRingSheafMapOfNatTrans (θ : Φ ⟶ Φ') :
    (sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafMapOfNatTrans J O θ) =
      θ.app (ringSheaf O) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The spaces-étale direct image as a right Kan extension -/

/-- The comparison functor of Stacks 03G1 is cocontinuous. -/
instance isCocontinuous_comparisonFunctor (X : AlgebraicSpaces B S hS) :
    (comparisonFunctor B S hS X).IsCocontinuous
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  (comparisonFunctor_specialCocontinuous B S hS X).1

/-- Right Kan extensions of presheaves of sets valued in the universe of the structure rings
exist along the comparison functor of Stacks 03G1. -/
instance hasPointwiseRightKanExtension_comparisonFunctor (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) :
    (comparisonFunctor B S hS X).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-- The right Kan extension along the comparison functor of Stacks 03G1, on sheaves of sets
valued in the universe of the structure rings: a quasi-inverse of the comparison equivalence
whose sections are computed by a limit over the étale scheme charts. -/
noncomputable abbrev smallEtaleComparisonRan (X : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS X) (Type u) :=
  (comparisonFunctor B S hS X).sheafPushforwardCocontinuous (Type u)
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)

/-- The quasi-inverse of the comparison equivalence of Stacks 03G1 is the right Kan extension
along the comparison functor: both are right adjoint to the comparison restriction. -/
noncomputable def smallEtaleComparisonRanIso (X : AlgebraicSpaces B S hS) :
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse ≅
      smallEtaleComparisonRan B S hS X :=
  Adjunction.rightAdjointUniq (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction
    ((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))

/-- The direct image of sheaves of sets on the small étale sites, with the quasi-inverse of the
comparison equivalence replaced by the right Kan extension along the comparison functor. -/
noncomputable def smallEtaleDirectImageRan (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
  smallEtaleComparisonRan B S hS X ⋙
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
    smallEtaleComparisonRestriction B S hS Y

/-- The direct image of sheaves of sets is the right Kan extension form of itself. -/
noncomputable def smallEtaleDirectImageRanIso (f : X ⟶ Y) :
    smallEtaleDirectImage B S hS f ≅ smallEtaleDirectImageRan B S hS f :=
  Functor.isoWhiskerRight (smallEtaleComparisonRanIso B S hS X) _

/-- The right Kan extension form of the direct image preserves finite products, being
isomorphic to the direct image. -/
instance smallEtaleDirectImageRan_preservesFiniteProducts (f : X ⟶ Y) :
    PreservesFiniteProducts (smallEtaleDirectImageRan B S hS f) :=
  ⟨fun _ ↦ preservesLimitsOfShape_of_natIso (smallEtaleDirectImageRanIso B S hS f)⟩

/-! ### The chartwise pullback of regular functions -/

/-- The algebraic space `X ×_Y V`, étale over `X`, attached to an étale scheme chart `V`
of `Y`. -/
noncomputable abbrev chartBaseChange (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    SpacesEtale B S hS X :=
  (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj V)

/-- Given an étale scheme chart `V` of `Y` and an étale scheme chart of `X` over `X ×_Y V`,
the induced morphism of the underlying objects of the big fppf site of `S`: the Yoneda
preimage of the composite with the cartesian projection to `V`. -/
noncomputable def chartBaseChangeMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
  yoneda.preimage
    (((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)).hom)

/-- The chartwise morphism is characterized by its Yoneda morphism, which is the composite of
the given morphism with the cartesian projection. -/
theorem yoneda_map_chartBaseChangeMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    yoneda.map (chartBaseChangeMap B S hS f V j) =
      ((SpacesEtale.toSpaces B S hS X).map j.hom.unop ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)).hom :=
  yoneda.map_preimage _

/-- The Yoneda morphism of a chart morphism is the comparison functor's morphism of algebraic
spaces, as an equality of morphisms of presheaves. -/
theorem toSpaces_comparisonFunctor_map_hom (X : AlgebraicSpaces B S hS)
    {U V : SmallEtale B S hS X.1} (k : U ⟶ V) :
    ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k)).hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map k) :=
  eq_of_heq (comparisonFunctor_map B S hS X k)

/-- The chartwise morphisms are compatible with morphisms of charts of `X` over `X ×_Y V`. -/
theorem chartBaseChangeMap_comp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂) :
    chartBaseChangeMap B S hS f V j₂ =
      (SmallEtale.toOver B S hS X.1).map φ.right.unop ≫ chartBaseChangeMap B S hS f V j₁ := by
  apply yoneda.map_injective
  have hw : j₂.hom.unop =
      (comparisonFunctor B S hS X).map φ.right.unop ≫ j₁.hom.unop :=
    congrArg Quiver.Hom.unop (StructuredArrow.w φ).symm
  rw [Functor.map_comp, yoneda_map_chartBaseChangeMap, yoneda_map_chartBaseChangeMap, hw,
    Functor.map_comp, Category.assoc,
    ← toSpaces_comparisonFunctor_map_hom B S hS X φ.right.unop]
  rfl

/-- The chartwise morphisms are compatible with morphisms of charts of `Y`: base changing a
chart morphism of `Y` and composing is pulling back along it. -/
theorem chartBaseChangeMap_map (f : X ⟶ Y) {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op) :
    chartBaseChangeMap B S hS f V₂
        (StructuredArrow.mk
          (((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom)) =
      chartBaseChangeMap B S hS f V₁ j ≫ (SmallEtale.toOver B S hS Y.1).map m := by
  apply yoneda.map_injective
  rw [Functor.map_comp, yoneda_map_chartBaseChangeMap, yoneda_map_chartBaseChangeMap,
    ← toSpaces_comparisonFunctor_map_hom B S hS Y m]
  have hn : (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map m)) ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V₂) =
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V₁) ≫
        (SpacesEtale.toSpaces B S hS Y).map ((comparisonFunctor B S hS Y).map m) :=
    (spacesBaseChange B S hS f).projection.naturality _
  change (((SpacesEtale.toSpaces B S hS X).map
      (j.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map m)) ≫ _)).hom = _
  rw [Functor.map_comp, Category.assoc, hn]
  rfl

/-! ### The structure map -/

/-- The structure sheaf of an algebraic space as a sheaf of (not necessarily commutative)
rings on its small étale site, in which its sheaves of modules are indexed. -/
noncomputable abbrev structureRingSheaf (X : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)

/-- The sheaf of sets underlying the structure sheaf of an algebraic space. -/
noncomputable abbrev structureSetSheaf (X : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
    (structureRingSheaf B S hS X)

/-- Pullback of regular functions from an étale chart `V` of `Y` to an étale chart of `X`
over `X ×_Y V`. -/
noncomputable def chartPullback (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (structureSetSheaf B S hS Y).obj.obj (op V) ⟶
      (structureSetSheaf B S hS X).obj.obj j.right :=
  (forget CommRingCat.{u}).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j)).op)

/-- Regular functions pulled back along a morphism that factors as `b ≫ c` are pulled back along
`c` and then `b`. -/
private theorem forget_map_Gamma_toScheme_op_of_eq_comp {P Q R : BigFppfOver B S hS}
    {a : P ⟶ R} {b : P ⟶ Q} {c : Q ⟶ R} (h : a = b ≫ c) :
    (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a).op) =
      (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map c).op) ≫
        (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map b).op) := by
  rw [h, Functor.map_comp, op_comp, Functor.map_comp, Functor.map_comp]

/-- Pullback of functions is compatible with morphisms of charts of `X` over `X ×_Y V`. -/
theorem chartPullback_comp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂) :
    chartPullback B S hS f V j₂ =
      chartPullback B S hS f V j₁ ≫
        (structureSetSheaf B S hS X).obj.map φ.right := by
  exact forget_map_Gamma_toScheme_op_of_eq_comp B S hS (chartBaseChangeMap_comp B S hS f V φ)

/-- The cone of chartwise pullbacks of regular functions, whose limit is the sections of the
direct image of the structure sheaf over `V`. -/
noncomputable def chartPullbackCone (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Cone (StructuredArrow.proj (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op ⋙ (structureSetSheaf B S hS X).obj) where
  pt := (structureSetSheaf B S hS Y).obj.obj (op V)
  π :=
    { app := fun j ↦ chartPullback B S hS f V j
      naturality := fun _ _ φ ↦
        (Category.id_comp _).trans (chartPullback_comp B S hS f V φ) }

/-- The sections of the direct image of the structure sheaf of `X` over an étale chart `V`
of `Y` are the limit of the sections of the structure sheaf of `X` over the étale charts of
`X` above `X ×_Y V`. -/
noncomputable def chartIsLimit (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    IsLimit ((Functor.RightExtension.mk _
      ((comparisonFunctor B S hS X).op.ranCounit.app
        (structureSetSheaf B S hS X).obj)).coneAt
      (op (chartBaseChange B S hS f V))) :=
  (comparisonFunctor B S hS X).op.isPointwiseRightKanExtensionRanCounit
    (structureSetSheaf B S hS X).obj (op (chartBaseChange B S hS f V))

/-- The structure map on sections over an étale chart `V` of `Y`: a regular function on `V` is
sent to the family of its pullbacks to the étale charts of `X` above `X ×_Y V`. -/
noncomputable def structureMapApp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (structureSetSheaf B S hS Y).obj.obj (op V) ⟶
      ((comparisonFunctor B S hS X).op.ran.obj
        (structureSetSheaf B S hS X).obj).obj
        (op (chartBaseChange B S hS f V)) :=
  (chartIsLimit B S hS f V).lift (chartPullbackCone B S hS f V)

/-- The projection of the sections of the direct image over `V` to the sections of the
structure sheaf of `X` over an étale chart above `X ×_Y V`, as a natural transformation of
sections functors: restriction along the given morphism followed by the counit of the
comparison adjunction. -/
noncomputable def chartProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    smallEtaleDirectImageRan B S hS f ⋙
        sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V) ⟶
      sectionsFunctor (SmallEtale.topology B S hS X.1) j.right :=
  Functor.whiskerLeft (smallEtaleComparisonRan B S hS X) (sectionsRestrict j.hom) ≫
    Functor.whiskerRight ((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit
      (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right)

/-- The projection natural transformation is, on the structure sheaf, the projection of the
limit cone. -/
theorem chartProjection_app_apply (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j).app (structureSetSheaf B S hS X) a =
      ((Functor.RightExtension.mk _
        ((comparisonFunctor B S hS X).op.ranCounit.app
          (structureSetSheaf B S hS X).obj)).coneAt
        (op (chartBaseChange B S hS f V))).π.app j a := by
  have h : (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app
        (structureSetSheaf B S hS X)).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app (structureSetSheaf B S hS X).obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  change (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app
        (structureSetSheaf B S hS X)).hom.app j.right
      (((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map j.hom a) = _
  rw [h]
  rfl

/-- The structure map followed by a chart projection is pullback of functions along the
induced morphism of charts. -/
theorem chartProjection_structureMapApp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (g : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        (structureMapApp B S hS f V g) =
      chartPullback B S hS f V j g := by
  rw [chartProjection_app_apply]
  exact congrArg (fun φ ↦ φ g)
    ((chartIsLimit B S hS f V).fac (chartPullbackCone B S hS f V) j)

/-- Pullback of regular functions along the induced morphism of charts, as a ring
homomorphism. -/
noncomputable def chartPullbackRingHom (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (structureRingSheaf B S hS Y).obj.obj (op V) →+*
      (structureRingSheaf B S hS X).obj.obj j.right :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j)).op).hom

/-- Sections over an étale chart `V` of `Y` of the direct image, as a functor of the sheaf
on the small étale site of `X`. -/
noncomputable abbrev directImageSections (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤ Type u :=
  smallEtaleDirectImageRan B S hS f ⋙
    sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)

/-- Two sections of the direct image over `V` agree as soon as all their chart projections
agree: the sections are a limit over the charts. -/
theorem chartProjection_ext (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {a b : ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).obj
      (op (chartBaseChange B S hS f V))}
    (h : ∀ j, (chartProjection B S hS f V j).app (structureSetSheaf B S hS X) a =
      (chartProjection B S hS f V j).app (structureSetSheaf B S hS X) b) :
    a = b := by
  refine (Types.isLimitEquivSections (chartIsLimit B S hS f V)).injective
    (Subtype.ext (funext fun j ↦ ?_))
  exact (chartProjection_app_apply B S hS f V j a).symm.trans
    ((h j).trans (chartProjection_app_apply B S hS f V j b))

/-- The structure map on sections is additive for the transported addition. -/
theorem structureMapApp_add (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (x y : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    structureMapApp B S hS f V (x + y) =
      ringAddObj (structureRingSheaf B S hS X) (directImageSections B S hS f V)
        (structureMapApp B S hS f V x) (structureMapApp B S hS f V y) := by
  refine chartProjection_ext B S hS f V (fun j ↦ ?_)
  refine (chartProjection_structureMapApp B S hS f V j (x + y)).trans ?_
  refine ((chartPullbackRingHom B S hS f V j).map_add x y).trans ?_
  refine (congrArg₂ (· + ·) (chartProjection_structureMapApp B S hS f V j x).symm
    (chartProjection_structureMapApp B S hS f V j y).symm).trans ?_
  exact (sectionsFunctor_map_ringAddHom (structureRingSheaf B S hS X) j.right _ _).symm.trans
    (ringAddObj_naturality (structureRingSheaf B S hS X)
      (chartProjection B S hS f V j) _ _).symm

/-- The structure map on sections is multiplicative for the transported multiplication. -/
theorem structureMapApp_mul (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (x y : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    structureMapApp B S hS f V (x * y) =
      ringMulObj (structureRingSheaf B S hS X) (directImageSections B S hS f V)
        (structureMapApp B S hS f V x) (structureMapApp B S hS f V y) := by
  refine chartProjection_ext B S hS f V (fun j ↦ ?_)
  refine (chartProjection_structureMapApp B S hS f V j (x * y)).trans ?_
  refine ((chartPullbackRingHom B S hS f V j).map_mul x y).trans ?_
  refine (congrArg₂ (· * ·) (chartProjection_structureMapApp B S hS f V j x).symm
    (chartProjection_structureMapApp B S hS f V j y).symm).trans ?_
  exact (sectionsFunctor_map_ringMulHom (structureRingSheaf B S hS X) j.right _ _).symm.trans
    (ringMulObj_naturality (structureRingSheaf B S hS X)
      (chartProjection B S hS f V j) _ _).symm

/-- The structure map on sections preserves the zero section. -/
theorem structureMapApp_zero (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    structureMapApp B S hS f V (0 : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) =
      ringZeroObj (structureRingSheaf B S hS X) (directImageSections B S hS f V) := by
  refine chartProjection_ext B S hS f V (fun j ↦ ?_)
  refine (chartProjection_structureMapApp B S hS f V j 0).trans ?_
  refine (chartPullbackRingHom B S hS f V j).map_zero.trans ?_
  exact (sectionsFunctor_map_ringZeroHom (structureRingSheaf B S hS X) j.right _).symm.trans
    (ringZeroObj_naturality (structureRingSheaf B S hS X)
      (chartProjection B S hS f V j)).symm

/-- The structure map on sections preserves the unit section. -/
theorem structureMapApp_one (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    structureMapApp B S hS f V (1 : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) =
      ringOneObj (structureRingSheaf B S hS X) (directImageSections B S hS f V) := by
  refine chartProjection_ext B S hS f V (fun j ↦ ?_)
  refine (chartProjection_structureMapApp B S hS f V j 1).trans ?_
  refine (chartPullbackRingHom B S hS f V j).map_one.trans ?_
  exact (sectionsFunctor_map_ringOneHom (structureRingSheaf B S hS X) j.right _).symm.trans
    (ringOneObj_naturality (structureRingSheaf B S hS X)
      (chartProjection B S hS f V j)).symm

/-- Restricting a section of the direct image along a morphism of charts of `Y` and projecting
to a chart of `X` is projecting to the base-changed chart. -/
theorem chartProjection_map (f : X ⟶ Y) {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).obj
      (op (chartBaseChange B S hS f V₂))) :
    (chartProjection B S hS f V₁ j).app (structureSetSheaf B S hS X)
        (((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map m)).op a) =
      (chartProjection B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom))).app
        (structureSetSheaf B S hS X) a := by
  rw [chartProjection_app_apply, chartProjection_app_apply]
  simp only [Functor.RightExtension.coneAt_π_app, types_comp_apply, Functor.RightExtension.mk_left,
    Functor.RightExtension.mk_hom, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self,
    ← Functor.map_comp_apply]
  rfl

/-- Pullback of functions along a base-changed chart morphism is restriction followed by
pullback. -/
theorem chartPullback_map (f : X ⟶ Y) {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (j : StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op)
    (x : ToType ((structureRingSheaf B S hS Y).obj.obj (op V₂))) :
    chartPullback B S hS f V₂ (StructuredArrow.mk
        (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map m)).op ≫ j.hom)) x =
      chartPullback B S hS f V₁ j ((structureSetSheaf B S hS Y).obj.map m.op x) := by
  exact congrArg (fun φ ↦ φ x)
    (forget_map_Gamma_toScheme_op_of_eq_comp B S hS (chartBaseChangeMap_map B S hS f m j))

/-- The structure map on sections is natural in the étale chart of `Y`. -/
theorem structureMapApp_naturality (f : X ⟶ Y) {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₁ ⟶ V₂)
    (x : ToType ((structureRingSheaf B S hS Y).obj.obj (op V₂))) :
    structureMapApp B S hS f V₁ ((structureSetSheaf B S hS Y).obj.map m.op x) =
      ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map
        ((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)).op
        (structureMapApp B S hS f V₂ x) := by
  refine chartProjection_ext B S hS f V₁ (fun j ↦ ?_)
  refine (chartProjection_structureMapApp B S hS f V₁ j _).trans (Eq.symm ?_)
  refine (chartProjection_map B S hS f m j _).trans ?_
  exact (chartProjection_structureMapApp B S hS f V₂ _ x).trans
    (chartPullback_map B S hS f m j x)

/-! ### The structure map and the direct image of modules -/

/-- The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` as a morphism of sheaves of rings on the small
étale site of `Y`, with the direct image taken in its right Kan extension form: on an étale
chart `V` of `Y` it sends a regular function to the family of its pullbacks to the étale charts
of `X` above `X ×_Y V`. -/
noncomputable def structureSharpRan (f : X ⟶ Y) :
    structureRingSheaf B S hS Y ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImageRan B S hS f) (structureRingSheaf B S hS X) where
  hom :=
    { app := fun Z ↦
        letI := ringObjRing (structureRingSheaf B S hS X)
          (smallEtaleDirectImageRan B S hS f ⋙
            sectionsFunctor (SmallEtale.topology B S hS Y.1) Z)
        RingCat.ofHom
        { toFun := structureMapApp B S hS f Z.unop
          map_add' := structureMapApp_add B S hS f Z.unop
          map_mul' := structureMapApp_mul B S hS f Z.unop
          map_zero' := structureMapApp_zero B S hS f Z.unop
          map_one' := structureMapApp_one B S hS f Z.unop }
      naturality := fun _ _ g ↦ by
        refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        exact structureMapApp_naturality B S hS f g.unop x }

/-- **Stacks 03G8, the structure map.** For a morphism `f : X ⟶ Y` of algebraic spaces, the
canonical homomorphism `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of sheaves of rings on the small étale site
of `Y`. -/
noncomputable def structureSharp (f : X ⟶ Y) :
    structureRingSheaf B S hS Y ⟶ structureRingSheafDirectImage B S hS f :=
  structureSharpRan B S hS f ≫
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv

/-- **Stacks 03D6, part (1)**, unconditionally, and the direct-image half of Stacks 03LU: the
direct image of `𝒪_X`-modules along a morphism of algebraic spaces, read as `𝒪_Y`-modules by
restriction of scalars along the structure map.

The inverse-image half of Stacks 03LU is
`AlgebraicGeometry.Space.modulePullback`, and the adjunction is
`AlgebraicGeometry.Space.modulePullbackAdjunction`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`).  That adjunction is
stated for the direct image of Stacks 03D6, part (1) attached to the morphism of ringed topoi,
which is this functor up to a comparison that is not yet supplied; see the implementation notes
of that file. -/
@[stacks 03LU "pushforward"]
noncomputable def modulePushforward (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  modulePushforwardOfStructureMap B S hS f (structureSharp B S hS f)

end AlgebraicGeometry.Space

end
