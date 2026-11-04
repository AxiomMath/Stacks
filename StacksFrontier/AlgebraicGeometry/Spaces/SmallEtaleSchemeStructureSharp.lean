module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.RingedSiteHom

/-!
# Stacks 03G8, part (2): the structure map of a morphism of schemes

Stacks 03G8 attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the
structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of `AlgebraicGeometry.Space.structureSharp` and makes
`(f_small, f♯)` a morphism of ringed topoi; part (2) of the lemma says that for a morphism of
*schemes* that structure map agrees with the one of Descent, Remark 070R.  This file proves
part (2).

The structure map is defined chartwise: over an étale chart `V` of `Y` it sends a regular
function to the family of its pullbacks to the étale charts of `X` above the algebraic space
`X ×_Y V`, the sections of `f_*𝒪_X` over `V` being the limit of the sections over those charts.
When `f` is *representable* that limit is attained at a single chart, namely the base-changed
chart `X ×_Y V` of Stacks 03G2, part (4), which
`AlgebraicGeometry.Space.chartBaseChangeArrowIsInitial` exhibits as an initial object of the
indexing category.  So the whole of `f_*𝒪_X` is restriction along chart base change, and the
structure map becomes pullback of regular functions along the cartesian projection
`X ×_Y V ⟶ V` of schemes — which is exactly the map of Stacks 070R.

A morphism of schemes over `S` is a morphism `AlgebraicGeometry.Space.representedSpaceMap` of
representable algebraic spaces, and it is representable by
`AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map`; so the representable case contains
the scheme case, and no hypothesis is carried in the scheme-case statement.

## Main definitions

* `AlgebraicGeometry.Space.chartProjectionSharp` and
  `AlgebraicGeometry.Space.chartProjectionSharpDirectImage` are the identification of the direct
  image `f_*𝒪_X` with restriction of `𝒪_X` along chart base change, for a representable `f`:
  over an étale chart `V` of `Y` it is the projection of the limit computing the sections of
  `f_*𝒪_X` to the base-changed chart `X ×_Y V`.  It is an isomorphism of sheaves of rings.
* `AlgebraicGeometry.Space.cartesianProjection` is the family of cartesian projections
  `X ×_Y V ⟶ V` of schemes, and `AlgebraicGeometry.Space.cartesianProjectionSharp` and
  `AlgebraicGeometry.Space.cartesianProjectionSharpCommRing` are pullback of global regular
  functions along them, as a homomorphism of sheaves of rings and of sheaves of commutative
  rings.

## Main results

* `AlgebraicGeometry.Space.chartProjection_structureMapApp_chartBaseChangeArrow`: over an étale
  chart `V` of `Y`, the structure map read through the base-changed chart is pullback of
  regular functions along `X ×_Y V ⟶ V`.
* `AlgebraicGeometry.Space.bijective_chartProjection_chartBaseChangeArrow` and
  `AlgebraicGeometry.Space.isIso_chartProjectionSharpDirectImage`: that reading is a bijection
  on sections, and an isomorphism of sheaves of rings.
* `AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage` and
  `AlgebraicGeometry.Space.fSharp_comp_chartProjectionSharpDirectImage`: for a representable
  morphism, the structure map of Stacks 03G8 — in its sheaf-of-rings form and as the `fSharp`
  of the morphism of ringed topoi — is, through that isomorphism, pullback along the cartesian
  projections.
* `AlgebraicGeometry.Space.cartesianProjectionSharpCommRing_eq_changeOfSites` and
  `AlgebraicGeometry.Space.structureSharp_representedSpaceMap_eq_changeOfSites` are
  **Stacks 03G8, part (2)**: for a morphism of schemes that map is
  `AlgebraicGeometry.ChangeOfSites.structureSharp`, the structure-sheaf homomorphism of
  Stacks 070R, taken for the presentation
  `AlgebraicGeometry.Space.schemeChartToOver` of the small étale site of a representable
  algebraic space as a site of schemes and for the cartesian projections.
* `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_hom_comp_fst`: for a
  morphism of schemes those cartesian projections are, through the comparison
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent` of the two chosen fibre
  products, the projections `pullback.fst` of the chosen fibre products of schemes.

## Implementation notes

The target of `AlgebraicGeometry.Space.structureSharp` is the direct image in its right Kan
extension form composed with the comparison
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`; the chart projections are natural only
for the Kan extension form, so `AlgebraicGeometry.Space.chartProjectionSharp` is built there and
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage` is its transport.

Naturality of the chart projection in the chart of `Y` is
`AlgebraicGeometry.Space.chartProjection_map` followed by the cone condition
`AlgebraicGeometry.Space.chartProjection_naturality` at the unique morphism
`AlgebraicGeometry.Space.chartBaseChangeArrowShiftHom` out of the initial object, which is base
change of the chart morphism by naturality of the comparison square
`AlgebraicGeometry.Space.smallBaseChange_comparison` of Stacks 03G2, part (4).

## What is not here

The comparison is with `AlgebraicGeometry.ChangeOfSites.structureSharp`, the 070R
structure-sheaf homomorphism of a change-of-topologies morphism of sites stated for an
arbitrary presentation of a site of schemes.  It is *not* stated against
`AlgebraicGeometry.smallEtaleRingedSiteHom`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RingedSiteHom.lean`), the
packaging of 070R, part (2) for the small étale site of a scheme in a big *étale* site: that
would have to be transported along
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, and the two structure sheaves are
identified only through `AlgebraicGeometry.toScheme_eq_post_comp_forget`, an equality of
functors that does not hold by `rfl`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- For a representable morphism the structure map, read through the base-changed chart, is
pullback of regular functions along the cartesian projection `X ×_Y V ⟶ V` of schemes. -/
theorem chartProjection_structureMapApp_chartBaseChangeArrow (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (x : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    (chartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app
        (structureSetSheaf B S hS X) (structureMapApp B S hS f V x) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op).hom x := by
  refine (chartProjection_structureMapApp B S hS f V
    (chartBaseChangeArrow B S hS f hf V) x).trans ?_
  rw [chartPullback, chartBaseChangeMap_chartBaseChangeArrow]
  rfl

/-- The projection of the sections of the direct image over an étale chart `V` of the target to
the sections over the base-changed chart is bijective: the base-changed chart is initial among
the charts of `X` above `X ×_Y V`, so the limit computing the sections is attained there. -/
theorem bijective_chartProjection_chartBaseChangeArrow (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    Function.Bijective ((chartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app
      (structureSetSheaf B S hS X)) := by
  have h : IsIso (((Functor.RightExtension.mk _
      ((comparisonFunctor B S hS X).op.ranCounit.app
        (structureSetSheaf B S hS X).obj)).coneAt
      (op (chartBaseChange B S hS f V))).π.app (chartBaseChangeArrow B S hS f hf V)) :=
    (chartIsLimit B S hS f V).isIso_π_app_of_isInitial _
      (chartBaseChangeArrowIsInitial B S hS f hf V)
  have hb := (isIso_iff_bijective _).mp h
  refine ⟨fun a b hab ↦ hb.1 ?_, fun y ↦ ?_⟩
  · exact (chartProjection_app_apply B S hS f V _ a).symm.trans
      (hab.trans (chartProjection_app_apply B S hS f V _ b))
  · obtain ⟨a, ha⟩ := hb.2 y
    exact ⟨a, (chartProjection_app_apply B S hS f V _ a).trans ha⟩

/-! ### The projection to the base-changed chart as a homomorphism of sheaves -/

/-- The shifted structured arrow occurring in `AlgebraicGeometry.Space.chartProjection_map`:
restricting a section of the direct image along a morphism `m : V₂ ⟶ V₁` of charts of `Y` and
projecting to the base-changed chart of `V₂` is projecting, at the level of `V₁`, to this
arrow. -/
abbrev chartBaseChangeArrowShift (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₂ ⟶ V₁) :
    StructuredArrow (op (chartBaseChange B S hS f V₁)) (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk (Y := op ((smallBaseChange B S hS f hf).obj V₂))
    (((spacesBaseChange B S hS f).functor.map ((comparisonFunctor B S hS Y).map m)).op ≫
      (chartBaseChangeArrow B S hS f hf V₂).hom)

/-- The base-changed chart of `V₁` maps to the shifted arrow of a morphism `m : V₂ ⟶ V₁` of
charts of `Y` by base change of `m` itself.  This is the naturality of the comparison square
`AlgebraicGeometry.Space.smallBaseChange_comparison` of Stacks 03G2, part (4). -/
def chartBaseChangeArrowShiftHom (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    {V₁ V₂ : SmallEtale B S hS Y.1} (m : V₂ ⟶ V₁) :
    chartBaseChangeArrow B S hS f hf V₁ ⟶ chartBaseChangeArrowShift B S hS f hf m := by
  refine StructuredArrow.homMk ((smallBaseChange B S hS f hf).map m).op ?_
  exact Quiver.Hom.unop_inj ((smallBaseChange_comparison B S hS f hf).hom.naturality m)

/-- **The sections of the direct image along a representable morphism are the sections over the
base-changed chart.** The projections of `AlgebraicGeometry.Space.chartProjection` to the
base-changed chart `X ×_Y V`, assembled into a homomorphism of sheaves of rings on the small
étale site of `Y` from the direct image in its right Kan extension form to restriction along
chart base change. -/
def chartProjectionSharp (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        (smallEtaleDirectImageRan B S hS f) (structureRingSheaf B S hS X) ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (structureRingSheaf B S hS X) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  { hom :=
    { app := fun Z ↦
        letI := ringObjRing (structureRingSheaf B S hS X)
          (smallEtaleDirectImageRan B S hS f ⋙
            sectionsFunctor (SmallEtale.topology B S hS Y.1) Z)
        RingCat.ofHom
          { toFun := (chartProjection B S hS f Z.unop
              (chartBaseChangeArrow B S hS f hf Z.unop)).app (structureSetSheaf B S hS X)
            map_add' := fun x y ↦
              (ringAddObj_naturality (structureRingSheaf B S hS X)
                  (chartProjection B S hS f Z.unop
                    (chartBaseChangeArrow B S hS f hf Z.unop)) x y).trans
                (sectionsFunctor_map_ringAddHom (structureRingSheaf B S hS X) _ _ _)
            map_mul' := fun x y ↦
              (ringMulObj_naturality (structureRingSheaf B S hS X)
                  (chartProjection B S hS f Z.unop
                    (chartBaseChangeArrow B S hS f hf Z.unop)) x y).trans
                (sectionsFunctor_map_ringMulHom (structureRingSheaf B S hS X) _ _ _)
            map_zero' :=
              (ringZeroObj_naturality (structureRingSheaf B S hS X)
                  (chartProjection B S hS f Z.unop
                    (chartBaseChangeArrow B S hS f hf Z.unop))).trans
                (sectionsFunctor_map_ringZeroHom (structureRingSheaf B S hS X) _ default)
            map_one' :=
              (ringOneObj_naturality (structureRingSheaf B S hS X)
                  (chartProjection B S hS f Z.unop
                    (chartBaseChangeArrow B S hS f hf Z.unop))).trans
                (sectionsFunctor_map_ringOneHom (structureRingSheaf B S hS X) _ default) }
      naturality := fun Z₁ Z₂ h ↦ by
        refine RingCat.hom_ext (RingHom.ext fun a ↦ ?_)
        exact (chartProjection_map B S hS f h.unop
            (chartBaseChangeArrow B S hS f hf Z₂.unop) a).trans
          (chartProjection_naturality B S hS f Z₁.unop
            (chartBaseChangeArrowShiftHom B S hS f hf h.unop) a) } }

/-- The projection to the base-changed chart is an isomorphism of sheaves of rings: over every
étale chart of the target it is bijective. -/
instance isIso_chartProjectionSharp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    IsIso (chartProjectionSharp B S hS f hf) := by
  let := isContinuous_smallBaseChange B S hS f hf
  have happ : ∀ Z, IsIso ((chartProjectionSharp B S hS f hf).hom.app Z) := fun Z ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_chartProjection_chartBaseChangeArrow B S hS f hf Z.unop
  have hpre : IsIso ((chartProjectionSharp B S hS f hf).hom) := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}).map
    (chartProjectionSharp B S hS f hf)) := hpre
  exact isIso_of_reflects_iso _ (sheafToPresheaf (SmallEtale.topology B S hS Y.1) RingCat.{u})

/-! ### Pullback of functions along the cartesian projection -/

/-- The cartesian projections `X ×_Y V ⟶ V`, as a natural transformation of the two functors
sending an étale chart of `Y` to an object of the big fppf site. -/
alias cartesianProjectionOver := AlgebraicGeometry.Space.smallBaseChangeProjection

/-- The cartesian projections, read on the underlying schemes. -/
def cartesianProjection (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    (smallBaseChange B S hS f hf ⋙ SmallEtale.toOver B S hS X.1) ⋙
        BigFppfOver.toScheme B S hS ⟶
      SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS :=
  Functor.whiskerRight (cartesianProjectionOver B S hS f hf) (BigFppfOver.toScheme B S hS)

/-- **The structure map of Stacks 070R, part (2), for a representable morphism of algebraic
spaces**: pullback of global regular functions along the cartesian projections
`X ×_Y V ⟶ V`, as a homomorphism of sheaves of rings on the small étale site of `Y`. -/
def cartesianProjectionSharp (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    structureRingSheaf B S hS Y ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (structureRingSheaf B S hS X) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  ⟨Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.op (cartesianProjection B S hS f hf)) Scheme.Γ)
    (forget₂ CommRingCat.{u} RingCat.{u})⟩

/-! ### The structure map is pullback along the cartesian projection -/

/-- **Stacks 03G8, part (2), for a representable morphism of algebraic spaces, in the right Kan
extension form of the direct image.** The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, followed by the
identification of the sections of `f_*𝒪_X` over an étale chart `V` of `Y` with the regular
functions on `X ×_Y V`, is pullback of regular functions along the cartesian projection
`X ×_Y V ⟶ V`. -/
theorem structureSharpRan_comp_chartProjectionSharp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    structureSharpRan B S hS f ≫ chartProjectionSharp B S hS f hf =
      cartesianProjectionSharp B S hS f hf := by
  let := isContinuous_smallBaseChange B S hS f hf
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Z
  refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  exact chartProjection_structureMapApp_chartBaseChangeArrow B S hS f hf Z.unop x

/-- The transport of `AlgebraicGeometry.Space.chartProjectionSharp` to the direct image in the
form in which the structure map `AlgebraicGeometry.Space.structureSharp` takes its values. -/
def chartProjectionSharpDirectImage (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    structureRingSheafDirectImage B S hS f ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (structureRingSheaf B S hS X) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).hom ≫
    chartProjectionSharp B S hS f hf

/-- Inverse images of a sheaf of rings along an isomorphism of finite-product-preserving functors
of sheaves of sets and back is the identity. -/
private theorem pullbackRingSheafMapOfNatTrans_hom_comp_inv.{w, w', v, v', t, t'}
    {C : Type t} [Category.{v} C] {D : Type t'} [Category.{v'} D]
    (J : GrothendieckTopology C) {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
    {Φ Φ' : Sheaf K (Type w') ⥤ Sheaf J (Type w)}
    [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
    (O : Sheaf K RingCat.{w'}) (ε : Φ ≅ Φ') :
    pullbackRingSheafMapOfNatTrans J O ε.hom ≫ pullbackRingSheafMapOfNatTrans J O ε.inv = 𝟙 _ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ RingCat.hom_ext (RingHom.ext fun x ↦
    congrFun (congrArg (fun m ↦ m.hom.app U) (ε.hom_inv_id_app (Sheaf.ringSheaf O))) x)))

/-- Passing between the two forms of the direct image and back is the identity. -/
private theorem pullbackRingSheafMapOfNatTrans_ranIso_inv_hom (f : X ⟶ Y) :
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).hom =
      𝟙 _ :=
  pullbackRingSheafMapOfNatTrans_hom_comp_inv _ _ (smallEtaleDirectImageRanIso B S hS f).symm

/-- Passing between the two forms of the direct image the other way round is the identity. -/
private theorem pullbackRingSheafMapOfNatTrans_ranIso_hom_inv (f : X ⟶ Y) :
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).hom ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv =
      𝟙 _ :=
  pullbackRingSheafMapOfNatTrans_hom_comp_inv _ _ (smallEtaleDirectImageRanIso B S hS f)

/-- The identification of the sections of the direct image over an étale chart of the target
with the regular functions on the base-changed chart is an isomorphism of sheaves of rings. -/
instance isIso_chartProjectionSharpDirectImage (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    IsIso (chartProjectionSharpDirectImage B S hS f hf) := by
  let := isContinuous_smallBaseChange B S hS f hf
  have h1 : IsIso (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).hom) :=
    ⟨⟨_, pullbackRingSheafMapOfNatTrans_ranIso_hom_inv B S hS f,
      pullbackRingSheafMapOfNatTrans_ranIso_inv_hom B S hS f⟩⟩
  have hd : chartProjectionSharpDirectImage B S hS f hf =
      pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).hom ≫
        chartProjectionSharp B S hS f hf := rfl
  rw [hd]
  infer_instance

/-- **Stacks 03G8, part (2), for a representable morphism of algebraic spaces.** The structure
map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8, followed by the identification
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage` of the sections of `f_*𝒪_X` over an
étale chart `V` of `Y` with the regular functions on the scheme `X ×_Y V`, is pullback of
regular functions along the cartesian projection `X ×_Y V ⟶ V` — which is the structure map of
the morphism of small étale ringed sites of Stacks 070R, part (2). -/
@[stacks 03G8 "part (2): the structure map is pullback along the cartesian projection"]
theorem structureSharp_comp_chartProjectionSharpDirectImage (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    structureSharp B S hS f ≫ chartProjectionSharpDirectImage B S hS f hf =
      cartesianProjectionSharp B S hS f hf := by
  let := isContinuous_smallBaseChange B S hS f hf
  have hdef : structureSharp B S hS f = structureSharpRan B S hS f ≫
      pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
        (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv := rfl
  have hd : chartProjectionSharpDirectImage B S hS f hf =
      pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).hom ≫
        chartProjectionSharp B S hS f hf := rfl
  rw [hdef, hd, Category.assoc, ← Category.assoc
    (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv),
    pullbackRingSheafMapOfNatTrans_ranIso_inv_hom, Category.id_comp]
  exact structureSharpRan_comp_chartProjectionSharp B S hS f hf

/-- **The structure map of Stacks 070R for a representable morphism of algebraic spaces, on
sheaves of commutative rings**: pullback of global regular functions along the cartesian
projections `X ×_Y V ⟶ V`. -/
def cartesianProjectionSharpCommRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (smallEtaleRingedTopos B S hS Y).O ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (smallEtaleRingedTopos B S hS X).O :=
  letI := isContinuous_smallBaseChange B S hS f hf
  ⟨Functor.whiskerRight (NatTrans.op (cartesianProjection B S hS f hf)) Scheme.Γ⟩

/-- Forgetting commutativity in `AlgebraicGeometry.Space.cartesianProjectionSharpCommRing`
gives `AlgebraicGeometry.Space.cartesianProjectionSharp`. -/
theorem sheafCompose_cartesianProjectionSharpCommRing (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (sheafCompose (SmallEtale.topology B S hS Y.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (cartesianProjectionSharpCommRing B S hS f hf) =
      cartesianProjectionSharp B S hS f hf := rfl

/-- **Stacks 03G8, part (2), for a representable morphism of algebraic spaces, on the morphism
of ringed topoi.** The structure map `f♯` of the morphism of small étale ringed topoi of
Stacks 03G8, read on sheaves of not necessarily commutative rings and followed by the
identification of the sections of `f_*𝒪_X` over an étale chart `V` of `Y` with the regular
functions on `X ×_Y V`, is pullback of regular functions along the cartesian projection
`X ×_Y V ⟶ V`. -/
@[stacks 03G8 "part (2): the same for the structure map of the morphism of ringed topoi"]
theorem fSharp_comp_chartProjectionSharpDirectImage (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (sheafCompose (SmallEtale.topology B S hS Y.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
          (smallEtaleRingedToposHom B S hS f).fSharp ≫
        chartProjectionSharpDirectImage B S hS f hf =
      cartesianProjectionSharp B S hS f hf := by
  let := isContinuous_smallBaseChange B S hS f hf
  rw [forgetCommRingSheaf_map_fSharp]
  exact structureSharp_comp_chartProjectionSharpDirectImage B S hS f hf

/-! ### Agreement with Stacks 070R, part (2), for a morphism of schemes -/

section Represented

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- For a morphism of schemes the cartesian projection of the chart base change is, through the
comparison `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent` of the two chosen
fibre products, the base-change projection of the small étale site of schemes. -/
theorem representedSmallEtaleBaseChangeComponent_hom_comp_fst
    (V : SmallEtale B S hS (yoneda.obj T)) :
    (representedSmallEtaleBaseChangeComponent B S hS g hg V).hom.hom.left ≫
        pullback.fst (yonedaEquiv V.1.hom).left g.left = (hg.snd V.1.hom).left := by
  rw [representedSmallEtaleBaseChangeComponent_hom]
  exact (isPullback_representedChart_schemes B S hS g hg V).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback (yonedaEquiv V.1.hom).left g.left)

/-- **Stacks 03G8, part (2).** For a morphism of schemes, `f♯` of the space construction *is*
the structure-sheaf homomorphism of Stacks 070R: the small étale site of the representable
algebraic space `yoneda.obj T` is a site of schemes over `T` through
`AlgebraicGeometry.Space.schemeChartToOver`, and over that presentation the map
`AlgebraicGeometry.Space.cartesianProjectionSharpCommRing` — which
`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage` identifies with
`f♯` — is `AlgebraicGeometry.ChangeOfSites.structureSharp`, the structure-sheaf homomorphism of
a change-of-topologies morphism of sites, formed with the cartesian projections. -/
@[stacks 03G8 "part (2): for a morphism of schemes this is the Stacks 070R structure map"]
theorem cartesianProjectionSharpCommRing_eq_changeOfSites :
    letI := isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg
    cartesianProjectionSharpCommRing B S hS (representedSpaceMap B S hS g) hg =
      AlgebraicGeometry.ChangeOfSites.structureSharp
        (SmallEtale.topology B S hS (yoneda.obj T))
        (SmallEtale.topology B S hS (yoneda.obj T'))
        (schemeChartToOver B S hS T) (schemeChartToOver B S hS T')
        (smallBaseChange B S hS (representedSpaceMap B S hS g) hg)
        (cartesianProjection B S hS (representedSpaceMap B S hS g) hg)
        (schemeChart_structure_isSheaf B S hS T)
        (schemeChart_structure_isSheaf B S hS T') := rfl

/-- **Stacks 03G8, part (2).** For a morphism of schemes `g : T' ⟶ T` over `S` the structure
map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8, followed by the canonical identification
`AlgebraicGeometry.Space.chartProjectionSharpDirectImage` of the sections of `f_*𝒪_{T'}` over an
étale chart `V` of `T` with the regular functions on the scheme `T' ×_T V`, *is* the structure
map of Stacks 070R: the map `AlgebraicGeometry.ChangeOfSites.structureSharp` of the
change-of-topologies morphism of sites given by base change of étale charts, formed with the
cartesian projections `T' ×_T V ⟶ V`.

The identification is an isomorphism, by
`AlgebraicGeometry.Space.isIso_chartProjectionSharpDirectImage`, so this is an equality of the
two structure maps and not merely a factorization. -/
@[stacks 03G8 "part (2): for a morphism of schemes, f♯ is the structure map of Stacks 070R"]
theorem structureSharp_representedSpaceMap_eq_changeOfSites :
    letI := isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)
    (sheafCompose (SmallEtale.topology B S hS (yoneda.obj T))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (AlgebraicGeometry.ChangeOfSites.structureSharp
          (SmallEtale.topology B S hS (yoneda.obj T))
          (SmallEtale.topology B S hS (yoneda.obj T'))
          (schemeChartToOver B S hS T) (schemeChartToOver B S hS T')
          (smallBaseChange B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g))
          (cartesianProjection B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g))
          (schemeChart_structure_isSheaf B S hS T)
          (schemeChart_structure_isSheaf B S hS T')) =
      structureSharp B S hS (representedSpaceMap B S hS g) ≫
        chartProjectionSharpDirectImage B S hS (representedSpaceMap B S hS g)
          (relativelyRepresentable_yoneda_map B S hS g) :=
  (congrArg (sheafCompose (SmallEtale.topology B S hS (yoneda.obj T))
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (cartesianProjectionSharpCommRing_eq_changeOfSites B S hS g
          (relativelyRepresentable_yoneda_map B S hS g)).symm).trans
    (structureSharp_comp_chartProjectionSharpDirectImage B S hS
      (representedSpaceMap B S hS g) (relativelyRepresentable_yoneda_map B S hS g)).symm

end Represented

end AlgebraicGeometry.Space

end
