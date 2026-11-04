module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# The inverse image of modules along a morphism of representable algebraic spaces

Let `B` be a big fppf site containing a scheme `S`, let `g : T' ⟶ T` be a morphism of the big
fppf category over `S` and let `φ` be the morphism of representable algebraic spaces it
represents. The small étale site of `yoneda.obj U` is identified with the small étale site of
the scheme underlying `U` by `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, and the
two structure sheaves agree across that identification. This file shows that across it, the
inverse image of modules `φ^*` becomes pullback of sheaves of modules along the morphism of small
étale ringed sites attached to the morphism of schemes underlying `g`.

Both inverse images are left adjoints, and the comparison is made on the direct images. For a
representable morphism the direct image of modules is the direct image along base change of étale
scheme charts, `AlgebraicGeometry.Space.modulePushforwardChartIso`, so its left adjoint is
pullback along the structure map `AlgebraicGeometry.Space.smallBaseChangeSharp`. Base change of
charts and base change of schemes are identified by
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, compatibly with the two structure
maps: over an étale chart `V` of `yoneda.obj T` both are pullback of regular functions along the
cartesian projection of `V` with `T'` over `T`.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeModulePullback`: pullback of `𝒪`-modules along the
  structure map of base change of étale scheme charts, the left adjoint of
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.
* `AlgebraicGeometry.Space.representedEquivSharp`: the structure comparison of the
  identification of the two small étale sites, the identity on sections.
* `AlgebraicGeometry.Space.representedSchemeStructureMapRing`: the structure map of the morphism
  of small étale ringed sites of the underlying morphism of schemes.
* `AlgebraicGeometry.Space.representedSpaceRouteAdjunction` and
  `AlgebraicGeometry.Space.representedSchemeRouteAdjunction`: the two composite adjunctions round
  the square of small étale ringed sites.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartIso`: for a representable morphism the inverse
  image of modules is pullback along base change of étale scheme charts.
* `AlgebraicGeometry.Space.representedStructureMapRing_square`: the two routes round the square
  of small étale ringed sites carry the structure sheaf of `T` to the structure sheaf of `T'` by
  the same map.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareIso`: the two routes round the
  square have the same direct image of modules; by
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_inv_app` it factors as
  `AlgebraicGeometry.Space.representedModulePushforwardSquareRestrictIso` and the whiskering of
  `AlgebraicGeometry.Space.modulePushforwardChartIso`.
* `AlgebraicGeometry.Space.representedModulePullbackIso`: the inverse image of modules along a
  morphism of representable algebraic spaces is the small étale pullback of the underlying
  morphism of schemes, across the identification of the two small étale sites;
  `AlgebraicGeometry.Space.representedModuleObjPullbackIso` reads it at one module.
* `AlgebraicGeometry.Space.unit_comp_representedModulePullbackIso_hom` and
  `AlgebraicGeometry.Space.unit_comp_representedModulePullbackIso_inv`: the unit of one route
  followed by the comparison is the unit of the other route.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`: the inverse image along `φ`
  of the associated module of a Zariski module on the scheme underlying `T` is the associated
  module of the Zariski pullback.

## Implementation notes

The objects of these sites admit two definitionally equal spellings which are not equal at the
reducible transparency used by instance resolution: the small étale site of the scheme underlying
`U` is written with `(AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U` on one side and with
`U.left.obj` on the other, and the structure sheaf of rings of an algebraic space is written
either as `AlgebraicGeometry.Space.smallEtaleRingSheaf` or as
`AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed site. So every functor and
structure map below is named with its type written out, the continuity instances of the two
composite functors are assembled by passing the components to
`CategoryTheory.Functor.isContinuous_comp` explicitly, and the square of pullbacks is built from
`SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂` followed by one
`CategoryTheory.Adjunction.leftAdjointUniq` with every adjunction supplied as an explicit term,
rather than from `SheafOfModules.pullbackSquareIso`.

The equations `unit_comp_representedModulePullbackIso_hom` and
`unit_comp_representedModulePullbackIso_inv` are stated at the natural transformations rather than
at a component: the component form exhausts the elaborator's recursion depth.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Pullback along base change of étale scheme charts -/

/-- For a representable morphism, the direct image of `𝒪_X`-modules along base change of étale
scheme charts has a left adjoint. -/
instance isRightAdjoint_pushforward_smallBaseChangeSharp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f hf)).IsRightAdjoint :=
  ((modulePullbackAdjunction B S hS f).ofNatIsoRight
    (modulePushforwardChartIso B S hS f hf)).isRightAdjoint

/-- Pullback of `𝒪_Y`-modules along the structure map of base change of étale scheme charts, the
left adjoint of `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`. -/
noncomputable def smallBaseChangeModulePullback (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    SheafOfModules.{u} (smallEtaleRingSheaf B S hS Y.1 Y.2) ⥤
      SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2) :=
  SheafOfModules.pullback.{u} (smallBaseChangeSharp B S hS f hf)

/-- Pullback along base change of charts is left adjoint to the direct image along base change of
charts. -/
noncomputable def smallBaseChangeModulePullbackAdjunction (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallBaseChangeModulePullback B S hS f hf ⊣
      SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f hf) :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (smallBaseChangeSharp B S hS f hf)

/-- For a representable morphism `f`, the inverse image of modules along `f` is pullback along
the structure map `AlgebraicGeometry.Space.smallBaseChangeSharp`, which over an étale chart `V` of
`Y` is pullback of regular functions along the cartesian projection `V ×_Y X ⟶ V`. -/
noncomputable def modulePullbackChartIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    modulePullback B S hS f ≅ smallBaseChangeModulePullback B S hS f hf :=
  Adjunction.leftAdjointUniq
    ((modulePullbackAdjunction B S hS f).ofNatIsoRight (modulePushforwardChartIso B S hS f hf))
    (smallBaseChangeModulePullbackAdjunction B S hS f hf)

/-! ### The square of small étale ringed sites of a representable morphism -/

/-- The inverse of a four-factor composite of natural isomorphisms, read at an object, splits
off its last factor. -/
theorem _root_.CategoryTheory.Iso.trans_trans_trans_inv_app {C D : Type*} [Category C]
    [Category D] {F₀ F₁ F₂ F₃ F₄ : C ⥤ D} (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃)
    (w : F₃ ≅ F₄) (X : C) :
    (a ≪≫ b ≪≫ c ≪≫ w).inv.app X = w.inv.app X ≫ (a ≪≫ b ≪≫ c).inv.app X := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]

section Represented

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- Base change of the small étale site of the scheme underlying `T` along the morphism of
schemes underlying `g`, with the two sites spelled as they are in the identification of the small
étale site of a representable algebraic space with the small étale site of the underlying
scheme. -/
noncomputable abbrev representedSchemeBaseChange :
    _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⥤
      _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property :=
  _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left

/-- Base change of schemes along the morphism underlying `g` is continuous, with the two small
étale sites of schemes spelled as they are in the identification of the small étale site of a
representable algebraic space with the small étale site of the underlying scheme. -/
instance isContinuous_representedSchemeBaseChange :
    (representedSchemeBaseChange B S hS g).IsContinuous
      (representedSchemeSmallEtaleTopology B S hS T)
      (representedSchemeSmallEtaleTopology B S hS T') :=
  _root_.AlgebraicGeometry.smallEtaleBaseChange_isContinuous (associatedBigEtaleSite B) g.left

/-- Base change of étale scheme charts along the represented morphism is continuous, with the
small étale sites of the two representable algebraic spaces spelled by the presheaves they are
the sites of. -/
instance isContinuous_representedSmallBaseChange :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T)) (SmallEtale.topology B S hS (yoneda.obj T')) :=
  isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg

/-- The structure comparison of the identification of the small étale site of `yoneda.obj U` with
the small étale site of the scheme underlying `U`: the identity, the two structure sheaves being
the same sheaf of rings by
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`. -/
noncomputable def representedEquivSharp (U : BigFppfOver B S hS) :
    representedStructureRingSheaf B S hS U ⟶
      ((representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSchemeSmallEtaleTopology B S hS U)).obj
        (representedSchemeStructureSheaf B S hS U) :=
  𝟙 _

/-- The structure map of the morphism of small étale ringed sites attached to the morphism of
schemes underlying `g`: over an étale `W / T` it is pullback of regular functions
along the projection `T' ×_T W ⟶ W`. -/
noncomputable abbrev representedSchemeStructureMapRing :
    representedSchemeStructureSheaf B S hS T ⟶
      ((representedSchemeBaseChange B S hS g).sheafPushforwardContinuous RingCat.{u}
        (representedSchemeSmallEtaleTopology B S hS T)
        (representedSchemeSmallEtaleTopology B S hS T')).obj
        (representedSchemeStructureSheaf B S hS T') :=
  _root_.AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) g.left

/-- The identification of the small étale site of a representable algebraic space followed by
base change of schemes is a continuous functor. -/
instance isContinuous_representedEquiv_comp_smallEtaleBaseChange :
    ((representedSmallEtaleEquivalence B S hS T).functor ⋙
        representedSchemeBaseChange B S hS g).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T') :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS T)
    (isContinuous_representedSchemeBaseChange B S hS g)

/-- Base change of étale scheme charts along the represented morphism followed by the
identification of the small étale site of a representable algebraic space is a continuous
functor. -/
instance isContinuous_smallBaseChange_comp_representedEquiv :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        (representedSmallEtaleEquivalence B S hS T').functor).IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T))
      (representedSchemeSmallEtaleTopology B S hS T') :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSmallBaseChange B S hS g hg)
    (isContinuous_representedSmallEtaleEquivalence_functor B S hS T')

/-- The two routes round the square of small étale ringed sites carry the structure sheaf of
`T` to the structure sheaf of `T'` by the same map: over an étale chart `V` of `yoneda.obj T`
both are pullback of regular functions along the cartesian projection of `V` with `T'` over
`T`. -/
theorem representedStructureMapRing_square :
    SheafOfModules.comparisonComp (representedEquivSharp B S hS T)
          (representedSchemeStructureMapRing B S hS g) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (representedSmallEtaleBaseChangeIso B S hS g hg).hom RingCat.{u}
          (SmallEtale.topology B S hS (yoneda.obj T))
          (representedSchemeSmallEtaleTopology B S hS T')).app
          (representedSchemeStructureSheaf B S hS T') =
      SheafOfModules.comparisonComp
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
        (representedEquivSharp B S hS T') := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V ↦ ?_)
  have key : (representedSmallEtaleBaseChangeComponent B S hS g hg V.unop).hom.hom.left ≫
      pullback.fst (yonedaEquiv V.unop.1.hom).left g.left = (hg.snd V.unop.1.hom).left := by
    rw [representedSmallEtaleBaseChangeComponent_hom]
    exact (isPullback_representedChart_schemes B S hS g hg V.unop).isoIsPullback_hom_fst _ _ _
  have hcomp : B.inclusion.map
          (representedSmallEtaleBaseChangeComponent B S hS g hg V.unop).hom.hom.left ≫
        B.inclusion.map (pullback.fst (yonedaEquiv V.unop.1.hom).left g.left) =
      (BigFppfOver.toScheme B S hS).map (hg.snd V.unop.1.hom) :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map key)
  have hΓ : Scheme.Γ.map
          (B.inclusion.map (pullback.fst (yonedaEquiv V.unop.1.hom).left g.left)).op ≫
        Scheme.Γ.map (B.inclusion.map
          (representedSmallEtaleBaseChangeComponent B S hS g hg V.unop).hom.hom.left).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hg.snd V.unop.1.hom)).op :=
    (Scheme.Γ.map_comp _ _).symm.trans
      (congrArg Scheme.Γ.map (op_comp.symm.trans (congrArg Quiver.Hom.op hcomp)))
  exact (((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans
    (congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map hΓ))

/-! ### The inverse image of modules across the identification of the sites -/

/-- The direct image of modules along the morphism of small étale ringed sites of the underlying
morphism of schemes has a left adjoint. -/
instance isRightAdjoint_pushforward_representedSchemeStructureMapRing :
    (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)).IsRightAdjoint :=
  _root_.AlgebraicGeometry.SmallEtale.pushforward_smallEtaleStructureMapRing_isRightAdjoint
    (associatedBigEtaleSite B) g.left

/-- Taking the direct image of modules along base change of schemes and then reading the result
on the small étale site of `yoneda.obj T` is isomorphic to reading a module on the small étale
site of `yoneda.obj T'` and taking the direct image along base change of étale charts. -/
noncomputable def representedModulePushforwardSquareRestrictIso :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor ≅
      (representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS g) hg :=
  SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
      (representedSchemeStructureMapRing B S hS g) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS g hg)
      (representedStructureMapRing_square B S hS g hg) ≪≫
    (SheafOfModules.pushforwardComp.{u}
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
      (representedEquivSharp B S hS T')).symm

/-- Taking the direct image of modules along base change of schemes and then reading the result
on the small étale site of `yoneda.obj T` is isomorphic to reading a module on the small étale
site of `yoneda.obj T'` and taking the direct image of modules along the represented morphism. -/
noncomputable def representedModulePushforwardSquareIso :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor ≅
      (representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g) :=
  SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
      (representedSchemeStructureMapRing B S hS g) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS g hg)
      (representedStructureMapRing_square B S hS g hg) ≪≫
    (SheafOfModules.pushforwardComp.{u}
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
      (representedEquivSharp B S hS T')).symm ≪≫
    Functor.isoWhiskerLeft ((representedSmallEtaleModuleEquivalence B S hS T').functor)
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).symm

/-- The composite adjunction round the space side of the square: the inverse image of modules
along the represented morphism, followed by the identification of the small étale site of
`yoneda.obj T'` with that of the scheme underlying `T'`, is left adjoint to that identification
followed by the direct image of modules. -/
noncomputable def representedSpaceRouteAdjunction :
    modulePullback B S hS (representedSpaceMap B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').inverse ⊣
      (representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g) :=
  (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
    (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction

/-- The composite adjunction round the scheme side of the square: the identification of the small
étale site of `yoneda.obj T` with that of the scheme underlying `T`, followed by pullback along
the morphism of small étale ringed sites of the underlying morphism of schemes, is left adjoint to
the same right adjoint as `AlgebraicGeometry.Space.representedSpaceRouteAdjunction`, the
comparison of the two direct images being
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`. -/
noncomputable def representedSchemeRouteAdjunction :
    (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
        SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⊣
      (representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g) :=
  ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.comp
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS g))).ofNatIsoRight
    (representedModulePushforwardSquareIso B S hS g hg)

/-- The inverse of `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` at a module is
the component of `AlgebraicGeometry.Space.modulePushforwardChartIso` followed by the inverse of
`AlgebraicGeometry.Space.representedModulePushforwardSquareRestrictIso`. -/
theorem representedModulePushforwardSquareIso_inv_app
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T')) :
    (representedModulePushforwardSquareIso B S hS g hg).inv.app M =
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj M) ≫
        (representedModulePushforwardSquareRestrictIso B S hS g hg).inv.app M :=
  Iso.trans_trans_trans_inv_app _ _ _ _ M

/-- Read through the identifications of the small étale site of `yoneda.obj U` with the small
étale site of the scheme underlying `U`, the inverse image of modules `φ^*` along the morphism `φ`
of representable algebraic spaces represented by `g : T' ⟶ T` is pullback of sheaves of modules
along the morphism of small étale ringed sites attached to the morphism of schemes underlying
`g`. -/
noncomputable def representedModulePullbackIso :
    modulePullback B S hS (representedSpaceMap B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').inverse ≅
      (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
        SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) :=
  Adjunction.leftAdjointUniq (representedSpaceRouteAdjunction B S hS g)
    (representedSchemeRouteAdjunction B S hS g hg)

/-- The unit of the space route, followed by
`AlgebraicGeometry.Space.representedModulePullbackIso`, is the unit of the scheme route. -/
theorem unit_comp_representedModulePullbackIso_hom :
    (representedSpaceRouteAdjunction B S hS g).unit ≫
        Functor.whiskerRight (representedModulePullbackIso B S hS g hg).hom
          ((representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
            modulePushforward B S hS (representedSpaceMap B S hS g)) =
      (representedSchemeRouteAdjunction B S hS g hg).unit :=
  Adjunction.unit_leftAdjointUniq_hom (representedSpaceRouteAdjunction B S hS g)
    (representedSchemeRouteAdjunction B S hS g hg)

/-- The unit of the scheme route, followed by the inverse of
`AlgebraicGeometry.Space.representedModulePullbackIso`, is the unit of the space route. -/
theorem unit_comp_representedModulePullbackIso_inv :
    (representedSchemeRouteAdjunction B S hS g hg).unit ≫
        Functor.whiskerRight (representedModulePullbackIso B S hS g hg).inv
          ((representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
            modulePushforward B S hS (representedSpaceMap B S hS g)) =
      (representedSpaceRouteAdjunction B S hS g).unit :=
  (Iso.comp_inv_eq (Functor.isoWhiskerRight (representedModulePullbackIso B S hS g hg)
      ((representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g)))).2
    (unit_comp_representedModulePullbackIso_hom B S hS g hg).symm

/-- For a sheaf of modules `M` on the small étale site of the scheme underlying `T`, the
inverse image along `φ` of the `𝒪`-module `M` becomes on the small étale site of `yoneda.obj T`
is the `𝒪`-module on the small étale site of `yoneda.obj T'` of the pullback of `M` along the
morphism of small étale ringed sites of the underlying morphism of schemes. -/
noncomputable def representedModuleObjPullbackIso
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M) ≅
      (representedSmallEtaleModuleEquivalence B S hS T').functor.obj
        ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).obj M) :=
  ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
      ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M))).symm ≪≫
    (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
      ((representedModulePullbackIso B S hS g hg).app
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj M) ≪≫
        (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS T).unitIso.app M).symm)

/-- For a Zariski sheaf of modules `𝓕` on the scheme underlying `T`, the inverse image along `φ`
of the `𝒪`-module that the associated module of `𝓕` becomes on the small étale site of
`yoneda.obj T` is the `𝒪`-module of the associated module of the Zariski pullback of `𝓕` along
the morphism of schemes underlying `g`. -/
noncomputable def representedAssociatedModulePullbackIso
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)) ≅
      (representedSmallEtaleModuleEquivalence B S hS T').functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
          ((Scheme.Modules.pullback (B.inclusion.map g.left)).obj 𝓕)) :=
  representedModuleObjPullbackIso B S hS g hg
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕) ≪≫
    (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
        (associatedBigEtaleSite B) g.left 𝓕).symm

end Represented

end AlgebraicGeometry.Space

end
