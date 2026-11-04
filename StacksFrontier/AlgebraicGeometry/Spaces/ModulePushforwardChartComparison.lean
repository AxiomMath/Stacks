module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength

/-!
# The direct image of modules along a representable morphism is base change of charts

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained
in a big fppf site `B`.  Two functors `Mod(𝒪_X) ⥤ Mod(𝒪_Y)` are available for such an `f`:

* `AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU, which is
  restriction of scalars along the structure map `f♯` of Stacks 03G8 applied to
  `Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` of
  `AlgebraicGeometry.Space.smallEtaleDirectImage` — the spaces-étale direct image conjugated by
  the comparison equivalence of Stacks 03G1, with the ring and module operations *transported*
  across that conjugation;
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, the concrete direct image whose
  sections over an étale chart `V` of `Y` are the sections of the module over the base-changed
  chart `V ×_Y X`, with structure map pullback of regular functions along the cartesian
  projection.

This file identifies them: `AlgebraicGeometry.Space.modulePushforwardChartIso`.

That identification is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionGeometricLength.lean` record as missing,
and it is missing in two pieces there.  The first — the transported ring and module operations
of `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` against the honest ones — is in fact
available, as `Stacks.Sheaves.ToposPullback.restrictionRingIso` and
`Stacks.Sheaves.ToposPullback.restrictionModuleIso`; those notes are stale on that point.  The
second, the identification of `AlgebraicGeometry.Space.structureSharp` with
`AlgebraicGeometry.Space.smallBaseChangeSharp`, is proved here as
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`.

The route is the one the source leaves implicit.  Sections of the direct image over `V` are the
limit of the sections over all étale scheme charts of `X` above the algebraic space `X ×_Y V`,
because the quasi-inverse of the comparison equivalence of Stacks 03G1 is a pointwise right Kan
extension (`AlgebraicGeometry.Space.ranChartIsLimit`).  When `f` is representable that index
category has an *initial* object: the base-changed scheme chart `V ×_Y X` of Stacks 03G2,
part (4) is itself such a chart, through the comparison isomorphism
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso`, and the comparison functor of
Stacks 03G1 is fully faithful, so every other chart above `X ×_Y V` factors through it
uniquely.  A limit over a category with an initial object is the value at that object, so the
limit collapses to the sections over `V ×_Y X` and the chart projection there is pullback along
the cartesian projection — which is exactly `smallBaseChangeSharp`.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeIndex` is the base-changed scheme chart `V ×_Y X`
  read as an étale scheme chart of `X` above `X ×_Y V`, i.e. as an object of the index category
  of the limit above.
* `AlgebraicGeometry.Space.chartRanApp` is the projection of that limit to its initial object,
  and `AlgebraicGeometry.Space.chartRanAppIso` is the same map as an isomorphism.
* `AlgebraicGeometry.Space.chartRanIso` is the resulting identification of the right Kan
  extension form of the direct image of sheaves of *sets* with restriction along base change of
  charts.
* `AlgebraicGeometry.Space.chartRingSheafMap` is the induced comparison of the direct image
  `f_*𝒪_X` of sheaves of rings with the restriction of `𝒪_X` along base change of charts.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeIndex_isInitial`: for a representable morphism the
  base-changed chart is an initial object of the index category of charts above `X ×_Y V`.
* `AlgebraicGeometry.Space.chartBaseChangeMap_smallBaseChangeIndex`: at that initial object the
  induced morphism of charts is the cartesian projection `V ×_Y X ⟶ V`.
* `AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`: **the structure map `f♯` of
  Stacks 03G8 is, for a representable morphism, pullback of regular functions along the
  cartesian projection** — that is, it is `AlgebraicGeometry.Space.smallBaseChangeSharp` read
  through the comparisons.
* `AlgebraicGeometry.Space.modulePushforwardChartIso`: **the direct image of modules of
  Stacks 03LU along a representable morphism is the direct image taken along base change of
  étale scheme charts.**

## Implementation notes

No declaration here carries a tag.  Stacks 04CF, the identity `f'_*(F|_U) = (f_*F)|_V`, is
already delivered for `AlgebraicGeometry.Space.modulePushforward` and an arbitrary morphism by
`AlgebraicGeometry.Space.modulePushforward_comp_overFunctorIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartRestriction.lean`), and the
agreement of the geometric direct image of Stacks 03G8 with scheme-chart base change is already
delivered by `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`.  What is added
here is the identification of the *functor on modules* being restricted, which is not the
assertion of either tag.

The comparison of sheaves of sets is built by hand rather than taken from
`AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`, which has the same
endpoints.  That one is assembled from `CategoryTheory.Functor.asEquivalence` of the comparison
restriction, whose inverse is extracted from an `IsEquivalence` instance and is therefore not
computable on sections; the structure-map identity cannot be checked through it.  The
hand-built comparison factors through the right Kan extension form
`AlgebraicGeometry.Space.smallEtaleDirectImageRan`, where the sections *are* a limit over the
charts, and `AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` carries it back; the
cancellation of that transport is the only place where the chosen quasi-inverse appears, and it
cancels formally.

`AlgebraicGeometry.Space.isContinuous_smallBaseChange_ringedSiteTarget` repeats the continuity
of base change of charts with the target topology spelled as the projection `.J` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`.  It is needed because the sheaf of rings
`AlgebraicGeometry.Space.structureRingSheaf`, through which
`AlgebraicGeometry.Space.structureSharp` is typed, is indexed by that projection, and instance
search does not unfold it — the same reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean`.

Three steps of the final assembly are definitional identities, used as such:
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans_comp`,
`SheafOfModules.pushforward_comp_restrictScalars` (restriction of scalars after a pushforward is
the pushforward along the composite structure map) and the fact that
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` is
`CategoryTheory.SheafOfModules.pushforward` of `AlgebraicGeometry.Space.smallBaseChangeSharp`.
They are stated in an abstract setting so that the final equality of functors is matched rather
than unfolded; spelled out concretely, the same equality sends the definitional unifier into a
`whnf` timeout.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  {Φ Φ' Φ'' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ'] [PreservesFiniteProducts Φ'']
  (O : Sheaf K RingCat.{ww'})

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The morphism of inverse-image sheaves of rings induced by a natural transformation is
functorial in that transformation: the transported ring structures are compared by the
transformation itself, so a composite induces the composite. -/
theorem pullbackRingSheafMapOfNatTrans_comp (θ : Φ ⟶ Φ') (θ' : Φ' ⟶ Φ'') :
    pullbackRingSheafMapOfNatTrans J O θ ≫ pullbackRingSheafMapOfNatTrans J O θ' =
      pullbackRingSheafMapOfNatTrans J O (θ ≫ θ') := rfl

end Stacks.Sheaves.ToposPullback

namespace SheafOfModules

universe wv wu wv' wu'

variable {C : Type wu} [Category.{wv} C] {D : Type wu'} [Category.{wv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsContinuous J K]

/-- Restriction of scalars after a direct image along a continuous functor of sites is the
direct image along the composite structure map: both only reindex sections and then read the
scalars through the two maps in turn. -/
theorem pushforward_comp_restrictScalars {R : Sheaf K RingCat.{u}} {T S : Sheaf J RingCat.{u}}
    (a : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) (b : S ⟶ T) :
    SheafOfModules.pushforward.{u} a ⋙ SheafOfModules.restrictScalars b =
      SheafOfModules.pushforward.{u} (b ≫ a) := rfl

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Applying an equality of maps of types -/

/-- An equality of morphisms of types, read on a point. -/
theorem typeHom_congr_apply {A C : Type u} {g h : A ⟶ C} (e : g = h) (a : A) : g a = h a :=
  congrArg (fun q : A ⟶ C => q a) e

/-! ### The chart projections of the right Kan extension -/

/-- The projection of the limit of chart sections to one chart, written out: restriction along
the given morphism followed by the counit of the Kan extension.  This is the definition of
`AlgebraicGeometry.Space.ranChartCone`, recorded for use in the two naturality lemmas below. -/
theorem ranChartCone_π_apply (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (W : SpacesEtale B S hS X)
    (j : StructuredArrow (op W) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj F).obj (op W)) :
    (ranChartCone B S hS X F W).π.app j a =
      ((comparisonFunctor B S hS X).op.ranCounit.app F).app j.right
        (((comparisonFunctor B S hS X).op.ran.obj F).map j.hom a) := rfl

/-- The chart projections are natural in the presheaf: the Kan extension and its counit both
are. -/
theorem ranChartCone_π_naturality (X : AlgebraicSpaces B S hS)
    {F F' : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u} (ψ : F ⟶ F') (W : SpacesEtale B S hS X)
    (j : StructuredArrow (op W) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj F).obj (op W)) :
    (ranChartCone B S hS X F' W).π.app j
        (((comparisonFunctor B S hS X).op.ran.map ψ).app (op W) a) =
      ψ.app j.right ((ranChartCone B S hS X F W).π.app j a) := by
  have h := CategoryTheory.congr_app
    ((comparisonFunctor B S hS X).op.ranCounit.naturality ψ) j.right
  refine (ranChartCone_π_apply B S hS X F' W j _).trans ?_
  refine Eq.trans (congrArg
    (((comparisonFunctor B S hS X).op.ranCounit.app F').app j.right)
    (NatTrans.naturality_apply ((comparisonFunctor B S hS X).op.ran.map ψ) j.hom a).symm) ?_
  exact typeHom_congr_apply h (((comparisonFunctor B S hS X).op.ran.obj F).map j.hom a)

/-- The chart projections form a cone: the projection to a chart followed by restriction to a
chart above it is the projection to the latter. -/
theorem ranChartCone_π_comp (X : AlgebraicSpaces B S hS)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (W : SpacesEtale B S hS X)
    {j j' : StructuredArrow (op W) (comparisonFunctor B S hS X).op} (φ : j ⟶ j')
    (a : ((comparisonFunctor B S hS X).op.ran.obj F).obj (op W)) :
    F.map φ.right ((ranChartCone B S hS X F W).π.app j a) =
      (ranChartCone B S hS X F W).π.app j' a :=
  typeHom_congr_apply ((ranChartCone B S hS X F W).w φ) a

/-! ### The base-changed chart as an initial index -/

/-- The base-changed scheme chart `V ×_Y X` of Stacks 03G2, part (4), read as an étale scheme
chart of `X` above the algebraic space `X ×_Y V`: the structure morphism is the comparison
isomorphism `AlgebraicGeometry.Space.smallBaseChangeComparisonIso` of the two base changes. -/
noncomputable def smallBaseChangeIndex (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk (Y := op ((smallBaseChange B S hS f hf).obj V))
    (smallBaseChangeComparisonIso B S hS f hf V).hom.op

/-- **The base-changed chart is an initial index.** For a representable morphism, every étale
scheme chart of `X` above `X ×_Y V` factors through the base-changed chart `V ×_Y X` by a unique
morphism of charts: the comparison functor of Stacks 03G1 is fully faithful, so a morphism to
`X ×_Y V` in the spaces-étale site comes from a unique morphism of scheme charts. -/
noncomputable def smallBaseChangeIndex_isInitial (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    IsInitial (smallBaseChangeIndex B S hS f hf V) := by
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  refine IsInitial.ofUniqueHom (fun j => StructuredArrow.homMk
    ((comparisonFunctor B S hS X).preimage
      (j.hom.unop ≫ (smallBaseChangeComparisonIso B S hS f hf V).inv)).op ?_) ?_
  · change (smallBaseChangeComparisonIso B S hS f hf V).hom.op ≫ _ = j.hom
    apply Quiver.Hom.unop_inj
    change (comparisonFunctor B S hS X).map
        ((comparisonFunctor B S hS X).preimage
          (j.hom.unop ≫ (smallBaseChangeComparisonIso B S hS f hf V).inv)) ≫
        (smallBaseChangeComparisonIso B S hS f hf V).hom = j.hom.unop
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro j m
    refine StructuredArrow.hom_ext _ _ ?_
    apply Quiver.Hom.unop_inj
    apply (comparisonFunctor B S hS X).map_injective
    have h : (comparisonFunctor B S hS X).map m.right.unop ≫
        (smallBaseChangeComparisonIso B S hS f hf V).hom = j.hom.unop :=
      congrArg Quiver.Hom.unop (StructuredArrow.w m)
    exact ((Iso.eq_comp_inv _).2 h).trans (Functor.map_preimage _ _).symm

/-- A morphism of étale charts of `Y` induces a morphism of the base-changed indices, over the
base change of the morphism of charts. -/
noncomputable def smallBaseChangeIndexMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {V₁ V₂ : SmallEtale B S hS Y.1} (k : V₁ ⟶ V₂) :
    smallBaseChangeIndex B S hS f hf V₂ ⟶
      (StructuredArrow.mk (((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map k)).op ≫
          (smallBaseChangeIndex B S hS f hf V₁).hom) :
        StructuredArrow (op (chartBaseChange B S hS f V₂))
          (comparisonFunctor B S hS X).op) :=
  StructuredArrow.homMk ((smallBaseChange B S hS f hf).map k).op (by
    change (smallBaseChangeComparisonIso B S hS f hf V₂).hom.op ≫
        ((comparisonFunctor B S hS X).map ((smallBaseChange B S hS f hf).map k)).op =
      ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map k)).op ≫
        (smallBaseChangeComparisonIso B S hS f hf V₁).hom.op
    exact Quiver.Hom.unop_inj ((smallBaseChange_comparison B S hS f hf).hom.naturality k))

/-! ### The comparison of sheaves of sets -/

/-- The projection of the limit of chart sections over `V` to its initial index: the sections of
the direct image of a presheaf over an étale chart `V` of `Y`, read as sections over the
base-changed chart `V ×_Y X`. -/
noncomputable abbrev chartRanApp (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (V : SmallEtale B S hS Y.1) :
    ((comparisonFunctor B S hS X).op.ran.obj F).obj (op (chartBaseChange B S hS f V)) ⟶
      F.obj (op ((smallBaseChange B S hS f hf).obj V)) :=
  (ranChartCone B S hS X F (chartBaseChange B S hS f V)).π.app
    (smallBaseChangeIndex B S hS f hf V)

/-- The projection to the initial index is an isomorphism: a limit over a category with an
initial object is the value at that object. -/
noncomputable def chartRanAppIso (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (V : SmallEtale B S hS Y.1) :
    ((comparisonFunctor B S hS X).op.ran.obj F).obj (op (chartBaseChange B S hS f V)) ≅
      F.obj (op ((smallBaseChange B S hS f hf).obj V)) :=
  IsLimit.conePointUniqueUpToIso (ranChartIsLimit B S hS X F (chartBaseChange B S hS f V))
    (limitOfDiagramInitial (smallBaseChangeIndex_isInitial B S hS f hf V) _)

/-- The isomorphism of `AlgebraicGeometry.Space.chartRanAppIso` is the chart projection: the
limit cone over a category with an initial object projects to that object by the identity. -/
theorem chartRanAppIso_hom (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (V : SmallEtale B S hS Y.1) :
    (chartRanAppIso B S hS f hf F V).hom = chartRanApp B S hS f hf F V :=
  have hπ : (coneOfDiagramInitial (smallBaseChangeIndex_isInitial B S hS f hf V)
        (StructuredArrow.proj (op (chartBaseChange B S hS f V))
          (comparisonFunctor B S hS X).op ⋙ F)).π.app
        (smallBaseChangeIndex B S hS f hf V) = 𝟙 _ :=
    (congrArg (StructuredArrow.proj (op (chartBaseChange B S hS f V))
        (comparisonFunctor B S hS X).op ⋙ F).map
      ((smallBaseChangeIndex_isInitial B S hS f hf V).hom_ext _ (𝟙 _))).trans
      (CategoryTheory.Functor.map_id _ _)
  (Category.comp_id _).symm.trans
    ((congrArg (fun q => (chartRanAppIso B S hS f hf F V).hom ≫ q) hπ.symm).trans
      ((limitOfDiagramInitial (smallBaseChangeIndex_isInitial B S hS f hf V) _).fac
        (ranChartCone B S hS X F (chartBaseChange B S hS f V))
        (smallBaseChangeIndex B S hS f hf V)))

/-- The chart projection `AlgebraicGeometry.Space.chartRanApp` is an isomorphism of types. -/
instance isIso_chartRanApp (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u) (V : SmallEtale B S hS Y.1) :
    IsIso (chartRanApp B S hS f hf F V) := by
  rw [← chartRanAppIso_hom]
  infer_instance

/-- The comparison on one sheaf of sets: the sections of the right Kan extension form of the
direct image over an étale chart `V` of `Y` are the sections over the base-changed chart
`V ×_Y X`.  Naturality in `V` is the compatibility of the base-changed indices with morphisms of
charts. -/
noncomputable def chartRanSheafHom (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleDirectImageRan B S hS f).obj G ⟶
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj G where
  hom :=
    { app := fun V => chartRanApp B S hS f hf G.obj V.unop
      naturality := fun V₂ V₁ m => by
        ext a
        refine (ranChartCone_π_map B S hS X G.obj
          ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map m.unop))
          (smallBaseChangeIndex B S hS f hf V₁.unop) a).trans ?_
        exact (ranChartCone_π_comp B S hS X G.obj (chartBaseChange B S hS f V₂.unop)
          (smallBaseChangeIndexMap B S hS f hf m.unop) a).symm }

/-- The comparison is natural in the sheaf of sets. -/
noncomputable def chartRanNatTrans (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallEtaleDirectImageRan B S hS f ⟶
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) where
  app G := chartRanSheafHom B S hS f hf G
  naturality G G' ψ := by
    ext V a
    exact ranChartCone_π_naturality B S hS X ψ.hom (chartBaseChange B S hS f V.unop)
      (smallBaseChangeIndex B S hS f hf V.unop) a

/-- The comparison `AlgebraicGeometry.Space.chartRanSheafHom` on a sheaf of sets is an
isomorphism of sheaves. -/
instance isIso_chartRanSheafHom (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    IsIso (chartRanSheafHom B S hS f hf G) := by
  have happ : ∀ V : (SmallEtale B S hS Y.1)ᵒᵖ,
      IsIso (((sheafToPresheaf (SmallEtale.topology B S hS Y.1) (Type u)).map
        (chartRanSheafHom B S hS f hf G)).app V) := fun V =>
    isIso_chartRanApp B S hS f hf G.obj V.unop
  have : IsIso ((sheafToPresheaf (SmallEtale.topology B S hS Y.1) (Type u)).map
      (chartRanSheafHom B S hS f hf G)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf (SmallEtale.topology B S hS Y.1) (Type u))

/-- The natural transformation `AlgebraicGeometry.Space.chartRanNatTrans` is a natural
isomorphism. -/
instance isIso_chartRanNatTrans (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    IsIso (chartRanNatTrans B S hS f hf) := by
  have happ : ∀ G : Sheaf (SmallEtale.topology B S hS X.1) (Type u),
      IsIso ((chartRanNatTrans B S hS f hf).app G) := fun G =>
    isIso_chartRanSheafHom B S hS f hf G
  exact NatIso.isIso_of_isIso_app _

/-- **For a representable morphism the direct image of sheaves of sets is restriction along base
change of étale scheme charts**, in the right Kan extension form of the direct image.

Unlike `AlgebraicGeometry.Space.smallEtaleDirectImageIsoSheafPushforward`, which has the same
endpoints, this one is computable on sections: it is the chart projection
`AlgebraicGeometry.Space.chartRanApp`.  See the implementation notes. -/
noncomputable def chartRanIso (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    smallEtaleDirectImageRan B S hS f ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  asIso (chartRanNatTrans B S hS f hf)

/-! ### The structure map -/

/-- At the initial index the induced morphism of charts is the cartesian projection
`V ×_Y X ⟶ V`: that is the defining property of the comparison isomorphism of the two base
changes. -/
theorem chartBaseChangeMap_smallBaseChangeIndex (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    chartBaseChangeMap B S hS f V (smallBaseChangeIndex B S hS f hf V) = hf.snd V.1.hom := by
  apply yoneda.map_injective
  refine (yoneda_map_chartBaseChangeMap B S hS f V
    (smallBaseChangeIndex B S hS f hf V)).trans ?_
  exact congrArg (fun q => q.hom)
    (smallBaseChangeComparisonIso_hom_projection B S hS f hf V)

open Stacks.Sheaves.ToposPullback in
/-- The structure map of Stacks 03G8 in its right Kan extension form, read through the
comparisons of this file, is `AlgebraicGeometry.Space.smallBaseChangeSharp`: on an étale chart
`V` of `Y` both send a regular function to its pullback along the cartesian projection
`V ×_Y X ⟶ V`. -/
theorem structureSharpRan_comp_chartRanIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureSharpRan B S hS f ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X) (chartRanIso B S hS f hf).hom ≫
        (restrictionRingIso (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
          (structureRingSheaf B S hS X)).hom =
      smallBaseChangeSharp B S hS f hf := by
  apply Sheaf.hom_ext
  ext V x
  refine (congrArg (fun φ => φ x) ((chartIsLimit B S hS f V.unop).fac
    (chartPullbackCone B S hS f V.unop) (smallBaseChangeIndex B S hS f hf V.unop))).trans ?_
  exact congrArg (fun g => ((forget CommRingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op)) x)
    (chartBaseChangeMap_smallBaseChangeIndex B S hS f hf V.unop)

open Stacks.Sheaves.ToposPullback in
/-- **The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 is, for a representable morphism,
pullback of regular functions along base change of étale scheme charts.**

This is the comparison that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean` list as the second
missing piece: `AlgebraicGeometry.Space.structureSharp` is built through the right Kan extension
of Stacks 03G1 and is here identified with
`AlgebraicGeometry.Space.smallBaseChangeSharp`, the structure map of the morphism of small étale
ringed *sites*, through the comparison of the direct images of sheaves of rings. -/
theorem structureSharp_comp_chartRanIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureSharp B S hS f ≫
        pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X)
          (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom ≫
        (restrictionRingIso (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
          (structureRingSheaf B S hS X)).hom =
      smallBaseChangeSharp B S hS f hf := by
  refine Eq.trans ?_ (structureSharpRan_comp_chartRanIso B S hS f hf)
  rw [structureSharp, Category.assoc]
  refine congrArg (fun q => structureSharpRan B S hS f ≫ q) ?_
  rw [← Category.assoc, pullbackRingSheafMapOfNatTrans_comp, Iso.trans_hom,
    Iso.inv_hom_id_assoc]

/-! ### The comparison of the direct images of modules -/

/-- Base change of étale scheme charts is continuous for the topologies of the small étale
ringed sites, with the target topology spelled as the projection `.J` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`; see the implementation notes. -/
instance isContinuous_smallBaseChange_ringedSiteTarget (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (smallBaseChange B S hS f hf).IsContinuous (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedSite B S hS X.1 X.2).J :=
  isContinuous_smallBaseChange B S hS f hf

open Stacks.Sheaves.ToposPullback in
/-- The comparison of the direct image `f_*𝒪_X` of the structure sheaf of rings with the
restriction of `𝒪_X` along base change of étale scheme charts, as a morphism of sheaves of
rings. -/
noncomputable def chartRingSheafMap (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureRingSheafDirectImage B S hS f ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        ((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1))
        (structureRingSheaf B S hS X) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
    (structureRingSheaf B S hS X)
    (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom

open Stacks.Sheaves.ToposPullback in
/-- Restriction of modules along base change of charts, read through the two ring comparisons and
the structure map of Stacks 03G8, *is*
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`: the three restrictions of scalars
collapse to one along the composite structure map, which is
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`. -/
theorem smallBaseChangeModulePushforward_eq (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    ((SheafOfModules.pushforward.{u}
            (𝟙 (((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
              (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
              (structureRingSheaf B S hS X))) ⋙
          SheafOfModules.restrictScalars (restrictionRingIso (SmallEtale.topology B S hS Y.1)
            (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
            (structureRingSheaf B S hS X)).hom) ⋙
        SheafOfModules.restrictScalars (chartRingSheafMap B S hS f hf)) ⋙
      SheafOfModules.restrictScalars (structureSharp B S hS f) =
    smallBaseChangeModulePushforward.{u, u} B S hS f hf := by
  rw [SheafOfModules.pushforward_comp_restrictScalars, Category.comp_id,
    SheafOfModules.pushforward_comp_restrictScalars,
    SheafOfModules.pushforward_comp_restrictScalars, chartRingSheafMap,
    structureSharp_comp_chartRanIso]
  rfl

open Stacks.Sheaves.ToposPullback in
/-- **The direct image of modules along a representable morphism of algebraic spaces is base
change of étale scheme charts.** For a representable `f : X ⟶ Y`, the direct image
`f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` of Stacks 03LU — built from the comparison equivalence of
Stacks 03G1 with the ring and module operations transported across it — is the concrete direct
image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, whose sections over an étale
chart `V` of `Y` are the sections over the base-changed chart `V ×_Y X` and whose structure map
is pullback of regular functions along the cartesian projection.

This is the identification that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionGeometricLength.lean` record as missing;
with it, results proved for either functor transfer to the other.  It carries no tag; see the
implementation notes. -/
noncomputable def modulePushforwardChartIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    modulePushforward B S hS f ≅ smallBaseChangeModulePushforward.{u, u} B S hS f hf := by
  refine ?_ ≪≫ eqToIso (smallBaseChangeModulePushforward_eq B S hS f hf)
  exact Functor.isoWhiskerRight
    (pullbackModuleFunctorIsoOfNatIso (SmallEtale.topology B S hS Y.1)
        (structureRingSheaf B S hS X)
        (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf)
        (chartRingSheafMap B S hS f hf)
        (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X)
          (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom) ≪≫
      Functor.isoWhiskerRight
        (restrictionModuleIso (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
          (structureRingSheaf B S hS X)) _)
    (SheafOfModules.restrictScalars (structureSharp B S hS f))

/-! ### The direct image along a closed immersion -/

/-- **For a closed immersion the direct image of modules of Stacks 03LU is the base-change
direct image.** A closed immersion is representable, so
`AlgebraicGeometry.Space.chartDirectImage` — the functor for which the geometric-stalk,
flatness, support and finiteness results on chart direct images are stated — computes
`AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU.  This is the specialisation of
`AlgebraicGeometry.Space.modulePushforwardChartIso` at which those results apply to the direct
image of Stacks 03LU. -/
noncomputable def modulePushforwardIsoChartDirectImage (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).obj G ≅ chartDirectImage.{u, u} B S hS f hf G :=
  (modulePushforwardChartIso B S hS f hf.rep).app G

end AlgebraicGeometry.Space

end
