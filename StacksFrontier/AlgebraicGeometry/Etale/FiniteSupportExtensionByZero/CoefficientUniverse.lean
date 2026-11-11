module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero.Stalk
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction

/-!
# Extension by zero is the finite-support direct image, at every coefficient universe

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`.
`StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero.Stalk` proves [Stacks, Tag 0F6Q]
for abelian sheaves with coefficients in `AddCommGrpCat.{u + 1}`: extension by zero `j_!` is the
direct image with compact support `j_!` of [Stacks, Tag 0F6R]. This file proves the same at the
coefficients `AddCommGrpCat.{max (u + 1) v}`, for every universe `v`, by the same argument.

## Main definitions

* `AlgebraicGeometry.abelianExtensionByZeroUniv`: extension by zero of abelian sheaves with
  coefficients in `AddCommGrpCat.{max (u + 1) v}`, the left adjoint of restriction
  (`AlgebraicGeometry.abelianExtensionByZeroAdjunctionUniv`).
* `AlgebraicGeometry.SmallEtale.etaleExtensionToFiniteSupportUniv`: the canonical map
  `j_{p!} ⟶ f_{p!}` from the presheaf extension by zero to the finite-support direct image
  presheaf.
* `AlgebraicGeometry.SmallEtale.abelianExtensionByZeroIsoFShriekUniv`: extension by zero is the
  direct image with compact support `AlgebraicGeometry.SmallEtale.fShriekFunctor`.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleExtensionToFiniteSupportUniv_sheafify_isIso`: the canonical
  map becomes an isomorphism after sheafification.

## Implementation notes

The construction and the proof are those of the coefficients `AddCommGrpCat.{u + 1}`: the
canonical map comes from the universal property of the left Kan extension and the graph
generators, and it is shown to be an isomorphism on every geometric stalk through the germ
decomposition of [Stacks, Tag 0F6P]. The finite-support direct image, the germ decomposition
and the stalk criterion `AlgebraicGeometry.isIso_of_isIso_etaleStalkMap` are all available at
every coefficient universe containing `u + 1`.

## References

* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/- Sheafification of abelian presheaves on the small étale site is taken through the essential
smallness of the site, as for `AlgebraicGeometry.SmallEtale.fShriekFunctor`, so that the two
sheafifications agree. -/
attribute [local instance high] AlgebraicGeometry.hasSheafify_smallEtaleTopology


namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Restriction of abelian étale sheaves along the étale morphism `U ⟶ X`. -/
public abbrev abelianRestrictionUniv :
    Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{max (u + 1) v} :=
  (smallEtalePostcompose B X hX U).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- The *presheaf* extension by zero `j_{p!}` of an abelian étale sheaf along the étale
morphism `U ⟶ X`: the left Kan extension `V ↦ ⨁_{φ : V → U} F(V →^φ U)` of the underlying
presheaf along the site functor `AlgebraicGeometry.smallEtalePostcompose`, before
sheafification. -/
public abbrev abelianPresheafExtensionByZeroUniv :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{max (u + 1) v} ⥤
      ((SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :=
  sheafToPresheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{max (u + 1) v} ⋙
    (smallEtalePostcompose B X hX U).op.lan

/-- Extension by zero of abelian étale sheaves along the étale
morphism `U ⟶ X`: the sheafification of `V ↦ ⨁_{V → U} F(V → U)`, realised as the sheaf
pullback of the continuous site functor `AlgebraicGeometry.smallEtalePostcompose`. -/
public def abelianExtensionByZeroUniv :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B X hX U)
    AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- Extension by zero is left adjoint to restriction, which is
the property characterising it. -/
public def abelianExtensionByZeroAdjunctionUniv :
    abelianExtensionByZeroUniv B X hX U ⊣ abelianRestrictionUniv B X hX U :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtalePostcompose B X hX U)
    AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- The supports finite over an étale test object are small at the coefficient universe, so
the colimit of Stacks 0F6M defining the finite-support direct image exists. -/
public theorem small_finiteSupport_smallEtaleUniv :
    ∀ V : SmallEtale B X hX, Small.{max (u + 1) v} (FiniteSupport B U.obj.hom V) :=
  fun _ => inferInstance

/-- The finite-support direct image presheaf of Stacks 0F6M, together with its
characterisation, for the étale morphism `U ⟶ X`. -/
public abbrev etaleFiniteSupportDataUniv :=
  finiteSupportPushforward B U.obj.hom (small_finiteSupport_smallEtaleUniv B X hX U)

/-- **Stacks 0F6M** for an étale morphism: the presheaf `f_{p!}F = colim_Z H_Z(F)` on the
small étale site of `X`, functorially in the abelian sheaf `F` on the small étale site
of `U`. -/
public abbrev etaleFiniteSupportPresheafUniv :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{max (u + 1) v} ⥤
      ((SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :=
  (etaleFiniteSupportDataUniv B X hX U).1


/-! ### The canonical comparison map -/

section Comparison

variable (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
  AddCommGrpCat.{max (u + 1) v})

/-! The graph generators `AlgebraicGeometry.SmallEtale.graphSectionToFiniteSupport` and their
naturality and restriction lemmas are stated at every coefficient universe in
`StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero.Comparison`; only their
assembly into a map to the finite-support direct image presheaf is made here. -/

/-- The graph generators, assembled into a morphism from `F` to the restriction along `U ⟶ X`
of the finite-support direct image of `F`. This is the datum the universal property of the
left Kan extension turns into the comparison map. -/
public def graphSectionPreunitUniv :
    F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙
      (etaleFiniteSupportPresheafUniv B X hX U).obj F where
  app W := graphSectionToFiniteSupport.{u, v} B X hX U F W.unop
  naturality _ _ g := (graphSectionToFiniteSupport_restrict.{u, v} B X hX U F g.unop).symm

end Comparison

/-! ### Stacks 0F6Q: the canonical map and its value on generators -/

/-- The canonical map `j_{p!} ⟶ f_{p!}` from the presheaf extension by zero
along the étale morphism `U ⟶ X` to the finite-support direct image presheaf, natural in the
abelian sheaf on the small étale site of `U`. It is the map the universal property of the left
Kan extension produces from the graph generators. -/
public def etaleExtensionToFiniteSupportUniv :
    abelianPresheafExtensionByZeroUniv.{u, v} B X hX U ⟶
      etaleFiniteSupportPresheafUniv.{u, v} B X hX U where
  app F := (smallEtalePostcompose B X hX U).op.lan.map (graphSectionPreunitUniv.{u, v} B X hX U F) ≫
    ((smallEtalePostcompose B X hX U).op.lanAdjunction AddCommGrpCat.{max (u + 1) v}).counit.app
      ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).obj F)
  naturality F G φ := by
    have hpre : φ.hom ≫ graphSectionPreunitUniv.{u, v} B X hX U G =
        graphSectionPreunitUniv.{u, v} B X hX U F ≫ Functor.whiskerLeft
          (smallEtalePostcompose B X hX U).op
          ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).map φ) := by
      refine NatTrans.ext (funext fun W => ?_)
      exact (graphSectionToFiniteSupport_naturality.{u, v} B X hX U φ W.unop).symm
    have hc := ((smallEtalePostcompose B X hX U).op.lanAdjunction
      AddCommGrpCat.{max (u + 1) v}).counit.naturality
        ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).map φ)
    change (smallEtalePostcompose B X hX U).op.lan.map (Functor.whiskerLeft
          (smallEtalePostcompose B X hX U).op
          ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).map φ)) ≫
        ((smallEtalePostcompose B X hX U).op.lanAdjunction
          AddCommGrpCat.{max (u + 1) v}).counit.app
          ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).obj G) =
      ((smallEtalePostcompose B X hX U).op.lanAdjunction
          AddCommGrpCat.{max (u + 1) v}).counit.app
          ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).obj F) ≫
        (etaleFiniteSupportPresheafUniv.{u, v} B X hX U).map φ at hc
    change (smallEtalePostcompose B X hX U).op.lan.map φ.hom ≫
        ((smallEtalePostcompose B X hX U).op.lan.map (graphSectionPreunitUniv.{u, v} B X hX U G) ≫
          ((smallEtalePostcompose B X hX U).op.lanAdjunction
            AddCommGrpCat.{max (u + 1) v}).counit.app
            ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).obj G)) =
      ((smallEtalePostcompose B X hX U).op.lan.map (graphSectionPreunitUniv.{u, v} B X hX U F) ≫
          ((smallEtalePostcompose B X hX U).op.lanAdjunction
            AddCommGrpCat.{max (u + 1) v}).counit.app
            ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).obj F)) ≫
        (etaleFiniteSupportPresheafUniv.{u, v} B X hX U).map φ
    rw [← Category.assoc, ← Functor.map_comp, hpre, Functor.map_comp, Category.assoc, hc,
      Category.assoc]

/-- The value of the canonical map on a generator of the presheaf extension
by zero: the section of `F` over an étale object `W → U`, viewed in the summand of `j_{p!}F`
over `W` indexed by `W ⟶ U`, goes to the colimit generator of `colim_Z H_Z(F)` at the graph of
`W → U`, carrying the section supported on that graph. Naturality of the comparison then
extends the formula to every lift `V ⟶ U` of an arbitrary étale test object `V ⟶ X`. -/
public theorem etaleExtensionToFiniteSupportUniv_on_graph
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{max (u + 1) v})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (s : F.obj.obj (op W)) :
    ((etaleExtensionToFiniteSupportUniv B X hX U).app F).app
        (op ((smallEtalePostcompose B X hX U).obj W))
        (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) s) =
      colimit.ι (finiteSupportDiagram B U.obj.hom F ((smallEtalePostcompose B X hX U).obj W))
        (etaleGraphFiniteSupport B X hX U W) (etaleGraphSection B X hX U F W s) := by
  have h := (((smallEtalePostcompose B X hX U).op.lanAdjunction
    AddCommGrpCat.{max (u + 1) v}).homEquiv F.obj
      ((etaleFiniteSupportPresheafUniv.{u, v} B X hX U).obj F)).apply_symm_apply
      (graphSectionPreunitUniv.{u, v} B X hX U F)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_symm_apply,
    Functor.lanAdjunction_unit] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op W)) s


/-! ### The stalks at a geometric point -/

section Stalk

variable (s : GeometricPoint X)
  (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{max (u + 1) v})

/-- The map from the stalk of `F` at a point of the geometric fibre to the stalk of the
presheaf extension by zero at the geometric point of `X` below it: the germ at an étale
neighbourhood of the fibre point is sent to the germ of the corresponding generator of the
left Kan extension over the same neighbourhood, viewed as an étale neighbourhood of `X`. -/
public def liftedStalkToExtensionUniv (x : GeometricFiberPoint B U.obj.hom s) :
    etaleStalk B U.obj.left.1 U.obj.left.property (x.toGeometricPoint B U.obj.hom s) F.obj ⟶
      etaleStalk B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F) := by
  refine colimit.desc _ {
    pt := etaleStalk B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F)
    ι := {
      app := fun N => ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app
          (op N.unop.1) ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))
          (op (liftedElement B X hX U s x N.unop.1 N.unop.2))
      naturality := ?_ } }
  intro N M k
  have hunit := ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).naturality k.unop.1.op
  have hw := colimit.w (etaleStalkDiagram B X hX s
    ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))
      (Quiver.Hom.op (liftedNeighborhoodMap B X hX U s x k.unop))
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ colimit.ι (etaleStalkDiagram B X hX s
    ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))
      (op (liftedElement B X hX U s x M.unop.1 M.unop.2))) hunit) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app
    (op N.unop.1) ≫ z) hw

/-- The germ decomposition `(f_{p!}F)_ȳ ⟶ ⊕_{j(x̄) = ȳ} F_x̄` of Stacks 0F6P for the étale
morphism `U ⟶ X`. -/
public abbrev etaleFiniteSupportStalkMapUniv :
    etaleStalk B X hX s ((etaleFiniteSupportPresheafUniv B X hX U).obj F) ⟶
      AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B U.obj.hom s F) :=
  finiteSupportStalkToFiberStalks.{u, max (u + 1) v} B U.obj.hom s F
    (small_finiteSupport_smallEtaleUniv B X hX U)

/-- On the summand at a point `x̄` of the geometric fibre, the germ decomposition sends the
germ of a graph generator over an étale neighbourhood of `x̄` to the germ of the section it
came from. -/
private theorem etaleFiniteSupportStalkMapUniv_graph
    (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W)
    (a : F.obj.obj (op W)) :
    (etaleFiniteSupportStalkMapUniv B X hX U s F
      (etaleGerm B X hX s ((etaleFiniteSupportPresheafUniv B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W q)
        (graphSectionToFiniteSupport.{u, v} B X hX U F W a))) x =
      etaleGerm B U.obj.left.1 U.obj.left.property (x.toGeometricPoint B U.obj.hom s) F.obj
        W q a := by
  have hcomp := etaleGraphIntoSupportOpen_comp B X hX U W
  have hfst : q.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (etaleGraphIntoSupportOpen B X hX U W) ≫
        (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
          (etaleGraphFiniteSupport B X hX U W)).ι ≫
        B.inclusion.map (pullback.fst
          ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
      (liftedPoint B X hX U s x W q).1 := by
    rw [← Category.assoc ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (etaleGraphIntoSupportOpen B X hX U W)), hcomp, etaleGraphMap_comp_fst B X hX U W]
    exact Category.comp_id _
  have hsnd : q.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (etaleGraphIntoSupportOpen B X hX U W) ≫
        (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
          (etaleGraphFiniteSupport B X hX U W)).ι ≫
        B.inclusion.map (pullback.snd
          ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) = x.1 := by
    rw [← Category.assoc ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (etaleGraphIntoSupportOpen B X hX U W)), hcomp, etaleGraphMap_comp_snd B X hX U W]
    exact q.2
  have h := finiteSupportStalkToFiberStalks_germ.{u, max (u + 1) v} B U.obj.hom s F
    (small_finiteSupport_smallEtaleUniv B X hX U) x
    ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W)
      (liftedPoint B X hX U s x W q))
    (etaleGraphFiniteSupport B X hX U W) (Functor.elementsMk _ W q)
    (etaleGraphIntoSupportOpen B X hX U W)
    hfst hsnd (etaleGraphSection B X hX U F W a)
  refine h.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  exact congrArg _ (etaleGraphSection_restrict B X hX U F W a)

/-- On every other summand the germ decomposition kills the germ of a graph generator: a point
of the geometric fibre at which the generator does not vanish lifts into the canonical open of
the graph, and on the graph the two projections agree, so that point is `x̄`. -/
private theorem etaleFiniteSupportStalkMapUniv_graph_ne
    (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W)
    (a : F.obj.obj (op W))
    (y : GeometricFiberPoint B U.obj.hom s) (hxy : y ≠ x) :
    (etaleFiniteSupportStalkMapUniv B X hX U s F
      (etaleGerm B X hX s ((etaleFiniteSupportPresheafUniv B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W q)
        (graphSectionToFiniteSupport.{u, v} B X hX U F W a))) y = 0 := by
  classical
  by_cases h : ∃ (V : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (y.toGeometricPoint B U.obj.hom s)).Elements)
      (t : V.1 ⟶ finiteSupportOpenObject B U.obj.hom
        ((smallEtalePostcompose B X hX U).obj W) (etaleGraphFiniteSupport B X hX U W)),
      (V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t ≫
          (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
            (etaleGraphFiniteSupport B X hX U W)).ι ≫
          B.inclusion.map (pullback.fst
            ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
        (liftedPoint B X hX U s x W q).1) ∧
      (V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t ≫
          (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
            (etaleGraphFiniteSupport B X hX U W)).ι ≫
          B.inclusion.map (pullback.snd
            ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) = y.1)
  · obtain ⟨V, t, hfst, hsnd⟩ := h
    have hg := finiteSupportStalkToFiberStalks_germ.{u, max (u + 1) v} B U.obj.hom s F
      (small_finiteSupport_smallEtaleUniv B X hX U) y
      ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W)
      (liftedPoint B X hX U s x W q))
      (etaleGraphFiniteSupport B X hX U W) V t hfst hsnd
      (etaleGraphSection B X hX U F W a)
    refine hg.trans ?_
    have hw : (V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t) ≫
        B.inclusion.map (finiteSupportOpenObject B U.obj.hom
          ((smallEtalePostcompose B X hX U).obj W)
          (etaleGraphFiniteSupport B X hX U W)).obj.hom = y.1 := by
      rw [Category.assoc, ← SmallEtale.toScheme_map_comp B U.obj.left.1 U.obj.left.property
        (openObjectι B U.obj.left.1 U.obj.left.property
          (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
          (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
            (etaleGraphFiniteSupport B X hX U W))), openObjectι_map]
      exact hsnd
    have hzero := etaleGerm_eq_zero_of_notMem_supportSection B U.obj.left.1
      U.obj.left.property (y.toGeometricPoint B U.obj.hom s) F
      (finiteSupportOpenObject B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
        (etaleGraphFiniteSupport B X hX U W))
      ⟨V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t, hw⟩
      (etaleGraphSection B X hX U F W a).val (by
        intro hmem
        have hz := (etaleGraphSection B X hX U F W a).property hmem
        have he := etaleGraph_fiber_eq_of_mem B X hX U W (y.toGeometricPoint
          B U.obj.hom s).source
          ((V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t) ≫
            (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
              (etaleGraphFiniteSupport B X hX U W)).ι) default hz
        have hsndL : ((V.2.1 ≫
            (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t) ≫
            (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
              (etaleGraphFiniteSupport B X hX U W)).ι) ≫
            B.inclusion.map (pullback.snd
              ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) = y.1 := by
          simpa only [Category.assoc] using hsnd
        have hfstL : ((V.2.1 ≫
            (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t) ≫
            (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
              (etaleGraphFiniteSupport B X hX U W)).ι) ≫
            B.inclusion.map (pullback.fst
              ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
            (liftedPoint B X hX U s x W q).1 := by
          simpa only [Category.assoc] using hfst
        refine hxy (Subtype.ext ?_)
        rw [← hsndL, he, ← Category.assoc, hfstL]
        exact q.2)
    let hk : V ⟶ (Functor.elementsMk _ (finiteSupportOpenObject B U.obj.hom
        ((smallEtalePostcompose B X hX U).obj W)
        (etaleGraphFiniteSupport B X hX U W))
        ⟨V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map t, hw⟩ :
          (geometricPointFiber B U.obj.left.1 U.obj.left.property
            (y.toGeometricPoint B U.obj.hom s)).Elements) := ⟨t, rfl⟩
    exact (ConcreteCategory.congr_hom (colimit.w (etaleStalkDiagram B U.obj.left.1
      U.obj.left.property (y.toGeometricPoint B U.obj.hom s) F.obj) (Quiver.Hom.op hk))
        (etaleGraphSection B X hX U F W a).val).trans hzero
  · exact finiteSupportStalkToFiberStalks_zero_of_no_open_lift.{u, max (u + 1) v} B U.obj.hom s F
      (small_finiteSupport_smallEtaleUniv B X hX U) y
      ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W)
      (liftedPoint B X hX U s x W q))
      (etaleGraphFiniteSupport B X hX U W) h (etaleGraphSection B X hX U F W a)

/-- Two maps out of the stalk of the presheaf extension by zero agree as soon as they agree on
the germs of the generators coming from étale objects over `U`: the stalk is a colimit over
étale neighbourhoods of `X`, and the extension by zero is pointwise a left Kan extension. -/
private theorem etaleExtensionStalkUniv_hom_ext {T : AddCommGrpCat.{max (u + 1) v}}
    {a b : etaleStalk B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F) ⟶ T}
    (h : ∀ (W : SmallEtale B U.obj.left.1 U.obj.left.property)
      (q : (geometricPointFiber B X hX s).obj ((smallEtalePostcompose B X hX U).obj W)),
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) ≫
          colimit.ι (etaleStalkDiagram B X hX s
            ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))
            (op ((geometricPointFiber B X hX s).elementsMk _ q)) ≫ a =
        ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) ≫
          colimit.ι (etaleStalkDiagram B X hX s
            ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))
            (op ((geometricPointFiber B X hX s).elementsMk _ q)) ≫ b) :
    a = b := by
  have hlke : ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F).IsLeftKanExtension
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj) := by
    change ((smallEtalePostcompose B X hX U).op.lan.obj F.obj).IsLeftKanExtension
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj)
    infer_instance
  apply colimit.hom_ext
  intro N
  apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F)
    ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj) (op N.unop.1)).hom_ext'
  intro W f
  have hw := colimit.w (etaleStalkDiagram B X hX s
    ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F))
      (Quiver.Hom.op (⟨f.unop, rfl⟩ : N.unop ⟶ (geometricPointFiber B X hX s).elementsMk
        ((smallEtalePostcompose B X hX U).obj W.unop)
        ((geometricPointFiber B X hX s).map f.unop N.unop.2)))
  change ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F).map f ≫
    colimit.ι (etaleStalkDiagram B X hX s
      ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F)) N =
      colimit.ι (etaleStalkDiagram B X hX s
        ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F))
        (op ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W.unop)
          ((geometricPointFiber B X hX s).map f.unop N.unop.2))) at hw
  change ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app W ≫
      (((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F).map f ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F)) N) ≫ a =
    ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app W ≫
      (((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F).map f ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZeroUniv.{u, v} B X hX U).obj F)) N) ≫ b
  rw [hw]
  exact h W.unop ((geometricPointFiber B X hX s).map f.unop N.unop.2)

/-- The map induced on the stalk at a geometric point of `X` by the canonical comparison. -/
public def comparisonStalkMapUniv :
    etaleStalk B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F) ⟶
      etaleStalk B X hX s ((etaleFiniteSupportPresheafUniv B X hX U).obj F) :=
  (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map
    ((etaleExtensionToFiniteSupportUniv B X hX U).app F)

/-- The stalk map of the comparison sends the germ of a section to the germ of its image. -/
private theorem comparisonStalkMapUniv_etaleGerm (V : SmallEtale B X hX)
    (q : (geometricPointFiber B X hX s).obj V)
    (t : ((abelianPresheafExtensionByZeroUniv B X hX U).obj F).obj (op V)) :
    comparisonStalkMapUniv B X hX U s F
        (etaleGerm B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F) V q t) =
      etaleGerm B X hX s ((etaleFiniteSupportPresheafUniv B X hX U).obj F) V q
        (((etaleExtensionToFiniteSupportUniv B X hX U).app F).app (op V) t) :=
  (ConcreteCategory.comp_apply _ _ t).symm.trans
    ((ConcreteCategory.congr_hom
      (colimit.ι_map (Functor.whiskerLeft (Functor.Elements.π
        (geometricPointFiber B X hX s)).op
        ((etaleExtensionToFiniteSupportUniv B X hX U).app F))
        (op ((geometricPointFiber B X hX s).elementsMk V q))) t).trans
      (ConcreteCategory.comp_apply _ _ t))

/-- The germ map out of the stalk of `F` at a point of the geometric fibre sends the germ of a
section over an étale neighbourhood of that point to the germ of the corresponding generator of
the left Kan extension. -/
public theorem liftedStalkToExtensionUniv_etaleGerm (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W) (t : F.obj.obj (op W)) :
    liftedStalkToExtensionUniv B X hX U s F x
        (etaleGerm B U.obj.left.1 U.obj.left.property
          (x.toGeometricPoint B U.obj.hom s) F.obj W q t) =
      etaleGerm B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W q)
        (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) t) := by
  have hm : colimit.ι (etaleStalkDiagram B U.obj.left.1 U.obj.left.property
        (x.toGeometricPoint B U.obj.hom s) F.obj) (op (Functor.elementsMk _ W q)) ≫
      liftedStalkToExtensionUniv B X hX U s F x =
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))
          (op (liftedElement B X hX U s x W q)) := by
    simp only [liftedStalkToExtensionUniv, colimit.ι_desc]
    rfl
  exact (ConcreteCategory.comp_apply _ _ t).symm.trans
    ((ConcreteCategory.congr_hom hm t).trans (ConcreteCategory.comp_apply _ _ t))

open scoped Classical in
/-- The germ maps out of the stalks of `F` over the geometric fibre split the composite of the
stalk map of the comparison with the germ decomposition of Stacks 0F6P: on the summand at `x̄`
the composite is the inclusion of that summand. -/
public theorem liftedStalkToExtensionUniv_comp (x : GeometricFiberPoint B U.obj.hom s)
    (g : ↑(etaleStalk B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s) F.obj)) :
    (comparisonStalkMapUniv B X hX U s F ≫ etaleFiniteSupportStalkMapUniv B X hX U s F)
        (liftedStalkToExtensionUniv B X hX U s F x g) =
      DirectSum.of (fun y : GeometricFiberPoint B U.obj.hom s =>
        ↑(etaleStalk B U.obj.left.1 U.obj.left.property
          (y.toGeometricPoint B U.obj.hom s) F.obj)) x g := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B U.obj.left.1 U.obj.left.property
    (x.toGeometricPoint B U.obj.hom s) F.obj g
  rw [liftedStalkToExtensionUniv_etaleGerm B X hX U s F x W q a,
    ConcreteCategory.comp_apply, comparisonStalkMapUniv_etaleGerm,
    etaleExtensionToFiniteSupportUniv_on_graph]
  refine DFinsupp.ext fun y => ?_
  by_cases hy : y = x
  · subst hy
    refine (etaleFiniteSupportStalkMapUniv_graph B X hX U s F y W q a).trans ?_
    exact (DirectSum.of_eq_same (β := fun z : GeometricFiberPoint B U.obj.hom s =>
      ↑(etaleStalk B U.obj.left.1 U.obj.left.property
        (z.toGeometricPoint B U.obj.hom s) F.obj)) y _).symm
  · refine (etaleFiniteSupportStalkMapUniv_graph_ne B X hX U s F x W q a y hy).trans ?_
    exact (DirectSum.of_eq_of_ne (β := fun z : GeometricFiberPoint B U.obj.hom s =>
      ↑(etaleStalk B U.obj.left.1 U.obj.left.property
        (z.toGeometricPoint B U.obj.hom s) F.obj)) x y _ hy).symm

/-- The map out of the direct sum assembled from the germ maps restricts to the germ map on each
summand. -/
private theorem toAddMonoid_liftedStalkToExtension_ofUniv
    [DecidableEq (GeometricFiberPoint B U.obj.hom s)] (x : GeometricFiberPoint B U.obj.hom s)
    (g : ↑(etaleStalk B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s) F.obj)) :
    DirectSum.toAddMonoid (fun y => (liftedStalkToExtensionUniv B X hX U s F y).hom)
        (DirectSum.of (fun y : GeometricFiberPoint B U.obj.hom s =>
          ↑(etaleStalk B U.obj.left.1 U.obj.left.property
            (y.toGeometricPoint B U.obj.hom s) F.obj)) x g) =
      liftedStalkToExtensionUniv B X hX U s F x g :=
  DirectSum.toAddMonoid_of (φ := fun y => (liftedStalkToExtensionUniv B X hX U s F y).hom) x g

open scoped Classical in
/-- The composite of the stalk map of the comparison with the germ decomposition of Stacks
0F6P is an isomorphism: it is inverted by the map assembled from the germ maps out of the
stalks of `F` over the geometric fibre. -/
private theorem isIso_stalk_comp_fiberStalksUniv :
    IsIso (comparisonStalkMapUniv B X hX U s F ≫ etaleFiniteSupportStalkMapUniv B X hX U s F) := by
  let r : AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B U.obj.hom s F) ⟶
      etaleStalk B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F) :=
    AddCommGrpCat.ofHom (DirectSum.toAddMonoid
      (fun x => (liftedStalkToExtensionUniv B X hX U s F x).hom))
  have hri : r ≫ (comparisonStalkMapUniv B X hX U s F ≫
      etaleFiniteSupportStalkMapUniv B X hX U s F) = 𝟙 _ := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    change (comparisonStalkMapUniv B X hX U s F ≫ etaleFiniteSupportStalkMapUniv B X hX U s F)
      (DirectSum.toAddMonoid
        (fun x => (liftedStalkToExtensionUniv B X hX U s F x).hom) z) = z
    refine DirectSum.induction_on z ?_ (fun x a => ?_) (fun z₁ z₂ h₁ h₂ => ?_)
    · simp
    · rw [toAddMonoid_liftedStalkToExtension_ofUniv]
      exact liftedStalkToExtensionUniv_comp B X hX U s F x a
    · rw [map_add, map_add, h₁, h₂]
  have hir : (comparisonStalkMapUniv B X hX U s F ≫
      etaleFiniteSupportStalkMapUniv B X hX U s F) ≫ r = 𝟙 _ := by
    refine etaleExtensionStalkUniv_hom_ext B X hX U s F fun W q => ?_
    refine ConcreteCategory.hom_ext _ _ fun t => ?_
    let x : GeometricFiberPoint B U.obj.hom s :=
      ⟨q.1 ≫ B.inclusion.map W.obj.hom,
        (congrArg (fun z => q.1 ≫ z)
          (B.inclusion.map_comp W.obj.hom U.obj.hom).symm).trans q.2⟩
    have hlift := liftedStalkToExtensionUniv_etaleGerm B X hX U s F x W ⟨q.1, rfl⟩ t
    change r ((comparisonStalkMapUniv B X hX U s F ≫ etaleFiniteSupportStalkMapUniv B X hX U s F)
        (etaleGerm B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F)
          ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W ⟨q.1, rfl⟩)
          (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) t))) =
      etaleGerm B X hX s ((abelianPresheafExtensionByZeroUniv B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W ⟨q.1, rfl⟩)
        (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) t)
    rw [← hlift, liftedStalkToExtensionUniv_comp]
    exact toAddMonoid_liftedStalkToExtension_ofUniv B X hX U s F x _
  exact ⟨r, hir, hri⟩

/-- The canonical map induces an isomorphism on the stalk at every
geometric point of `X`: by Stacks 0F6P the germ decomposition is an isomorphism, so both sides
become the direct sum of the stalks of `F` over the geometric fibre. -/
public theorem etaleExtensionToFiniteSupportUniv_stalk_isIso :
    IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map
      ((etaleExtensionToFiniteSupportUniv B X hX U).app F)) := by
  have := isIso_stalk_comp_fiberStalksUniv B X hX U s F
  exact (IsIso.of_isIso_comp_right _ (etaleFiniteSupportStalkMapUniv B X hX U s F) :
    IsIso (comparisonStalkMapUniv B X hX U s F))

end Stalk

/-! ### Stacks 0F6Q: the sheafified comparison is an isomorphism -/

/-- The canonical map `j_{p!}F ⟶ f_{p!}F` becomes an isomorphism after
sheafification: it is an isomorphism on every geometric stalk, both sides becoming the direct
sum of the stalks of `F` over the geometric fibre, and a map of abelian étale sheaves which is
an isomorphism on every geometric stalk is an isomorphism. So the sheaf `j_!F = (j_{p!}F)^#` of
Stacks 03S3 is identified with `(f_{p!}F)^#`. -/
public theorem etaleExtensionToFiniteSupportUniv_sheafify_isIso
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{max (u + 1) v}).map
      ((etaleExtensionToFiniteSupportUniv B X hX U).app F)) := by
  refine isIso_of_isIso_etaleStalkMap.{u, max (u + 1) v} B X hX _ fun s => ?_
  have hnat := toSheafify_naturality (D := AddCommGrpCat.{max (u + 1) v})
    (SmallEtale.topology B X hX)
    ((etaleExtensionToFiniteSupportUniv B X hX U).app F)
  have hsq := congrArg (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map hnat
  rw [Functor.map_comp, Functor.map_comp] at hsq
  have hP : IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map
      (toSheafify (D := AddCommGrpCat.{max (u + 1) v}) (SmallEtale.topology B X hX)
        ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))) :=
    isIso_etaleStalk_map_toSheafify B X hX s _
  have hQ : IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map
      (toSheafify (D := AddCommGrpCat.{max (u + 1) v}) (SmallEtale.topology B X hX)
        ((etaleFiniteSupportPresheafUniv B X hX U).obj F))) :=
    isIso_etaleStalk_map_toSheafify B X hX s _
  have := etaleExtensionToFiniteSupportUniv_stalk_isIso B X hX U s F
  have h1 : IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map
        (toSheafify (D := AddCommGrpCat.{max (u + 1) v}) (SmallEtale.topology B X hX)
          ((abelianPresheafExtensionByZeroUniv B X hX U).obj F)) ≫
      (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{max (u + 1) v}).map
        (sheafifyMap (D := AddCommGrpCat.{max (u + 1) v}) (SmallEtale.topology B X hX)
          ((etaleExtensionToFiniteSupportUniv B X hX U).app F))) := hsq ▸ inferInstance
  exact IsIso.of_isIso_comp_left ((etaleStalkPresheafFunctor B X hX s
    AddCommGrpCat.{max (u + 1) v}).map
      (toSheafify (D := AddCommGrpCat.{max (u + 1) v}) (SmallEtale.topology B X hX)
        ((abelianPresheafExtensionByZeroUniv B X hX U).obj F))) _

/-! ### Extension by zero is the direct image with compact support -/

/-- Extension by zero along an étale morphism `j : U ⟶ X` is the direct image with compact
support of `j`, with coefficients in `AddCommGrpCat.{max (u + 1) v}`: the canonical map
`j_{p!} ⟶ f_{p!}` is an isomorphism after sheafification. -/
public def abelianExtensionByZeroIsoFShriekUniv :
    abelianExtensionByZeroUniv.{u, v} B X hX U ≅ fShriekFunctor.{u, v} B U.obj.hom :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ _ (etaleExtensionToFiniteSupportUniv_sheafify_isIso B X hX U F))
    (fun φ => (Functor.whiskerRight (etaleExtensionToFiniteSupportUniv B X hX U)
      (presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{max (u + 1) v})).naturality φ)

end AlgebraicGeometry.SmallEtale

end
