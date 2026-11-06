module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero.Comparison

/-!
# Extension by zero is the finite-support direct image of an étale morphism

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, and
let `F` be an abelian sheaf on the small étale site of `U`. This file shows that the canonical
map `j_{p!}F ⟶ f_{p!}F` of Stacks 0F6Q, from the presheaf extension by zero to the
finite-support direct image presheaf of Stacks 0F6M, becomes an isomorphism after
sheafification, so that `j_!F = (j_{p!}F)^#` is also `(f_{p!}F)^#`.

That the map is an isomorphism after sheafification is checked on stalks at geometric points.
The stalk of `j_{p!}F` at a geometric point `ȳ` of `X` receives, for every point `x̄` of the
geometric fibre of `j` over `ȳ`, the stalk `F_x̄`, by taking an étale neighbourhood of `x̄` in
`U` and viewing it as an étale neighbourhood of `ȳ` in `X`; those maps assemble into a
two-sided inverse of the composite of the stalk map with the germ decomposition
`(f_{p!}F)_ȳ ⟶ ⨁_{j(x̄) = ȳ} F_x̄` of Stacks 0F6P. Both sides are therefore `⨁_{j(x̄) = ȳ} F_x̄`,
and a map of abelian étale presheaves which is an isomorphism on every geometric stalk becomes
an isomorphism after sheafification.

## Main definitions

* `AlgebraicGeometry.SmallEtale.liftedStalkToExtension` — the map from the stalk of `F` at a
  point of the geometric fibre of `U ⟶ X` to the stalk of the presheaf extension by zero.
* `AlgebraicGeometry.SmallEtale.comparisonStalkMap` — the map induced on the stalk at a
  geometric point of `X` by the canonical comparison.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleExtensionToFiniteSupport_stalk_isIso` — the canonical map
  is an isomorphism on the stalk at every geometric point of `X`.
* `AlgebraicGeometry.SmallEtale.etaleExtensionToFiniteSupport_sheafify_isIso` — the canonical
  map becomes an isomorphism after sheafification, identifying `j_!F` with `(f_{p!}F)^#`.

## Implementation notes

The stalk at a geometric point and the colimit over étale neighbourhoods are two spellings of
one group, interchangeable only at default transparency; a rewrite inside a goal mixing them
fails, so `AlgebraicGeometry.SmallEtale.comparisonStalkMap` fixes the stalk map once and
everything else is written in that spelling.

## References

* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-! ### The stalks at a geometric point -/

section Stalk

variable (s : GeometricPoint X)
  (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})

/-- A lift of a geometric point of `X` to an étale object over `U`, together with the point of
the geometric fibre it determines, read as a lift to that object viewed as étale over `X`. -/
public def liftedPoint (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W) :
    (geometricPointFiber B X hX s).obj ((smallEtalePostcompose B X hX U).obj W) :=
  ⟨q.1, by
    change q.1 ≫ B.inclusion.map (W.obj.hom ≫ U.obj.hom) = s.hom
    rw [Functor.map_comp, ← Category.assoc, q.2]
    exact x.2⟩

/-- An étale neighbourhood of a point of the geometric fibre of `U ⟶ X`, viewed as an étale
neighbourhood of the geometric point of `X` below it. -/
public def liftedElement (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W) :
    (geometricPointFiber B X hX s).Elements :=
  ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W)
      (liftedPoint B X hX U s x W q))

/-- A morphism of étale neighbourhoods of a point of the geometric fibre, viewed as a morphism
of étale neighbourhoods of the geometric point of `X` below it. -/
public def liftedNeighborhoodMap (x : GeometricFiberPoint B U.obj.hom s)
    {N M : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).Elements} (k : N ⟶ M) :
    liftedElement B X hX U s x N.1 N.2 ⟶ liftedElement B X hX U s x M.1 M.2 :=
  ⟨(smallEtalePostcompose B X hX U).map k.1, by
    apply Subtype.ext
    have h := congrArg Subtype.val k.2
    exact h⟩

/-- The map from the stalk of `F` at a point of the geometric fibre to the stalk of the
presheaf extension by zero at the geometric point of `X` below it: the germ at an étale
neighbourhood of the fibre point is sent to the germ of the corresponding generator of the
left Kan extension over the same neighbourhood, viewed as an étale neighbourhood of `X`. -/
public def liftedStalkToExtension (x : GeometricFiberPoint B U.obj.hom s) :
    etaleStalk B U.obj.left.1 U.obj.left.property (x.toGeometricPoint B U.obj.hom s) F.obj ⟶
      etaleStalk B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F) := by
  refine colimit.desc _ {
    pt := etaleStalk B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F)
    ι := {
      app := fun N => ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app
          (op N.unop.1) ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj F))
          (op (liftedElement B X hX U s x N.unop.1 N.unop.2))
      naturality := ?_ } }
  intro N M k
  have hunit := ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).naturality k.unop.1.op
  have hw := colimit.w (etaleStalkDiagram B X hX s
    ((abelianPresheafExtensionByZero B X hX U).obj F))
      (Quiver.Hom.op (liftedNeighborhoodMap B X hX U s x k.unop))
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ colimit.ι (etaleStalkDiagram B X hX s
    ((abelianPresheafExtensionByZero B X hX U).obj F))
      (op (liftedElement B X hX U s x M.unop.1 M.unop.2))) hunit) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun z => ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app
    (op N.unop.1) ≫ z) hw

/-- The germ decomposition `(f_{p!}F)_ȳ ⟶ ⊕_{j(x̄) = ȳ} F_x̄` of Stacks 0F6P for the étale
morphism `U ⟶ X`. -/
public abbrev etaleFiniteSupportStalkMap :
    etaleStalk B X hX s ((etaleFiniteSupportPresheaf B X hX U).obj F) ⟶
      AddCommGrpCat.of (fiberStalks.{u, u + 1} B U.obj.hom s F) :=
  finiteSupportStalkToFiberStalks.{u, u + 1} B U.obj.hom s F
    (small_finiteSupport_smallEtale B X hX U)

/-- Two sections over a subsingleton scheme of the base change `U ×_X W` which land on the
graph of `W → U` agree after both projections are composed with the structure morphism
`W ⟶ U`: on the graph the second projection is the first followed by `W ⟶ U`. -/
private theorem etaleGraph_fiber_eq_of_mem
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (T : Scheme.{u}) [Subsingleton T]
    (r : T ⟶ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)))
    (z : T) (hz : r.base z ∈ (etaleGraphFiniteSupport B X hX U W).1) :
    r ≫ B.inclusion.map
        (pullback.snd ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
      r ≫ B.inclusion.map
        (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) ≫
          B.inclusion.map W.obj.hom := by
  have hrange : Set.range r.base ⊆
      Set.range (B.inclusion.map (etaleGraphMap B X hX U W)).base := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y z]
    exact hz
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ B.inclusion.map (etaleGraphMap B X hX U W) = r :=
    ⟨IsOpenImmersion.lift (B.inclusion.map (etaleGraphMap B X hX U W)) r hrange,
      IsOpenImmersion.lift_fac _ r hrange⟩
  rw [Category.assoc, Category.assoc, etaleGraphMap_comp_snd, ← Category.assoc
    (B.inclusion.map (etaleGraphMap B X hX U W)), etaleGraphMap_comp_fst]
  exact congrArg (fun z => l ≫ z) (Category.id_comp (B.inclusion.map W.obj.hom)).symm

/-- On the summand at a point `x̄` of the geometric fibre, the germ decomposition sends the
germ of a graph generator over an étale neighbourhood of `x̄` to the germ of the section it
came from. -/
private theorem etaleFiniteSupportStalkMap_graph
    (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W)
    (a : F.obj.obj (op W)) :
    (etaleFiniteSupportStalkMap B X hX U s F
      (etaleGerm B X hX s ((etaleFiniteSupportPresheaf B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W q)
        (graphSectionToFiniteSupport B X hX U F W a))) x =
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
  have h := finiteSupportStalkToFiberStalks_germ.{u, u + 1} B U.obj.hom s F
    (small_finiteSupport_smallEtale B X hX U) x
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
private theorem etaleFiniteSupportStalkMap_graph_ne
    (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W)
    (a : F.obj.obj (op W))
    (y : GeometricFiberPoint B U.obj.hom s) (hxy : y ≠ x) :
    (etaleFiniteSupportStalkMap B X hX U s F
      (etaleGerm B X hX s ((etaleFiniteSupportPresheaf B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W q)
        (graphSectionToFiniteSupport B X hX U F W a))) y = 0 := by
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
    have hg := finiteSupportStalkToFiberStalks_germ.{u, u + 1} B U.obj.hom s F
      (small_finiteSupport_smallEtale B X hX U) y
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
  · exact finiteSupportStalkToFiberStalks_zero_of_no_open_lift.{u, u + 1} B U.obj.hom s F
      (small_finiteSupport_smallEtale B X hX U) y
      ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W)
      (liftedPoint B X hX U s x W q))
      (etaleGraphFiniteSupport B X hX U W) h (etaleGraphSection B X hX U F W a)

/-- Two maps out of the stalk of the presheaf extension by zero agree as soon as they agree on
the germs of the generators coming from étale objects over `U`: the stalk is a colimit over
étale neighbourhoods of `X`, and the extension by zero is pointwise a left Kan extension. -/
private theorem etaleExtensionStalk_hom_ext {T : AddCommGrpCat.{u + 1}}
    {a b : etaleStalk B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F) ⟶ T}
    (h : ∀ (W : SmallEtale B U.obj.left.1 U.obj.left.property)
      (q : (geometricPointFiber B X hX s).obj ((smallEtalePostcompose B X hX U).obj W)),
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) ≫
          colimit.ι (etaleStalkDiagram B X hX s
            ((abelianPresheafExtensionByZero B X hX U).obj F))
            (op ((geometricPointFiber B X hX s).elementsMk _ q)) ≫ a =
        ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) ≫
          colimit.ι (etaleStalkDiagram B X hX s
            ((abelianPresheafExtensionByZero B X hX U).obj F))
            (op ((geometricPointFiber B X hX s).elementsMk _ q)) ≫ b) :
    a = b := by
  have hlke : ((abelianPresheafExtensionByZero B X hX U).obj F).IsLeftKanExtension
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj) := by
    show ((smallEtalePostcompose B X hX U).op.lan.obj F.obj).IsLeftKanExtension
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj)
    infer_instance
  apply colimit.hom_ext
  intro N
  apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    ((abelianPresheafExtensionByZero B X hX U).obj F)
    ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj) (op N.unop.1)).hom_ext'
  intro W f
  have hw := colimit.w (etaleStalkDiagram B X hX s
    ((abelianPresheafExtensionByZero B X hX U).obj F))
      (Quiver.Hom.op (⟨f.unop, rfl⟩ : N.unop ⟶ (geometricPointFiber B X hX s).elementsMk
        ((smallEtalePostcompose B X hX U).obj W.unop)
        ((geometricPointFiber B X hX s).map f.unop N.unop.2)))
  change ((abelianPresheafExtensionByZero B X hX U).obj F).map f ≫
    colimit.ι (etaleStalkDiagram B X hX s
      ((abelianPresheafExtensionByZero B X hX U).obj F)) N =
      colimit.ι (etaleStalkDiagram B X hX s
        ((abelianPresheafExtensionByZero B X hX U).obj F))
        (op ((geometricPointFiber B X hX s).elementsMk ((smallEtalePostcompose B X hX U).obj W.unop)
          ((geometricPointFiber B X hX s).map f.unop N.unop.2))) at hw
  show ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app W ≫
      (((abelianPresheafExtensionByZero B X hX U).obj F).map f ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj F)) N) ≫ a =
    ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app W ≫
      (((abelianPresheafExtensionByZero B X hX U).obj F).map f ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj F)) N) ≫ b
  rw [hw]
  exact h W.unop ((geometricPointFiber B X hX s).map f.unop N.unop.2)

/-- The map induced on the stalk at a geometric point of `X` by the canonical comparison. -/
public def comparisonStalkMap :
    etaleStalk B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F) ⟶
      etaleStalk B X hX s ((etaleFiniteSupportPresheaf B X hX U).obj F) :=
  (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
    ((etaleExtensionToFiniteSupport B X hX U).app F)

/-- The stalk map of the comparison sends the germ of a section to the germ of its image. -/
private theorem comparisonStalkMap_etaleGerm (V : SmallEtale B X hX)
    (q : (geometricPointFiber B X hX s).obj V)
    (t : ((abelianPresheafExtensionByZero B X hX U).obj F).obj (op V)) :
    comparisonStalkMap B X hX U s F
        (etaleGerm B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F) V q t) =
      etaleGerm B X hX s ((etaleFiniteSupportPresheaf B X hX U).obj F) V q
        (((etaleExtensionToFiniteSupport B X hX U).app F).app (op V) t) :=
  (ConcreteCategory.comp_apply _ _ t).symm.trans
    ((ConcreteCategory.congr_hom
      (colimit.ι_map (Functor.whiskerLeft (Functor.Elements.π
        (geometricPointFiber B X hX s)).op
        ((etaleExtensionToFiniteSupport B X hX U).app F))
        (op ((geometricPointFiber B X hX s).elementsMk V q))) t).trans
      (ConcreteCategory.comp_apply _ _ t))

/-- The germ map out of the stalk of `F` at a point of the geometric fibre sends the germ of a
section over an étale neighbourhood of that point to the germ of the corresponding generator of
the left Kan extension. -/
public theorem liftedStalkToExtension_etaleGerm (x : GeometricFiberPoint B U.obj.hom s)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (q : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W) (t : F.obj.obj (op W)) :
    liftedStalkToExtension B X hX U s F x
        (etaleGerm B U.obj.left.1 U.obj.left.property
          (x.toGeometricPoint B U.obj.hom s) F.obj W q t) =
      etaleGerm B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W q)
        (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) t) := by
  have hm : colimit.ι (etaleStalkDiagram B U.obj.left.1 U.obj.left.property
        (x.toGeometricPoint B U.obj.hom s) F.obj) (op (Functor.elementsMk _ W q)) ≫
      liftedStalkToExtension B X hX U s F x =
      ((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) ≫
        colimit.ι (etaleStalkDiagram B X hX s
          ((abelianPresheafExtensionByZero B X hX U).obj F))
          (op (liftedElement B X hX U s x W q)) := by
    simp only [liftedStalkToExtension, colimit.ι_desc]
    rfl
  exact (ConcreteCategory.comp_apply _ _ t).symm.trans
    ((ConcreteCategory.congr_hom hm t).trans (ConcreteCategory.comp_apply _ _ t))

open scoped Classical in
/-- The germ maps out of the stalks of `F` over the geometric fibre split the composite of the
stalk map of the comparison with the germ decomposition of Stacks 0F6P: on the summand at `x̄`
the composite is the inclusion of that summand. -/
public theorem liftedStalkToExtension_comp (x : GeometricFiberPoint B U.obj.hom s)
    (g : ↑(etaleStalk B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s) F.obj)) :
    (comparisonStalkMap B X hX U s F ≫ etaleFiniteSupportStalkMap B X hX U s F)
        (liftedStalkToExtension B X hX U s F x g) =
      DirectSum.of (fun y : GeometricFiberPoint B U.obj.hom s =>
        ↑(etaleStalk B U.obj.left.1 U.obj.left.property
          (y.toGeometricPoint B U.obj.hom s) F.obj)) x g := by
  obtain ⟨W, q, a, rfl⟩ := exists_etaleGerm_eq B U.obj.left.1 U.obj.left.property
    (x.toGeometricPoint B U.obj.hom s) F.obj g
  rw [liftedStalkToExtension_etaleGerm B X hX U s F x W q a,
    ConcreteCategory.comp_apply, comparisonStalkMap_etaleGerm,
    etaleExtensionToFiniteSupport_on_graph]
  refine DFinsupp.ext fun y => ?_
  by_cases hy : y = x
  · subst hy
    refine (etaleFiniteSupportStalkMap_graph B X hX U s F y W q a).trans ?_
    exact (DirectSum.of_eq_same (β := fun z : GeometricFiberPoint B U.obj.hom s =>
      ↑(etaleStalk B U.obj.left.1 U.obj.left.property
        (z.toGeometricPoint B U.obj.hom s) F.obj)) y _).symm
  · refine (etaleFiniteSupportStalkMap_graph_ne B X hX U s F x W q a y hy).trans ?_
    exact (DirectSum.of_eq_of_ne (β := fun z : GeometricFiberPoint B U.obj.hom s =>
      ↑(etaleStalk B U.obj.left.1 U.obj.left.property
        (z.toGeometricPoint B U.obj.hom s) F.obj)) x y _ hy).symm

/-- The map out of the direct sum assembled from the germ maps restricts to the germ map on each
summand. -/
private theorem toAddMonoid_liftedStalkToExtension_of
    [DecidableEq (GeometricFiberPoint B U.obj.hom s)] (x : GeometricFiberPoint B U.obj.hom s)
    (g : ↑(etaleStalk B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s) F.obj)) :
    DirectSum.toAddMonoid (fun y => (liftedStalkToExtension B X hX U s F y).hom)
        (DirectSum.of (fun y : GeometricFiberPoint B U.obj.hom s =>
          ↑(etaleStalk B U.obj.left.1 U.obj.left.property
            (y.toGeometricPoint B U.obj.hom s) F.obj)) x g) =
      liftedStalkToExtension B X hX U s F x g :=
  DirectSum.toAddMonoid_of (φ := fun y => (liftedStalkToExtension B X hX U s F y).hom) x g

open scoped Classical in
/-- The composite of the stalk map of the comparison with the germ decomposition of Stacks
0F6P is an isomorphism: it is inverted by the map assembled from the germ maps out of the
stalks of `F` over the geometric fibre. -/
private theorem isIso_stalk_comp_fiberStalks :
    IsIso (comparisonStalkMap B X hX U s F ≫ etaleFiniteSupportStalkMap B X hX U s F) := by
  let r : AddCommGrpCat.of (fiberStalks.{u, u + 1} B U.obj.hom s F) ⟶
      etaleStalk B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F) :=
    AddCommGrpCat.ofHom (DirectSum.toAddMonoid
      (fun x => (liftedStalkToExtension B X hX U s F x).hom))
  have hri : r ≫ (comparisonStalkMap B X hX U s F ≫
      etaleFiniteSupportStalkMap B X hX U s F) = 𝟙 _ := by
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    show (comparisonStalkMap B X hX U s F ≫ etaleFiniteSupportStalkMap B X hX U s F)
      (DirectSum.toAddMonoid
        (fun x => (liftedStalkToExtension B X hX U s F x).hom) z) = z
    refine DirectSum.induction_on z ?_ (fun x a => ?_) (fun z₁ z₂ h₁ h₂ => ?_)
    · simp
    · rw [toAddMonoid_liftedStalkToExtension_of]
      exact liftedStalkToExtension_comp B X hX U s F x a
    · rw [map_add, map_add, h₁, h₂]
  have hir : (comparisonStalkMap B X hX U s F ≫
      etaleFiniteSupportStalkMap B X hX U s F) ≫ r = 𝟙 _ := by
    refine etaleExtensionStalk_hom_ext B X hX U s F fun W q => ?_
    refine ConcreteCategory.hom_ext _ _ fun t => ?_
    let x : GeometricFiberPoint B U.obj.hom s :=
      ⟨q.1 ≫ B.inclusion.map W.obj.hom,
        (congrArg (fun z => q.1 ≫ z)
          (B.inclusion.map_comp W.obj.hom U.obj.hom).symm).trans q.2⟩
    have hlift := liftedStalkToExtension_etaleGerm B X hX U s F x W ⟨q.1, rfl⟩ t
    show r ((comparisonStalkMap B X hX U s F ≫ etaleFiniteSupportStalkMap B X hX U s F)
        (etaleGerm B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F)
          ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W ⟨q.1, rfl⟩)
          (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) t))) =
      etaleGerm B X hX s ((abelianPresheafExtensionByZero B X hX U).obj F)
        ((smallEtalePostcompose B X hX U).obj W) (liftedPoint B X hX U s x W ⟨q.1, rfl⟩)
        (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) t)
    rw [← hlift, liftedStalkToExtension_comp]
    exact toAddMonoid_liftedStalkToExtension_of B X hX U s F x _
  exact ⟨r, hir, hri⟩

/-- **Stacks 0F6Q on stalks.** The canonical map induces an isomorphism on the stalk at every
geometric point of `X`: by Stacks 0F6P the germ decomposition is an isomorphism, so both sides
become the direct sum of the stalks of `F` over the geometric fibre. -/
public theorem etaleExtensionToFiniteSupport_stalk_isIso :
    IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
      ((etaleExtensionToFiniteSupport B X hX U).app F)) := by
  have := isIso_stalk_comp_fiberStalks B X hX U s F
  exact (IsIso.of_isIso_comp_right _ (etaleFiniteSupportStalkMap B X hX U s F) :
    IsIso (comparisonStalkMap B X hX U s F))

end Stalk

/-! ### Stacks 0F6Q: the sheafified comparison is an isomorphism -/

/-- **Stacks 0F6Q.** The canonical map `j_{p!}F ⟶ f_{p!}F` becomes an isomorphism after
sheafification: it is an isomorphism on every geometric stalk, both sides becoming the direct
sum of the stalks of `F` over the geometric fibre, and a map of abelian étale sheaves which is
an isomorphism on every geometric stalk is an isomorphism. So the sheaf `j_!F = (j_{p!}F)^#` of
Stacks 03S3 is identified with `(f_{p!}F)^#`. -/
@[stacks 0F6Q "isomorphism after sheafification"]
public theorem etaleExtensionToFiniteSupport_sheafify_isIso
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) :
    IsIso ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).map
      ((etaleExtensionToFiniteSupport B X hX U).app F)) := by
  refine isIso_of_isIso_etaleStalkMap.{u, u + 1} B X hX _ fun s => ?_
  have hnat := toSheafify_naturality (SmallEtale.topology B X hX)
    ((etaleExtensionToFiniteSupport B X hX U).app F)
  have hsq := congrArg (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map hnat
  rw [Functor.map_comp, Functor.map_comp] at hsq
  have hP : IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
      (toSheafify (SmallEtale.topology B X hX)
        ((abelianPresheafExtensionByZero B X hX U).obj F))) :=
    isIso_etaleStalk_map_toSheafify B X hX s _
  have hQ : IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
      (toSheafify (SmallEtale.topology B X hX)
        ((etaleFiniteSupportPresheaf B X hX U).obj F))) :=
    isIso_etaleStalk_map_toSheafify B X hX s _
  have := etaleExtensionToFiniteSupport_stalk_isIso B X hX U s F
  have h1 : IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
        (toSheafify (SmallEtale.topology B X hX)
          ((abelianPresheafExtensionByZero B X hX U).obj F)) ≫
      (etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{u + 1}).map
        (sheafifyMap (SmallEtale.topology B X hX)
          ((etaleExtensionToFiniteSupport B X hX U).app F))) := hsq ▸ inferInstance
  exact IsIso.of_isIso_comp_left ((etaleStalkPresheafFunctor B X hX s
    AddCommGrpCat.{u + 1}).map (toSheafify (SmallEtale.topology B X hX)
      ((abelianPresheafExtensionByZero B X hX U).obj F))) _

end AlgebraicGeometry.SmallEtale

end
