module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleTopology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ContinuousAugmentationSiteFunctors
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousFunctor

/-!
# The total site of the strict components of a simplicial algebraic space

Let `X` be a simplicial algebraic space. The total site of the simplicial site
`strictSimplicialSite X` of strict components (Stacks 09WC) has objects the pairs `(n, x)`
with `x` a strict object of degree `n`, and morphisms `(n, x) ⟶ (m, y)` the pairs of a simplex
map `φ : [m] ⟶ [n]` and a morphism `x ⟶ u_φ(y)`. Realizing the strict objects compares it with
the spaces-étale site `X_{spaces,étale}` of Stacks 0DE7: `(n, x)` goes to the realization of `x`
over `X_n`, and `(φ, g)` to `g` followed by the projection of `u_φ(y)` to `y`, a morphism over
`X(φ)`. This comparison is an equivalence of categories and a dense subsite, so the total site
of the strict components and `X_{spaces,étale}` have equivalent topoi.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTotalComparison`: the comparison
  functor from the total site of the strict components to `X_{spaces,étale}`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTotalComparison_isEquivalence`: it is
  an equivalence of categories.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTotalComparison_isDenseSubsite`: a
  sieve of the total site covers exactly when its image in `X_{spaces,étale}` covers.
* `CategoryTheory.SimplicialSite.mem_totalTopology_iff_simplicialSmallEtaleStrictTotal`: a sieve
  of the total site of a simplicial site covers exactly when its restriction to the component of
  its target covers.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.Pseudofunctor
  CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)}

/-! ### The projection of `u_φ(y)` to `y` -/

/-- The projection `V ×_{X_k} X_n ⟶ V ×_{X_k} X_m` from the realization of `u_φ(y)` to that of
`y`, a morphism over `X(φ)`. -/
abbrev StrictObj.transitionProj {m n : SimplexCategory} (φ : m ⟶ n) (y : StrictObj X m) :
    pullback y.obj.1.hom (X.map (y.simplex ≫ φ).op) ⟶
      pullback y.obj.1.hom (X.map y.simplex.op) :=
  StrictObj.transitionRealizeHom φ y ≫
    pullback.fst (pullback.snd y.obj.1.hom (X.map y.simplex.op)) (X.map φ.op)

/-- The projection of `u_φ(y)` to `y` commutes with the first projections to `V`. -/
theorem StrictObj.transitionProj_fst {m n : SimplexCategory} (φ : m ⟶ n) (y : StrictObj X m) :
    StrictObj.transitionProj φ y ≫ pullback.fst y.obj.1.hom (X.map y.simplex.op) =
      pullback.fst y.obj.1.hom (X.map (y.simplex ≫ φ).op) :=
  ((StrictObj.transitionRealizeHom_fst φ y) =≫ _).trans (pullback.lift_fst _ _ _)

/-- The projection of `u_φ(y)` to `y` lies over `X(φ) : X_n ⟶ X_m`. -/
theorem StrictObj.transitionProj_snd {m n : SimplexCategory} (φ : m ⟶ n) (y : StrictObj X m) :
    StrictObj.transitionProj φ y ≫ pullback.snd y.obj.1.hom (X.map y.simplex.op) =
      pullback.snd y.obj.1.hom (X.map (y.simplex ≫ φ).op) ≫ X.map φ.op :=
  ((StrictObj.transitionRealizeHom_fst φ y) =≫ _).trans (pullback.lift_snd _ _ _)

/-- The projection of `u_𝟙(y) = y` to `y` is the identity. -/
theorem StrictObj.transitionProj_id {n : SimplexCategory} (y : StrictObj X n) :
    StrictObj.transitionProj (𝟙 n) y = 𝟙 (pullback y.obj.1.hom (X.map y.simplex.op)) :=
  StrictObj.transitionRealizeHom_id_fst y

/-- The projections compose: `u_{φ ≫ φ'}(y) ⟶ u_φ(y) ⟶ y`. -/
theorem StrictObj.transitionProj_comp {l m n : SimplexCategory} (φ : l ⟶ m) (φ' : m ⟶ n)
    (y : StrictObj X l) :
    StrictObj.transitionProj (φ ≫ φ') y =
      StrictObj.transitionProj φ' (y.transition φ) ≫ StrictObj.transitionProj φ y :=
  (StrictObj.realizeCompHom_comp_fst y.obj y.simplex φ φ').trans (Category.assoc _ _ _).symm

/-- The projections are natural: `u_φ(g)` followed by the projection is the projection followed
by `g`. -/
theorem StrictObj.transitionProj_natural {m n : SimplexCategory} (φ : m ⟶ n)
    {y z : StrictComponent X m} (g : y ⟶ z) :
    ((strictTransition X φ).map g).hom.hom.left ≫ StrictObj.transitionProj φ z =
      StrictObj.transitionProj φ y ≫ g.hom.hom.left :=
  pullback.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (StrictObj.transitionProj_fst φ z)).trans
      ((strictTransition_map_hom_left_fst φ g).trans
        ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm))))
    (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (StrictObj.transitionProj_snd φ z)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ X.map φ.op) (StrictObj.hom_snd ((strictTransition X φ).map g)))))).trans
      ((Category.assoc _ _ _).trans ((congrArg (StrictObj.transitionProj φ y ≫ ·)
        (StrictObj.hom_snd g)).trans (StrictObj.transitionProj_snd φ y))).symm)

/-- An `eqToHom` of strict components realizes to an `eqToHom`. -/
theorem StrictObj.eqToHom_hom_left {n : SimplexCategory} {x x' : StrictComponent X n}
    (p : x = x') :
    (eqToHom p).hom.hom.left = eqToHom (congrArg (fun z : StrictObj X n ↦ z.realize.1.left) p) := by
  subst p
  rfl

/-! ### The comparison functor -/

attribute [local implicit_reducible] CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

attribute [local simp] PrelaxFunctor.map₂_eqToHom

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

namespace CategoryTheory.SimplicialSite

/-- The inverse compositor of the total pseudofunctor of a simplicial site is the transport
along the composition equality of the cosimplicial diagram. -/
theorem totalPseudofunctor_mapComp_inv_app_simplicialSmallEtaleStrictTotal (C : SimplicialSite.{u})
    {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (V : C.underlying.obj l) :
    (C.totalPseudofunctor.mapComp ψ.op.op.toLoc φ.op.op.toLoc).inv.toNatTrans.app V =
      eqToHom
        (Functor.congr_obj (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)) V).symm := by
  simp only [SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp, eqToIso.inv,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rfl

/-- A composite in the total site of a simplicial site: its fibre is the first fibre, followed
by the transition of the second, followed by the transport along the composition equality. -/
theorem totalPseudofunctor_comp_fiber_simplicialSmallEtaleStrictTotal (C : SimplicialSite.{u})
    {a b c : CoGrothendieck C.totalPseudofunctor} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).fiber = f.fiber ≫ (C.underlying.map f.base.unop).toFunctor.map g.fiber ≫
      eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor
        (C.underlying.map_comp g.base.unop f.base.unop)) c.fiber).symm :=
  congrArg (f.fiber ≫ (C.underlying.map f.base.unop).toFunctor.map g.fiber ≫ ·)
    (totalPseudofunctor_mapComp_inv_app_simplicialSmallEtaleStrictTotal C g.base.unop f.base.unop
      c.fiber)

/-- A sieve of the total site of a simplicial site covers exactly when its restriction to the
component of its target covers: the component inclusions are continuous and cocontinuous. -/
theorem mem_totalTopology_iff_simplicialSmallEtaleStrictTotal (C : SimplicialSite.{u})
    {U : CoGrothendieck C.totalPseudofunctor}
    (S : Sieve U) :
    S ∈ C.totalTopology U ↔ S.functorPullback (CoGrothendieck.ι C.totalPseudofunctor U.base) ∈
      (C.coverage U.base.unop).toGrothendieck U.fiber := by
  have : (CoGrothendieck.ι C.totalPseudofunctor U.base).IsCocontinuous
      (C.coverage U.base.unop).toGrothendieck C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous C.situation U.base.unop
  have : (CoGrothendieck.ι C.totalPseudofunctor U.base).IsContinuous
      (C.coverage U.base.unop).toGrothendieck C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous C.situation U.base.unop
  refine ⟨fun hS ↦ Functor.cover_lift (CoGrothendieck.ι C.totalPseudofunctor U.base)
    (C.coverage U.base.unop).toGrothendieck C.totalTopology hS, fun hS ↦ ?_⟩
  have h := (CoverPreserving.of_isContinuous
    (CoGrothendieck.ι C.totalPseudofunctor U.base)
    (C.coverage U.base.unop).toGrothendieck C.totalTopology).cover_preserve hS
  exact C.totalTopology.superset_covering
    (Sieve.functorPullback_pushforward_le (CoGrothendieck.ι C.totalPseudofunctor U.base) S) h

end CategoryTheory.SimplicialSite

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)}

variable (X) in
/-- The total site of the strict components of `X`. -/
abbrev StrictTotal := CoGrothendieck (strictSimplicialSite X).totalPseudofunctor

/-- The strict object of an object of the total site. -/
abbrev StrictTotal.obj (a : StrictTotal X) : StrictComponent X a.base.unop := a.fiber

/-- The morphism `x ⟶ u_φ(y)` of strict components underlying a morphism of the total site. -/
abbrev StrictTotal.fiberHom {a b : StrictTotal X} (f : a ⟶ b) :
    a.obj ⟶ (b.obj.transition f.base.unop : StrictComponent X a.base.unop) :=
  f.fiber

/-- The fibre morphism of an identity of the total site is the identity. -/
theorem StrictTotal.fiberHom_id (a : StrictTotal X) :
    StrictTotal.fiberHom (𝟙 a) = 𝟙 a.obj :=
  (CategoryTheory.SimplicialSite.Morphism.totalPseudofunctor_mapId_inv_app _ _ _).trans
    (eqToHom_refl _ _)

/-- The fibre morphism of a composite `f ≫ g` is that of `f` followed by the transition of that of
`g`. -/
theorem StrictTotal.fiberHom_comp {a b c : StrictTotal X} (f : a ⟶ b) (g : b ⟶ c) :
    StrictTotal.fiberHom (f ≫ g) =
      StrictTotal.fiberHom f ≫ (strictTransition X f.base.unop).map (StrictTotal.fiberHom g) :=
  (CategoryTheory.SimplicialSite.totalPseudofunctor_comp_fiber_simplicialSmallEtaleStrictTotal
      _ f g).trans
    (congrArg (StrictTotal.fiberHom f ≫ ·)
      ((congrArg (_ ≫ ·) (eqToHom_refl _ _)).trans (Category.comp_id _)))

variable (X) in
/-- **The comparison of the total site of the strict components with `X_{spaces,étale}`**:
`(n, x)` goes to the realization of `x` over `X_n`, and `(φ, g : x ⟶ u_φ(y))` to `g` followed by
the projection of `u_φ(y)` to `y`, a morphism over `X(φ)`. -/
def strictTotalComparison : StrictTotal X ⥤ SimplicialSpacesEtaleSite B S hS X where
  obj a := ⟨a.base.unop, a.obj.realize⟩
  map {_ b} f := ⟨f.base.unop,
    (StrictTotal.fiberHom f).hom.hom.left ≫ StrictObj.transitionProj f.base.unop b.obj,
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (StrictObj.transitionProj_snd _ b.obj)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (StrictObj.hom_snd (StrictTotal.fiberHom f)))))⟩
  map_id a := Hom.ext rfl
    ((congrArg (fun k : (a.obj ⟶ (a.obj.transition (𝟙 a.base).unop : StrictComponent X _)) ↦
      k.hom.hom.left ≫ StrictObj.transitionProj (𝟙 a.base).unop a.obj)
        (StrictTotal.fiberHom_id a)).trans
      ((Category.id_comp _).trans (StrictObj.transitionProj_id a.obj)))
  map_comp {a _ c} f g := Hom.ext rfl
    ((congrArg (fun k : (a.obj ⟶ (c.obj.transition (f ≫ g).base.unop : StrictComponent X _)) ↦
      k.hom.hom.left ≫ StrictObj.transitionProj (f ≫ g).base.unop c.obj)
        (StrictTotal.fiberHom_comp f g)).trans
      ((congrArg (_ ≫ ·) (StrictObj.transitionProj_comp g.base.unop f.base.unop c.obj)).trans
        (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (StrictObj.transitionProj_natural f.base.unop
            (StrictTotal.fiberHom g))).trans (Category.assoc _ _ _))))).trans
          (Category.assoc _ _ _).symm)))

/-- The comparison sends a morphism `(φ, g)` to a morphism over the simplex map `φ`. -/
theorem strictTotalComparison_map_base {a b : StrictTotal X} (f : a ⟶ b) :
    ((strictTotalComparison X).map f).base = f.base.unop := rfl

/-- The comparison sends `(φ, g)` to `g` followed by the projection of `u_φ(y)` to `y`. -/
theorem strictTotalComparison_map_hom {a b : StrictTotal X} (f : a ⟶ b) :
    ((strictTotalComparison X).map f).hom =
      (StrictTotal.fiberHom f).hom.hom.left ≫ StrictObj.transitionProj f.base.unop b.obj := rfl

/-- The comparison functor is faithful. -/
instance strictTotalComparison_faithful : (strictTotalComparison X).Faithful where
  map_injective {a b} f f' h := by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨fb', ff'⟩ := f'
    obtain rfl : fb = fb' := Quiver.Hom.unop_inj (congrArg Hom.base h)
    have hh := congrArg Hom.hom h
    change ff.hom.hom.left ≫ StrictObj.transitionProj fb.unop b.obj =
      ff'.hom.hom.left ≫ StrictObj.transitionProj fb.unop b.obj at hh
    have hf : (ff : a.obj ⟶ (b.obj.transition fb.unop : StrictComponent X _)) = ff' :=
      StrictObj.hom_ext (x := a.obj) (y := (b.obj.transition fb.unop : StrictComponent X _))
        (((congrArg (ff.hom.hom.left ≫ ·) (StrictObj.transitionProj_fst fb.unop b.obj)).symm.trans
          (Category.assoc _ _ _).symm).trans ((hh =≫ _).trans ((Category.assoc _ _ _).trans
            (congrArg (ff'.hom.hom.left ≫ ·) (StrictObj.transitionProj_fst fb.unop b.obj)))))
    subst hf
    rfl

/-- The morphism `x ⟶ u_φ(y)` of strict components lifting a morphism `t` of
`X_{spaces,étale}` between the realizations: `t` and the structure map of `x`, into the fibre
product `V ×_{X_k} X_n`. -/
def strictTotalComparison_preimageFiber {a b : StrictTotal X}
    (t : (strictTotalComparison X).obj a ⟶ (strictTotalComparison X).obj b) :
    a.obj ⟶ (b.obj.transition t.base : StrictComponent X a.base.unop) :=
  have hw : t.hom ≫ pullback.snd b.obj.obj.1.hom (X.map b.obj.simplex.op) =
      pullback.snd a.obj.obj.1.hom (X.map a.obj.simplex.op) ≫ X.map t.base.op := t.w
  InducedCategory.homMk (ObjectProperty.homMk (Over.homMk
    (pullback.lift (t.hom ≫ pullback.fst b.obj.obj.1.hom (X.map b.obj.simplex.op))
      (pullback.snd a.obj.obj.1.hom (X.map a.obj.simplex.op))
      ((Category.assoc _ _ _).trans ((congrArg (t.hom ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.map b.obj.simplex.op) hw).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((congrArg X.map (op_comp (f := b.obj.simplex) (g := t.base))).trans
              (X.map_comp _ _)).symm)))))))
    (pullback.lift_snd _ _ _)))

/-- The lift `strictTotalComparison_preimageFiber t` followed by the first projection is `t`
followed by the first projection. -/
theorem strictTotalComparison_preimageFiber_fst {a b : StrictTotal X}
    (t : (strictTotalComparison X).obj a ⟶ (strictTotalComparison X).obj b) :
    (strictTotalComparison_preimageFiber t).hom.hom.left ≫
        pullback.fst b.obj.obj.1.hom (X.map (b.obj.simplex ≫ t.base).op) =
      t.hom ≫ pullback.fst b.obj.obj.1.hom (X.map b.obj.simplex.op) :=
  pullback.lift_fst _ _ _

/-- The lift `strictTotalComparison_preimageFiber t` followed by the second projection is the
structure map of `x`. -/
theorem strictTotalComparison_preimageFiber_snd {a b : StrictTotal X}
    (t : (strictTotalComparison X).obj a ⟶ (strictTotalComparison X).obj b) :
    (strictTotalComparison_preimageFiber t).hom.hom.left ≫
        pullback.snd b.obj.obj.1.hom (X.map (b.obj.simplex ≫ t.base).op) =
      pullback.snd a.obj.obj.1.hom (X.map a.obj.simplex.op) :=
  pullback.lift_snd _ _ _

/-- The comparison functor is full. -/
instance strictTotalComparison_full : (strictTotalComparison X).Full where
  map_surjective {a b} t := by
    have hw : t.hom ≫ pullback.snd b.obj.obj.1.hom (X.map b.obj.simplex.op) =
        pullback.snd a.obj.obj.1.hom (X.map a.obj.simplex.op) ≫ X.map t.base.op := t.w
    refine ⟨⟨t.base.op, strictTotalComparison_preimageFiber t⟩,
      Hom.ext rfl ((strictTotalComparison_map_hom _).trans (pullback.hom_ext ?_ ?_))⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (StrictObj.transitionProj_fst t.base b.obj)).trans
          (strictTotalComparison_preimageFiber_fst t))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (StrictObj.transitionProj_snd t.base b.obj)).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ X.map t.base.op) (strictTotalComparison_preimageFiber_snd t)).trans
            hw.symm)))

/-- The comparison functor is essentially surjective. -/
instance strictTotalComparison_essSurj : (strictTotalComparison X).EssSurj where
  mem_essImage V := ⟨⟨op V.degree, StrictObj.ofSpacesEtale V.obj⟩,
    ⟨(degreeInclusion X V.degree).mapIso (StrictObj.realizeOfSpacesEtaleIso V.obj)⟩⟩

/-- **The total site of the strict components is equivalent to `X_{spaces,étale}`.** -/
instance strictTotalComparison_isEquivalence : (strictTotalComparison X).IsEquivalence where

/-! ### Compatibility with the topologies -/

/-- The comparison restricted to a component is the realization followed by the inclusion of
the degree. -/
theorem strictTotalComparison_map_ι {b : SimplexCategoryᵒᵖ} {y z : StrictComponent X b.unop}
    (g : y ⟶ z) :
    (strictTotalComparison X).map
        ((CoGrothendieck.ι (strictSimplicialSite X).totalPseudofunctor b).map g) =
      (degreeInclusion X b.unop).map ((strictRealize X b.unop).map g) := by
  have hg : StrictTotal.fiberHom
      ((CoGrothendieck.ι (strictSimplicialSite X).totalPseudofunctor b).map g) = g :=
    (congrArg (g ≫ ·) (StrictTotal.fiberHom_id
      ((CoGrothendieck.ι (strictSimplicialSite X).totalPseudofunctor b).obj z))).trans
      (Category.comp_id _)
  exact Hom.ext rfl ((congrArg (fun k : (y ⟶ (z.transition (𝟙 b.unop) : StrictComponent X _)) ↦
    k.hom.hom.left ≫ StrictObj.transitionProj (𝟙 b.unop) z) hg).trans
      ((congrArg (_ ≫ ·) (StrictObj.transitionProj_id z)).trans (Category.comp_id _)))

/-- A sieve of `X_{spaces,étale}` on an object of degree `n` covers exactly when its restriction
to `(X_n)_{spaces,étale}` covers. -/
theorem mem_topology_iff_functorPullback_degreeInclusion_mem {n : SimplexCategory}
    {V : SpacesEtale B S hS (X.obj (op n))} (R : Sieve ((degreeInclusion X n).obj V)) :
    R ∈ topology X ((degreeInclusion X n).obj V) ↔
      R.functorPullback (degreeInclusion X n) ∈ SpacesEtale.topology B S hS _ V :=
  ⟨fun hR ↦ functorPullback_degreeInclusion_mem hR, fun hR ↦ (topology X).superset_covering
    (Sieve.functorPullback_pushforward_le _ R) (functorPushforward_degreeInclusion_mem hR)⟩

/-- The two restrictions of a sieve of the total site to `(X_n)_{spaces,étale}` agree: through
the component and the realization, and through the comparison and the degree. -/
theorem functorPushforward_functorPullback_ι_eq {U : StrictTotal X} (R : Sieve U) :
    (R.functorPullback (CoGrothendieck.ι _ U.base)).functorPushforward
        (strictRealize X U.base.unop) =
      (R.functorPushforward (strictTotalComparison X)).functorPullback
        (degreeInclusion X U.base.unop) := by
  apply le_antisymm
  · rintro W f ⟨y, g, h, hg, rfl⟩
    exact ⟨(CoGrothendieck.ι _ U.base).obj y, (CoGrothendieck.ι _ U.base).map g,
      (degreeInclusion X U.base.unop).map h, hg,
      (Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (strictTotalComparison_map_ι g).symm)⟩
  · rintro W f ⟨V', s, t, hs, ht⟩
    obtain ⟨W', ⟨e⟩⟩ : ∃ W' : StrictComponent X U.base.unop,
        Nonempty ((strictRealize X U.base.unop).obj W' ≅ W) :=
      ⟨_, ⟨StrictObj.realizeOfSpacesEtaleIso W⟩⟩
    obtain ⟨τ, hτ⟩ := (strictTotalComparison X).map_surjective
      (show (strictTotalComparison X).obj ((CoGrothendieck.ι _ U.base).obj W') ⟶
        (strictTotalComparison X).obj V' from (degreeInclusion X U.base.unop).map e.hom ≫ t)
    obtain ⟨g', hg'⟩ := (strictRealize X U.base.unop).map_surjective (X := W')
      (Y := StrictTotal.obj U) (e.hom ≫ f)
    have hι : (CoGrothendieck.ι _ U.base).map g' = τ ≫ s :=
      (strictTotalComparison X).map_injective <|
        (strictTotalComparison_map_ι g').trans ((congrArg (degreeInclusion X _).map hg').trans
          ((Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·) ht).trans
            ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hτ.symm).trans
              (Functor.map_comp _ _ _).symm)))))
    refine ⟨W', g', e.inv, ?_, ?_⟩
    · change R ((CoGrothendieck.ι _ U.base).map g')
      rw [hι]
      exact R.downward_closed hs τ
    · rw [hg', Iso.inv_hom_id_assoc]

/-- **The comparison is a dense subsite**: a sieve of the total site of the strict components
covers exactly when its image in `X_{spaces,étale}` does. Hence it is an equivalence of sites. -/
instance strictTotalComparison_isDenseSubsite :
    (strictTotalComparison X).IsDenseSubsite (strictSimplicialSite X).totalTopology
      (topology X) where
  functorPushforward_mem_iff {U R} := by
    let T : Sieve (StrictTotal.obj U) := R.functorPullback (CoGrothendieck.ι _ U.base)
    have hD : T ∈ (strictTopology X U.base.unop).toPrecoverage.toGrothendieck (StrictTotal.obj U) ↔
        T ∈ strictTopology X U.base.unop (StrictTotal.obj U) := by
      rw [strictTopology_toPrecoverage_toGrothendieck]
    exact ((mem_topology_iff_functorPullback_degreeInclusion_mem
      (V := (StrictTotal.obj U).realize) (R.functorPushforward (strictTotalComparison X))).trans
        ((Iff.of_eq (congrArg (· ∈ SpacesEtale.topology B S hS _ (StrictTotal.obj U).realize)
          (functorPushforward_functorPullback_ι_eq R).symm)).trans
          ((Functor.functorPushforward_mem_iff (strictTopology X U.base.unop)
            (SpacesEtale.topology B S hS _) (strictRealize X U.base.unop) (S := T)).trans
            hD.symm))).trans
      (CategoryTheory.SimplicialSite.mem_totalTopology_iff_simplicialSmallEtaleStrictTotal _ R).symm

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
