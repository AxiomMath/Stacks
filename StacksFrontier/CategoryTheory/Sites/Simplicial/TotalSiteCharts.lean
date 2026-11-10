module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringRigid
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite

/-!
# Charts on the total site of a simplicial semi-representable object

Let `K` be a simplicial semi-representable object of a site `(C, J)`. An object of the total
site `(C/K)_total` of Stacks 0D8B in simplicial degree `n` is an object `V` of `C` together with
a morphism `V ⟶ K_{n,i}` to one of the components of `K_n`, that is, a morphism of
semi-representable objects `V ⟶ K_n`; we call it the *chart* of the object. A morphism of the
total site lying over a simplex map `φ : [m] ⟶ [n]` is a morphism `g : V ⟶ W` of `C` carrying the
chart of the source, pushed along `K(φ) : K_n ⟶ K_m`, to the chart of the target.

This file makes that description usable: it builds objects and morphisms of the total site out
of charts, shows that a morphism is determined by its simplex map and its underlying morphism of
`C`, and that charts are compatible with every morphism. For a sheaf of sets on the total site it
then records the two facts that descent arguments use:

* a cartesian sheaf is sent by every *cross* morphism — one whose underlying morphism of `C` is
  an identity — to a bijection;
* in a fixed simplicial degree the sheaf is separated and satisfies gluing for the families of
  morphisms whose underlying morphisms of `C` lie in a covering sieve.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.chartObjTotalSiteCharts`: the object of the total
  site with given degree and chart.
* `CategoryTheory.SimplicialSemiRepresentable.chartHomTotalSiteCharts`: the morphism of the total
  site with given simplex map and underlying morphism.
* `CategoryTheory.SimplicialSemiRepresentable.chartTotalSiteCharts`: the chart of an object of the
  total site.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.totalForget_map_chartHom_totalSiteCharts`: the
  underlying morphism of `chartHomTotalSiteCharts` is the given one.
* `CategoryTheory.SimplicialSemiRepresentable.chart_comp_totalSiteCharts`: charts are compatible
  with morphisms.
* `CategoryTheory.SimplicialSemiRepresentable.bijective_map_chartHom_id_totalSiteCharts`: a
  cartesian sheaf of sets sends cross morphisms to bijections (Stacks 07TF read on sections).
* `CategoryTheory.SimplicialSemiRepresentable.fibre_ext_totalSiteCharts` and
  `CategoryTheory.SimplicialSemiRepresentable.exists_fibre_glue_totalSiteCharts`: separation and
  gluing in a fixed simplicial degree along a covering sieve of `C`.

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

variable {C : Type u} [SmallCategory C] {K : SimplicialObject (FormalCoproduct.{u} C)}

/-! ### Objects and morphisms from charts -/

private theorem eqToHom_self_comp {D : Type*} [Category D] {X Y : D} (p : X = X) (f : X ⟶ Y) :
    eqToHom p ≫ f = f := by
  simp

private theorem comp_eqToHom_self {D : Type*} [Category D] {X Y : D} (f : X ⟶ Y) (p : Y = Y) :
    f ≫ eqToHom p = f := by
  simp

/-- The object of `C/L` given by an object `V` of `C` and a morphism of semi-representable objects
`V ⟶ L`. -/
abbrev componentObjTotalSiteCharts {L : FormalCoproduct.{u} C} {V : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ L) : ComponentOver L :=
  ⟨c.f PUnit.unit, Over.mk (c.φ PUnit.unit)⟩

/-- The morphism of `C/L` with underlying morphism `g`, between objects given by compatible
morphisms of semi-representable objects. -/
def componentHomMkTotalSiteCharts {L : FormalCoproduct.{u} C} {V W : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ L) (d : (FormalCoproduct.incl C).obj W ⟶ L)
    (g : V ⟶ W) (h : c = (FormalCoproduct.incl C).map g ≫ d) :
    componentObjTotalSiteCharts c ⟶ componentObjTotalSiteCharts d := by
  subst h
  exact CategoryTheory.Sigma.SigmaHom.mk (Over.homMk g)

/-- The underlying morphism of `componentHomMkTotalSiteCharts c d g h` is `g`. -/
theorem componentOverForget_map_componentHomMk_totalSiteCharts {L : FormalCoproduct.{u} C} {V W : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ L) (d : (FormalCoproduct.incl C).obj W ⟶ L)
    (g : V ⟶ W) (h : c = (FormalCoproduct.incl C).map g ≫ d) :
    (componentOverForget L).map (componentHomMkTotalSiteCharts c d g h) = g := by
  subst h
  rfl

/-- The forgetful functor `C/L ⥤ C` is faithful. -/
instance componentOverForget_faithful_totalSiteCharts (L : FormalCoproduct.{u} C) :
    (componentOverForget L).Faithful where
  map_injective {X Y} f g hfg := by
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    exact congrArg CategoryTheory.Sigma.SigmaHom.mk (Over.OverMorphism.ext hfg)

variable (K) in
/-- The object of the total site in simplicial degree `n` with chart `c`. -/
abbrev chartObjTotalSiteCharts (n : SimplexCategoryᵒᵖ) {V : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ K.obj n) : Grothendieck (slices K) :=
  ⟨n, componentObjTotalSiteCharts c⟩

/-- The morphism of the total site lying over `φ`, with underlying morphism `g`. -/
def chartHomTotalSiteCharts {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) {V W : C}
    {c : (FormalCoproduct.incl C).obj V ⟶ K.obj m} {d : (FormalCoproduct.incl C).obj W ⟶ K.obj n}
    (g : V ⟶ W) (h : c ≫ K.map φ = (FormalCoproduct.incl C).map g ≫ d) :
    chartObjTotalSiteCharts K m c ⟶ chartObjTotalSiteCharts K n d :=
  ⟨φ, componentHomMkTotalSiteCharts (c ≫ K.map φ) d g h⟩

/-- The morphism `chartHomTotalSiteCharts φ g h` lies over `φ`. -/
@[simp]
theorem chartHom_base_totalSiteCharts {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) {V W : C}
    {c : (FormalCoproduct.incl C).obj V ⟶ K.obj m} {d : (FormalCoproduct.incl C).obj W ⟶ K.obj n}
    (g : V ⟶ W) (h : c ≫ K.map φ = (FormalCoproduct.incl C).map g ≫ d) :
    (chartHomTotalSiteCharts φ g h).base = φ := rfl

/-- The underlying morphism of `chartHomTotalSiteCharts φ g h` is `g`. -/
@[simp]
theorem totalForget_map_chartHom_totalSiteCharts {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) {V W : C}
    {c : (FormalCoproduct.incl C).obj V ⟶ K.obj m} {d : (FormalCoproduct.incl C).obj W ⟶ K.obj n}
    (g : V ⟶ W) (h : c ≫ K.map φ = (FormalCoproduct.incl C).map g ≫ d) :
    (totalForget K).map (chartHomTotalSiteCharts φ g h) = g :=
  (totalForget_map K _).trans (componentOverForget_map_componentHomMk_totalSiteCharts _ _ g h)

/-- The chart of an object of the total site: the morphism of semi-representable objects from
its underlying object of `C` to `K` in its simplicial degree. -/
def chartTotalSiteCharts (x : Grothendieck (slices K)) :
    (FormalCoproduct.incl C).obj ((totalForget K).obj x) ⟶ K.obj x.base :=
  FormalCoproduct.Hom.fromIncl x.fiber.1 x.fiber.2.hom

/-- Every object of the total site is the object given by its degree and its chart. -/
theorem chartObj_chart_totalSiteCharts (x : Grothendieck (slices K)) :
    chartObjTotalSiteCharts K x.base (chartTotalSiteCharts x) = x := rfl

/-- The chart of `chartObjTotalSiteCharts K n c` is `c`. -/
@[simp]
theorem chart_chartObj_totalSiteCharts (n : SimplexCategoryᵒᵖ) {V : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ K.obj n) :
    chartTotalSiteCharts (chartObjTotalSiteCharts K n c) = c := rfl

/-- A morphism of `C/L` carries the semi-representable morphism of its source to the composite
of its underlying morphism with that of its target. -/
theorem fromIncl_comp_componentOver_totalSiteCharts {L : FormalCoproduct.{u} C}
    {X Y : ComponentOver L} (f : X ⟶ Y) :
    (FormalCoproduct.Hom.fromIncl X.1 X.2.hom :
        (FormalCoproduct.incl C).obj ((componentOverForget L).obj X) ⟶ L) =
      (FormalCoproduct.incl C).map ((componentOverForget L).map f) ≫
        (FormalCoproduct.Hom.fromIncl Y.1 Y.2.hom :
          (FormalCoproduct.incl C).obj ((componentOverForget L).obj Y) ⟶ L) := by
  rcases f with @⟨i, X, Y, f⟩
  refine FormalCoproduct.hom_ext rfl fun _ => ?_
  exact (comp_eqToHom_self _ _).trans (Over.w f).symm

/-- **Charts are compatible with morphisms of the total site.** -/
theorem chart_comp_totalSiteCharts {x y : Grothendieck (slices K)} (t : x ⟶ y) :
    chartTotalSiteCharts x ≫ K.map t.base =
      (FormalCoproduct.incl C).map ((totalForget K).map t) ≫ chartTotalSiteCharts y := by
  rw [totalForget_map]
  exact fromIncl_comp_componentOver_totalSiteCharts t.fiber

/-- The underlying morphism of the inclusion of a morphism of `C/K_n` is its underlying
morphism. -/
@[simp]
theorem totalForget_map_ι_eq_componentOverForget_map_totalSiteCharts {n : SimplexCategoryᵒᵖ}
    {Y X : ComponentOver (K.obj n)} (f : Y ⟶ X) :
    (totalForget K).map ((Grothendieck.ι (slices K) n).map f) =
      (componentOverForget (K.obj n)).map f := by
  rw [totalForget_map]
  change (componentOverForget (K.obj n)).map (eqToHom _ ≫ f) = _
  refine ((componentOverForget (K.obj n)).map_comp (eqToHom _) f).trans ?_
  refine (congrArg (· ≫ (componentOverForget (K.obj n)).map f)
    (eqToHom_map (componentOverForget (K.obj n)) _)).trans ?_
  exact eqToHom_self_comp (D := C) _ _

/-- The chart of the source of a morphism of `C/K_n` is the underlying morphism followed by the
chart of the target. -/
theorem chart_ι_totalSiteCharts {n : SimplexCategoryᵒᵖ} {Y X : ComponentOver (K.obj n)}
    (f : Y ⟶ X) :
    chartTotalSiteCharts (⟨n, Y⟩ : Grothendieck (slices K)) =
      (FormalCoproduct.incl C).map ((componentOverForget (K.obj n)).map f) ≫
        chartTotalSiteCharts (⟨n, X⟩ : Grothendieck (slices K)) :=
  fromIncl_comp_componentOver_totalSiteCharts f

/-! ### Cross morphisms -/

/-- The cross morphism of the total site out of `chartObjTotalSiteCharts K m c` over `φ`: its
underlying morphism is the identity and its target has the pushed-forward chart. -/
abbrev crossHomTotalSiteCharts {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) {V : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ K.obj m) :
    chartObjTotalSiteCharts K m c ⟶ chartObjTotalSiteCharts K n (c ≫ K.map φ) :=
  chartHomTotalSiteCharts φ (𝟙 V) (by simp)

/-! ### Cartesian sheaves send cross morphisms to bijections -/

variable (J : GrothendieckTopology C) [J.toCoverage.HasPullbacks]

variable (K) in
/-- **Stacks 0D85.** The transition functor of a simplex map is continuous for the component
topologies of the simplicial site of `K`: they are the componentwise localized topologies, for
which the relocalization functor is continuous. The instance is
`CategoryTheory.SimplicialSemiRepresentable.componentOverMap_isContinuous`, downstream. -/
theorem isContinuous_componentOverMap_componentTopology_totalSiteCharts {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (componentOverMap (K.map φ.op)).IsContinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology m) := by
  rw [componentTopology_eq, componentTopology_eq]
  exact LocalizationSites.relocalizationFunctor_isContinuous (transitionSites J K φ.op)

attribute [local instance] isContinuous_componentOverMap_componentTopology_totalSiteCharts

/-- If the canonical transition of Stacks 09WF of a sheaf of sets on the total site at a simplex
map `φ` is invertible, then restriction along every Cartesian lift of `φ` is a bijection on
sections. -/
theorem bijective_map_ιNatTrans_of_isIso_totalSiteCharts {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (situation J K).totalTopology (Type u))
    (hG : IsIso (((situation J K).fiberTransition φ).app G))
    (U : ComponentOver (K.obj (op n))) :
    Function.Bijective
      (G.obj.map ((Grothendieck.ιNatTrans (F := slices K) φ.op).app U).op) := by
  let u := componentOverMap (K.map φ.op)
  have : u.IsContinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology m) :=
    isContinuous_componentOverMap_componentTopology_totalSiteCharts K J φ
  let adj₂ := u.sheafAdjunctionCocontinuous (Type u) ((situation J K).componentTopology n)
    ((situation J K).componentTopology m)
  let A : ((situation J K).restrict m).obj G ⟶
      (u.sheafPushforwardCocontinuous (Type u) ((situation J K).componentTopology n)
        ((situation J K).componentTopology m)).obj (((situation J K).restrict n).obj G) :=
    ((situation J K).restrictTransition φ).app G
  have h₁ : IsIso ((adj₂.homEquiv _ _).symm A) :=
    ((Adjunction.isIso_homEquiv_symm_iff ((situation J K).transitionMorphism φ).adj adj₂ A).1 hG)
  have h₂ : ((adj₂.homEquiv _ _).symm A).hom =
      ((u.op.ranAdjunction (Type u)).homEquiv _ _).symm A.hom := by
    have h := u.sheafAdjunctionCocontinuous_homEquiv_apply_hom (Type u)
      ((situation J K).componentTopology n) ((situation J K).componentTopology m)
      ((adj₂.homEquiv _ _).symm A)
    exact (Equiv.eq_symm_apply _).2
      (h.symm.trans (congrArg (fun t => t.hom) (Equiv.apply_symm_apply (adj₂.homEquiv _ _) A)))
  have h₃ : IsIso (((adj₂.homEquiv _ _).symm A).hom.app (op U)) := by
    have : IsIso ((adj₂.homEquiv _ _).symm A).hom :=
      (sheafToPresheaf _ _).map_isIso ((adj₂.homEquiv _ _).symm A)
    infer_instance
  rw [h₂] at h₃
  have key := SimplicialSiteSituation.restrictTransition_inr_app (simplicialSite J K) φ G U
  exact (isIso_iff_bijective _).1 ((congrArg IsIso key).mp h₃)

/-- **A cartesian sheaf of sets sends cross morphisms to bijections.** For a cartesian sheaf on
the total site, restriction along a morphism of the total site lying over a simplex map and whose
underlying morphism of `C` is an identity is a bijection on sections. -/
theorem bijective_map_chartHom_id_totalSiteCharts
    (G : Sheaf (situation J K).totalTopology (Type u))
    (hG : (situation J K).IsCartesianSheaf G) {m n : SimplexCategory} (φ : m ⟶ n) {V : C}
    (c : (FormalCoproduct.incl C).obj V ⟶ K.obj (op n))
    (d : (FormalCoproduct.incl C).obj V ⟶ K.obj (op m))
    (h : c ≫ K.map φ.op = (FormalCoproduct.incl C).map (𝟙 V) ≫ d) :
    Function.Bijective (G.obj.map (chartHomTotalSiteCharts φ.op (𝟙 V) h).op) := by
  obtain rfl : d = c ≫ K.map φ.op := by simpa using h.symm
  have ht : chartHomTotalSiteCharts φ.op (𝟙 V) h =
      (Grothendieck.ιNatTrans (F := slices K) φ.op).app (componentObjTotalSiteCharts c) := by
    refine total_hom_ext K _ _ rfl ?_
    rw [totalForget_map_chartHom_totalSiteCharts]
    exact ((totalForget_map K ((Grothendieck.ιNatTrans (F := slices K) φ.op).app
      (componentObjTotalSiteCharts c))).trans ((sliceForget K (op m)).map_id _)).symm
  rw [ht]
  exact bijective_map_ιNatTrans_of_isIso_totalSiteCharts J φ G (hG φ) _

/-! ### Separation and gluing in a fixed simplicial degree -/

/-- The pullback along `sliceForget` of a covering sieve of `C` is a sheaf-covering sieve for the
restriction of a sheaf on the total site to simplicial degree `n`. -/
private theorem isSheafFor_functorPullback_sliceForget_totalSiteCharts
    (G : Sheaf (situation J K).totalTopology (Type u)) (n : SimplexCategory)
    (X : ComponentOver (K.obj (op n))) {R : Sieve ((componentOverForget (K.obj (op n))).obj X)}
    (hR : R ∈ J _) :
    Presieve.IsSheafFor (((situation J K).restrict n).obj G).obj
      (R.functorPullback (sliceForget K (op n))).arrows :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (((situation J K).restrict n).obj G).property _
    (Functor.cover_lift (sliceForget K (op n)) ((situation J K).componentTopology n) J hR)

/-- **Separation in a fixed simplicial degree.** Two sections of a sheaf on the total site over
an object of degree `n` agree if they agree after restriction along every morphism of `C/K_n`
whose underlying morphism lies in a fixed covering sieve. -/
theorem fibre_ext_totalSiteCharts (G : Sheaf (situation J K).totalTopology (Type u))
    (n : SimplexCategory)
    (X : ComponentOver (K.obj (op n))) {R : Sieve ((componentOverForget (K.obj (op n))).obj X)}
    (hR : R ∈ J _) (w w' : G.obj.obj (op ⟨op n, X⟩))
    (h : ∀ ⦃Y : ComponentOver (K.obj (op n))⦄ (f : Y ⟶ X),
      R ((componentOverForget (K.obj (op n))).map f) →
        G.obj.map ((Grothendieck.ι (slices K) (op n)).map f).op w =
          G.obj.map ((Grothendieck.ι (slices K) (op n)).map f).op w') :
    w = w' := by
  have hsh := isSheafFor_functorPullback_sliceForget_totalSiteCharts J G n X hR
  exact hsh.isSeparatedFor.ext fun Y f hf => h f hf

/-- **Gluing in a fixed simplicial degree.** A family of sections indexed by the morphisms of
`C/K_n` into `X` whose underlying morphisms lie in a covering sieve, compatible with restriction,
is the family of restrictions of one section. -/
theorem exists_fibre_glue_totalSiteCharts (G : Sheaf (situation J K).totalTopology (Type u))
    (n : SimplexCategory)
    (X : ComponentOver (K.obj (op n))) {R : Sieve ((componentOverForget (K.obj (op n))).obj X)}
    (hR : R ∈ J _)
    (val : ∀ ⦃Y : ComponentOver (K.obj (op n))⦄ (f : Y ⟶ X),
      R ((componentOverForget (K.obj (op n))).map f) → G.obj.obj (op ⟨op n, Y⟩))
    (hval : ∀ ⦃Y Y' : ComponentOver (K.obj (op n))⦄ (f : Y ⟶ X) (g : Y' ⟶ Y)
      (hf : R ((componentOverForget (K.obj (op n))).map f))
      (hgf : R ((componentOverForget (K.obj (op n))).map (g ≫ f))),
        G.obj.map ((Grothendieck.ι (slices K) (op n)).map g).op (val f hf) = val (g ≫ f) hgf) :
    ∃ w : G.obj.obj (op ⟨op n, X⟩), ∀ ⦃Y : ComponentOver (K.obj (op n))⦄ (f : Y ⟶ X)
      (hf : R ((componentOverForget (K.obj (op n))).map f)),
        G.obj.map ((Grothendieck.ι (slices K) (op n)).map f).op w = val f hf := by
  let G' := ((situation J K).restrict n).obj G
  have hsh := isSheafFor_functorPullback_sliceForget_totalSiteCharts J G n X hR
  let x : Presieve.FamilyOfElements G'.obj (R.functorPullback (sliceForget K (op n))).arrows :=
    fun Y f hf => val f hf
  have hx : x.Compatible :=
    (Presieve.compatible_iff_sieveCompatible x).2 fun Y Y' f g hf => (hval f g hf _).symm
  exact ⟨hsh.amalgamate x hx, fun Y f hf => hsh.valid_glue hx f hf⟩

end CategoryTheory.SimplicialSemiRepresentable

end
