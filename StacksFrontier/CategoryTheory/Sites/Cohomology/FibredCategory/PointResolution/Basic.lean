module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory

/-!
# Fibrewise point resolutions of a fibred category

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site, as in the standing
data of Stacks 08P8, and let `A : D ⥤ CosimplicialObject C` be a family of cosimplicial objects
`A_{•,V}` lying over the objects `V` of `D` (that is, `A ⋙ p` is constant on `V`), functorial in
`V`. Suppose that each `A_{•,V}` is a *point resolution* of the fibre `C_V` in the sense of
Stacks 08Q9: for every object `W` of `C_V` the simplicial set `Mor_{C_V}(A_{•,V}, W)` is homotopy
equivalent to a point. This is the situation of Stacks 08VB (for the Zariski site of a scheme)
and of Stacks 08VL (for the étale site of an algebraic space).

For an abelian presheaf `G` on `C` this file forms the simplicial presheaf `V ↦ G(A_{•,V})` on
`D`, its Moore complex, and the presheaf `V ↦ H_0(G(A_{•,V}))`, and proves that the latter functor
is left adjoint to restriction along `p`.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.pointEvaluation`: `G ↦ (V ↦ G(A_{•,V}))`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.pointMooreComplex`: its Moore complex.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.pointZero`: `G ↦ (V ↦ H_0(G(A_{•,V})))`.

## Main results

* `CategoryTheory.SimplicialObject.eqvGen_edgeRel_of_homotopyEquivalences`: a simplicial set
  homotopy equivalent to a point is connected.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.map_comp_eq_of_isHomLift`: restriction
  along two maps `A_{0,V} ⟶ y` over the same base map agrees after any map killing the
  degree-one differential.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.pointZeroAdjunction`: `pointZero` is left
  adjoint to restriction along `p`; this is the degree-zero case of Stacks 08Q9, fibre by fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  (A : s.base.C ⥤ CosimplicialObject s.C)

/-- The functor `[n] ↦ (V ↦ A_{n,V})`, read on opposite categories. -/
abbrev pointEvaluationShape : SimplexCategoryᵒᵖ ⥤ (s.base.Cᵒᵖ ⥤ s.Cᵒᵖ) :=
  A.flip.op ⋙ Functor.opHom _ _

/-- The simplicial presheaf `V ↦ G(A_{•,V})` attached to a presheaf `G` on the total category. -/
abbrev pointEvaluation : (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ⥤
    SimplicialObject (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :=
  Functor.whiskeringRight _ _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (pointEvaluationShape s A)

/-- The complex of presheaves `V ↦ G(A_{•,V})`. -/
abbrev pointMooreComplex : (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ⥤
    ChainComplex (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ℕ :=
  pointEvaluation s A ⋙ alternatingFaceMapComplex _

example (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) (V : s.base.C) :
    (((pointMooreComplex s A).obj G).X 0).obj (op V) = G.obj (op ((A.obj V).obj ⦋0⦌)) := rfl

/-- The degree-one differential of `V ↦ G(A_{•,V})` at `V` is `G(δ⁰) - G(δ¹)`. -/
lemma pointMooreComplex_d_one_zero_app (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
    (V : s.base.C) :
    (((pointMooreComplex s A).obj G).d 1 0).app (op V) =
      G.map ((A.obj V).map (SimplexCategory.δ (0 : Fin 2))).op -
        G.map ((A.obj V).map (SimplexCategory.δ (1 : Fin 2))).op := by
  change (((alternatingFaceMapComplex _).obj ((pointEvaluation s A).obj G)).d (0 + 1) 0).app
    (op V) = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_one_zsmul, ← sub_eq_add_neg]
  rfl

/-- The presheaf `V ↦ H_0(G(A_{•,V}))`, the cokernel of the two cofaces
`G(A_{1,V}) ⇉ G(A_{0,V})`. -/
abbrev pointZero : (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) ⥤
    (s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) where
  obj G := ((pointMooreComplex s A).obj G).opcycles 0
  map η := HomologicalComplex.opcyclesMap ((pointMooreComplex s A).map η) 0
  map_id G := by
    rw [CategoryTheory.Functor.map_id]
    exact HomologicalComplex.opcyclesMap_id _ 0
  map_comp η η' := by
    rw [CategoryTheory.Functor.map_comp]
    exact HomologicalComplex.opcyclesMap_comp _ _ 0

/-- The functor `G ↦ (V ↦ G(A_{•,V}))` to complexes is additive. -/
instance pointMooreComplex_additive : (pointMooreComplex s A).Additive where
  map_add {G G' f g} := by
    ext n V : 3
    rfl

/-- The functor `G ↦ (V ↦ H_0(G(A_{•,V})))` is additive. -/
instance pointZero_additive : (pointZero s A).Additive where
  map_add {G G' f g} := by
    change HomologicalComplex.opcyclesMap ((pointMooreComplex s A).map (f + g)) 0 = _
    rw [Functor.map_add]
    refine (cancel_epi (HomologicalComplex.pOpcycles _ 0)).1 ?_
    rw [HomologicalComplex.p_opcyclesMap, Preadditive.comp_add, HomologicalComplex.p_opcyclesMap,
      HomologicalComplex.p_opcyclesMap, HomologicalComplex.add_f_apply, Preadditive.add_comp]

end Stacks.Sites.FibredCategory.FibredCategorySituation

namespace CategoryTheory.SimplicialObject

universe v

/-- Two `0`-simplices of a simplicial set are *joined by an edge* when some `1`-simplex has them
as its two faces. -/
def EdgeRel (X : SimplicialObject (Type v)) (a b : X _⦋0⦌) : Prop :=
  ∃ σ : X _⦋1⦌, X.δ 1 σ = a ∧ X.δ 0 σ = b

/-- A simplicial homotopy joins the images of every `0`-simplex by an edge. -/
lemma edgeRel_of_homotopy {X Y : SimplicialObject (Type v)} {f g : X ⟶ Y}
    (H : Homotopy f g) (x : X _⦋0⦌) : EdgeRel Y (f.app _ x) (g.app _ x) :=
  ⟨H.h (n := 0) 0 x,
    by simpa using ConcreteCategory.congr_hom (H.h_last_comp_δ_last 0) x,
    by
      have := ConcreteCategory.congr_hom (H.h_zero_comp_δ_zero 0) x
      rwa [ConcreteCategory.comp_apply] at this⟩

/-- Homotopic maps of simplicial sets send every `0`-simplex to `0`-simplices joined by a chain of
edges. -/
lemma eqvGen_edgeRel_of_eqvGen {X Y : SimplicialObject (Type v)} {f g : X ⟶ Y}
    (h : Relation.EqvGen (fun f g : X ⟶ Y => Nonempty (Homotopy f g)) f g) (x : X _⦋0⦌) :
    Relation.EqvGen (EdgeRel Y) (f.app _ x) (g.app _ x) := by
  induction h with
  | rel f g H => exact .rel _ _ (edgeRel_of_homotopy H.some x)
  | refl f => exact .refl _
  | symm f g _ ih => exact .symm _ _ ih
  | trans f g k _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- **A simplicial set homotopy equivalent to a point is connected**: any two of its
`0`-simplices are joined by a chain of edges. -/
lemma eqvGen_edgeRel_of_homotopyEquivalences {X : SimplicialObject (Type v)}
    {f : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1}}
    (hf : homotopyEquivalences (Type v) f) (a b : X _⦋0⦌) :
    Relation.EqvGen (EdgeRel X) a b := by
  obtain ⟨g, h₁, -⟩ := hf
  have ha := eqvGen_edgeRel_of_eqvGen h₁ a
  have hb := eqvGen_edgeRel_of_eqvGen h₁ b
  have hfa : (f ≫ g).app _ a = (f ≫ g).app _ b := rfl
  exact .trans _ _ _ (.symm _ _ ha) (hfa ▸ hb)

/-- A simplicial set homotopy equivalent to a point has a `0`-simplex. -/
lemma nonempty_of_homotopyEquivalences {X : SimplicialObject (Type v)}
    {f : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1}}
    (hf : homotopyEquivalences (Type v) f) : Nonempty (X _⦋0⦌) := by
  obtain ⟨g, -, -⟩ := hf
  exact ⟨g.app _ PUnit.unit⟩

end CategoryTheory.SimplicialObject

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)

include hA in
/-- Every term `A_{n,V}` lies over `V`. -/
lemma obj_obj_proj (V : s.base.C) (n : SimplexCategory) : s.p.obj ((A.obj V).obj n) = V :=
  Functor.congr_obj (Functor.congr_obj hA V) n

include hA in
/-- The cosimplicial structure maps of `A_{•,V}` lie over the identity of `V`. -/
lemma isHomLift_obj_map (V : s.base.C) {n m : SimplexCategory} (f : n ⟶ m) :
    s.p.IsHomLift (𝟙 V) ((A.obj V).map f) :=
  ((Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).map f).2

include hA in
/-- The maps `A_{n,V'} ⟶ A_{n,V}` lie over `V' ⟶ V`. -/
lemma isHomLift_map_app {V' V : s.base.C} (h : V' ⟶ V) (n : SimplexCategory) :
    s.p.IsHomLift h ((A.map h).app n) := by
  have e := NatTrans.congr_app (Functor.congr_hom hA h) n
  simp only [Functor.comp_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    NatTrans.comp_app, eqToHom_app, Functor.const_map_app] at e
  exact IsHomLift.of_fac' s.p h _ (obj_obj_proj s hA V' n) (obj_obj_proj s hA V n) e

variable (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
  ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
    SimplicialObject.homotopyEquivalences (Type vC) f)

include hres in
/-- **Restriction along any two maps `A_{0,V} ⟶ y` over the same base map agrees after a map
killing the degree-one differential.** -/
theorem map_comp_eq_of_isHomLift {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (φ : ((pointMooreComplex s A).obj G).X 0 ⟶ H)
    (hφ : ((pointMooreComplex s A).obj G).d 1 0 ≫ φ = 0)
    {V : s.base.C} {y : s.C} (k : V ⟶ s.p.obj y) (g g' : (A.obj V).obj ⦋0⦌ ⟶ y)
    [s.p.IsHomLift k g] [s.p.IsHomLift k g'] :
    G.map g.op ≫ φ.app (op V) = G.map g'.op ≫ φ.app (op V) := by
  let π := Functor.IsPreFibered.pullbackMap (p := s.p) (rfl : s.p.obj y = s.p.obj y) k
  let W : s.p.Fiber V := ⟨_, Functor.IsPreFibered.pullbackObj_proj (p := s.p) rfl k⟩
  let F := Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)
  have hδ : G.map ((A.obj V).map (SimplexCategory.δ (0 : Fin 2))).op ≫ φ.app (op V) =
      G.map ((A.obj V).map (SimplexCategory.δ (1 : Fin 2))).op ≫ φ.app (op V) := by
    have := NatTrans.congr_app hφ (op V)
    rwa [NatTrans.comp_app, pointMooreComplex_d_one_zero_app, Preadditive.sub_comp,
      NatTrans.app_zero, sub_eq_zero] at this
  have hδ' : ∀ {z z' : s.C} (τ : (A.obj V).obj ⦋1⦌ ⟶ z) (u : z ⟶ z'),
      G.map (((A.obj V).map (SimplexCategory.δ (0 : Fin 2)) ≫ τ) ≫ u).op ≫ φ.app (op V) =
        G.map (((A.obj V).map (SimplexCategory.δ (1 : Fin 2)) ≫ τ) ≫ u).op ≫ φ.app (op V) := by
    intro z z' τ u
    simp only [op_comp, Functor.map_comp, Category.assoc, hδ]
  have key : ∀ a b : F.obj ⦋0⦌ ⟶ W, Relation.EqvGen
      (SimplicialObject.EdgeRel (F.op ⋙ yoneda.obj W)) a b →
      G.map (Functor.Fiber.fiberInclusion.map a ≫ π).op ≫ φ.app (op V) =
        G.map (Functor.Fiber.fiberInclusion.map b ≫ π).op ≫ φ.app (op V) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      obtain ⟨σ, rfl, rfl⟩ := hab
      let σ' : F.obj ⦋1⦌ ⟶ W := σ
      have e : ∀ i : Fin 2, Functor.Fiber.fiberInclusion.map
          (SimplicialObject.δ (F.op ⋙ yoneda.obj W) i σ) =
            (A.obj V).map (SimplexCategory.δ i) ≫ Functor.Fiber.fiberInclusion.map σ' :=
        fun _ => rfl
      rw [e 1, e 0]
      exact (hδ' (Functor.Fiber.fiberInclusion.map σ') π).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨f, hf⟩ := hres V W
  rw [← Functor.IsCartesian.fac s.p k π g, ← Functor.IsCartesian.fac s.p k π g']
  exact key (Functor.Fiber.homMk s.p V (Functor.IsCartesian.map s.p k π g))
    (Functor.Fiber.homMk s.p V (Functor.IsCartesian.map s.p k π g'))
    (SimplicialObject.eqvGen_edgeRel_of_homotopyEquivalences hf _ _)

/-! ### The degree-zero functor is left adjoint to restriction along the projection -/

/-- A chosen map `A_{0,p(y)} ⟶ y` in the fibre over `p(y)`. -/
def pointSection (y : s.C) :
    (Functor.Fiber.inducedFunctor (Functor.congr_obj hA (s.p.obj y))).obj ⦋0⦌ ⟶
      (⟨y, rfl⟩ : s.p.Fiber (s.p.obj y)) :=
  (SimplicialObject.nonempty_of_homotopyEquivalences (hres _ ⟨y, rfl⟩).choose_spec).some

/-- The underlying map `A_{0,p(y)} ⟶ y` of `pointSection`. -/
abbrev pointSectionHom (y : s.C) : (A.obj (s.p.obj y)).obj ⦋0⦌ ⟶ y :=
  Functor.Fiber.fiberInclusion.map (pointSection s hA hres y)

/-- The chosen map `A_{0,p(y)} ⟶ y` lies over the identity of `p(y)`. -/
instance isHomLift_pointSectionHom (y : s.C) :
    s.p.IsHomLift (𝟙 (s.p.obj y)) (pointSectionHom s hA hres y) :=
  (pointSection s hA hres y).2

variable {s} in
/-- The map `G ⟶ p^*H` attached to a map out of `V ↦ G(A_{0,V})` killing the degree-one
differential: over `y` it is restriction along the chosen map `A_{0,p(y)} ⟶ y`. -/
def pointZeroLift {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (φ : ((pointMooreComplex s A).obj G).X 0 ⟶ H)
    (hφ : ((pointMooreComplex s A).obj G).d 1 0 ≫ φ = 0) : G ⟶ s.p.op ⋙ H where
  app y := G.map (pointSectionHom s hA hres y.unop).op ≫ φ.app (op (s.p.obj y.unop))
  naturality {y y'} k := by
    have hnat := φ.naturality (s.p.map k.unop).op
    have := isHomLift_map_app s hA (s.p.map k.unop) ⦋0⦌
    have key := map_comp_eq_of_isHomLift s hA hres φ hφ (s.p.map k.unop)
      (pointSectionHom s hA hres y'.unop ≫ k.unop)
      ((A.map (s.p.map k.unop)).app ⦋0⦌ ≫ pointSectionHom s hA hres y.unop)
    simp only [op_comp, Functor.map_comp, Category.assoc] at key
    change G.map k ≫ G.map (pointSectionHom s hA hres y'.unop).op ≫ φ.app _ =
      (G.map (pointSectionHom s hA hres y.unop).op ≫ φ.app _) ≫ H.map (s.p.map k.unop).op
    rwa [Category.assoc, ← hnat]

/-- Naturality of `ψ : G ⟶ p^*H` along a map `f` lying over `k`, written with the transport
maps `eqToHom` along `p x = V` and `p y = V'`. -/
private lemma map_comp_app_eqToHom {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}} (ψ : G ⟶ s.p.op ⋙ H)
    {x y : s.C} {V V' : s.base.C} (k : V ⟶ V') (f : x ⟶ y) [s.p.IsHomLift k f]
    (hx : s.p.obj x = V) (hy : s.p.obj y = V') :
    G.map f.op ≫ ψ.app (op x) ≫ H.map (eqToHom hx.symm).op =
      ψ.app (op y) ≫ H.map (eqToHom hy.symm).op ≫ H.map k.op := by
  have hψ := ψ.naturality f.op
  have hp := IsHomLift.fac' s.p k f
  rw [← Category.assoc, hψ]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hp, Category.assoc,
    op_comp, Functor.map_comp, eqToHom_op, eqToHom_map]
  simp

variable {s} in
/-- The map out of `V ↦ G(A_{0,V})` attached to a map `G ⟶ p^*H`: over `V` it is the component at
`A_{0,V}`, which lies over `V`. -/
def pointZeroRestrict {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}} (ψ : G ⟶ s.p.op ⋙ H) :
    ((pointMooreComplex s A).obj G).X 0 ⟶ H where
  app V := ψ.app (op ((A.obj V.unop).obj ⦋0⦌)) ≫
    H.map (eqToHom (obj_obj_proj s hA V.unop ⦋0⦌).symm).op
  naturality {V V'} h := by
    have := isHomLift_map_app s hA h.unop ⦋0⦌
    have hψ := ψ.naturality ((A.map h.unop).app ⦋0⦌).op
    have hp := IsHomLift.fac' s.p h.unop ((A.map h.unop).app ⦋0⦌)
    change G.map ((A.map h.unop).app ⦋0⦌).op ≫ ψ.app _ ≫ H.map _ = (ψ.app _ ≫ H.map _) ≫ H.map h
    rw [← Category.assoc, hψ]
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hp, Category.assoc,
      op_comp, Functor.map_comp, eqToHom_op, eqToHom_map]
    simp

include hA in
/-- The map out of `V ↦ G(A_{0,V})` attached to `G ⟶ p^*H` kills the degree-one differential. -/
lemma d_one_zero_comp_pointZeroRestrict {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}} (ψ : G ⟶ s.p.op ⋙ H) :
    ((pointMooreComplex s A).obj G).d 1 0 ≫ pointZeroRestrict hA ψ = 0 := by
  ext V : 2
  rw [NatTrans.comp_app, pointMooreComplex_d_one_zero_app, NatTrans.app_zero,
    Preadditive.sub_comp, sub_eq_zero]
  have := isHomLift_obj_map s hA V.unop (SimplexCategory.δ (0 : Fin 2))
  have := isHomLift_obj_map s hA V.unop (SimplexCategory.δ (1 : Fin 2))
  change G.map _ ≫ ψ.app _ ≫ H.map _ = G.map _ ≫ ψ.app _ ≫ H.map _
  rw [map_comp_app_eqToHom s ψ (𝟙 V.unop) _ (obj_obj_proj s hA _ _) (obj_obj_proj s hA _ _),
    map_comp_app_eqToHom s ψ (𝟙 V.unop) _ (obj_obj_proj s hA _ _) (obj_obj_proj s hA _ _)]

variable {s} in
/-- `pointZeroRestrict` is a left inverse of `pointZeroLift`. -/
lemma pointZeroRestrict_pointZeroLift {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (φ : ((pointMooreComplex s A).obj G).X 0 ⟶ H)
    (hφ : ((pointMooreComplex s A).obj G).d 1 0 ≫ φ = 0) :
    pointZeroRestrict hA (pointZeroLift hA hres φ hφ) = φ := by
  ext V : 2
  set e := (obj_obj_proj s hA V.unop ⦋0⦌).symm
  have := isHomLift_map_app s hA (eqToHom e) ⦋0⦌
  have : s.p.IsHomLift (eqToHom e) (𝟙 ((A.obj V.unop).obj ⦋0⦌)) :=
    IsHomLift.of_fac' s.p (eqToHom e) _ (obj_obj_proj s hA V.unop ⦋0⦌) rfl (by simp)
  have key := map_comp_eq_of_isHomLift s hA hres φ hφ (eqToHom e)
    ((A.map (eqToHom e)).app ⦋0⦌ ≫ pointSectionHom s hA hres ((A.obj V.unop).obj ⦋0⦌))
    (𝟙 _)
  have hnat := φ.naturality (eqToHom e).op
  change (G.map (pointSectionHom s hA hres _).op ≫ φ.app _) ≫ H.map (eqToHom e).op = φ.app V
  rw [Category.assoc, ← hnat]
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  exact key.trans (by simp)

variable {s} in
/-- `pointZeroLift` is a left inverse of `pointZeroRestrict`. -/
lemma pointZeroLift_pointZeroRestrict {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}} (ψ : G ⟶ s.p.op ⋙ H) :
    pointZeroLift hA hres (pointZeroRestrict hA ψ) (d_one_zero_comp_pointZeroRestrict s hA ψ) =
      ψ := by
  ext y : 2
  change G.map _ ≫ ψ.app _ ≫ H.map _ = ψ.app y
  rw [map_comp_app_eqToHom s ψ (𝟙 (s.p.obj y.unop)) _ (obj_obj_proj s hA _ _) rfl]
  simp

variable {s} in
/-- Maps `H_0(G(A_{•,-})) ⟶ H` correspond to maps `G ⟶ p^*H`. -/
def pointZeroHomEquiv (G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC})
    (H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}) :
    ((pointZero s A).obj G ⟶ H) ≃
      (G ⟶ ((Functor.whiskeringLeft _ _ AddCommGrpCat.{max w uD vD uC vC}).obj s.p.op).obj H) where
  toFun φ := pointZeroLift hA hres (((pointMooreComplex s A).obj G).pOpcycles 0 ≫
      (show ((pointMooreComplex s A).obj G).opcycles 0 ⟶ H from φ))
    (by rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp])
  invFun ψ := ((pointMooreComplex s A).obj G).descOpcycles (pointZeroRestrict hA ψ) 1
    (by simp) (d_one_zero_comp_pointZeroRestrict s hA ψ)
  left_inv φ := by
    refine (cancel_epi (((pointMooreComplex s A).obj G).pOpcycles 0)).1 ?_
    rw [HomologicalComplex.p_descOpcycles, pointZeroRestrict_pointZeroLift]
  right_inv ψ := by
    dsimp only
    simp only [HomologicalComplex.p_descOpcycles]
    exact pointZeroLift_pointZeroRestrict hA hres ψ

variable {s} in
/-- The component at `y` of the map `G ⟶ p^*H` attached to `φ : H_0(G(A_{•,-})) ⟶ H` is
restriction along the chosen map `A_{0,p(y)} ⟶ y` followed by `φ` at `p(y)`. -/
lemma pointZeroHomEquiv_apply_app {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (φ : (pointZero s A).obj G ⟶ H) (y : s.Cᵒᵖ) :
    (pointZeroHomEquiv hA hres G H φ).app y = G.map (pointSectionHom s hA hres y.unop).op ≫
      (((pointMooreComplex s A).obj G).pOpcycles 0 ≫
        (show ((pointMooreComplex s A).obj G).opcycles 0 ⟶ H from φ)).app
          (op (s.p.obj y.unop)) := rfl

variable {s} in
/-- The map `H_0(G(A_{•,-})) ⟶ H` attached to `ψ : G ⟶ p^*H`, composed with the projection
from `V ↦ G(A_{0,V})`, is `pointZeroRestrict ψ`. -/
lemma pOpcycles_pointZeroHomEquiv_symm {G : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    {H : s.base.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC vC}}
    (ψ : G ⟶ ((Functor.whiskeringLeft _ _ AddCommGrpCat.{max w uD vD uC vC}).obj s.p.op).obj H) :
    ((pointMooreComplex s A).obj G).pOpcycles 0 ≫
        (show ((pointMooreComplex s A).obj G).opcycles 0 ⟶ H from
          (pointZeroHomEquiv hA hres G H).symm ψ) =
      pointZeroRestrict hA ψ :=
  HomologicalComplex.p_descOpcycles _ _ 1 (by simp) (d_one_zero_comp_pointZeroRestrict s hA ψ)

/-- **The degree-zero functor `G ↦ (V ↦ H_0(G(A_{•,V})))` is left adjoint to restriction along the
projection.** This is the degree-zero part of Stacks 08Q9, fibre by fibre. -/
def pointZeroAdjunction :
    pointZero s A ⊣ (Functor.whiskeringLeft _ _ AddCommGrpCat.{max w uD vD uC vC}).obj s.p.op :=
  Adjunction.mkOfHomEquiv
    { homEquiv G H := pointZeroHomEquiv hA hres G H
      homEquiv_naturality_left_symm := by
        intro G' G H α ψ
        refine (cancel_epi (((pointMooreComplex s A).obj G').pOpcycles 0)).1 ?_
        have h3 : ((pointMooreComplex s A).obj G').pOpcycles 0 ≫
            (show ((pointMooreComplex s A).obj G').opcycles 0 ⟶
                ((pointMooreComplex s A).obj G).opcycles 0 from (pointZero s A).map α) =
              ((pointMooreComplex s A).map α).f 0 ≫
                ((pointMooreComplex s A).obj G).pOpcycles 0 :=
          HomologicalComplex.p_opcyclesMap _ 0
        have h4 : pointZeroRestrict hA (α ≫ ψ) =
            ((pointMooreComplex s A).map α).f 0 ≫ pointZeroRestrict hA ψ := by
          ext V : 2
          simp only [pointZeroRestrict, NatTrans.comp_app, Category.assoc]
          rfl
        refine (pOpcycles_pointZeroHomEquiv_symm hA hres (α ≫ ψ)).trans (h4.trans ?_)
        rw [← pOpcycles_pointZeroHomEquiv_symm hA hres ψ, ← Category.assoc, ← h3,
          Category.assoc]
      homEquiv_naturality_right := by
        intro G H H' φ g
        ext y : 2
        rw [pointZeroHomEquiv_apply_app]
        change _ = (pointZeroHomEquiv hA hres G H φ).app y ≫ g.app _
        rw [pointZeroHomEquiv_apply_app]
        simp only [NatTrans.comp_app, Category.assoc]
        rfl }

end Stacks.Sites.FibredCategory.FibredCategorySituation
