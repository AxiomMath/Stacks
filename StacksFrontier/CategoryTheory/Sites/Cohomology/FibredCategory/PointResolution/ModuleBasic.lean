module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic

/-!
# Fibrewise point resolutions at module coefficients

In the situation of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Basic`, let `O` be a
presheaf of rings on the base and give the total category the presheaf of rings `O ∘ p`, the
inverse image `p⁻¹O`. Since every term `A_{n,V}` lies over `V`, the ring `(p⁻¹O)(A_{n,V})` is
`O(p(A_{n,V})) = O(V)`, so for a presheaf of `p⁻¹O`-modules `G` the presheaf `V ↦ G(A_{n,V})` is a
presheaf of `O`-modules, and the cosimplicial structure maps of `A_{•,V}`, which lie over the
identity of `V`, make `V ↦ G(A_{•,V})` a simplicial presheaf of `O`-modules. This file forms it,
its Moore complex and its degree-zero homology `V ↦ H_0(G(A_{•,V}))`, and proves that the latter
functor is left adjoint to restriction along `p`, the degree-zero case of Stacks 08Q9 at module
coefficients, fibre by fibre.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointLevel`: `G ↦ (V ↦ G(A_{n,V}))`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointEvaluation`: the simplicial
  presheaf of `O`-modules `V ↦ G(A_{•,V})`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointMooreComplex`: its Moore
  complex.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointZero`:
  `G ↦ (V ↦ H_0(G(A_{•,V})))`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.moduleRestriction`: restriction of
  presheaves of modules along `p`.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointMooreComplexForgetIso`: the
  underlying complex of abelian presheaves is `pointMooreComplex` of the underlying abelian
  presheaf.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.modulePointZeroAdjunction`:
  `modulePointZero` is left adjoint to `moduleRestriction`.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe uD vD uC vC w

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})
  {A : s.base.C ⥤ CosimplicialObject s.C}
  (hA : A ⋙ (Functor.whiskeringRight SimplexCategory s.C s.base.C).obj s.p =
    Functor.const SimplexCategory)
  (O : s.base.Cᵒᵖ ⥤ RingCat.{max w uD vD uC vC})

variable (A) in
/-- The functor `V ↦ A_{n,V}`. -/
abbrev pointLevel (n : SimplexCategory) : s.base.C ⥤ s.C :=
  A ⋙ (evaluation SimplexCategory s.C).obj n

/-- The identification `O(V) ⟶ O(p(A_{n,V}))` of the ring of `V` with the ring of the inverse
image `p⁻¹O` at `A_{n,V}`, which lies over `V`. -/
def pointRingMap (n : SimplexCategory) : O ⟶ (pointLevel s A n).op ⋙ s.p.op ⋙ O where
  app V := O.map (eqToHom (obj_obj_proj s hA V.unop n)).op
  naturality {V W} g := by
    have := isHomLift_map_app s hA g.unop n
    have hp := IsHomLift.fac' s.p g.unop ((A.map g.unop).app n)
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ← O.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    simp [hp]

/-- The identifications `O(V) ≅ O(p(A_{n,V}))` are compatible with the cosimplicial structure
maps of `A_{•,V}`, which lie over the identity of `V`. -/
lemma pointRingMap_comp_map {m n : SimplexCategory} (θ : m ⟶ n) (V : s.base.Cᵒᵖ) :
    (pointRingMap s hA O n).app V ≫ (s.p.op ⋙ O).map ((A.obj V.unop).map θ).op =
      (pointRingMap s hA O m).app V := by
  have := isHomLift_obj_map s hA V.unop θ
  have hp := IsHomLift.fac' s.p (𝟙 V.unop) ((A.obj V.unop).map θ)
  simp only [pointRingMap, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ← O.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp [hp]

/-- The presheaf of `O`-modules `V ↦ G(A_{n,V})` attached to a presheaf of `p⁻¹O`-modules. -/
abbrev modulePointLevel (n : SimplexCategory) :
    PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) ⥤
      PresheafOfModules.{max w uD vD uC vC} O :=
  PresheafOfModules.pushforward (pointRingMap s hA O n)

/-- The structure map `G(A_{n,V}) ⟶ G(A_{m,V})` of the simplicial presheaf of `O`-modules
`V ↦ G(A_{•,V})`, for `θ : [m] ⟶ [n]`. -/
def modulePointLevelMap (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O))
    {m n : SimplexCategory} (θ : m ⟶ n) :
    (modulePointLevel s hA O n).obj G ⟶ (modulePointLevel s hA O m).obj G :=
  PresheafOfModules.homMk (((pointEvaluation s A).obj G.presheaf).map θ.op) (by
    intro V r x
    exact (G.map_smul ((A.obj V.unop).map θ).op ((pointRingMap s hA O n).app V r) x).trans
      (congrArg (· • G.map ((A.obj V.unop).map θ).op x)
        (ConcreteCategory.congr_hom (pointRingMap_comp_map s hA O θ V) r)))

/-- The underlying map of abelian presheaves of a structure map of `V ↦ G(A_{•,V})` is the one of
the abelian simplicial presheaf. -/
lemma toPresheaf_map_modulePointLevelMap (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O))
    {m n : SimplexCategory} (θ : m ⟶ n) :
    (PresheafOfModules.toPresheaf O).map (modulePointLevelMap s hA O G θ) =
      ((pointEvaluation s A).obj G.presheaf).map θ.op := rfl

/-- The simplicial presheaf of `O`-modules `V ↦ G(A_{•,V})`. -/
def modulePointEvaluationObj (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) :
    SimplicialObject (PresheafOfModules.{max w uD vD uC vC} O) where
  obj n := (modulePointLevel s hA O n.unop).obj G
  map θ := modulePointLevelMap s hA O G θ.unop
  map_id n := (PresheafOfModules.toPresheaf O).map_injective
    (((pointEvaluation s A).obj G.presheaf).map_id n)
  map_comp θ θ' := (PresheafOfModules.toPresheaf O).map_injective
    (((pointEvaluation s A).obj G.presheaf).map_comp θ θ')

/-- **The simplicial presheaf of `O`-modules `V ↦ G(A_{•,V})`**, functorially in the presheaf of
`p⁻¹O`-modules `G`. -/
def modulePointEvaluation :
    PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) ⥤
      SimplicialObject (PresheafOfModules.{max w uD vD uC vC} O) where
  obj G := modulePointEvaluationObj s hA O G
  map η :=
    { app n := (modulePointLevel s hA O n.unop).map η
      naturality _ _ θ := (PresheafOfModules.toPresheaf O).map_injective
        (((pointEvaluation s A).map ((PresheafOfModules.toPresheaf _).map η)).naturality θ) }
  map_id G := NatTrans.ext (funext fun n => (modulePointLevel s hA O n.unop).map_id G)
  map_comp η η' := NatTrans.ext (funext fun n => (modulePointLevel s hA O n.unop).map_comp η η')

/-- Forgetting the module structure of `V ↦ G(A_{•,V})` gives the simplicial presheaf of
abelian groups of the underlying abelian presheaf of `G`. -/
def modulePointEvaluationForgetIso :
    modulePointEvaluation s hA O ⋙
        (SimplicialObject.whiskering _ _).obj (PresheafOfModules.toPresheaf O) ≅
      PresheafOfModules.toPresheaf (s.p.op ⋙ O) ⋙ pointEvaluation s A :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
    (fun _ => rfl)

/-- `G ↦ (V ↦ G(A_{n,V}))` is additive. -/
instance modulePointLevel_additive (n : SimplexCategory) :
    (modulePointLevel s hA O n).Additive where
  map_add := rfl

/-- `G ↦ (V ↦ G(A_{•,V}))` is additive. -/
instance modulePointEvaluation_additive : (modulePointEvaluation s hA O).Additive where
  map_add := NatTrans.ext (funext fun n => (modulePointLevel s hA O n.unop).map_add)

/-- **The complex of presheaves of `O`-modules `V ↦ G(A_{•,V})`**: the Moore complex of
`modulePointEvaluation`. -/
abbrev modulePointMooreComplex :
    PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) ⥤
      ChainComplex (PresheafOfModules.{max w uD vD uC vC} O) ℕ :=
  modulePointEvaluation s hA O ⋙ alternatingFaceMapComplex _

/-- **Forgetting the module structure of the complex `V ↦ G(A_{•,V})`** gives the complex of
abelian presheaves `V ↦ G(A_{•,V})` of the underlying abelian presheaf of `G`. -/
def modulePointMooreComplexForgetIso :
    modulePointMooreComplex s hA O ⋙
        (PresheafOfModules.toPresheaf O).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      PresheafOfModules.toPresheaf (s.p.op ⋙ O) ⋙ pointMooreComplex s A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (modulePointEvaluation s hA O)
      (eqToIso (map_alternatingFaceMapComplex (PresheafOfModules.toPresheaf O))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (modulePointEvaluationForgetIso s hA O) _ ≪≫
    Functor.associator _ _ _

/-- The underlying map of abelian presheaves of a differential of `V ↦ G(A_{•,V})` is the
differential of the abelian complex. -/
lemma toPresheaf_map_modulePointMooreComplex_d
    (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)) (n : ℕ) :
    (PresheafOfModules.toPresheaf O).map (((modulePointMooreComplex s hA O).obj G).d (n + 1) n) =
      ((pointMooreComplex s A).obj G.presheaf).d (n + 1) n := by
  simp only [Functor.comp_obj, alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Functor.map_sum, Functor.map_zsmul]
  rfl

/-- The presheaf of `O`-modules `V ↦ H_0(G(A_{•,V}))`, the cokernel of the two cofaces
`G(A_{1,V}) ⇉ G(A_{0,V})`. -/
abbrev modulePointZero :
    PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) ⥤
      PresheafOfModules.{max w uD vD uC vC} O where
  obj G := ((modulePointMooreComplex s hA O).obj G).opcycles 0
  map η := HomologicalComplex.opcyclesMap ((modulePointMooreComplex s hA O).map η) 0
  map_id G := by
    rw [CategoryTheory.Functor.map_id]
    exact HomologicalComplex.opcyclesMap_id _ 0
  map_comp η η' := by
    rw [CategoryTheory.Functor.map_comp]
    exact HomologicalComplex.opcyclesMap_comp _ _ 0

/-- `G ↦ (V ↦ H_0(G(A_{•,V})))` is additive. -/
instance modulePointZero_additive : (modulePointZero s hA O).Additive where
  map_add {G G' f g} := by
    change HomologicalComplex.opcyclesMap ((modulePointMooreComplex s hA O).map (f + g)) 0 = _
    rw [Functor.map_add]
    refine (cancel_epi (HomologicalComplex.pOpcycles _ 0)).1 ?_
    rw [HomologicalComplex.p_opcyclesMap, Preadditive.comp_add, HomologicalComplex.p_opcyclesMap,
      HomologicalComplex.p_opcyclesMap, HomologicalComplex.add_f_apply, Preadditive.add_comp]

/-- Restriction of presheaves of modules along the projection, `H ↦ p^*H`, from `O`-modules to
`p⁻¹O`-modules. -/
abbrev moduleRestriction :
    PresheafOfModules.{max w uD vD uC vC} O ⥤
      PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O) :=
  PresheafOfModules.pushforward (F := s.p) (𝟙 (s.p.op ⋙ O))

variable (hres : ∀ (V : s.base.C) (W : s.p.Fiber V),
  ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj hA V)).op ⋙ yoneda.obj W ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{vC + 1},
    SimplicialObject.homotopyEquivalences (Type vC) f)

variable {s O}

/-- A map killing the degree-one differential at module coefficients kills it on underlying
abelian presheaves. -/
lemma d_one_zero_comp_toPresheaf_map {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O}
    (φ : ((modulePointMooreComplex s hA O).obj G).X 0 ⟶ H)
    (hφ : ((modulePointMooreComplex s hA O).obj G).d 1 0 ≫ φ = 0) :
    ((pointMooreComplex s A).obj G.presheaf).d 1 0 ≫ (PresheafOfModules.toPresheaf O).map φ =
      0 := by
  have h2 := congrArg (PresheafOfModules.toPresheaf O).map hφ
  rw [Functor.map_comp, Functor.map_zero] at h2
  exact (congrArg (· ≫ (PresheafOfModules.toPresheaf O).map φ)
    (toPresheaf_map_modulePointMooreComplex_d s hA O G 0)).symm.trans h2

/-- The map `G ⟶ p^*H` attached to a map out of `V ↦ G(A_{0,V})` killing the degree-one
differential, at module coefficients: the underlying map of abelian presheaves is
`pointZeroLift`. -/
def modulePointZeroLift {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O}
    (φ : ((modulePointMooreComplex s hA O).obj G).X 0 ⟶ H)
    (hφ : ((modulePointMooreComplex s hA O).obj G).d 1 0 ≫ φ = 0) :
    G ⟶ (moduleRestriction s O).obj H :=
  PresheafOfModules.homMk (M₂ := (moduleRestriction s O).obj H)
    (pointZeroLift (G := G.presheaf) (H := H.presheaf) hA hres
      ((PresheafOfModules.toPresheaf O).map φ)
      (d_one_zero_comp_toPresheaf_map hA φ hφ)) (by
    intro y r m
    have hp := IsHomLift.fac' s.p (𝟙 (s.p.obj y.unop)) (pointSectionHom s hA hres y.unop)
    have hr : (s.p.op ⋙ O).map (pointSectionHom s hA hres y.unop).op r =
        (pointRingMap s hA O ⦋0⦌).app (op (s.p.obj y.unop)) r := by
      simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, pointRingMap, hp,
        Category.id_comp, eqToHom_trans]
    change φ.app (op (s.p.obj y.unop)) (G.map (pointSectionHom s hA hres y.unop).op (r • m)) =
      r • φ.app (op (s.p.obj y.unop)) (G.map (pointSectionHom s hA hres y.unop).op m)
    rw [G.map_smul, hr]
    exact (φ.app (op (s.p.obj y.unop))).hom.map_smul r _)

/-- The underlying map of abelian presheaves of `modulePointZeroLift` is `pointZeroLift`. -/
lemma toPresheaf_map_modulePointZeroLift {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O}
    (φ : ((modulePointMooreComplex s hA O).obj G).X 0 ⟶ H)
    (hφ : ((modulePointMooreComplex s hA O).obj G).d 1 0 ≫ φ = 0) :
    (PresheafOfModules.toPresheaf _).map (modulePointZeroLift hA hres φ hφ) =
      pointZeroLift (G := G.presheaf) (H := H.presheaf) hA hres
        ((PresheafOfModules.toPresheaf O).map φ) (d_one_zero_comp_toPresheaf_map hA φ hφ) :=
  rfl

/-- The map out of `V ↦ G(A_{0,V})` attached to a map `G ⟶ p^*H`, at module coefficients: the
underlying map of abelian presheaves is `pointZeroRestrict`. -/
def modulePointZeroRestrict {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O} (ψ : G ⟶ (moduleRestriction s O).obj H) :
    ((modulePointMooreComplex s hA O).obj G).X 0 ⟶ H :=
  PresheafOfModules.homMk (M₁ := ((modulePointMooreComplex s hA O).obj G).X 0)
    (pointZeroRestrict (G := G.presheaf) (H := H.presheaf) hA
      ((PresheafOfModules.toPresheaf _).map ψ)) (by
    intro V r m
    have hr : O.map (eqToHom (obj_obj_proj s hA V.unop ⦋0⦌).symm).op
        ((pointRingMap s hA O ⦋0⦌).app V r) = r := by
      simp only [pointRingMap, ← ConcreteCategory.comp_apply, ← O.map_comp, ← op_comp,
        eqToHom_trans, eqToHom_refl, op_id, O.map_id, ConcreteCategory.id_apply]
    change H.map (eqToHom (obj_obj_proj s hA V.unop ⦋0⦌).symm).op
        (ψ.app (op ((A.obj V.unop).obj ⦋0⦌))
          ((show (s.p.op ⋙ O).obj (op ((A.obj V.unop).obj ⦋0⦌)) from
              (pointRingMap s hA O ⦋0⦌).app V r) •
            (show G.obj (op ((A.obj V.unop).obj ⦋0⦌)) from m))) =
      r • H.map (eqToHom (obj_obj_proj s hA V.unop ⦋0⦌).symm).op
        (ψ.app (op ((A.obj V.unop).obj ⦋0⦌)) (show G.obj (op ((A.obj V.unop).obj ⦋0⦌)) from m))
    rw [(ψ.app (op ((A.obj V.unop).obj ⦋0⦌))).hom.map_smul]
    refine (H.map_smul _ _ _).trans ?_
    rw [hr])

/-- The underlying map of abelian presheaves of `modulePointZeroRestrict` is
`pointZeroRestrict`. -/
lemma toPresheaf_map_modulePointZeroRestrict
    {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O} (ψ : G ⟶ (moduleRestriction s O).obj H) :
    (PresheafOfModules.toPresheaf O).map (modulePointZeroRestrict hA ψ) =
      pointZeroRestrict (G := G.presheaf) (H := H.presheaf) hA
        ((PresheafOfModules.toPresheaf _).map ψ) :=
  rfl

/-- `modulePointZeroRestrict` kills the degree-one differential. -/
lemma d_one_zero_comp_modulePointZeroRestrict
    {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O} (ψ : G ⟶ (moduleRestriction s O).obj H) :
    ((modulePointMooreComplex s hA O).obj G).d 1 0 ≫ modulePointZeroRestrict hA ψ = 0 := by
  refine (PresheafOfModules.toPresheaf O).map_injective ?_
  rw [Functor.map_comp, Functor.map_zero]
  exact (congrArg (· ≫ (PresheafOfModules.toPresheaf O).map (modulePointZeroRestrict hA ψ))
    (toPresheaf_map_modulePointMooreComplex_d s hA O G 0)).trans
      (d_one_zero_comp_pointZeroRestrict s hA (G := G.presheaf) (H := H.presheaf)
        ((PresheafOfModules.toPresheaf _).map ψ))

/-- `modulePointZeroRestrict` is a left inverse of `modulePointZeroLift`. -/
lemma modulePointZeroRestrict_modulePointZeroLift
    {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O}
    (φ : ((modulePointMooreComplex s hA O).obj G).X 0 ⟶ H)
    (hφ : ((modulePointMooreComplex s hA O).obj G).d 1 0 ≫ φ = 0) :
    modulePointZeroRestrict hA (modulePointZeroLift hA hres φ hφ) = φ :=
  (PresheafOfModules.toPresheaf O).map_injective
    (pointZeroRestrict_pointZeroLift (G := G.presheaf) (H := H.presheaf) hA hres _
      (d_one_zero_comp_toPresheaf_map hA φ hφ))

/-- `modulePointZeroLift` is a left inverse of `modulePointZeroRestrict`. -/
lemma modulePointZeroLift_modulePointZeroRestrict
    {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O} (ψ : G ⟶ (moduleRestriction s O).obj H) :
    modulePointZeroLift hA hres (modulePointZeroRestrict hA ψ)
      (d_one_zero_comp_modulePointZeroRestrict hA ψ) = ψ :=
  (PresheafOfModules.toPresheaf _).map_injective
    (pointZeroLift_pointZeroRestrict (G := G.presheaf) (H := H.presheaf) hA hres
      ((PresheafOfModules.toPresheaf _).map ψ))

variable (O) in
/-- The bijection underlying `modulePointZeroAdjunction`. -/
def modulePointZeroHomEquiv (G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O))
    (H : PresheafOfModules.{max w uD vD uC vC} O) :
    ((modulePointZero s hA O).obj G ⟶ H) ≃ (G ⟶ (moduleRestriction s O).obj H) where
  toFun φ := modulePointZeroLift hA hres (((modulePointMooreComplex s hA O).obj G).pOpcycles 0 ≫ φ)
    (by rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp])
  invFun ψ := ((modulePointMooreComplex s hA O).obj G).descOpcycles (modulePointZeroRestrict hA ψ)
    1 (by simp) (d_one_zero_comp_modulePointZeroRestrict hA ψ)
  left_inv φ := by
    refine (cancel_epi (((modulePointMooreComplex s hA O).obj G).pOpcycles 0)).1 ?_
    rw [HomologicalComplex.p_descOpcycles, modulePointZeroRestrict_modulePointZeroLift]
  right_inv ψ := by
    simpa only [HomologicalComplex.p_descOpcycles] using
      modulePointZeroLift_modulePointZeroRestrict hA hres ψ

/-- The inverse bijection of `modulePointZeroHomEquiv`, read on `V ↦ G(A_{0,V})`, is
`modulePointZeroRestrict`. -/
lemma pOpcycles_modulePointZeroHomEquiv_symm
    {G : PresheafOfModules.{max w uD vD uC vC} (s.p.op ⋙ O)}
    {H : PresheafOfModules.{max w uD vD uC vC} O} (ψ : G ⟶ (moduleRestriction s O).obj H) :
    ((modulePointMooreComplex s hA O).obj G).pOpcycles 0 ≫
        (modulePointZeroHomEquiv hA O hres G H).symm ψ = modulePointZeroRestrict hA ψ :=
  HomologicalComplex.p_descOpcycles _ _ 1 (by simp) (d_one_zero_comp_modulePointZeroRestrict hA ψ)

variable (s O) in
/-- **The degree-zero functor `G ↦ (V ↦ H_0(G(A_{•,V})))` on presheaves of modules is left
adjoint to restriction along the projection.** On underlying abelian presheaves the bijection is
the one of `pointZeroAdjunction`. -/
def modulePointZeroAdjunction : modulePointZero s hA O ⊣ moduleRestriction s O :=
  Adjunction.mkOfHomEquiv
    { homEquiv G H := modulePointZeroHomEquiv hA O hres G H
      homEquiv_naturality_left_symm := by
        intro G' G H α ψ
        refine (cancel_epi (((modulePointMooreComplex s hA O).obj G').pOpcycles 0)).1 ?_
        rw [pOpcycles_modulePointZeroHomEquiv_symm]
        change _ = _ ≫ HomologicalComplex.opcyclesMap ((modulePointMooreComplex s hA O).map α) 0 ≫
          (modulePointZeroHomEquiv hA O hres G H).symm ψ
        rw [HomologicalComplex.p_opcyclesMap_assoc, pOpcycles_modulePointZeroHomEquiv_symm]
        refine (PresheafOfModules.toPresheaf O).map_injective ?_
        ext V x
        rfl
      homEquiv_naturality_right := by
        intro G H H' φ g
        refine (PresheafOfModules.toPresheaf _).map_injective ?_
        ext y x
        rfl }

end Stacks.Sites.FibredCategory.FibredCategorySituation
