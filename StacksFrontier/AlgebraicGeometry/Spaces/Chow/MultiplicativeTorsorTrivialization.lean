module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleLocalTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCartesianAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecUniversalMap

/-!
# The trivialization `q^*ℒ ≅ 𝒪_T` of the pullback of `ℒ` to its multiplicative torsor

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor (`AlgebraicGeometry.Space.torsorOfInvertible`).  This
file constructs the isomorphism `α : q^*ℒ ≅ 𝒪_T` of clause (2) of Stacks 0EQG.

## Main definitions

* `AlgebraicGeometry.Space.torsorTautologicalFMap`: the tautological linear map of sections
  `Γ(V, ℒ^{⊗ 1}) ⟶ Γ(U, 𝒪_T)` over the commuting squares of étale charts `U ⟶ V` over `q`.
* `AlgebraicGeometry.Space.torsorTautologicalHom`: the tautological morphism
  `γ : q^*ℒ^{⊗ 1} ⟶ 𝒪_T`.
* `AlgebraicGeometry.Space.torsorOfInvertibleTrivialization`: the trivialization
  `α : q^*ℒ ≅ 𝒪_T`.

## Main results

* `AlgebraicGeometry.Space.isIso_torsorTautologicalHom`: `γ` is an isomorphism.
* `AlgebraicGeometry.Space.torsorOfInvertible_clause_two`: there is an isomorphism
  `q^*ℒ ≅ 𝒪_T`.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-- The degree-one piece `ℒ^{⊗ 1}` of the Laurent algebra, as an `𝒪_X`-module. -/
abbrev laurentPieceOne : Modules.{u, u} D.site D.base D.base_mem X hp.1 :=
  (laurentGradedAlgebra D p hp L hL).piece 1

/-- The inclusion `Γ(V, ℒ^{⊗ 1}) ⟶ 𝒜(V)` of the degree-one piece into the sections of the Laurent
algebra sheaf. -/
def laurentPieceOneIncl (V : SmallEtale D.site D.base D.base_mem X) :
    (laurentPieceOne D p hp L hL).val.obj (op V) →+
      (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V) :=
  (((laurentCommUnit D p hp L hL).app (op V)).hom.toAddMonoidHom).comp
    (DirectSum.of (fun n : ℤ => ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V)) 1)

/-- The point of `T` with values in the scheme of an étale chart `U` of `T`: the chart itself. -/
def torsorChartPoint (U : SmallEtale D.site D.base D.base_mem
    (torsorOfInvertibleSpace D p hp L hL).obj) :
    RelativeSpecPoint D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL)
      U.obj.left :=
  relativeSpecPointsEquiv D.site D.base D.base_mem _ U.obj.left (yonedaEquiv U.obj.hom)

/-- The underlying point of `X` of the chart point of the chart `d.U` is the composite of `d.g`
with the structure morphism of `d.V`. -/
theorem torsorChartPoint_pt (d : ChartDiagram D.site D.base D.base_mem
    (torsorOfInvertibleSpace D p hp L hL).obj X (torsorOfInvertibleProjection D p hp L hL).hom) :
    yonedaEquiv.symm (torsorChartPoint D p hp L hL d.U).pt = yoneda.map d.g ≫ d.V.obj.hom := by
  rw [← d.comm]
  exact (congrArg yonedaEquiv.symm (yonedaEquiv_comp d.U.obj.hom
    (torsorOfInvertibleProjection D p hp L hL).hom).symm).trans (Equiv.symm_apply_apply _ _)

/-- The chart point is compatible with morphisms of charts. -/
theorem torsorChartPoint_map {U U' : SmallEtale D.site D.base D.base_mem
    (torsorOfInvertibleSpace D p hp L hL).obj} (i : U' ⟶ U) :
    torsorChartPoint D p hp L hL U' =
      (torsorChartPoint D p hp L hL U).map D.site D.base D.base_mem
        ((SmallEtale.toOver D.site D.base D.base_mem _).map i) := by
  let P := relativeSpecPoints D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
    (laurentAlgebraSheaf D p hp L hL)
  have h1 : yonedaEquiv (U'.obj.hom : yoneda.obj U'.obj.left ⟶ P) =
      P.map ((SmallEtale.toOver D.site D.base D.base_mem _).map i).op
        (yonedaEquiv (U.obj.hom : yoneda.obj U.obj.left ⟶ P)) :=
    (congrArg yonedaEquiv ((SmallEtale.inclusion D.site D.base D.base_mem _).map i).w).symm.trans
      (yonedaEquiv_naturality _ _).symm
  exact (congrArg (relativeSpecPointsEquiv D.site D.base D.base_mem _ U'.obj.left) h1).trans
    (relativeSpecPointsEquiv_map D.site D.base D.base_mem _ _ _)

/-- The inclusion of the degree-one piece is compatible with restriction. -/
theorem laurentPieceOneIncl_map {V V' : SmallEtale D.site D.base D.base_mem X} (j : V' ⟶ V)
    (s : (laurentPieceOne D p hp L hL).val.obj (op V)) :
    laurentPieceOneIncl D p hp L hL V' ((laurentPieceOne D p hp L hL).val.map j.op s) =
      (laurentAlgebraSheaf D p hp L hL).right.obj.map j.op
        (laurentPieceOneIncl D p hp L hL V s) := by
  have h := ConcreteCategory.congr_hom ((laurentCommUnit D p hp L hL).naturality j.op)
    (DirectSum.of (fun n : ℤ => ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V)) 1 s)
  refine Eq.trans ?_ h
  change ((laurentCommUnit D p hp L hL).app (op V')).hom
      ((laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl 1
        ((laurentPieceOne D p hp L hL).val.map j.op s)) =
    ((laurentCommUnit D p hp L hL).app (op V')).hom
      ((laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.totalRestrict j.op
        ((laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl 1 s))
  exact congrArg _ (Stacks.GradedAlgebra.totalRestrict_incl _ _ _ _).symm

/-- The inclusion of the degree-one piece is semilinear over the structure map of the Laurent
algebra sheaf. -/
theorem laurentPieceOneIncl_smul (V : SmallEtale D.site D.base D.base_mem X)
    (r : chartRing D.site D.base D.base_mem X hp.1 V)
    (s : (laurentPieceOne D p hp L hL).val.obj (op V)) :
    laurentPieceOneIncl D p hp L hL V (r • s) =
      (laurentAlgebraSheaf D p hp L hL).algebraMap (op V) r *
        laurentPieceOneIncl D p hp L hL V s := by
  change ((laurentCommUnit D p hp L hL).app (op V)).hom
      ((laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl 1 (r • s)) =
    ((laurentCommUnit D p hp L hL).app (op V)).hom (laurentChartStructureMap D p hp L hL r) *
      ((laurentCommUnit D p hp L hL).app (op V)).hom
        ((laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl 1 s)
  refine Eq.trans ?_ (map_mul _ _ _)
  let r' : (tensorStructureSheaf D p hp).obj.obj (op V) := r
  have e := (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl_smul (X := op V) 1 r' s
  have e2 := (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.smul_mul_eq (X := op V)
    r' 1 ((laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.incl 1 s)
  rw [one_mul] at e2
  exact congrArg _ (e.trans e2.symm)

/-- **The tautological linear map of sections along `q`**: over a commuting square of étale
charts `U ⟶ V` over `q`, a section of `ℒ^{⊗ 1}` over `V` goes to the value on `U` of its image in
the Laurent algebra under the point of `T` that `U` is. -/
def torsorTautologicalFMap :
    ModuleFMap D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL)
      (SheafOfModules.unit _) (laurentPieceOne D p hp L hL) where
  app d s := (torsorChartPoint D p hp L hL d.U).chartEval D.site D.base D.base_mem d.V d.g
    (torsorChartPoint_pt D p hp L hL d) (laurentPieceOneIncl D p hp L hL d.V s)
  naturality d d' i j h s := by
    rw [laurentPieceOneIncl_map]
    have hj : yoneda.map ((SmallEtale.toOver D.site D.base D.base_mem X).map j) ≫ d.V.obj.hom =
        d'.V.obj.hom :=
      ((SmallEtale.inclusion D.site D.base D.base_mem X).map j).w
    have h2 : yonedaEquiv.symm (torsorChartPoint D p hp L hL d'.U).pt =
        yoneda.map (d'.g ≫ (SmallEtale.toOver D.site D.base D.base_mem X).map j) ≫
          d.V.obj.hom := by
      rw [torsorChartPoint_pt, Functor.map_comp, Category.assoc, hj]
    have e1 := RelativeSpecPoint.map_comp_chartEval D.site D.base D.base_mem j d'.g
      (torsorChartPoint D p hp L hL d'.U) (torsorChartPoint_pt D p hp L hL d') h2
    refine (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
      (laurentPieceOneIncl D p hp L hL d.V s)) e1).trans ?_
    have hi := torsorChartPoint_map D p hp L hL i
    have h3 : yonedaEquiv.symm ((torsorChartPoint D p hp L hL d.U).map D.site D.base D.base_mem
        ((SmallEtale.toOver D.site D.base D.base_mem _).map i)).pt =
        yoneda.map ((SmallEtale.toOver D.site D.base D.base_mem _).map i ≫ d.g) ≫ d.V.obj.hom := by
      rw [← hi, h, h2]
    have e3 := RelativeSpecPoint.chartEval_congr D.site D.base D.base_mem d.V h.symm hi h2 h3
    have e4 := RelativeSpecPoint.chartEval_map D.site D.base D.base_mem d.V
      ((SmallEtale.toOver D.site D.base D.base_mem _).map i) d.g (torsorChartPoint D p hp L hL d.U)
      (torsorChartPoint_pt D p hp L hL d) h3
    refine Eq.trans (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
      (laurentPieceOneIncl D p hp L hL d.V s)) e3) ?_
    refine Eq.trans (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
      (laurentPieceOneIncl D p hp L hL d.V s)) e4) ?_
    rfl
  map_add d s t := by
    dsimp only
    rw [map_add, map_add]
    rfl
  map_smul d r s := by
    dsimp only
    rw [laurentPieceOneIncl_smul, map_mul]
    exact congrArg (· * _) (RelativeSpecPoint.chartEval_algebraMap D.site D.base D.base_mem d.V
      d.g (torsorChartPoint D p hp L hL d.U) (torsorChartPoint_pt D p hp L hL d) r)

/-! ### The tautological morphism `q^*ℒ^{⊗ 1} ⟶ 𝒪_T` -/

/-- **The tautological morphism `γ : q^*ℒ^{⊗ 1} ⟶ 𝒪_T`**: the transpose of the tautological
linear map of sections along `q` under the adjunction `q^* ⊣ q_*`. -/
def torsorTautologicalHom :
    (modulePullback D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL)).obj
        (laurentPieceOne D p hp L hL) ⟶ SheafOfModules.unit _ :=
  ((modulePullbackAdjunction D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL)).homEquiv _ _).symm
    ((modulePushforwardHomEquiv D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL) _ _).symm
      (torsorTautologicalFMap D p hp L hL))

/-- The value of the tautological morphism on the pullback of a section of `ℒ^{⊗ 1}` over a
chart diagram is the tautological map of sections. -/
theorem torsorTautologicalHom_unitSection
    (d : ChartDiagram D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj X
      (torsorOfInvertibleProjection D p hp L hL).hom)
    (s : (laurentPieceOne D p hp L hL).val.obj (op d.V)) :
    (torsorTautologicalHom D p hp L hL).val.app (op d.U)
        (modulePullbackUnitSection D.site D.base D.base_mem
          (torsorOfInvertibleProjection D p hp L hL) (laurentPieceOne D p hp L hL) d s) =
      (torsorTautologicalFMap D p hp L hL).app d s := by
  rw [← modulePullbackHomFMap_app]
  unfold modulePullbackHomFMap torsorTautologicalHom
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### A free generating family over a chart is a trivialization -/

/-- **A compatible family freely generating an `𝒪_X`-module over every chart over `V` is a
trivialization of the module over the slice of `V`.** -/
theorem nonempty_iso_unit_of_freeFamily (M : SheafOfModules.{u} (tensorStructureSheaf D p hp))
    (V : SmallEtale D.site D.base D.base_mem X)
    (e : (W : SmallEtale D.site D.base D.base_mem X) → (W ⟶ V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem X) (k : W ⟶ V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale D.site D.base D.base_mem X) (k : W ⟶ V),
      Function.Bijective fun r : (tensorStructureSheaf D p hp).obj.obj (op W) ↦ r • e W k) :
    Nonempty (M.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V)) := by
  let sec : (M.over V).val.sections := ⟨fun W => e W.unop.left W.unop.hom, fun {W W'} f => by
    refine (hcompat W.unop.left W'.unop.left W.unop.hom f.unop.left).trans ?_
    congr 1
    exact Over.w f.unop⟩
  let φ : SheafOfModules.unit ((tensorStructureSheaf D p hp).over V) ⟶ M.over V :=
    ⟨(M.over V).val.unitHomEquiv.symm sec⟩
  have hφ1 : ∀ W : (CategoryTheory.Over V)ᵒᵖ,
      φ.val.app W (1 : (tensorStructureSheaf D p hp).obj.obj (op W.unop.left)) =
        e W.unop.left W.unop.hom := fun W =>
    (congrArg (fun t : (M.over V).val.sections => t.val W)
      ((M.over V).val.unitHomEquiv.apply_symm_apply sec) :)
  have hφ : ∀ W : (CategoryTheory.Over V)ᵒᵖ, ∀ r : (tensorStructureSheaf D p hp).obj.obj
      (op W.unop.left), φ.val.app W r = r • e W.unop.left W.unop.hom := by
    intro W r
    rw [← hφ1 W]
    refine Eq.trans ?_ ((φ.val.app W).hom.map_smul r
      (1 : (tensorStructureSheaf D p hp).obj.obj (op W.unop.left)))
    congr 1
    exact (mul_one r).symm
  have : IsIso φ := Stacks.SheafOfModules.isIso_of_bijective_val_app φ fun W => by
    rw [funext (hφ W)]
    exact hbij W.unop.left W.unop.hom
  exact ⟨(asIso φ).symm⟩

/-! ### The tautological morphism over a chart trivializing `ℒ` -/

section Trivial

variable (d : ChartDiagram D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj X
      (torsorOfInvertibleProjection D p hp L hL).hom)
    (eL : L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V))
    (hV : (SmallEtale.topology D.site D.base D.base_mem X).IsQuasiCompactObject d.V)

/-- The generating family of `ℒ^{⊗ 1}` over the charts over `d.V` given by a trivialization of
`ℒ` over `d.V`. -/
def laurentPieceOneFamily (W : SmallEtale D.site D.base D.base_mem X) (k : W ⟶ d.V) :
    (laurentPieceOne D p hp L hL).val.obj (op W) :=
  (laurentPieceOne D p hp L hL).val.map k.op (laurentChartGenerator D p hp L hL eL 1)

/-- The generating family `laurentPieceOneFamily` is compatible with restriction. -/
theorem laurentPieceOneFamily_compat (W W' : SmallEtale D.site D.base D.base_mem X)
    (k : W ⟶ d.V) (g : W' ⟶ W) :
    ((laurentPieceOne D p hp L hL).val.map g.op).hom (laurentPieceOneFamily D p hp L hL d eL W k) =
      laurentPieceOneFamily D p hp L hL d eL W' (g ≫ k) := by
  unfold laurentPieceOneFamily
  rw [op_comp]
  exact (PresheafOfModules.map_comp_apply _ _ _ _).symm

/-- Over every chart `W` over `d.V`, the member of `laurentPieceOneFamily` at `W` freely
generates the sections of `ℒ^{⊗ 1}` over `W`. -/
theorem bijective_smul_laurentPieceOneFamily (W : SmallEtale D.site D.base D.base_mem X)
    (k : W ⟶ d.V) :
    Function.Bijective fun r : chartRing D.site D.base D.base_mem X hp.1 W ↦
      r • laurentPieceOneFamily D p hp L hL d eL W k := by
  have hinv := Stacks.SheafOfModules.iso_inv_app_eq_smul (tensorStructureRingPresheaf D p hp)
    (isSheaf_tensorStructureRingPresheaf D p hp) ((laurentGradedAlgebra D p hp L hL).piece 1)
    (laurentPieceTrivialization D p hp L hL eL 1) k
  have hb : Function.Bijective
      ((laurentPieceTrivialization D p hp L hL eL 1).inv.val.app (op (Over.mk k))) := by
    set ε := laurentPieceTrivialization D p hp L hL eL 1
    refine Function.bijective_iff_has_inverse.2 ⟨ε.hom.val.app (op (Over.mk k)), fun x => ?_,
      fun y => ?_⟩
    · change ((ε.inv ≫ ε.hom).val.app (op (Over.mk k))) x = x
      rw [ε.inv_hom_id]
      rfl
    · change ((ε.hom ≫ ε.inv).val.app (op (Over.mk k))) y = y
      rw [ε.hom_inv_id]
      rfl
  rw [funext hinv] at hb
  exact hb

/-- **Over a quasi-compact chart trivializing `ℒ` the tautological map sends the generator to a
unit.** -/
theorem isUnit_torsorTautologicalFMap_app :
    IsUnit (show chartRing D.site D.base D.base_mem _ (torsorOfInvertibleSpace D p hp L hL).property
        d.U from (torsorTautologicalFMap D p hp L hL).app d
      (laurentPieceOneFamily D p hp L hL d eL d.V (𝟙 d.V))) := by
  have h1 : laurentPieceOneFamily D p hp L hL d eL d.V (𝟙 d.V) =
      laurentChartGenerator D p hp L hL eL 1 := by
    unfold laurentPieceOneFamily
    rw [op_id]
    exact PresheafOfModules.map_id_apply _ _ _
  change IsUnit ((ConcreteCategory.hom ((torsorChartPoint D p hp L hL d.U).chartEval D.site D.base
    D.base_mem d.V d.g (torsorChartPoint_pt D p hp L hL d))) (laurentPieceOneIncl D p hp L hL d.V
    (laurentPieceOneFamily D p hp L hL d eL d.V (𝟙 d.V))))
  rw [h1]
  exact ((laurentChartUnit D p hp L hL eL).isUnit.map
    ((laurentCommUnit D p hp L hL).app (op d.V)).hom).map _

include eL in
/-- **Over every chart above `d.U`, the tautological morphism is bijective**, `ℒ` being trivial
over `d.V`. -/
theorem bijective_torsorTautologicalHom_app (W : SmallEtale D.site D.base D.base_mem
    (torsorOfInvertibleSpace D p hp L hL).obj) (k : W ⟶ d.U) :
    Function.Bijective ((torsorTautologicalHom D p hp L hL).val.app (op W)) := by
  have hinv : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have hM := (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L
    1).toAlgebraicGeometry
  set G := modulePullbackChartGenerator D.site D.base D.base_mem
    (torsorOfInvertibleProjection D p hp L hL) (laurentPieceOne D p hp L hL) d
    (laurentPieceOneFamily D p hp L hL d eL) W k with hG
  have hGbij := bijective_smul_modulePullbackChartGenerator D.site D.base D.base_mem
    (torsorOfInvertibleProjection D p hp L hL) (laurentPieceOne D p hp L hL) hM d
    (laurentPieceOneFamily D p hp L hL d eL) (laurentPieceOneFamily_compat D p hp L hL d eL)
    (bijective_smul_laurentPieceOneFamily D p hp L hL d eL) W k
  set γ := torsorTautologicalHom D p hp L hL
  set s₀ := modulePullbackUnitSection D.site D.base D.base_mem
    (torsorOfInvertibleProjection D p hp L hL) (laurentPieceOne D p hp L hL) d
    (laurentPieceOneFamily D p hp L hL d eL d.V (𝟙 d.V)) with hs₀
  have hG' : G = ((modulePullback D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL)).obj (laurentPieceOne D p hp L hL)).val.map k.op
        s₀ := by
    rw [hG, hs₀, ← modulePullbackChartFMap_app_eq_unitSection, ← modulePullbackChartGenerator_id,
      modulePullbackChartGenerator_compat, Category.comp_id]
  set u : chartRing D.site D.base D.base_mem _ (torsorOfInvertibleSpace D p hp L hL).property W :=
    γ.val.app (op W) G with hu
  have hunit : IsUnit u := by
    have : u = (SheafOfModules.unit _ : SheafOfModules _).val.map k.op
        (γ.val.app (op d.U) s₀) := by
      rw [hu, hG']
      exact ConcreteCategory.congr_hom (γ.val.naturality k.op) s₀
    rw [this, hs₀, torsorTautologicalHom_unitSection]
    exact (isUnit_torsorTautologicalFMap_app D p hp L hL d eL).map
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site D.base D.base_mem _
        (torsorOfInvertibleSpace D p hp L hL).property).O).obj.map k.op).hom
  have hlin : ∀ r : chartRing D.site D.base D.base_mem _
      (torsorOfInvertibleSpace D p hp L hL).property W,
      γ.val.app (op W) (r • G) = r * u := fun r => (γ.val.app (op W)).hom.map_smul r G
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · obtain ⟨a', rfl⟩ := hGbij.2 a
    obtain ⟨b', rfl⟩ := hGbij.2 b
    rw [hunit.mul_left_inj.1 ((hlin a').symm.trans (hab.trans (hlin b')))]
  · refine ⟨((show chartRing D.site D.base D.base_mem _
      (torsorOfInvertibleSpace D p hp L hL).property W from y) * ↑hunit.unit⁻¹) • G, ?_⟩
    rw [hlin, mul_assoc, IsUnit.val_inv_mul, mul_one]

end Trivial

/-! ### The tautological morphism is an isomorphism -/

include hL in
/-- Through every point of an étale chart of `T` there is a chart over it lying over a commuting
square of charts over `q` whose chart of `X` is affine and trivializes `ℒ`. -/
theorem exists_trivial_chartDiagram_at_point (U : SmallEtale D.site D.base D.base_mem
    (torsorOfInvertibleSpace D p hp L hL).obj) (z : chartScheme U) :
    ∃ (d : ChartDiagram D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj X
        (torsorOfInvertibleProjection D p hp L hL).hom) (f : d.U ⟶ U),
      Nonempty (L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V)) ∧
        z ∈ Set.range ((BigFppfOver.toScheme D.site D.base D.base_mem).map
          ((SmallEtale.toOver D.site D.base D.base_mem _).map f)) := by
  obtain ⟨d₀, k₀, z₀, -, hV₀, hz₀⟩ := exists_affine_chartDiagram_at_chartPoint D.site D.base
    D.base_mem (torsorOfInvertibleProjection D p hp L hL) U z
  have hL' : IsInvertibleModule (B := D.site) ⟨X, hp.1⟩ L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  obtain ⟨g, hvg, e, hcompat, hbij⟩ := exists_basicOpen_freeGenerator D.site D.base D.base_mem
    ⟨X, hp.1⟩ L hL' d₀.V hV₀ ((BigFppfOver.toScheme D.site D.base D.base_mem).map d₀.g z₀)
  let O := (BigFppfOver.toScheme D.site D.base D.base_mem).map d₀.g ⁻¹ᵁ
    (chartScheme d₀.V).basicOpen g
  refine ⟨d₀.restrictOpens O ((chartScheme d₀.V).basicOpen g) le_rfl,
    openChartInclusion D.site D.base D.base_mem _ d₀.U O ≫ k₀,
    nonempty_iso_unit_of_freeFamily D p hp L _ e hcompat hbij, ⟨⟨z₀, hvg⟩, ?_⟩⟩
  change ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      ((SmallEtale.toOver D.site D.base D.base_mem _).map (openChartInclusion D.site D.base
        D.base_mem _ d₀.U O)) ≫ (BigFppfOver.toScheme D.site D.base D.base_mem).map
      ((SmallEtale.toOver D.site D.base D.base_mem _).map k₀)) ⟨z₀, hvg⟩ = z
  rw [toScheme_map_toOver_map_openChartInclusion, ← hz₀]
  rfl

include hL in
/-- **The tautological morphism `γ : q^*ℒ^{⊗ 1} ⟶ 𝒪_T` is an isomorphism.** -/
theorem isIso_torsorTautologicalHom : IsIso (torsorTautologicalHom D p hp L hL) := by
  refine Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app
    (torsorTautologicalHom D p hp L hL)
    (P := fun W => Function.Bijective ((torsorTautologicalHom D p hp L hL).val.app (op W)))
    (fun U => ?_) (fun _ h => h)
  choose d f he hz using exists_trivial_chartDiagram_at_point D p hp L hL U
  refine ⟨chartScheme U, fun z => (d z).U, f, ?_, fun z =>
    bijective_torsorTautologicalHom_app D p hp L hL (d z) (he z).some (d z).U (𝟙 _)⟩
  exact (SmallEtale.mem_topology_iff_exists_mem_range D.site D.base D.base_mem _ _).2 fun z =>
    ⟨(d z).U, f z, Sieve.ofArrows_mk _ _ z, hz z⟩

/-- **The trivialization `α : q^*ℒ ≅ 𝒪_T`**: the identification `ℒ ≅ ℒ^{⊗ 1}` pulled back along
`q`, followed by the tautological isomorphism `q^*ℒ^{⊗ 1} ≅ 𝒪_T`. -/
def torsorOfInvertibleTrivialization :
    (modulePullback D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL)).obj L ≅
      SheafOfModules.unit _ :=
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L
  (modulePullback D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL)).mapIso
      (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso (tensorStructureRingPresheaf D p hp)
        (isSheaf_tensorStructureRingPresheaf D p hp) L).symm ≪≫
    @asIso _ _ _ _ (torsorTautologicalHom D p hp L hL) (isIso_torsorTautologicalHom D p hp L hL)

/-- There is an isomorphism `α : q^*ℒ ≅ 𝒪_T`. -/
@[stacks 0EQG "clause (2): there is an isomorphism alpha : q^*L ≅ O_T"]
theorem torsorOfInvertible_clause_two :
    Nonempty ((modulePullback D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL)).obj L ≅ SheafOfModules.unit _) :=
  ⟨torsorOfInvertibleTrivialization D p hp L hL⟩

end AlgebraicGeometry.Space

end
