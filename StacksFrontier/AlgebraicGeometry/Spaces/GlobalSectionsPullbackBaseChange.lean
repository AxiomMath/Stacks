module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBijectiveOfModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of an inverse image over affine bases

Let `g : Y' ⟶ Y` be a morphism of algebraic spaces and `𝓝` a quasi-coherent `𝒪_Y`-module.  The
unit `𝓝 ⟶ g_*g^*𝓝` of **Stacks 03LU**, read on global sections through **Stacks 0732**, is a
`Γ(Y, 𝒪_Y)`-linear map `Γ(Y, 𝓝) ⟶ Γ(Y', g^*𝓝)`; its extension of scalars is the
`Γ(Y', 𝒪_{Y'})`-linear map

`Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} Γ(Y, 𝓝) ⟶ Γ(Y', g^*𝓝)`,  `b ⊗ s ↦ b · g^*s`.

When `Y` and `Y'` have terminal affine étale charts — that is, when they are affine — this map is
an isomorphism.  This is the statement that over affine bases the global sections of the inverse
image of a quasi-coherent module are the base change of its global sections (compare Descent,
Proposition **03DX**), and it identifies the source side of **Stacks 073K**, part (1), with the
source side of part (2).

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsPullbackMap`: the `Γ(Y, 𝒪_Y)`-linear map
  `Γ(Y, 𝓝) ⟶ Γ(Y', g^*𝓝)`.
* `AlgebraicGeometry.Space.globalSectionsPullbackBaseChange`: its extension of scalars.

## Main results

* `AlgebraicGeometry.Space.isIso_globalSectionsPullbackBaseChange`: **over a chart diagram of
  terminal affine charts, the extension of scalars is an isomorphism.**

## Implementation notes

The two tensor products in play are over different rings: the comparison is stated over the
global function rings, which lie in `Type (u + 1)`, while the chart bijectivity
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite` is
stated over the coordinate rings of the charts.  Evaluation at the terminal charts identifies the
global function rings and global sections with the chart ones, and the additive map
`AlgebraicGeometry.Space.chartTensorToGlobalTensor` carries the chart tensor product onto the
global one.  It is only shown to be *surjective*; together with the chart value formula
`AlgebraicGeometry.Space.modulePullbackGlobalSection_val_chartDiagram`, which says that the
comparison after it and evaluation is the bijective chart comparison, that suffices.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open scoped ChangeOfRings

universe u

namespace CategoryTheory.Functor

/-- **The compatible families of a presheaf of sets are its values at a terminal object.** -/
@[sga "3 I 2.3.3.1" "partial"]
theorem bijective_sections_eval_of_isTerminal {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type*)
    {V : C} (hV : IsTerminal V) :
    Function.Bijective (fun s : F.sections ↦ s.1 (op V)) := by
  have key : ∀ (s : F.sections) (U : Cᵒᵖ), F.map (hV.from U.unop).op (s.1 (op V)) = s.1 U :=
    fun s U ↦ s.2 (hV.from U.unop).op
  refine ⟨fun s t h ↦ Subtype.ext (funext fun U ↦
    (key s U).symm.trans ((congrArg _ h).trans (key t U))), fun x ↦ ?_⟩
  refine ⟨⟨fun U ↦ F.map (hV.from U.unop).op x, fun {U U'} f ↦ ?_⟩, ?_⟩
  · rw [← Functor.map_comp_apply]
    exact congrArg (fun k ↦ F.map k x) (Quiver.Hom.unop_inj (hV.hom_ext _ _))
  · show F.map (hV.from V).op x = x
    rw [show hV.from V = 𝟙 V from hV.hom_ext _ _, op_id, Functor.map_id_apply]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

/-- Evaluation of compatible families of a presheaf of rings at a terminal object, as a ring
equivalence. -/
def sectionsSubringEvalEquiv {C : Type*} [Category* C] (R : Cᵒᵖ ⥤ RingCat.{u}) {V : C}
    (hV : IsTerminal V) : RingCat.sectionsSubring R ≃+* R.obj (op V) :=
  RingEquiv.ofBijective ((Pi.evalRingHom (fun j ↦ ToType (R.obj j)) (op V)).comp
      (RingCat.sectionsSubring R).subtype) <| by
    have h := Functor.bijective_sections_eval_of_isTerminal (R ⋙ forget RingCat.{u}) hV
    refine ⟨fun a b hab ↦ Subtype.ext ?_, fun x ↦ ?_⟩
    · exact congrArg Subtype.val (h.injective (a₁ := ⟨a.1, a.2⟩) (a₂ := ⟨b.1, b.2⟩) hab)
    · obtain ⟨s, hs⟩ := h.surjective x
      exact ⟨⟨s.1, s.2⟩, hs⟩

/-- The evaluation equivalence `sectionsSubringEvalEquiv R hV` sends a compatible family `a` to its
value `a.1 (op V)` at the terminal object `V`. -/
theorem sectionsSubringEvalEquiv_apply {C : Type*} [Category* C] (R : Cᵒᵖ ⥤ RingCat.{u})
    {V : C} (hV : IsTerminal V) (a : RingCat.sectionsSubring R) :
    sectionsSubringEvalEquiv R hV a = a.1 (op V) :=
  rfl

/-- Evaluation of global sections of a sheaf of modules at a terminal object, as an additive
equivalence. -/
def sectionsEvalAddEquiv {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {V : C} (hV : IsTerminal V) :
    M.sections ≃+ M.val.obj (op V) :=
  AddEquiv.ofBijective (M := M.sections) (N := M.val.obj (op V))
    ({ toFun := fun s ↦ s.1 (op V)
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : M.sections →+ M.val.obj (op V))
    (Functor.bijective_sections_eval_of_isTerminal (M.val.presheaf ⋙ forget _) hV)

/-- The evaluation equivalence `sectionsEvalAddEquiv M hV` sends a global section `s` to its value
`s.1 (op V)` at the terminal object `V`. -/
theorem sectionsEvalAddEquiv_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {V : C} (hV : IsTerminal V)
    (s : M.sections) : sectionsEvalAddEquiv M hV s = s.1 (op V) :=
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Y' : AlgebraicSpaces B S hS}

/-- **The inverse image of global sections**, `Γ(Y, 𝓝) ⟶ Γ(Y', g^*𝓝)`: the unit of
**Stacks 03LU** on global sections of `Y`, followed by the comparison of **Stacks 0732**. -/
def globalSectionsPullbackMap (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj N ⟶
      (globalSectionsRestrictScalars B S hS g).obj
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)).obj
            ((modulePullback B S hS g).obj N)) :=
  (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map
      ((modulePullbackAdjunction B S hS g).unit.app N) ≫
    (globalSectionsPushforwardIsoSite B S hS g).hom.app ((modulePullback B S hS g).obj N)

/-- The inverse image of global sections, as the composite it is defined to be. -/
theorem globalSectionsPullbackMap_eq (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map
        ((modulePullbackAdjunction B S hS g).unit.app N) ≫
      (globalSectionsPushforwardIsoSite B S hS g).hom.app ((modulePullback B S hS g).obj N) =
    globalSectionsPullbackMap B S hS g N :=
  rfl

/-- **The extension of scalars of the inverse image of global sections**,
`Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} Γ(Y, 𝓝) ⟶ Γ(Y', g^*𝓝)`. -/
def globalSectionsPullbackBaseChange (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (globalSectionsRingHomSite B S hS g)).obj
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj N) ⟶
      (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)).obj
        ((modulePullback B S hS g).obj N) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (globalSectionsRingHomSite B S hS g)).homEquiv _ _).symm (globalSectionsPullbackMap B S hS g N)

/-- The extension of scalars on a pure tensor. -/
theorem globalSectionsPullbackBaseChange_tmul (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (b : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj N) :
    (globalSectionsPullbackBaseChange B S hS g N).hom
        (b ⊗ₜ[RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj,
          globalSectionsRingHomSite B S hS g] s) =
      b • (globalSectionsPullbackMap B S hS g N).hom s :=
  rfl

/-- **The inverse image of a global section, on a chart diagram.** -/
theorem globalSectionsPullbackMap_val_chartDiagram (g : Y' ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj N)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom) :
    ((globalSectionsPullbackMap B S hS g N).hom s).1 (op d.U) =
      modulePullbackChartSection B S hS g N d (s.1 (op d.V)) :=
  modulePullbackGlobalSection_val_chartDiagram g N s d

section TerminalCharts

variable (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom) (hU : IsTerminal d.U) (hV : IsTerminal d.V)

/-- Evaluation of the global sections of `𝓝` at a terminal chart is semilinear over evaluation of
global regular functions; stated for the inverse equivalences. -/
theorem sectionsEvalAddEquiv_symm_smul (r : chartRing B S hS Y.1 Y.2 d.V)
    (x : N.val.obj (op d.V)) :
    (sectionsEvalAddEquiv N hV).symm (r • x) =
      (sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj hV).symm r •
        (sectionsEvalAddEquiv N hV).symm x := by
  refine (sectionsEvalAddEquiv N hV).injective ?_
  rw [AddEquiv.apply_symm_apply]
  show r • x =
    (sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj hV)
        ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
          hV).symm r) •
      (sectionsEvalAddEquiv N hV) ((sectionsEvalAddEquiv N hV).symm x)
  rw [RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The ring map of **Stacks 0732** read through evaluation at terminal charts is pullback of
regular functions along the chart diagram. -/
theorem globalSectionsRingHomSite_sectionsSubringEvalEquiv_symm
    (r : chartRing B S hS Y.1 Y.2 d.V) :
    globalSectionsRingHomSite B S hS g
        ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
          hV).symm r) =
      (sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj
          hU).symm (chartDiagramRestrict B S hS g d r) := by
  refine (sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj
    hU).injective ?_
  rw [RingEquiv.apply_symm_apply]
  have h := globalSectionsRingHomSite_val_chartDiagram B S hS g
    ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj hV).symm r)
    d
  refine h.trans ?_
  show chartDiagramRestrict B S hS g d
    ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj hV)
      ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
        hV).symm r)) = chartDiagramRestrict B S hS g d r
  rw [RingEquiv.apply_symm_apply]

/-- Evaluation at the terminal chart of `Y'` of global sections of `g^*𝓝` is semilinear over
evaluation of global regular functions. -/
theorem sectionsEvalAddEquiv_smul_symm (a : chartRing B S hS Y'.1 Y'.2 d.U)
    (p : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)).obj
        ((modulePullback B S hS g).obj N)) :
    sectionsEvalAddEquiv ((modulePullback B S hS g).obj N) hU
        ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj
          hU).symm a • p) =
      a • sectionsEvalAddEquiv ((modulePullback B S hS g).obj N) hU p :=
  congrArg (fun t : chartRing B S hS Y'.1 Y'.2 d.U ↦
      t • sectionsEvalAddEquiv ((modulePullback B S hS g).obj N) hU p)
    ((sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj
      hU).apply_symm_apply a)

include hU hV in
/-- **Over a chart diagram of terminal affine charts, the extension of scalars of the inverse
image of global sections of a quasi-coherent module is bijective**:
`Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} Γ(Y, 𝓝) ≅ Γ(Y', g^*𝓝)`. -/
theorem bijective_globalSectionsPullbackBaseChange (hN : N.IsQuasicoherentOnSite)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective (globalSectionsPullbackBaseChange B S hS g N).hom := by
  let := chartDiagramAlgebra B S hS g d
  exact Stacks.ModuleCat.bijective_extendScalars_homEquiv_symm_of_model
    (globalSectionsRingHomSite B S hS g) (globalSectionsPullbackMap B S hS g N)
    (R := chartRing B S hS Y.1 Y.2 d.V) (R' := chartRing B S hS Y'.1 Y'.2 d.U)
    (Mc := N.val.obj (op d.V))
    (sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj hV).symm
    (sectionsSubringEvalEquiv (ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O).obj hU).symm
    (globalSectionsRingHomSite_sectionsSubringEvalEquiv_symm B S hS g d hU hV)
    (sectionsEvalAddEquiv N hV).symm (sectionsEvalAddEquiv_symm_smul B S hS g N d hV)
    (sectionsEvalAddEquiv ((modulePullback B S hS g).obj N) hU)
    (sectionsEvalAddEquiv_smul_symm B S hS g N d hU)
    (modulePullbackChartBaseChange B S hS g N d) (map_add _)
    (fun a x ↦ congrArg (a • ·) ((congrArg (modulePullbackChartSection B S hS g N d)
      ((sectionsEvalAddEquiv N hV).apply_symm_apply x).symm).trans
      (globalSectionsPullbackMap_val_chartDiagram B S hS g N
        ((sectionsEvalAddEquiv N hV).symm x) d).symm))
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g N hN d haU haV)

include hU hV in
/-- **Over a chart diagram of terminal affine charts, the extension of scalars of the inverse
image of global sections of a quasi-coherent module is an isomorphism**:
`Γ(Y', 𝒪_{Y'}) ⊗_{Γ(Y, 𝒪_Y)} Γ(Y, 𝓝) ≅ Γ(Y', g^*𝓝)`. -/
theorem isIso_globalSectionsPullbackBaseChange (hN : N.IsQuasicoherentOnSite)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    IsIso (globalSectionsPullbackBaseChange B S hS g N) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_globalSectionsPullbackBaseChange B S hS g N d hU hV hN haU haV)

end TerminalCharts

end AlgebraicGeometry.Space

end
