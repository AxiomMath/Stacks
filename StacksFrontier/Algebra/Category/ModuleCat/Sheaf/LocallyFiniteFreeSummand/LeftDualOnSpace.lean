module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.Coevaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
import StacksCore.Tactic.StacksAttribute

/-!
# The dual sheaf is a left dual

Let `(X, O_X)` be a ringed space and let `F` be a sheaf of `O_X`-modules which is locally a
direct summand of a finite free module. Stacks 0FNV asserts that the dual `F^∨`, together with
the coevaluation and evaluation of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFiniteFreeSummand/Coevaluation.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean`, is a left dual of `F` in the
monoidal category of `O_X`-modules — the monoidal structure constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OnSpaceMonoidal.lean`.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.dualSheafExactPairing` is the exact pairing.

## Main results

* `Stacks.SheafOfModules.OnSpace.dualSheaf_isLeftDual`: Stacks 0FNV, phrased so that the
  monoidal structure is exhibited together with the equations identifying its unit, its tensor
  product and its pairing morphisms with the canonical sheaf constructions.
* `Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_exactPairing`: Stacks 0FNW (1)
  with **no** coherence hypotheses, obtained by discharging the three coherence hypotheses of
  `Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_exactPairing` against the constructed
  monoidal structure.

## Implementation notes

The snake identities are checked locally: around every point the coevaluation is a finite sum
of pure tensors (`coevaluation_locally_sum`), and on such an open both composites reduce, by
the section formulas for the associator and the two unitors, to the dual-basis identity.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FNW](https://stacks.math.columbia.edu/tag/0FNW)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct MonoidalCategory

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] restrFun ORestr PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ ModuleCat.restrictScalars internalHom
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] monoidal

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- **The monoidal structure of `monoidal`, at the spelling of the index the site-level tensor
API carries.** `Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩` has
`⟨X.presheaf ⋙ forget₂ CommRingCat RingCat, _⟩` for its underlying sheaf of rings — the first
component reaches `X.presheaf` by an iota step, available at every transparency — whereas
`structureSheafRing X` reaches that only after a delta step; a goal is keyed into the typeclass
discrimination tree with only `@[reducible]` definitions unfolded, and `structureSheafRing` is
`@[instance_reducible]`, so `monoidal` is not retrieved at the site-level spelling. The two
indices are equal by `rfl`, so this is that same structure under a key the search does find. -/
@[instance_reducible]
noncomputable def monoidalRingSheaf :
    MonoidalCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)) :=
  monoidal X

attribute [local instance] monoidalRingSheaf

/-- The evaluation pairing `F^∨ ⊗ F ⟶ O_X`, with its source written as the tensor product of
`monoidal` rather than as `tensorSheaf`.  The two are equal objects by `monoidal_tensorObj`, but
only one of the spellings matches the section formulas of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OnSpaceMonoidal.lean`, and mixing them makes
a goal fail to be type-correct
at `implicit` transparency. -/
@[sga "3 VIB 11.8.0" "more general", sga "5 IIIB 5.0" "5.0.2, special case"]
noncomputable abbrev evaluationTensor (F : SheafOfModules.{u} (structureSheafRing X)) :
    dualSheaf X F ⊗ F ⟶ 𝟙_ (SheafOfModules.{u} (structureSheafRing X)) :=
  evaluation X F

/-- The coevaluation `O_X ⟶ F ⊗ F^∨`, with its target written as the tensor product of
`monoidal`; see `evaluationTensor`. -/
noncomputable abbrev coevaluationTensor (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    𝟙_ (SheafOfModules.{u} (structureSheafRing X)) ⟶ F ⊗ dualSheaf X F :=
  coevaluation X F hF

/-- The evaluation pairing on a local pure tensor is the value of the functional. -/
theorem evaluation_tmul (F : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) (l : (dualSheaf X F).val.obj (op U)) (f : F.val.obj (op U)) :
    ((evaluationTensor X F).val.app (op U)).hom
      (tensorObjTmul X (dualSheaf X F) F (op U) l f) =
      unitSection X (op U) (dualEval X F l f) := by
  have h := ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
    (structureSheafRing X).property).homEquiv
      ((PresheafOfModules.tensorObj (O := X.presheaf) ((dualSheaf X F).val) (F.val)))
      (SheafOfModules.unit (structureSheafRing X))).apply_symm_apply
        (_root_.Stacks.SheafOfModules.evaluationPresheaf X.presheaf
          (structureSheafRing X).property F)
  exact congrArg (fun q => (q.app (op U)).hom (l ⊗ₜ[X.presheaf.obj (op U)] f)) h

/-- Restriction along the identity does nothing. -/
theorem map_id_apply (F : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) (s : F.val.obj (op U)) :
    (F.val.map (𝟙 U).op).hom s = s := by
  rw [CategoryTheory.op_id, F.val.map_id]
  exact ModuleCat.restrictScalarsId'App_inv_apply _
    (congrArg RingCat.Hom.hom ((structureSheafRing X).obj.map_id (op U))) _ _

/-- If the coevaluation is the finite sum `∑ j, e j ⊗ l j` on `U`, then `(e, l)` is a dual
basis for `F` over `U`. -/
theorem coevaluation_sum_identity
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F)
    (U : Opens X.carrier) {I : Type*} [Fintype I]
    (e : I → F.val.obj (op U))
    (l : I → (dualSheaf X F).val.obj (op U))
    (h : ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j, toTensorSheafSection X F (dualSheaf X F) (op U)
        (e j ⊗ₜ[X.presheaf.obj (op U)] l j))
    (V : (Over U)ᵒᵖ) (f : F.val.obj (op V.unop.left)) :
    ∑ j, dualValue X F (l j) V f • resSection X F V (e j) = f := by
  classical
  have hc := congrArg (fun q : SheafOfModules.unit (structureSheafRing X) ⟶ sheafHom X F F =>
    homApp X F F ((q.val.app (op U)).hom (1 : X.presheaf.obj (op U))) V f)
    (coevaluation_comp_tensorDualToEndomorphism X F hF)
  change homApp X F F (((tensorDualToEndomorphism X F).val.app (op U)).hom
    (((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)))) V f =
      homApp X F F (((identityEndomorphism X F).val.app (op U)).hom
        (1 : X.presheaf.obj (op U))) V f at hc
  rw [h, identityEndomorphism_apply_one] at hc
  rw [map_sum] at hc
  refine Eq.trans (Finset.sum_congr rfl fun j _ =>
    (tensorDualToEndomorphism_tmul_apply X F U (e j) (l j) V f).symm) ?_
  refine Eq.trans ?_ hc
  exact (sheafHom_sum_apply X F F U Finset.univ
    (fun j => ((tensorDualToEndomorphism X F).val.app (op U)).hom
      (toTensorSheafSection X F (dualSheaf X F) (op U)
        (e j ⊗ₜ[X.presheaf.obj (op U)] l j))) V f).symm

/-- Around every point there is an open on all of whose subopens the coevaluation is a finite
sum of pure tensors. -/
theorem coevaluation_locally_sum
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) (x : X.carrier) :
    ∃ W : Opens X.carrier, x ∈ W ∧ ∀ (U : Opens X.carrier) (_ : U ⟶ W),
      ∃ (n : ℕ) (e : Fin n → F.val.obj (op U))
        (l : Fin n → (dualSheaf X F).val.obj (op U)),
        ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
          ∑ j, toTensorSheafSection X F (dualSheaf X F) (op U)
            (e j ⊗ₜ[X.presheaf.obj (op U)] l j) := by
  obtain ⟨W, hxW, n, ⟨r⟩⟩ := hF x
  refine ⟨W, hxW, fun U k => ⟨n,
    fun j => (F.val.map k.op).hom (splittingBasisSection X F W n r.r j),
    fun j => ((dualSheaf X F).val.map k.op).hom (splittingDualSection X F W n r.i j), ?_⟩⟩
  have h := congrArg (fun s =>
      (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        ((dualSheaf X F)))).val.map k.op).hom s)
    (coevaluation_apply_eq_sum_of_retract X F hF W n r.i r.r r.retract)
  rw [map_sum] at h
  refine Eq.trans ?_ (h.trans ?_)
  · have hn := PresheafOfModules.naturality_apply (coevaluation X F hF).val k.op
      (1 : X.presheaf.obj (op W))
    change ((coevaluation X F hF).val.app (op U)).hom
      ((X.presheaf.map k.op).hom 1) = _ at hn
    rw [map_one] at hn
    exact hn
  · exact Finset.sum_congr rfl fun j _ =>
      tensorSection_restrict X F (dualSheaf X F) k _ _

/-- A dual basis for `F` over `U` expands every section of the dual over `U`. -/
theorem dual_sum_identity
    (F : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) {I : Type*} [Fintype I]
    (e : I → F.val.obj (op U))
    (l : I → (dualSheaf X F).val.obj (op U))
    (hb : ∀ (V : (Over U)ᵒᵖ) (f : F.val.obj (op V.unop.left)),
      ∑ j, dualValue X F (l j) V f • resSection X F V (e j) = f)
    (s : (dualSheaf X F).val.obj (op U)) :
    ∑ j, dualEval X F s (e j) • l j = s := by
  classical
  apply PresheafOfModules.hom_ext
  intro V
  ext f
  change dualValue X F (∑ j, dualEval X F s (e j) • l j) V f = dualValue X F s V f
  refine Eq.trans (sheafHom_sum_apply X F (SheafOfModules.unit (structureSheafRing X)) U
    Finset.univ (fun j => dualEval X F s (e j) • l j) V f) ?_
  calc
    _ = ∑ j, dualValue X F s V (dualValue X F (l j) V f • resSection X F V (e j)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Eq.trans (sheafHom_smul_apply X F _ U (dualEval X F s (e j)) (l j) V f) ?_
      refine Eq.trans ?_ ((s.app V).hom.map_smul (dualValue X F (l j) V f)
        (resSection X F V (e j))).symm
      have hn : dualValue X F s V (resSection X F V (e j)) =
          (X.presheaf.map V.unop.hom.op).hom (dualEval X F s (e j)) :=
        PresheafOfModules.naturality_apply s
          (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op (e j)
      exact (mul_comm _ _).trans (congrArg
        (fun z : X.presheaf.obj (op V.unop.left) => dualValue X F (l j) V f * z) hn.symm)
    _ = _ := (map_sum (s.app V).hom _ _).symm.trans
      (congrArg (dualValue X F s V) (hb V f))

/-- A finite expansion of the coevaluation, rewritten with the pure tensors of `tensorObjTmul`. -/
private theorem coevaluation_one_eq_sum_tensorObjTmul
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F)
    (U : Opens X.carrier) {I : Type*} [Fintype I]
    (e : I → F.val.obj (op U))
    (l : I → (dualSheaf X F).val.obj (op U))
    (h : ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j, toTensorSheafSection X F (dualSheaf X F) (op U)
        (e j ⊗ₜ[X.presheaf.obj (op U)] l j)) :
    ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j, tensorObjTmul X F (dualSheaf X F) (op U) (e j) (l j) :=
  h.trans (Finset.sum_congr rfl fun j _ =>
    (tensorObjTmul_eq X F (dualSheaf X F) (op U) (e j) (l j)).symm)

/-- The first snake identity, checked on sections of an open carrying a finite expansion of
the coevaluation. -/
theorem evaluation_coevaluation_apply_of_sum
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F)
    (U : Opens X.carrier) {I : Type*} [Fintype I]
    (e : I → F.val.obj (op U))
    (l : I → (dualSheaf X F).val.obj (op U))
    (h : ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j, toTensorSheafSection X F (dualSheaf X F) (op U)
        (e j ⊗ₜ[X.presheaf.obj (op U)] l j))
    (s : F.val.obj (op U)) :
    (((λ_ F).inv ≫ coevaluationTensor X F hF ▷ F ≫
      (α_ F (dualSheaf X F) F).hom ≫ F ◁ evaluationTensor X F ≫
      (ρ_ F).hom).val.app (op U)).hom s = s := by
  classical
  have h' := coevaluation_one_eq_sum_tensorObjTmul X F hF U e l h
  have hstart : (((λ_ F).inv).val.app (op U)).hom s =
      tensorObjTmul X (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) F (op U)
        (unitSection X (op U) 1) s :=
    leftUnitor_inv_apply X F (op U) s
  have hcoev : ((coevaluationTensor X F hF ▷ F).val.app (op U)).hom
      (tensorObjTmul X (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) F (op U)
        (unitSection X (op U) 1) s) =
      ∑ j, tensorObjTmul X (F ⊗ dualSheaf X F) F (op U)
        (tensorObjTmul X F (dualSheaf X F) (op U) (e j) (l j)) s := by
    refine Eq.trans (whiskerRight_tmul X (coevaluationTensor X F hF) F (op U)
      (unitSection X (op U) 1) s) ?_
    refine Eq.trans (congrArg (fun z : (F ⊗ dualSheaf X F).val.obj (op U) =>
      tensorObjTmul X (F ⊗ dualSheaf X F) F (op U) z s) h') ?_
    exact tensorObjTmul_sum_left X (F ⊗ dualSheaf X F) F (op U) Finset.univ _ s
  have hterm (j : I) :
      (((α_ F (dualSheaf X F) F).hom ≫ F ◁ evaluationTensor X F ≫
        (ρ_ F).hom).val.app (op U)).hom
          (tensorObjTmul X (F ⊗ dualSheaf X F) F (op U)
            (tensorObjTmul X F (dualSheaf X F) (op U) (e j) (l j)) s) =
      dualEval X F (l j) s • e j := by
    have h1 := associator_tmul X F (dualSheaf X F) F (op U) (e j) (l j) s
    have h2 := (whiskerLeft_tmul X F (evaluationTensor X F) (op U) (e j)
      (tensorObjTmul X (dualSheaf X F) F (op U) (l j) s)).trans
      (congrArg (fun z : (𝟙_ (SheafOfModules.{u} (structureSheafRing X))).val.obj (op U) =>
        tensorObjTmul X F (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) (op U) (e j) z)
        (evaluation_tmul X F U (l j) s))
    have h3 := rightUnitor_tmul X F (op U) (e j) (dualEval X F (l j) s)
    exact sheaf_comp3_app_apply_of X (α_ F (dualSheaf X F) F).hom
      (F ◁ evaluationTensor X F) (ρ_ F).hom (op U) _ h1 h2 h3
  refine Eq.trans (sheaf_comp3_app_apply_of X (λ_ F).inv (coevaluationTensor X F hF ▷ F)
    ((α_ F (dualSheaf X F) F).hom ≫ F ◁ evaluationTensor X F ≫ (ρ_ F).hom) (op U) s
    hstart hcoev rfl) ?_
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hterm j) ?_
  have hb := coevaluation_sum_identity X F hF U e l h (op (Over.mk (𝟙 U))) s
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hb
  exact congrArg (fun z : F.val.obj (op U) => dualEval X F (l j) s • z)
    (map_id_apply X F U (e j)).symm

/-- The second snake identity, checked on sections of an open carrying a finite expansion of
the coevaluation. -/
theorem coevaluation_evaluation_apply_of_sum
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F)
    (U : Opens X.carrier) {I : Type*} [Fintype I]
    (e : I → F.val.obj (op U))
    (l : I → (dualSheaf X F).val.obj (op U))
    (h : ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j, toTensorSheafSection X F (dualSheaf X F) (op U)
        (e j ⊗ₜ[X.presheaf.obj (op U)] l j))
    (s : (dualSheaf X F).val.obj (op U)) :
    (((ρ_ (dualSheaf X F)).inv ≫ dualSheaf X F ◁ coevaluationTensor X F hF ≫
      (α_ (dualSheaf X F) F (dualSheaf X F)).inv ≫
      evaluationTensor X F ▷ dualSheaf X F ≫
      (λ_ (dualSheaf X F)).hom).val.app (op U)).hom s = s := by
  classical
  have h' := coevaluation_one_eq_sum_tensorObjTmul X F hF U e l h
  have hstart : (((ρ_ (dualSheaf X F)).inv).val.app (op U)).hom s =
      tensorObjTmul X (dualSheaf X F)
        (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) (op U) s
        (unitSection X (op U) 1) :=
    rightUnitor_inv_apply X (dualSheaf X F) (op U) s
  have hcoev : ((dualSheaf X F ◁ coevaluationTensor X F hF).val.app (op U)).hom
      (tensorObjTmul X (dualSheaf X F)
        (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) (op U) s
        (unitSection X (op U) 1)) =
      ∑ j, tensorObjTmul X (dualSheaf X F) (F ⊗ dualSheaf X F) (op U) s
        (tensorObjTmul X F (dualSheaf X F) (op U) (e j) (l j)) := by
    refine Eq.trans (whiskerLeft_tmul X (dualSheaf X F) (coevaluationTensor X F hF) (op U) s
      (unitSection X (op U) 1)) ?_
    refine Eq.trans (congrArg (fun z : (F ⊗ dualSheaf X F).val.obj (op U) =>
      tensorObjTmul X (dualSheaf X F) (F ⊗ dualSheaf X F) (op U) s z) h') ?_
    exact tensorObjTmul_sum_right X (dualSheaf X F) (F ⊗ dualSheaf X F) (op U) s
      Finset.univ _
  have hterm (j : I) :
      (((α_ (dualSheaf X F) F (dualSheaf X F)).inv ≫
        evaluationTensor X F ▷ dualSheaf X F ≫
        (λ_ (dualSheaf X F)).hom).val.app (op U)).hom
          (tensorObjTmul X (dualSheaf X F) (F ⊗ dualSheaf X F) (op U) s
            (tensorObjTmul X F (dualSheaf X F) (op U) (e j) (l j))) =
      dualEval X F s (e j) • l j := by
    have h1 := associator_inv_tmul X (dualSheaf X F) F (dualSheaf X F) (op U) s (e j) (l j)
    have h2 := (whiskerRight_tmul X (evaluationTensor X F) (dualSheaf X F) (op U)
      (tensorObjTmul X (dualSheaf X F) F (op U) s (e j)) (l j)).trans
      (congrArg (fun z : (𝟙_ (SheafOfModules.{u} (structureSheafRing X))).val.obj (op U) =>
        tensorObjTmul X (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))
          (dualSheaf X F) (op U) z (l j))
        (evaluation_tmul X F U s (e j)))
    have h3 := leftUnitor_tmul X (dualSheaf X F) (op U) (dualEval X F s (e j)) (l j)
    exact sheaf_comp3_app_apply_of X (α_ (dualSheaf X F) F (dualSheaf X F)).inv
      (evaluationTensor X F ▷ dualSheaf X F) (λ_ (dualSheaf X F)).hom (op U) _ h1 h2 h3
  refine Eq.trans (sheaf_comp3_app_apply_of X (ρ_ (dualSheaf X F)).inv
    (dualSheaf X F ◁ coevaluationTensor X F hF)
    ((α_ (dualSheaf X F) F (dualSheaf X F)).inv ≫ evaluationTensor X F ▷ dualSheaf X F ≫
      (λ_ (dualSheaf X F)).hom) (op U) s hstart hcoev rfl) ?_
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hterm j) ?_
  exact dual_sum_identity X F U e l (coevaluation_sum_identity X F hF U e l h) s

/-- **The exact pairing exhibiting `F^∨` as a left dual of `F`** in the monoidal category of
`O_X`-modules, for `F` locally a direct summand of a finite free module. -/
@[instance_reducible]
noncomputable def dualSheafExactPairing
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    ExactPairing F (dualSheaf X F) :=
  { coevaluation' := coevaluationTensor X F hF
    evaluation' := evaluationTensor X F
    coevaluation_evaluation' := by
      apply (cancel_epi (ρ_ (dualSheaf X F)).inv).mp
      apply (cancel_mono (λ_ (dualSheaf X F)).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      apply hom_ext_of_locally X
      intro x
      obtain ⟨W, hxW, hW⟩ := coevaluation_locally_sum X F hF x
      refine ⟨W, hxW, fun U k => ?_⟩
      obtain ⟨n, e, l, h⟩ := hW U k
      ext s
      exact coevaluation_evaluation_apply_of_sum X F hF U e l h s
    evaluation_coevaluation' := by
      apply (cancel_epi (λ_ F).inv).mp
      apply (cancel_mono (ρ_ F).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      apply hom_ext_of_locally X
      intro x
      obtain ⟨W, hxW, hW⟩ := coevaluation_locally_sum X F hF x
      refine ⟨W, hxW, fun U k => ?_⟩
      obtain ⟨n, e, l, h⟩ := hW U k
      ext s
      exact evaluation_coevaluation_apply_of_sum X F hF U e l h s }

/-! ### Identifying the monoidal structure with the canonical sheaf constructions -/

/-- The monoidal tensor product of two morphisms is the canonical induced morphism of tensor
product sheaves. This is `monoidal_tensorHom` with its two `eqToHom`s, which are identities,
removed. -/
theorem tensorHom_eq {A A' B B' : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
        ((f, g) : (_, _) ⟶ (_, _))) :=
  tensor_hom_ext X fun U a b =>
    (tensorHom_tmul X f g U a b).trans
      (tensorSheafMap_app_toTensorSheafSection X A B A' B' f g U.unop a b).symm

/-- The hand-rolled functoriality of the presheaf tensor product of Tag 01CB is the monoidal
one. -/
theorem presheafTensorMap_eq_tensorHom
    {F F' G G' : PresheafOfModules.{u} (O X)} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (PresheafOfModules.tensorHom (O := (X).presheaf) (φ) (ψ)) = φ ⊗ₘ ψ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext m n
  rfl

/-- The ringed-space and site-level tensor maps use the same native bifunctor; their sheaf
conditions differ only by proof irrelevance. -/
theorem tensorSheafMap_eq_site
    {A A' B B' : SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ A') (g : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
      ((f, g) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
          (forget₂ CommRingCat RingCat) ((structureSheafRing X).property)⟩)).map
        ((f, g) : (_, _) ⟶ (_, _))) :=
  rfl

/-- The pure tensor of two local sections, in the site-level spelling, is the canonical image
of the pure tensor. -/
theorem tensorSection_eq
    (A B : SheafOfModules.{u} (structureSheafRing X))
    (V : (Opens X.carrier)ᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) :
    _root_.Stacks.SheafOfModules.tensorSection X.presheaf (structureSheafRing X).property
        (monoidal_tensorObj X) A B V a b = tensorObjTmul X A B V a b := by
  change ((eqToHom (monoidal_tensorObj X A B).symm).val.app V)
      (tensorObjTmul X A B V a b) = _
  rw [show eqToHom (monoidal_tensorObj X A B).symm = 𝟙
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (A)).obj (B))) from
    eqToHom_refl _ _]
  rfl

/-- A local section of the structure sheaf, viewed in the tensor unit, is itself. -/
theorem unitTensorSection_eq
    (V : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj V) :
    _root_.Stacks.SheafOfModules.unitTensorSection X.presheaf
        (structureSheafRing X).property (monoidal_tensorUnit X) V r =
      unitSection X V r := by
  change ((eqToHom (monoidal_tensorUnit X).symm).val.app V) r = _
  rw [show eqToHom (monoidal_tensorUnit X).symm =
    𝟙 (SheafOfModules.unit (structureSheafRing X)) from eqToHom_refl _ _]
  rfl

/-- **Stacks Project, Tag 0FNW (1)**, with no coherence hypotheses: a sheaf of modules with a
left dual in the monoidal category of `O_X`-modules is locally a direct summand of a finite
free module.

The three coherence hypotheses of
`Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_exactPairing` — which constrain the
supplied monoidal instance on local pure tensors — are discharged here against the constructed
monoidal structure by `associator_tmul`, `leftUnitor_tmul` and `rightUnitor_tmul`. -/
@[stacks 0FNW "local_finite_free_summand"]
theorem isLocallyFiniteFreeSummand_of_exactPairing
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (p : ExactPairing F G) :
    IsLocallyFiniteFreeSummand X F := by
  refine _root_.Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_exactPairing X F G
    (monoidal X) (monoidal_tensorUnit X) (monoidal_tensorObj X) ?_ ?_ ?_ ?_ p
  · intro A A' B B' f g
    exact (monoidal_tensorHom X f g).trans (tensorSheafMap_eq_site X f g)
  · intro A B D V a b c
    rw [tensorSection_eq, tensorSection_eq, tensorSection_eq, tensorSection_eq,
      associator_tmul]
  · intro A V r a
    rw [tensorSection_eq, unitTensorSection_eq]
    exact leftUnitor_tmul X A V r a
  · intro A V a r
    rw [tensorSection_eq, unitTensorSection_eq]
    exact rightUnitor_tmul X A V a r

/-- **Stacks Project, Tag 0FNV.** For a sheaf of modules which is locally a direct summand of
a finite free module, its internal-Hom dual, with the canonical coevaluation and evaluation, is
a left dual.

The monoidal structure is exhibited together with the equations identifying its unit, its
tensor product on objects and on morphisms, and its pairing morphisms, with the canonical
sheaf constructions. -/
@[stacks 0FNV "sheaf_module_left_dual"]
theorem dualSheaf_isLeftDual
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    ∃ (M : MonoidalCategory (SheafOfModules.{u} (structureSheafRing X))),
      letI := M
      ∃ (hunit : 𝟙_ (SheafOfModules.{u} (structureSheafRing X)) =
          SheafOfModules.unit (structureSheafRing X))
        (htensor : ∀ A B : SheafOfModules.{u} (structureSheafRing X),
          A ⊗ B = (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (A)).obj (B)))
        (_htensorMap : ∀ {A A' B B' : SheafOfModules.{u} (structureSheafRing X)}
          (f : A ⟶ A') (g : B ⟶ B'),
          eqToHom (htensor A B).symm ≫ (f ⊗ₘ g) ≫ eqToHom (htensor A' B') =
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
              ((f, g) : (_, _) ⟶ (_, _))))
        (p : ExactPairing F (dualSheaf X F)),
        @ExactPairing.coevaluation _ _ _ _ _ p =
          eqToHom hunit ≫ coevaluation X F hF ≫
            eqToHom (htensor F (dualSheaf X F)).symm ∧
        @ExactPairing.evaluation _ _ _ _ _ p =
          eqToHom (htensor (dualSheaf X F) F) ≫ evaluation X F ≫ eqToHom hunit.symm := by
  refine ⟨monoidal X, monoidal_tensorUnit X, monoidal_tensorObj X,
    fun f g => monoidal_tensorHom X f g, dualSheafExactPairing X F hF, ?_, ?_⟩
  · rfl
  · rfl

end Stacks.SheafOfModules.OnSpace
