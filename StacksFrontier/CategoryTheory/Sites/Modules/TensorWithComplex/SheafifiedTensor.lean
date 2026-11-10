module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseComplex
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseTensor
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseComplex

/-!
# The sheafified tensor complex

Part of `StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex` (see there for the
overview).
This file shows that the sectionwise evaluation of the regular module is an isomorphism after
sheafification, sheafifies the sectionwise tensor complex, makes it functorial on cochains of
differential graded modules, and builds the evaluation maps used for the tensor-Hom adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open DifferentialGraded DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o r i

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

attribute [local instance]
  instAdditiveSheafOfModulesCRingSheafOPresheafOfModulesObjFunctorOppositeRingCatIsSheafJForget

-- `PresheafOfModules.map` lands in `ModuleCat.restrictScalars`, whose carrier is the underlying
-- module; unfolding it is what lets the sectionwise rewrite lemmas below match.
attribute [local implicit_reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]

section

private def moduleDegreeCast {S : Type*} [Ring S] (P : ℤ → ModuleCat.{r} S)
    {a b : ℤ} (h : a = b) : P a →ₗ[S] P b := by
  subst b
  exact LinearMap.id

private lemma moduleDegreeCast_apply {S : Type*} [Ring S] (P : ℤ → ModuleCat.{r} S)
    {a b : ℤ} (h : a = b) (x : P a) :
    moduleDegreeCast P h x = cast (congrArg (fun i => (P i : Type r)) h) x := by
  subst b
  rfl

section RegularInverse


variable (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
variable (D : TensorWithComplexData.{u, v, w, t, s, o} X R K)


private lemma regularIdentity_smul (p : ℤ) (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s} X K)).grading p) :
    MulOpposite.op ((((Rep.{u, v, w, t, s, o} X R K)).algebraHom p).symm (((Rep.{u, v, w, t, s, o} X
      R
        K)).moduleHom (liftComplex.{u, v, w, t, s} X K) p x) : ((Rep.{u, v, w, t, s, o} X R
            K)).algebra.A) •
      (regularIdentity.{u, v, w, t, s, o} X R K : ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)).M) = (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj
              (liftComplex.{u, v, w, t, s} X K)).M) := by
  obtain ⟨z, hz, hc⟩ := ((Rep.{u, v, w, t, s, o} X R K)).module_action (liftComplex.{u, v, w, t, s}
    X K)
      0 p p (zero_add p)
    (regularIdentity.{u, v, w, t, s, o} X R K) ((((Rep.{u, v, w, t, s, o} X R K)).algebraHom p).symm
        (((Rep.{u, v, w, t, s, o} X R K)).moduleHom (liftComplex.{u, v, w, t, s} X K) p x))
  have he : z = x := by
    apply (((Rep.{u, v, w, t, s, o} X R K)).moduleHom (liftComplex.{u, v, w, t, s} X K) p).injective
    rw [hc]
    simp only [regularIdentity, LinearEquiv.apply_symm_apply]
    exact (CompDG.{u, v, w, t, s, o} X R).id_comp _
  exact hz.symm.trans (congrArg Subtype.val he)

private noncomputable def regularSectionwiseUnit (U : X.Cᵒᵖ) (d : ℤ) :
    (((liftComplex.{u, v, w, t, s} X K)).X d).val.obj U
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] ((D.sectionwise
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))).X d).obj U
          :=
  (moduleDegreeCast (fun i => ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K))).X i).obj U) (zero_add d)).comp
    (show ((liftComplex.{u, v, w, t, s} X K).X d).val.obj U
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K))).X (0 + d)).obj U from
    { __ := (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s}
        X K)) 0 d U (regularIdentity.{u, v, w, t, s, o} X R K)).toAddHom
      map_smul' a y := D.sectionwisePure_smul ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)) 0 d U
        (regularIdentity.{u, v, w, t, s, o} X R K) a y })

private lemma regularSectionwiseUnit_apply (U : X.Cᵒᵖ) (d : ℤ)
    (y : (((liftComplex.{u, v, w, t, s} X K)).X d).val.obj U) :
    regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U d y =
      cast (congrArg (fun i => (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K))).X i).obj U : Type _)) (zero_add d))
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
          X
            K)) 0 d U (regularIdentity.{u, v, w, t, s, o} X R K) y) := by
  exact moduleDegreeCast_apply (fun i => ((D.sectionwise
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))).X i).obj U)
    (zero_add d) _

private lemma regularSectionwiseEval_unit (U : X.Cᵒᵖ) (d : ℤ)
    (y : (((liftComplex.{u, v, w, t, s} X K)).X d).val.obj U) :
    regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d
      (regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U d y) = y := by
  rw [regularSectionwiseUnit_apply]
  exact regularSectionwiseEval_identity_pure.{u, v, w, t, s, o} X R K D U d y

private lemma sectionwisePure_heq
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    (x : M.grading p) (x' : M.grading p')
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U)
    (y' : ((liftComplex.{u, v, w, t, s} X K).X q').val.obj U)
    (hx : HEq x x') (hy : HEq y y') :
    HEq (D.sectionwisePure M p q U x y) (D.sectionwisePure M p' q' U x' y') := by
  subst p'
  subst q'
  cases hx
  cases hy
  rfl

private lemma regularEvalMap_degree_heq (U : X.Cᵒᵖ) (p q d d' : ℤ)
    (h : p + q = d) (h' : p + q = d')
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)).grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq (regularEvalMap.{u, v, w, t, s, o} X R K d p q h U x y)
      (regularEvalMap.{u, v, w, t, s, o} X R K d' p q h' U x y) := by
  subst d
  subst d'
  rfl

private lemma regularSectionwiseUnit_eval_pure (U : X.Cᵒᵖ) (p q : ℤ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading p)
      (y :
        (((liftComplex.{u, v, w, t, s} X K)).X q).val.obj U) :
    regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U (p + q)
      (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U (p + q)
        (D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
          X
            K)) p q U x y)) = D.sectionwisePure ((Rep.{u, v, w, t, s, o} X R K).functor.obj
                (liftComplex.{u, v, w, t, s} X K)) p q U x y := by
  have he := regularSectionwiseEval_pure.{u, v, w, t, s, o} X R K D U (p + q) p q rfl x y
  simp only [cast_eq] at he
  rw [he, regularSectionwiseUnit_apply]
  let a := (((Rep.{u, v, w, t, s, o} X R K)).algebraHom p).symm (((Rep.{u, v, w, t, s, o} X R
    K)).moduleHom
      (liftComplex.{u, v, w, t, s} X K) p x)
  have hb := D.sectionwisePure_balance ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v,
      w, t, s} X K)) 0 q p U
    (regularIdentity.{u, v, w, t, s, o} X R K) a y
  have hx : HEq (⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) •
    ((regularIdentity.{u, v, w, t, s, o} X R K) : ((Rep.{u, v, w, t, s, o} X R K).functor.obj
    (liftComplex.{u, v, w, t, s} X
          K)).M),
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).smul_mem 0 p _
        a
          (regularIdentity.{u, v, w, t, s, o} X R K).property a.property⟩ : ((Rep.{u, v, w, t, s, o}
            X R
              K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading (0 + p)) x := by
    apply (Subtype.heq_iff_coe_eq (fun z => by rw [zero_add])).mpr
    exact regularIdentity_smul.{u, v, w, t, s, o} X R K p x
  have hl := sectionwisePure_heq.{u, v, w, t, s, o} X R K D ((Rep.{u, v, w, t, s, o} X R
    K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) U
    (zero_add p) rfl _ x y y hx (HEq.rfl)
  have hy : HEq
      (((((Rep.{u, v, w, t, s, o} X R K).algebraHom p a).v q (q + p) (by omega)).val.app U) y)
      ((regularBalanced.{u, v, w, t, s, o} X R K U (p + q)).toFun p q rfl x y) := by
    dsimp only [a]
    rw [LinearEquiv.apply_symm_apply]
    change HEq (regularEvalMap.{u, v, w, t, s, o} X R K (q + p) p q (by omega) U x y)
      (regularEvalMap.{u, v, w, t, s, o} X R K (p + q) p q rfl U x y)
    exact regularEvalMap_degree_heq.{u, v, w, t, s, o} X R K U p q _ _ _ _ x y
  have hr := sectionwisePure_heq.{u, v, w, t, s, o} X R K D ((Rep.{u, v, w, t, s, o} X R
    K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) U rfl (add_comm q p)
    (regularIdentity.{u, v, w, t, s, o} X R K) (regularIdentity.{u, v, w, t, s, o} X R K) _ _
      (HEq.rfl) hy
  exact eq_of_heq ((cast_heq _ _).trans (hr.symm.trans (hb.symm.trans hl)))


private lemma sectionwisePure_hom_ext
    (M : (dgCategory.{_, _, max u v w t s} ((Rep.{u, v, w, t, s, o} X R K)).algebra).Obj)
    (U : X.Cᵒᵖ) (d : ℤ)
      (P : ModuleCat.{max u v w t s} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    {f g : ((D.sectionwise M).X d).obj U
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U] P}
    (h : ∀ (p q : ℤ) (hpq : p + q = d) (x : M.grading p)
      (y : (((liftComplex.{u, v, w, t, s} X K)).X q).val.obj U),
      f (cast (congrArg (fun i => (((D.sectionwise M).X i).obj U : Type _)) hpq)
        (D.sectionwisePure M p q U x y)) =
      g (cast (congrArg (fun i => (((D.sectionwise M).X i).obj U : Type _)) hpq)
        (D.sectionwisePure M p q U x y))) : f = g := by
  let b : BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K M U d P :=
    { toFun := fun _ _ _ => 0
      map_smul := by intros; simp
      balance := by intros; simp }
  apply sub_eq_zero.mp
  apply sectionwiseTensorUniversal_ext.{u, v, w, t, s, o} X R K D M U d P b
  · intro p q hpq x y
    change f _ - g _ = 0
    exact sub_eq_zero.mpr (h p q hpq x y)
  · intros
    rfl

private lemma regularSectionwiseUnit_eval (U : X.Cᵒᵖ) (d : ℤ) :
    (regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U d).comp
      (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d) = LinearMap.id := by
  apply sectionwisePure_hom_ext.{u, v, w, t, s, o} X R K D ((Rep.{u, v, w, t, s, o} X R
    K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) U d
    (((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
      K))).X
        d).obj U)
  intro p q h x y
  subst d
  exact regularSectionwiseUnit_eval_pure.{u, v, w, t, s, o} X R K D U p q x y

private noncomputable def regularSectionwiseEquiv (U : X.Cᵒᵖ) (d : ℤ) :
    ((D.sectionwise ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X
      K))).X
        d).obj U ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
          (((liftComplex.{u, v, w, t, s} X K)).X d).val.obj U :=
  LinearEquiv.ofLinearMap
    (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U d)
    (regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U d)
    (by ext y; exact regularSectionwiseEval_unit.{u, v, w, t, s, o} X R K D U d y)
    (regularSectionwiseUnit_eval.{u, v, w, t, s, o} X R K D U d)

private lemma regularSectionwiseEvalHom_isIso :
    IsIso (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D) := by
  have (d : ℤ) (U : X.Cᵒᵖ) :
      IsIso (((regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D).f d).app U) := by
    let e := (regularSectionwiseEquiv.{u, v, w, t, s, o} X R K D U d).toModuleIso
    have he : e.hom = ((regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D).f d).app U := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      rfl
    rw [← he]
    exact e.isIso_hom
  have (d : ℤ) : IsIso ((regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D).f d) := by
    let e := PresheafOfModules.isoMk
      (fun U => asIso (((regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D).f d).app U))
      (by
        intro U V f
        exact ((regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D).f d).naturality f)
    have he : e.hom = (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D).f d := by
      ext U
      rfl
    rw [← he]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _


/-- On each degree and each object of the site, the sectionwise unit `y ↦ 1 ⊗ y` is the inverse of
the component of the sectionwise evaluation. -/
private lemma regularSectionwiseEvalHom_inv_apply
    [IsIso (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D)]
    (q : ℤ) (U : X.Cᵒᵖ) (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    (((inv (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D)).f q).app U) y =
      regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U q y := by
  have hinj : Function.Injective (regularSectionwiseEval.{u, v, w, t, s, o} X R K D U q) := by
    intro z z' hz
    have h := congrArg (regularSectionwiseUnit.{u, v, w, t, s, o} X R K D U q) hz
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      regularSectionwiseUnit_eval.{u, v, w, t, s, o} X R K D U q] at h
  apply hinj
  rw [regularSectionwiseEval_unit.{u, v, w, t, s, o} X R K D U q y]
  have h := congrArg (fun φ => ((φ.f q).app U) y)
    (IsIso.inv_hom_id (regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D))
  exact h

private lemma sectionwiseToSheaf_cast_heq
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) {a b : ℤ} (h : a = b) (z : ((D.sectionwise M).X a).obj U) :
    HEq (((D.sectionwiseToSheaf M).f b).app U
        (cast (congrArg (fun i => (((D.sectionwise M).X i).obj U : Type _)) h) z))
      (((D.sectionwiseToSheaf M).f a).app U z) := by
  subst b
  rfl

/-- **The inverse of the regular isomorphism is `y ↦ 1 ⊗ y`.** For any tensor data `D` on `K`,
the map `K ⟶ Hom(K, K) ⊗_E K` sending a section `y` to the pure tensor of the identity of `K`
with `y` is an isomorphism of complexes of `O`-modules. This is the content of
`AlgebraicGeometry.RingedSite.tensorWithComplexDG_regular`, with the isomorphism specified on
sections. -/
public theorem TensorWithComplexData.exists_isIso_pure_regular :
    ∃ j : (liftComplex.{u, v, w, t, s} X K : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) ⟶
        D.functor.obj
          ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)),
      IsIso j ∧ ∀ (q : ℤ) (U : X.Cᵒᵖ) (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
        HEq (((j.f q).val.app U) y)
          (D.pure ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))
            0 q U (((Rep.{u, v, w, t, s, o} X R K).moduleHom
              (liftComplex.{u, v, w, t, s} X K) 0).symm
              ((CompDG.{u, v, w, t, s, o} X R).id (liftComplex.{u, v, w, t, s} X K))) y) := by
  let : (SheafOfModules.forget.{max u v w t s} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Full :=
    (SheafOfModules.fullyFaithfulForget.{max u v w t s}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).full
  let : (SheafOfModules.forget.{max u v w t s}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Faithful :=
    (SheafOfModules.fullyFaithfulForget.{max u v w t s}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).faithful
  let G := (SheafOfModules.forget.{max u v w t s}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let e := regularSectionwiseEvalHom.{u, v, w, t, s, o} X R K D
  have : IsIso e := regularSectionwiseEvalHom_isIso.{u, v, w, t, s, o} X R K D
  obtain ⟨g, hg, hu⟩ := D.sectionwiseUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) (liftComplex.{u, v, w, t, s} X K) e
  let j : HomologicalComplex.Hom (liftComplex.{u, v, w, t, s} X K) (D.functor.obj
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))) := G.preimage
    (inv e ≫ D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)))
  have hj : G.map j = inv e ≫ D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) := G.map_preimage _
  refine ⟨j, ⟨g, ?_, ?_⟩, ?_⟩
  · apply G.map_injective
    rw [Functor.map_comp, hj, Category.assoc, hg]
    simp
  · obtain ⟨g', hg', hu'⟩ := D.sectionwiseUniversal ((Rep.{u, v, w, t, s, o} X R K).functor.obj
      (liftComplex.{u, v, w, t, s} X K)) (D.functor.obj ((Rep.{u, v, w, t, s, o} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)))
      (D.sectionwiseToSheaf ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s}
        X K)))
    exact (hu' _ (by
      change D.sectionwiseToSheaf _ ≫ G.map (g ≫ j) = _
      rw [Functor.map_comp, ← Category.assoc, hg, hj]
      simp)).trans (hu' _ (by simp)).symm
  · intro q U y
    have h := congrArg (fun φ => ((φ.f q).app U) y) hj
    change ((j.f q).val.app U) y = _ at h
    rw [h]
    change HEq (((D.sectionwiseToSheaf _).f q).app U (((inv e).f q).app U y)) _
    rw [regularSectionwiseEvalHom_inv_apply.{u, v, w, t, s, o} X R K D q U y,
      regularSectionwiseUnit_apply, D.pure_eq_sectionwise]
    exact sectionwiseToSheaf_cast_heq.{u, v, w, t, s, o} X R K D _ U (zero_add q) _

private noncomputable def regularSheafIso :
    CategoryTheory.Iso (C := CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
      (D.functor.obj ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K))) (liftComplex.{u, v, w, t, s} X K) := by
  apply Classical.choice
  obtain ⟨j, hj, -⟩ := TensorWithComplexData.exists_isIso_pure_regular.{u, v, w, t, s, o} X R K D
  exact ⟨(asIso j).symm⟩

end RegularInverse

end

private noncomputable def tensorSheafified
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) :
    CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ :=
  (complexSheafification.{u, v, w, t, s} X).obj
    (tensorSectionwise.{u, v, w, t, s, o} X R K M)

private noncomputable def tensorSectionwiseUnit
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) :
    tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (tensorSheafified.{u, v, w, t, s, o} X R K M) :=
  (complexSheafificationAdjunction.{u, v, w, t, s} X).unit.app
    (tensorSectionwise.{u, v, w, t, s, o} X R K M)

private lemma tensorSectionwiseUnit_universal
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (f : tensorSectionwise.{u, v, w, t, s, o} X R K M ⟶
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :
    ∃! g : tensorSheafified.{u, v, w, t, s, o} X R K M ⟶ P,
      tensorSectionwiseUnit.{u, v, w, t, s, o} X R K M ≫
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g = f :=
  complexSheafification_universal.{u, v, w, t, s} X
    (tensorSectionwise.{u, v, w, t, s, o} X R K M) P f

private noncomputable def tensorSheafifiedPure
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (p q : ℤ) (U : X.Cᵒᵖ) :
    M.grading p →ₗ[ℤ] tensorSections.{u, v, w, t, s} X K U q →ₗ[ℤ]
      (((tensorSheafified.{u, v, w, t, s, o} X R K M).X (p + q)).val.obj U) := by
  let e : TensorDegree.{u, v, w, t, s, o} X R K M U (p + q) →ₗ[ℤ]
      (((tensorSheafified.{u, v, w, t, s, o} X R K M).X (p + q)).val.obj U) :=
    ((((complexSheafificationAdjunction.{u, v, w, t, s} X).unit.app
      (tensorSectionwise.{u, v, w, t, s, o} X R K M)).f (p + q)).app U).hom.restrictScalars ℤ
  exact (tensorDegreePure.{u, v, w, t, s, o} X R K M U (p + q) p q rfl).compr₂ e

private noncomputable def tensorPresheafCochain
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) :
    CochainComplex.HomComplex.Cochain
      (tensorSectionwise.{u, v, w, t, s, o} X R K L)
      (tensorSectionwise.{u, v, w, t, s, o} X R K M) n :=
  CochainComplex.HomComplex.Cochain.mk
    (fun d e h => tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h)

private lemma tensorPresheafCochain_add
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f g : (dgCategory _).Hom L M n) :
    tensorPresheafCochain.{u, v, w, t, s, o} X R K (f + g) =
      tensorPresheafCochain.{u, v, w, t, s, o} X R K f +
        tensorPresheafCochain.{u, v, w, t, s, o} X R K g := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro d e h
  change tensorPresheafMap.{u, v, w, t, s, o} X R K (f + g) d e h =
    tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h +
      tensorPresheafMap.{u, v, w, t, s, o} X R K g d e h
  exact tensorPresheafMap_add.{u, v, w, t, s, o} X R K f g d e h

private lemma tensorPresheafCochain_zsmul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (a : ℤ) (f : (dgCategory _).Hom L M n) :
    tensorPresheafCochain.{u, v, w, t, s, o} X R K (a • f) =
      a • tensorPresheafCochain.{u, v, w, t, s, o} X R K f := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro d e h
  change tensorPresheafMap.{u, v, w, t, s, o} X R K (a • f) d e h =
    a • tensorPresheafMap.{u, v, w, t, s, o} X R K f d e h
  exact tensorPresheafMap_zsmul.{u, v, w, t, s, o} X R K a f d e h

private lemma tensorPresheafCochain_id
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) :
    tensorPresheafCochain.{u, v, w, t, s, o} X R K ((dgCategory _).id M) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (tensorSectionwise.{u, v, w, t, s, o} X R K M)) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro d e h
  have he : e = d := by omega
  cases he
  simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
    HomologicalComplex.id_f]
  ext U z
  change tensorDegreeMap.{u, v, w, t, s, o} X R K ((dgCategory _).id M) U d d
      (add_zero d) z = z
  rw [tensorDegreeMap_id]
  rfl

private lemma tensorPresheafCochain_comp
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M N : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {m n k : ℤ} (hmn : m + n = k)
    (g : (dgCategory _).Hom M N m) (f : (dgCategory _).Hom L M n) :
    tensorPresheafCochain.{u, v, w, t, s, o} X R K ((dgCategory _).comp hmn g f) =
      (tensorPresheafCochain.{u, v, w, t, s, o} X R K f).comp
        (tensorPresheafCochain.{u, v, w, t, s, o} X R K g) (by omega) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro d j hdj
  let e := d + n
  rw [CochainComplex.HomComplex.Cochain.comp_v
    (tensorPresheafCochain.{u, v, w, t, s, o} X R K f)
    (tensorPresheafCochain.{u, v, w, t, s, o} X R K g)
    (by omega : n + m = k) d e j rfl (by omega)]
  ext U z
  change tensorDegreeMap.{u, v, w, t, s, o} X R K ((dgCategory _).comp hmn g f)
      U d j (by omega) z =
    (tensorDegreeMap.{u, v, w, t, s, o} X R K g U e j (by omega))
      ((tensorDegreeMap.{u, v, w, t, s, o} X R K f U d e rfl) z)
  exact LinearMap.congr_fun
    (tensorDegreeMap_comp.{u, v, w, t, s, o} X R K hmn g f U d e j rfl (by omega)) z

private noncomputable def tensorSheafifiedCochain
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) :
    CochainComplex.HomComplex.Cochain
      (tensorSheafified.{u, v, w, t, s, o} X R K L)
      (tensorSheafified.{u, v, w, t, s, o} X R K M) n :=
  by
    let : (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).left_adjoint_additive
    exact (tensorPresheafCochain.{u, v, w, t, s, o} X R K f).map
      (PresheafOfModules.sheafification.{max u v w t s}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))

private lemma tensorSheafifiedCochain_add
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f g : (dgCategory _).Hom L M n) :
    tensorSheafifiedCochain.{u, v, w, t, s, o} X R K (f + g) =
      tensorSheafifiedCochain.{u, v, w, t, s, o} X R K f +
        tensorSheafifiedCochain.{u, v, w, t, s, o} X R K g := by
  unfold tensorSheafifiedCochain
  rw [tensorPresheafCochain_add, CochainComplex.HomComplex.Cochain.map_add]
  rfl

private lemma tensorSheafifiedCochain_zsmul
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (a : ℤ) (f : (dgCategory _).Hom L M n) :
    tensorSheafifiedCochain.{u, v, w, t, s, o} X R K (a • f) =
      a • tensorSheafifiedCochain.{u, v, w, t, s, o} X R K f := by
  let : (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).left_adjoint_additive
  unfold tensorSheafifiedCochain
  rw [tensorPresheafCochain_zsmul]
  apply CochainComplex.HomComplex.Cochain.ext
  intro d e h
  change (PresheafOfModules.sheafification.{max u v w t s}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (a • (tensorPresheafCochain.{u, v, w, t, s, o} X R K f).v d e h) =
    a • (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      ((tensorPresheafCochain.{u, v, w, t, s, o} X R K f).v d e h)
  exact (PresheafOfModules.sheafification.{max u v w t s}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map_zsmul

private lemma tensorSheafifiedCochain_id
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj) :
    tensorSheafifiedCochain.{u, v, w, t, s, o} X R K ((dgCategory _).id M) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (tensorSheafified.{u, v, w, t, s, o} X R K M)) := by
  unfold tensorSheafifiedCochain
  rw [tensorPresheafCochain_id, CochainComplex.HomComplex.Cochain.map_ofHom]
  simp
  rfl

private lemma tensorSheafifiedCochain_comp
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M N : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {m n k : ℤ} (hmn : m + n = k)
    (g : (dgCategory _).Hom M N m) (f : (dgCategory _).Hom L M n) :
    tensorSheafifiedCochain.{u, v, w, t, s, o} X R K ((dgCategory _).comp hmn g f) =
      (tensorSheafifiedCochain.{u, v, w, t, s, o} X R K f).comp
        (tensorSheafifiedCochain.{u, v, w, t, s, o} X R K g) (by omega) := by
  let : (PresheafOfModules.sheafification.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{max u v w t s}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).left_adjoint_additive
  unfold tensorSheafifiedCochain
  rw [tensorPresheafCochain_comp, CochainComplex.HomComplex.Cochain.map_comp]
  rfl

private lemma tensorSheafifiedCochain_d_of_presheaf
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n)
    (h : tensorPresheafCochain.{u, v, w, t, s, o} X R K ((dgCategory _).d f) =
      CochainComplex.HomComplex.δ n (n + 1)
        (tensorPresheafCochain.{u, v, w, t, s, o} X R K f)) :
    tensorSheafifiedCochain.{u, v, w, t, s, o} X R K ((dgCategory _).d f) =
      (CompDG.{u, v, w, t, s, o} X R).d
        (tensorSheafifiedCochain.{u, v, w, t, s, o} X R K f) := by
  unfold tensorSheafifiedCochain
  rw [h, ← CochainComplex.HomComplex.δ_map]
  rfl

universe w'

private noncomputable def liftGraded {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, v, w} A) (N : DifferentialGradedModule.{u, v, w'} A)
    (f : ∀ p, M.grading p →ₗ[R] N.grading p) : M.M →ₗ[R] N.M :=
  (DirectSum.toModule R ℤ N.M (fun p => (N.grading p).subtype.comp (f p))).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

private lemma liftGraded_apply {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, v, w} A) (N : DifferentialGradedModule.{u, v, w'} A)
    (f : ∀ p, M.grading p →ₗ[R] N.grading p) (p : ℤ) (x : M.grading p) :
    liftGraded M N f x = (f p x : N.M) := by
  simp [liftGraded]

private noncomputable def homOfGraded {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, v, w} A) (N : DifferentialGradedModule.{u, v, w'} A)
    (f : ∀ p, M.grading p →ₗ[R] N.grading p)
    (hf : ∀ p n (x : M.grading p) (a : A.grading n),
      (f (p + n) ⟨MulOpposite.op (a : A.A) • (x : M.M), M.smul_mem p n x a x.property a.property⟩ :
          N.M) =
        MulOpposite.op (a : A.A) • (f p x : N.M))
    (hd : ∀ p (x : M.grading p),
      (f (p + 1) ⟨M.d x, M.d_mem p x x.property⟩ : N.M) = N.d (f p x)) :
    DifferentialGradedModule.Hom M N where
  toFun := liftGraded M N f
  map_grading p x hx := by
    rw [liftGraded_apply M N f p ⟨x, hx⟩]
    exact (f p ⟨x, hx⟩).property
  map_smul x a := by
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | @homogeneous p x =>
      induction a using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | add a b ha hb => simp only [MulOpposite.op_add, add_smul, map_add, ha, hb]
      | @homogeneous n a =>
        rw [liftGraded_apply M N f p x,
          liftGraded_apply M N f (p+n) ⟨_, M.smul_mem p n x a x.property a.property⟩]
        exact hf p n x a
  map_d := by
    apply DirectSum.decompose_lhom_ext M.grading
    intro p
    ext x
    change liftGraded M N f (M.d x) = N.d (liftGraded M N f x)
    rw [liftGraded_apply M N f p x,
      liftGraded_apply M N f (p+1) ⟨_, M.d_mem p x x.property⟩]
    exact hd p x

private def homCocycle {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, v} R}
    {M N : DifferentialGradedModule.{u, v, w} A} (f : DifferentialGradedModule.Hom M N) :
    (dgCategory A).Cocycle M N := by
  refine ⟨⟨f.toFun, ?_, ?_⟩, ?_⟩
  · intro p x hx
    simpa using f.map_grading p x hx
  · intro a x
    exact f.map_smul x a
  · apply Subtype.ext
    rw [dgCategory_d_val]
    change N.d.comp f.toFun - gradedSign R 0 • f.toFun.comp M.d = 0
    simp only [gradedSign, Int.natAbs_zero, pow_zero, one_smul, sub_eq_zero]
    exact f.map_d.symm


private def cocycleHom {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, v} R}
    {M N : DifferentialGradedModule.{u, v, w} A} (f : (dgCategory A).Cocycle M N) :
    DifferentialGradedModule.Hom M N where
  toFun := f.1.1
  map_smul x a := f.1.2.2 a x
  map_grading n x hx := by simpa only [add_zero] using f.1.2.1 n x hx
  map_d := by
    have h := congrArg Subtype.val f.2
    change N.d.comp f.1.1 - gradedSign R 0 • f.1.1.comp M.d = 0 at h
    simp only [gradedSign, Int.natAbs_zero, pow_zero, one_smul, sub_eq_zero] at h
    exact h.symm

private def cocycleHomEquiv {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, v} R}
    (M N : DifferentialGradedModule.{u, v, w} A) :
    (dgCategory A).Cocycle M N ≃ DifferentialGradedModule.Hom M N where
  toFun := cocycleHom
  invFun := homCocycle
  left_inv f := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv f := by apply DifferentialGradedModule.Hom.ext; rfl


private noncomputable def evaluationEvalMap (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (d p q : ℤ) (h : p + q = d) (U : X.Cᵒᵖ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p) :
    (((liftComplex.{u, v, w, t, s} X K).X q).val.obj U)
      →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U]
      ((P.X d).val.obj U) :=
  ((((Rep.{u, v, w, t, s, o} X R K).moduleHom P p x).v q d (by omega)).val.app U).hom

private lemma evaluationEvalMap_natural (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (d p q : ℤ) (h : p + q = d) {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p) (y :
      ((liftComplex.{u, v, w, t, s} X
        K).X q).val.obj U) :
    (P.X d).val.map f (evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U x y) =
      evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h V x (((liftComplex.{u, v, w, t, s} X K).X
          q).val.map f y) := by
  have hn := (((Rep.{u, v, w, t, s, o} X R K).moduleHom P p x).v q d (by omega)).val.naturality f
  have heq := congrArg (fun g => g y) hn
  change ((((Rep.{u, v, w, t, s, o} X R K).moduleHom P p x).v q d (by omega)).val.app V).hom
      (((liftComplex.{u, v, w, t, s} X K).X q).val.map f y) =
    ((P.X d).val.map f)
      (((((Rep.{u, v, w, t, s, o} X R K).moduleHom P p x).v q d (by omega)).val.app U).hom y) at heq
  exact heq.symm

private lemma evaluationEvalMap_d (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (p q : ℤ) (U : X.Cᵒᵖ)
    (x : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p) (y :
      ((liftComplex.{u, v, w, t, s} X
        K).X q).val.obj U) :
    ((P.d (p + q) (p + q + 1)).val.app U)
        (evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q) p q (by omega) U x y) =
      evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q + 1) (p + 1) q (by omega) U
          ⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj P).d x,
            ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).d_mem p x x.property⟩ y +
        (p.negOnePow : ℤ) •
          evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q + 1) p (q + 1) (by omega) U x
            ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y) := by
  let x' : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading (p + 1) :=
    ⟨((Rep.{u, v, w, t, s, o} X R K).functor.obj P).d x,
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).d_mem p x x.property⟩
  have hd := congrArg
    (fun f => ((f.v q (p + q + 1) (by omega)).val.app U) y)
    ((Rep.{u, v, w, t, s, o} X R K).module_d P p x)
  change evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q + 1) (p + 1) q (by omega) U x' y =
      ((((CompDG.{u, v, w, t, s, o} X R).d (((Rep.{u, v, w, t, s, o} X R K).moduleHom P p) x)).v q
        (p + q +
          1) (by omega)).val.app U) y
    at hd
  rw [CochainComplex.dgCategoryLinear_d_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
    (((Rep.{u, v, w, t, s, o} X R K).moduleHom P p) x) q (p + q + 1) (by omega)
      (p + q) (q + 1) (by omega) (by omega)] at hd
  rw [Units.smul_def] at hd
  simp only [SheafOfModules.add_val, SheafOfModules.comp_val,
    PresheafOfModules.add_app, PresheafOfModules.comp_app] at hd
  rw [sheafModule_zsmul_val] at hd
  simp only [PresheafOfModules.zsmul_app, 
    ModuleCat.hom_add, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp] at hd
  rw [Int.negOnePow_succ] at hd
  change ((P.d (p + q) (p + q + 1)).val.app U)
      (evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q) p q (by omega) U x y) =
    evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q + 1) (p + 1) q (by omega) U x' y +
      (p.negOnePow : ℤ) •
        evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q + 1) p (q + 1) (by omega) U x
          ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)
  rw [hd]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    ]
  dsimp only [evaluationEvalMap]
  let b := ((P.d (p + q) (p + q + 1)).val.app U)
    (evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q) p q (by omega) U x y)
  let c := evaluationEvalMap.{u, v, w, t, s, o} X R K P (p + q + 1) p (q + 1) (by omega) U x
    ((((liftComplex.{u, v, w, t, s} X K).d q (q + 1)).val.app U) y)
  change b = (b + (-p.negOnePow : ℤ) • c) + p.negOnePow • c
  have hcancel : (-p.negOnePow : ℤ) • c + p.negOnePow • c = 0 := by
    have hs : (-p.negOnePow : ℤ) = -(p.negOnePow : ℤ) := by simp
    rw [hs, neg_zsmul]
    exact neg_add_cancel _
  calc
    b = b + 0 := by simp
    _ = b + ((-p.negOnePow : ℤ) • c + p.negOnePow • c) := by rw [hcancel]
    _ = (b + (-p.negOnePow : ℤ) • c) + p.negOnePow • c :=
      (add_assoc b ((-p.negOnePow : ℤ) • c) (p.negOnePow • c)).symm

private noncomputable def evaluationEvalAddHom (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (d p q : ℤ) (h : p + q = d) (U : X.Cᵒᵖ) :
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading p →+
      ((((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) →ₗ[ℤ] ((P.X d).val.obj U)) where
  toFun x := (evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U x).restrictScalars ℤ
  map_zero' := by
    ext y
    simp [evaluationEvalMap]
    rfl
  map_add' := by
    intro x y
    ext z
    simp [evaluationEvalMap]

private noncomputable def evaluationBalanced (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ)
    (U : X.Cᵒᵖ) (d : ℤ) :
    BalancedDegreeMap.{u, v, w, t, s, o, max u v w t s} X R K ((Rep.{u, v, w, t, s, o} X R
      K).functor.obj P)
        U d
      (ModuleCat.of ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
        ((P.X d).val.obj U)) where
  toFun p q h := (evaluationEvalAddHom.{u, v, w, t, s, o} X R K P d p q h U).toIntLinearMap
  map_smul := by
    intro p q h x r y
    change ((evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U x) (r • y)) =
      r • ((evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U x) y)
    exact (evaluationEvalMap.{u, v, w, t, s, o} X R K P d p q h U x).map_smul r y
  balance := by
    intro p q n h₁ h₂ x a y
    let x' : ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).grading (p + n) :=
      ⟨MulOpposite.op (a : (Rep.{u, v, w, t, s, o} X R K).algebra.A) • (x : ((Rep.{u, v, w, t, s, o}
        X R
          K).functor.obj P).M),
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj P).smul_mem p n x a x.property a.property⟩
    obtain ⟨z, hz, hcomp⟩ := (Rep.{u, v, w, t, s, o} X R K).module_action P p n (p + n) (by omega) x
      a
    have hx : x' = z := by
      apply Subtype.ext
      exact hz.symm
    have hm := congrArg (fun z => (Rep.{u, v, w, t, s, o} X R K).moduleHom P (p + n) z) hx
    change evaluationEvalMap.{u, v, w, t, s, o} X R K P d (p + n) q h₁ U x' y =
      evaluationEvalMap.{u, v, w, t, s, o} X R K P d p (q + n) h₂ U x
        (((((Rep.{u, v, w, t, s, o} X R K).algebraHom n a).v q (q + n) (by omega)).val.app U).hom y)
    simp only [evaluationEvalMap]
    rw [hm, hcomp]
    rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R)
      (h := (show p + n = p + n from by omega))
      (g := ((Rep.{u, v, w, t, s, o} X R K).moduleHom P p) x)
      (f := ((Rep.{u, v, w, t, s, o} X R K).algebraHom n) a)
      q (q + n) d (by omega) (by omega)]
    rfl



attribute [local instance_reducible] tensorSectionwise tensorDegreePresheaf tensorSheafified
  tensorPresheafMap tensorPresheafDifferential

private lemma tensorPresheafCochain_d
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {L M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n : ℤ} (f : (dgCategory _).Hom L M n) :
    tensorPresheafCochain.{u, v, w, t, s, o} X R K ((dgCategory _).d f) =
      CochainComplex.HomComplex.δ n (n + 1)
        (tensorPresheafCochain.{u, v, w, t, s, o} X R K f) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro d e h
  have he : e = d + n + 1 := by omega
  cases he
  rw [CochainComplex.HomComplex.δ_v n (n + 1) rfl _ d (d + n + 1) h
    (d + n) (d + 1) (by omega) rfl]
  change tensorPresheafMap.{u, v, w, t, s, o} X R K ((dgCategory _).d f) d (d + n + 1) h =
    tensorPresheafMap.{u, v, w, t, s, o} X R K f d (d + n) _ ≫
      CochainComplex.of.d _ (tensorPresheafDifferential.{u, v, w, t, s, o} X R K M) (d + n) (d + n +
        1) +
    (n + 1).negOnePow •
      (CochainComplex.of.d _ (tensorPresheafDifferential.{u, v, w, t, s, o} X R K L) d (d + 1) ≫
        tensorPresheafMap.{u, v, w, t, s, o} X R K f (d + 1) (d + n + 1) _)
  rw [CochainComplex.of_d, CochainComplex.of_d]
  rw [Units.smul_def]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hd := LinearMap.congr_fun (tensorDegreeMap_d.{u, v, w, t, s, o} X R K f U d) z
  change tensorDegreeMap.{u, v, w, t, s, o} X R K ((dgCategory _).d f) U d (d+n+1) _ z =
    tensorDegreeDifferential.{u, v, w, t, s, o} X R K M U (d+n)
      (tensorDegreeMap.{u, v, w, t, s, o} X R K f U d (d+n) _ z) +
    ((n+1).negOnePow : ℤ) •
      (tensorDegreeMap.{u, v, w, t, s, o} X R K f U (d+1) (d+n+1) _
        (tensorDegreeDifferential.{u, v, w, t, s, o} X R K L U d z)) at hd
  simpa only [PresheafOfModules.add_app, PresheafOfModules.zsmul_app,
    PresheafOfModules.comp_app, ModuleCat.hom_add, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    tensorPresheafMap, tensorPresheafDifferential] using hd

end AlgebraicGeometry.RingedSite
