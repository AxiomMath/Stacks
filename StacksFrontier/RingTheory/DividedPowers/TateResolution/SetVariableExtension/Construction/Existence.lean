module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.OneVariableLift
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.OneVariableLift
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.FiniteVariable
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.FiniteVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.DirectLimit
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.DirectLimit
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage

/-!
# Existence of the set-variable divided power extension

This file transports a graded algebra with divided powers along an algebra equivalence, which
moves the direct limit of the finite-variable stages to the required universe, identifies each
successor stage with the one-variable extension of its predecessor, and proves the main result
`exists_setVariableDividedPowerExtension` (Tag 0F4I).
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

attribute [local instance] prodGradedAlgebra prodStrictlyGradedComm

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

attribute [local instance] finiteVariable_directedSystem

private abbrev ringEquivAlgebra {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {C : Type w} [Ring C]
    (e : A.carrier ≃+* C) : Algebra R C :=
  (e.toRingHom.comp (algebraMap R A.carrier)).toAlgebra' (by
    intro r x
    obtain ⟨a,rfl⟩ := e.surjective x
    change e ((algebraMap R A.carrier) r) * e a = e a * e ((algebraMap R A.carrier) r)
    simpa only [map_mul] using congrArg e (Algebra.commutes r a))

private def ringEquivAlgEquiv {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {C : Type w} [Ring C]
    (e : A.carrier ≃+* C) :
    letI := ringEquivAlgebra A e
    A.carrier ≃ₐ[R] C := by
  let := ringEquivAlgebra A e
  exact { e with commutes' := fun _ => rfl }

section Transport
open scoped DirectSum
variable {R : Type u} [CommRing R] (A : GradedDPAlgebra.{u, v} R)
variable {C : Type w} [Ring C] [Algebra R C] (e : A.carrier ≃ₐ[R] C)

private abbrev transportedGrade (A : GradedDPAlgebra.{u, v} R)
    (e : A.carrier ≃ₐ[R] C) (m : ℕ) : Submodule R C :=
  (A.grade m).comap e.symm.toLinearMap

@[instance_reducible] private noncomputable def transportedGradedAlgebra
    (A : GradedDPAlgebra.{u, v} R) (e : A.carrier ≃ₐ[R] C) :
    GradedAlgebra (transportedGrade A e) := by
  classical
  let P := transportedGrade A e
  let l (m : ℕ) : A.grade m →+ P m :=
    { toFun := fun x => ⟨e x, by
        change e.symm (e x) ∈ A.grade m
        simpa only [AlgEquiv.symm_apply_apply] using x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  let dc : C →+ ⨁ m, P m :=
    ((DirectSum.toAddMonoid fun m => (DirectSum.of _ m).comp (l m)).comp
      (DirectSum.decomposeAddEquiv A.grade).toAddMonoidHom).comp e.symm.toRingEquiv.toAddMonoidHom
  have hc {m : ℕ} {x : C} (hx : x ∈ P m) :
      dc x = DirectSum.of _ m ⟨x,hx⟩ := by
    have hx' : e.symm x ∈ A.grade m := hx
    change DirectSum.toAddMonoid _ (DirectSum.decompose A.grade (e.symm x)) = _
    rw [DirectSum.decompose_of_mem A.grade hx', DirectSum.toAddMonoid_of]
    exact congrArg (DirectSum.of _ m) (Subtype.ext (e.apply_symm_apply x))
  have hdc (a : A.carrier) : DirectSum.coeAddMonoidHom P (dc (e a)) = e a := by
    induction a using DirectSum.Decomposition.inductionOn A.grade with
    | zero => simp only [map_zero]
    | homogeneous a =>
      rw [hc (show e a ∈ P _ from by
        change e.symm (e a) ∈ A.grade _
        simpa only [AlgEquiv.symm_apply_apply] using a.property), DirectSum.coeAddMonoidHom_of]
    | add a b ha hb => simp only [map_add, ha, hb]
  let dec := DirectSum.Decomposition.ofAddHom P dc
    (by ext x; obtain ⟨a,rfl⟩ := e.surjective x; exact hdc a)
    (by
      apply DirectSum.addHom_ext
      intro m x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      exact hc x.property)
  exact { dec with
    one_mem := by change e.symm 1 ∈ A.grade 0; simpa only [map_one] using
      (SetLike.GradedOne.one_mem : (1 : A.carrier) ∈ A.grade 0)
    mul_mem := by
      intro i j x y hx hy
      change e.symm (x*y) ∈ A.grade (i+j)
      rw [map_mul]
      exact SetLike.mul_mem_graded hx hy }

attribute [local instance] transportedGradedAlgebra

private theorem transportedStrictlyGradedComm (A : GradedDPAlgebra.{u, v} R)
    (e : A.carrier ≃ₐ[R] C) : IsStrictlyGradedComm (transportedGrade A e) where
  graded_comm hx hy := by
    apply e.symm.injective
    simpa only [map_mul, map_smul, AlgEquiv.toLinearMap_apply] using
      IsStrictlyGradedComm.graded_comm (𝒜 := A.grade) hx hy
  odd_sq_zero hx := by
    apply e.symm.injective
    simpa only [map_pow, map_zero, AlgEquiv.toLinearMap_apply] using
      IsStrictlyGradedComm.odd_sq_zero (𝒜 := A.grade) hx

attribute [local instance] transportedStrictlyGradedComm

private theorem exists_transportedDividedPowers (A : GradedDPAlgebra.{u, v} R)
    (e : A.carrier ≃ₐ[R] C) :
    ∃! δ : DividedPowerStructure (transportedGrade A e),
      ∀ n a, a ∈ positiveEvenPart A.grade → δ.dpow n (e a) = e (A.gamma.dpow n a) := by
  obtain ⟨δ,hδ,hu⟩ := existsUnique_dividedPowerStructure_of_finiteStages
    (fun _ : Finset Unit => A.carrier) (fun _ => A.grade) (fun _ => A.gamma)
    (transportedGrade A e) (fun _ => AlgHom.id R A.carrier) (fun _ => e.toAlgHom)
    (fun _ _ => rfl)
    (fun _ m a ha => by change e.symm (e a) ∈ A.grade m; simpa using ha)
    (fun m x hx => ⟨∅,e.symm x,hx,e.apply_symm_apply x⟩)
    (fun S T x y h => ⟨S ∪ T,Finset.subset_union_left,Finset.subset_union_right,e.injective h⟩)
    (fun _ _ _ h => h) (fun _ _ _ _ => rfl)
  exact ⟨δ,hδ ∅,fun ε hε => hu ε (fun _ => hε)⟩

@[reducible] private noncomputable def transportedDPAlgebra (A : GradedDPAlgebra.{u, v} R)
    (e : A.carrier ≃ₐ[R] C) : GradedDPAlgebra.{u, w} R where
  carrier := C
  ring := inferInstance
  algebra := inferInstance
  grade := transportedGrade A e
  graded := inferInstance
  strict := inferInstance
  gamma := (exists_transportedDividedPowers A e).choose

private noncomputable def transportForward (A : GradedDPAlgebra.{u, v} R)
    (e : A.carrier ≃ₐ[R] C) : GradedDPHom A (transportedDPAlgebra A e) where
  hom := e.toAlgHom
  map_grade := fun m a ha => by change e.symm (e a) ∈ A.grade m; simpa using ha
  map_dpow := (exists_transportedDividedPowers A e).choose_spec.1

private noncomputable def transportBackward (A : GradedDPAlgebra.{u, v} R)
    (e : A.carrier ≃ₐ[R] C) : GradedDPHom (transportedDPAlgebra A e) A where
  hom := e.symm.toAlgHom
  map_grade := fun _ _ ha => ha
  map_dpow := by
    intro n x hx
    have ha := algHom_mem_positiveEvenPart (transportedGrade A e) A.grade e.symm.toAlgHom
      (fun _ _ h => h) hx
    apply e.injective
    change e (A.gamma.dpow n (e.symm x)) =
      e (e.symm ((transportedDPAlgebra A e).gamma.dpow n x))
    simpa only [AlgEquiv.apply_symm_apply] using
      ((exists_transportedDividedPowers A e).choose_spec.1 n (e.symm x) ha).symm
end Transport

private theorem oneVariableExtension_hom_eq_id {R : Type u} [CommRing R]
    (X : GradedDPAlgebra.{u, v} R) (d : ℕ) (hd : 0 < d)
    (l : GradedDPHom (oneVariableExtension X d hd).algebra
      (oneVariableExtension X d hd).algebra)
    (hl : ∀ a, l.hom ((oneVariableExtension X d hd).coefficient.hom a) =
      (oneVariableExtension X d hd).coefficient.hom a)
    (ht : l.hom (oneVariableExtension X d hd).generator =
      (oneVariableExtension X d hd).generator) :
    l = GradedDPHom.id (oneVariableExtension X d hd).algebra := by
  obtain ⟨m,hm,hu⟩ := oneVariableExtension_existsUnique_lift X d hd
    (oneVariableExtension X d hd).algebra (oneVariableExtension X d hd).coefficient
    (oneVariableExtension X d hd).generator (oneVariableExtension X d hd).generator_mem
  exact (hu l ⟨hl,ht⟩).trans (hu (GradedDPHom.id _) ⟨fun _ => rfl,rfl⟩).symm

/-- If `g` lifts `f` and `k` lifts a left inverse `r` of `f` on one-variable extensions, then
`k ∘ g` is the identity. -/
private theorem oneVariableExtension_comp_eq_id {R : Type u} [CommRing R]
    {A : GradedDPAlgebra.{u, v} R} {B : GradedDPAlgebra.{u, w} R}
    (f : GradedDPHom A B) (r : GradedDPHom B A) (hr : ∀ a, r.hom (f.hom a) = a)
    (d : ℕ) (hd : 0 < d)
    (g : GradedDPHom (oneVariableExtension A d hd).algebra (oneVariableExtension B d hd).algebra)
    (k : GradedDPHom (oneVariableExtension B d hd).algebra (oneVariableExtension A d hd).algebra)
    (hg₁ : ∀ a, g.hom ((oneVariableExtension A d hd).coefficient.hom a) =
      (oneVariableExtension B d hd).coefficient.hom (f.hom a))
    (hg₂ : g.hom (oneVariableExtension A d hd).generator = (oneVariableExtension B d hd).generator)
    (hk₁ : ∀ b, k.hom ((oneVariableExtension B d hd).coefficient.hom b) =
      (oneVariableExtension A d hd).coefficient.hom (r.hom b))
    (hk₂ : k.hom (oneVariableExtension B d hd).generator =
      (oneVariableExtension A d hd).generator) :
    k.comp g = GradedDPHom.id (oneVariableExtension A d hd).algebra := by
  apply oneVariableExtension_hom_eq_id A d hd
  · intro a
    change k.hom (g.hom ((oneVariableExtension A d hd).coefficient.hom a)) = _
    rw [hg₁, hk₁, hr]
  · change k.hom (g.hom (oneVariableExtension A d hd).generator) = _
    rw [hg₂, hk₂]

private theorem oneVariableExtension_inverse_lifts {R : Type u} [CommRing R]
    {A : GradedDPAlgebra.{u, v} R} {B : GradedDPAlgebra.{u, w} R}
    (f : GradedDPHom A B) (r : GradedDPHom B A)
    (hr : ∀ a, r.hom (f.hom a) = a) (hf : ∀ b, f.hom (r.hom b) = b)
    (d : ℕ) (hd : 0 < d) :
    let E := oneVariableExtension A d hd
    let F := oneVariableExtension B d hd
    ∃ g : GradedDPHom E.algebra F.algebra,
    ∃ k : GradedDPHom F.algebra E.algebra,
      (∀ a, g.hom (E.coefficient.hom a) = F.coefficient.hom (f.hom a)) ∧
      g.hom E.generator = F.generator ∧
      (∀ x, k.hom (g.hom x) = x) ∧ (∀ y, g.hom (k.hom y) = y) := by
  let E := oneVariableExtension A d hd
  let F := oneVariableExtension B d hd
  obtain ⟨g,hg,_⟩ := oneVariableExtension_existsUnique_lift A d hd F.algebra
    (F.coefficient.comp f) F.generator F.generator_mem
  obtain ⟨k,hk,_⟩ := oneVariableExtension_existsUnique_lift B d hd E.algebra
    (E.coefficient.comp r) E.generator E.generator_mem
  have hkg := oneVariableExtension_comp_eq_id f r hr d hd g k hg.1 hg.2 hk.1 hk.2
  have hgk := oneVariableExtension_comp_eq_id r f hf d hd k g hk.1 hk.2 hg.1 hg.2
  exact ⟨g,k,hg.1,hg.2,fun x => congrArg (fun l => l.hom x) hkg,
    fun x => congrArg (fun l => l.hom x) hgk⟩

private theorem GradedDPHom.map_dpow_of_inverse {R : Type u} [CommRing R]
    {A : GradedDPAlgebra.{u, v} R} {B : GradedDPAlgebra.{u, w} R}
    (f : GradedDPHom A B) (r : GradedDPHom B A)
    (hr : ∀ a, r.hom (f.hom a) = a) (n : ℕ) (a : A.carrier) :
    B.gamma.dpow n (f.hom a) = f.hom (A.gamma.dpow n a) := by
  by_cases ha : a ∈ positiveEvenPart A.grade
  · exact f.map_dpow n a ha
  · have hb : f.hom a ∉ positiveEvenPart B.grade := by
      intro h
      have := algHom_mem_positiveEvenPart B.grade A.grade r.hom r.map_grade h
      rw [hr] at this
      exact ha this
    rw [B.gamma.dpow_null hb,A.gamma.dpow_null ha,map_zero]

private theorem finiteVariableStage_map_mem {R : Type u} [CommRing R]
    {A : Type v} [Ring A] [Algebra R A]
    {B : GradedDPAlgebra.{u, w} R} {C : GradedDPAlgebra.{u, z} R}
    (f : GradedDPHom B C) (r : GradedDPHom C B) (hr : ∀ b, r.hom (f.hom b) = b)
    (ι : A →ₐ[R] B.carrier) {J : Type*} (T : J → B.carrier) (S : Finset J)
    {x : B.carrier} (hx : x ∈ finiteVariableStage B.gamma ι T S) :
    f.hom x ∈ finiteVariableStage C.gamma (f.hom.comp ι) (fun j => f.hom (T j)) S := by
  let Q := finiteVariableStage C.gamma (f.hom.comp ι) (fun j => f.hom (T j)) S
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a,rfl⟩ | ⟨j,hj,rfl | ⟨n,rfl⟩⟩
    · exact Subring.subset_closure (Or.inl ⟨a,rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨j,hj,Or.inl rfl⟩)
    · rw [← f.map_dpow_of_inverse r hr]
      exact Subring.subset_closure (Or.inr ⟨j,hj,Or.inr ⟨n,rfl⟩⟩)
  | zero => rw [map_zero]; exact Q.zero_mem
  | one => rw [map_one]; exact Q.one_mem
  | add a b ha hb ha' hb' => rw [map_add]; exact Q.add_mem ha' hb'
  | neg a ha ha' => rw [map_neg]; exact Q.neg_mem ha'
  | mul a b ha hb ha' hb' => rw [map_mul]; exact Q.mul_mem ha' hb'

private theorem setVariableStage_realization {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (C : GradedDPAlgebra.{u, z} R)
    (f : GradedDPHom (setVariableAlgebra A deg hdeg) C)
    (r : GradedDPHom C (setVariableAlgebra A deg hdeg))
    (hr : ∀ x, r.hom (f.hom x) = x) (_hf : ∀ y, f.hom (r.hom y) = y)
    (S : Finset J) :
    ∃ e : (finiteVariableAlgebra A deg hdeg S).carrier ≃+*
      finiteVariableStage C.gamma (f.hom.comp (setVariableCoefficient A deg hdeg).hom)
        (fun j => f.hom (setVariableGenerator A deg hdeg j)) S,
      ∀ x, (e x : C.carrier) = f.hom ((setVariableStageInclusion A deg hdeg S).hom x) := by
  let Q := finiteVariableStage C.gamma (f.hom.comp (setVariableCoefficient A deg hdeg).hom)
    (fun j => f.hom (setVariableGenerator A deg hdeg j)) S
  let i := f.comp (setVariableStageInclusion A deg hdeg S)
  have hi (x) : i.hom x ∈ Q := finiteVariableStage_map_mem f r hr _ _ S
    (setVariableStageInclusion_mem_finiteStage A deg hdeg S x)
  obtain ⟨s,hs⟩ := setVariableStageInclusion_exists_retraction A deg hdeg S
  let q := s.comp r
  have hqi (x) : q.hom (i.hom x) = x := by
    change s.hom (r.hom (f.hom ((setVariableStageInclusion A deg hdeg S).hom x))) = x
    rw [hr,hs]
  have hQ : Q ≤ i.hom.toRingHom.range := by
    apply Subring.closure_le.mpr
    rintro x (⟨a,rfl⟩ | ⟨j,hj,rfl | ⟨n,rfl⟩⟩)
    · refine ⟨(finiteVariableCoefficient A deg hdeg S).hom a, ?_⟩
      change f.hom ((setVariableStageInclusion A deg hdeg S).hom
        ((finiteVariableCoefficient A deg hdeg S).hom a)) = _
      rw [setVariableStageInclusion_coefficient]; rfl
    · refine ⟨finiteVariableGenerator A deg hdeg S ⟨j,hj⟩, ?_⟩
      change f.hom ((setVariableStageInclusion A deg hdeg S).hom
        (finiteVariableGenerator A deg hdeg S ⟨j,hj⟩)) = _
      rw [setVariableStageInclusion_generator]
    · refine ⟨(finiteVariableAlgebra A deg hdeg S).gamma.dpow n
        (finiteVariableGenerator A deg hdeg S ⟨j,hj⟩), ?_⟩
      change i.hom ((finiteVariableAlgebra A deg hdeg S).gamma.dpow n
        (finiteVariableGenerator A deg hdeg S ⟨j,hj⟩)) = _
      rw [← i.map_dpow_of_inverse q hqi]
      change C.gamma.dpow n (f.hom ((setVariableStageInclusion A deg hdeg S).hom
        (finiteVariableGenerator A deg hdeg S ⟨j,hj⟩))) = _
      rw [setVariableStageInclusion_generator]
  let k := i.hom.toRingHom.codRestrict Q hi
  have hk : Function.Bijective k := by
    constructor
    · exact fun x y h => (Function.LeftInverse.injective hqi) (congrArg Subtype.val h)
    · intro x
      obtain ⟨y,hy⟩ := hQ x.property
      exact ⟨y,Subtype.ext hy⟩
  exact ⟨RingEquiv.ofBijective k hk,fun _ => rfl⟩

private theorem setVariable_successor_realization {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (C : GradedDPAlgebra.{u, z} R)
    (f : GradedDPHom (setVariableAlgebra A deg hdeg) C)
    (r : GradedDPHom C (setVariableAlgebra A deg hdeg))
    (hr : ∀ x, r.hom (f.hom x) = x) (hf : ∀ y, f.hom (r.hom y) = y)
    (S : Finset J) (j : J) (hj : j ∉ S) :
    letI : DecidableEq J := Classical.decEq J
    let Q := fun S => finiteVariableStage C.gamma
      (f.hom.comp (setVariableCoefficient A deg hdeg).hom)
      (fun j => f.hom (setVariableGenerator A deg hdeg j)) S
    ∃ aS : Algebra R (Q S), letI := aS
    (∀ r : R, ((algebraMap R (Q S) r : Q S) : C.carrier) = algebraMap R C.carrier r) ∧
    ∃ Sᵢ : ℕ → Submodule R (Q S), ∃ gS : GradedAlgebra Sᵢ, letI := gS
    ∃ cS : IsStrictlyGradedComm Sᵢ, letI := cS
    ∃ δS : DividedPowerStructure Sᵢ,
      (∀ n (b : Q S), b ∈ positiveEvenPart Sᵢ →
        (δS.dpow n b : C.carrier) = C.gamma.dpow n b) ∧
      let B : GradedDPAlgebra R := ⟨Q S,inferInstance,aS,Sᵢ,gS,cS,δS⟩
      let E := oneVariableExtension B (deg j) (hdeg j)
      ∃ e : E.algebra.carrier ≃+* Q (insert j S),
        (∀ b : Q S, (e (E.coefficient.hom b) : C.carrier) = b) ∧
        (e E.generator : C.carrier) = f.hom (setVariableGenerator A deg hdeg j) ∧
        (∀ m x, x ∈ E.algebra.grade m ↔ (e x : C.carrier) ∈ C.grade m) ∧
        (∀ n x, x ∈ positiveEvenPart E.algebra.grade →
          C.gamma.dpow n (e x : C.carrier) = (e (E.algebra.gamma.dpow n x) : C.carrier)) := by
  classical
  let Q := fun S => finiteVariableStage C.gamma
    (f.hom.comp (setVariableCoefficient A deg hdeg).hom)
    (fun j => f.hom (setVariableGenerator A deg hdeg j)) S
  obtain ⟨eS,heS⟩ := setVariableStage_realization A deg hdeg C f r hr hf S
  obtain ⟨eT,heT⟩ := setVariableStage_realization A deg hdeg C f r hr hf (insert j S)
  let F := finiteVariableAlgebra A deg hdeg S
  let := ringEquivAlgebra F eS
  let a := ringEquivAlgEquiv F eS
  let B := transportedDPAlgebra F a
  let p := transportForward F a
  let q := transportBackward F a
  let inc := (f.comp (setVariableStageInclusion A deg hdeg S)).comp q
  have hinc (b : Q S) : inc.hom b = b := by
    change f.hom ((setVariableStageInclusion A deg hdeg S).hom (eS.symm b)) = b
    rw [← heS,eS.apply_symm_apply]
  refine ⟨inferInstance,?_,B.grade,B.graded,B.strict,B.gamma,?_,?_⟩
  · intro r
    exact (hinc (algebraMap R (Q S) r)).symm.trans (inc.hom.commutes r)
  · intro n b hb
    simpa only [hinc] using (inc.map_dpow n b hb).symm
  · obtain ⟨g,k,hg,hgt,hkg,hgk⟩ := oneVariableExtension_inverse_lifts q p
      (fun x => a.apply_symm_apply x) (fun x => a.symm_apply_apply x) (deg j) (hdeg j)
    obtain ⟨l,m,hl,hlt,hml,hlm⟩ := finiteVariable_insert_inverse_lifts A deg hdeg S j hj
    have hml' x : m.hom (l.hom x) = x := congrArg (fun t => t.hom x) hml
    have hlm' x : l.hom (m.hom x) = x := congrArg (fun t => t.hom x) hlm
    let L := l.comp g
    let M := k.comp m
    have hML (x) : M.hom (L.hom x) = x := by
      change k.hom (m.hom (l.hom (g.hom x))) = x
      rw [hml',hkg]
    have hLM (x) : L.hom (M.hom x) = x := by
      change l.hom (g.hom (k.hom (m.hom x))) = x
      rw [hgk,hlm']
    let e : (oneVariableExtension B (deg j) (hdeg j)).algebra.carrier ≃+* Q (insert j S) :=
      (RingEquiv.ofBijective L.hom.toRingHom
        ⟨Function.LeftInverse.injective hML,Function.RightInverse.surjective hLM⟩).trans eT
    let i := (f.comp (setVariableStageInclusion A deg hdeg (insert j S))).comp L
    have hei (x) : (e x : C.carrier) = i.hom x := heT _
    obtain ⟨s,hs⟩ := setVariableStageInclusion_exists_retraction A deg hdeg (insert j S)
    let back := M.comp (s.comp r)
    have hback (x) : back.hom (i.hom x) = x := by
      change M.hom (s.hom (r.hom (f.hom
        ((setVariableStageInclusion A deg hdeg (insert j S)).hom (L.hom x))))) = x
      rw [hr,hs,hML]
    refine ⟨e,?_,?_,?_,?_⟩
    · intro b
      rw [hei]
      change f.hom ((setVariableStageInclusion A deg hdeg (insert j S)).hom
        (l.hom (g.hom ((oneVariableExtension B (deg j) (hdeg j)).coefficient.hom b)))) = b
      rw [hg,hl,setVariableStageInclusion_map]
      exact hinc b
    · rw [hei]
      change f.hom ((setVariableStageInclusion A deg hdeg (insert j S)).hom
        (l.hom (g.hom (oneVariableExtension B (deg j) (hdeg j)).generator))) = _
      rw [hgt,hlt,setVariableStageInclusion_generator]
    · intro m x
      rw [hei]
      constructor
      · exact i.map_grade m x
      · intro hx
        simpa only [hback] using back.map_grade m (i.hom x) hx
    · intro n x hx
      simp only [hei]
      exact i.map_dpow n x hx

/-- A set of positive-degree variables has a free strictly graded-commutative algebra with
divided powers over a graded divided-power algebra. Every element involves only finitely many
variables (including their divided powers). The universal property fixes the coefficient and
generator maps, and requires target maps to preserve grading and divided powers. -/
@[stacks 0F4I "set-indexed construction"]
public theorem exists_setVariableDividedPowerExtension
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    [IsStrictlyGradedComm Aᵢ] (γ : DividedPowerStructure Aᵢ)
    (J : Type w) (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) :
    ∃ (C : Type (max u v w)) (ringC : Ring C),
      letI : Ring C := ringC
      ∃ (algebraC : Algebra R C),
        letI : Algebra R C := algebraC
        ∃ (Cᵢ : ℕ → Submodule R C) (gradedC : GradedAlgebra Cᵢ),
          letI : GradedAlgebra Cᵢ := gradedC
          ∃ (strictC : IsStrictlyGradedComm Cᵢ),
            letI : IsStrictlyGradedComm Cᵢ := strictC
            ∃ (δ : DividedPowerStructure Cᵢ) (ι : A →ₐ[R] C) (T : J → C),
              Function.Injective ι ∧
              (∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m) ∧
              (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
                δ.dpow n (ι a) = ι (γ.dpow n a)) ∧
              (∀ j : J, T j ∈ Cᵢ (deg j)) ∧
              (∀ x : C, ∃ S : Finset J,
                x ∈ finiteVariableStage δ ι T S) ∧
              (∀ (S : Finset J) (j : J), j ∉ S →
                letI : DecidableEq J := Classical.decEq J
                ∃ (aS : Algebra R (finiteVariableStage δ ι T S)),
                  letI : Algebra R (finiteVariableStage δ ι T S) := aS
                  (∀ r : R, ((algebraMap R (finiteVariableStage δ ι T S) r :
                    finiteVariableStage δ ι T S) : C) = algebraMap R C r) ∧
                  ∃ (Sᵢ : ℕ → Submodule R (finiteVariableStage δ ι T S))
                    (gS : GradedAlgebra Sᵢ),
                    letI : GradedAlgebra Sᵢ := gS
                    ∃ (cS : IsStrictlyGradedComm Sᵢ),
                      letI : IsStrictlyGradedComm Sᵢ := cS
                      ∃ δS : DividedPowerStructure Sᵢ,
                      (∀ (n : ℕ) (b : finiteVariableStage δ ι T S),
                        b ∈ positiveEvenPart Sᵢ →
                          (δS.dpow n b : C) = δ.dpow n (b : C)) ∧
                      (∀ hodd : Odd (deg j),
                        ∃ e : OddVariableExtension Sᵢ (deg j) ≃+*
                            finiteVariableStage δ ι T (insert j S),
                          (∀ b : finiteVariableStage δ ι T S,
                            ((e (OddVariableExtension.inclusion
                              Sᵢ (deg j) b) : finiteVariableStage δ ι T (insert j S)) : C) = b) ∧
                          ((e (OddVariableExtension.generator
                            Sᵢ (deg j)) : finiteVariableStage δ ι T (insert j S)) : C) = T j ∧
                          (∀ (m : ℕ)
                            (x : OddVariableExtension Sᵢ (deg j)),
                            x ∈
                                OddVariableExtension.grade
                                  Sᵢ (deg j) m ↔
                              (e x : C) ∈ Cᵢ m) ∧
                          (∀ (n : ℕ)
                            (x : OddVariableExtension Sᵢ (deg j)),
                            x ∈ positiveEvenPart
                              (OddVariableExtension.grade Sᵢ (deg j)) →
                            δ.dpow n (e x : C) =
                              (e ((oddVariableDividedPowerStructure
                                Sᵢ δS (deg j) (hdeg j) hodd).dpow n x) : C))) ∧
                      (∀ heven : Even (deg j),
                        letI : Fact (Even (deg j)) := ⟨heven⟩
                        ∃ e : EvenVariableAlgebra
                            (finiteVariableStage δ ι T S) ≃+*
                            finiteVariableStage δ ι T (insert j S),
                          (∀ b : finiteVariableStage δ ι T S,
                            ((e (EvenVariableAlgebra.coeffEmbedding
                              b) :
                              finiteVariableStage δ ι T (insert j S)) : C) = b) ∧
                          ((e (EvenVariableAlgebra.monomial
                            1 1) : finiteVariableStage δ ι T (insert j S)) : C) = T j ∧
                          (∀ (m : ℕ)
                            (x : EvenVariableAlgebra
                              (finiteVariableStage δ ι T S)),
                            x ∈
                                EvenVariableAlgebra.grade
                                  Sᵢ (deg j) m ↔
                              (e x : C) ∈ Cᵢ m) ∧
                          (∀ (n : ℕ)
                            (x : EvenVariableAlgebra
                              (finiteVariableStage δ ι T S)),
                            x ∈ positiveEvenPart
                              (EvenVariableAlgebra.grade Sᵢ (deg j)) →
                            δ.dpow n (e x : C) =
                              (e ((evenVariableDividedPowerStructure (deg j) (hdeg j)
                                δS).dpow n x) : C)))) ∧
              (∀ {D : Type z} [Ring D] [Algebra R D]
                  (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ]
                  [IsStrictlyGradedComm Dᵢ] (ε : DividedPowerStructure Dᵢ)
                  (f : A →ₐ[R] D) (t : J → D),
                  (∀ (m : ℕ) (a : A), a ∈ Aᵢ m → f a ∈ Dᵢ m) →
                  (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart Aᵢ →
                    ε.dpow n (f a) = f (γ.dpow n a)) →
                  (∀ j : J, t j ∈ Dᵢ (deg j)) →
                  ∃! g : C →ₐ[R] D,
                    (∀ a : A, g (ι a) = f a) ∧
                    (∀ j : J, g (T j) = t j) ∧
                    (∀ (m : ℕ) (x : C), x ∈ Cᵢ m → g x ∈ Dᵢ m) ∧
                    (∀ (n : ℕ) (x : C), x ∈ positiveEvenPart Cᵢ →
                      ε.dpow n (g x) = g (δ.dpow n x))) := by
  classical
  let A₀ : GradedDPAlgebra R := ⟨A,inferInstance,inferInstance,Aᵢ,
    inferInstance,inferInstance,γ⟩
  let B := setVariableAlgebra A₀ deg hdeg
  let C₀ := ULift.{u} B.carrier
  let e₀ : B.carrier ≃+* C₀ := ULift.ringEquiv.symm
  let := ringEquivAlgebra B e₀
  let e := ringEquivAlgEquiv B e₀
  let C := transportedDPAlgebra B e
  let F := transportForward B e
  let K := transportBackward B e
  have hKF (x) : K.hom (F.hom x) = x := e.symm_apply_apply x
  have hFK (x) : F.hom (K.hom x) = x := e.apply_symm_apply x
  let ι := F.comp (setVariableCoefficient A₀ deg hdeg)
  let T := fun j => F.hom (setVariableGenerator A₀ deg hdeg j)
  refine ⟨C.carrier,C.ring,C.algebra,C.grade,C.graded,C.strict,C.gamma,ι.hom,T,
    ?_,ι.map_grade,ι.map_dpow,?_,?_,?_,?_⟩
  · exact e.injective.comp (setVariableCoefficient_injective A₀ deg hdeg)
  · intro j
    exact F.map_grade (deg j) _ (setVariableGenerator_mem A₀ deg hdeg j)
  · intro x
    obtain ⟨S,hS⟩ := setVariableAlgebra_finite_support A₀ deg hdeg (K.hom x)
    refine ⟨S,?_⟩
    have h := finiteVariableStage_map_mem F K hKF
      (setVariableCoefficient A₀ deg hdeg).hom (setVariableGenerator A₀ deg hdeg) S hS
    rwa [hFK] at h
  · intro S j hj
    obtain ⟨aS,hmapS,Sᵢ,gS,cS,δS,hδ,hE⟩ :=
      setVariable_successor_realization A₀ deg hdeg C F K hKF hFK S j hj
    let := aS
    let := gS
    let := cS
    refine ⟨aS,hmapS,Sᵢ,gS,cS,δS,hδ,?_,?_⟩
    · intro ho
      dsimp only at hE
      rw [oneVariableExtension, dite_eq_left ho] at hE
      exact hE
    · intro he
      have ho : ¬ Odd (deg j) := by
        rintro ⟨k, hk⟩
        obtain ⟨l, hl⟩ := he
        omega
      dsimp only at hE
      rw [oneVariableExtension, dite_eq_right ho] at hE
      exact hE
  · intro D ringD algebraD Dᵢ gradedD strictD ε f t hf hγ ht
    let D₀ : GradedDPAlgebra R := ⟨D,ringD,algebraD,Dᵢ,gradedD,strictD,ε⟩
    let f₀ : GradedDPHom A₀ D₀ := ⟨f,hf,hγ⟩
    obtain ⟨g,hg,hu⟩ := setVariableAlgebra_existsUnique_lift A₀ deg hdeg D₀ f₀ t ht
    let G := g.comp K
    refine ⟨G.hom,⟨?_,?_,G.map_grade,G.map_dpow⟩,?_⟩
    · intro a
      change g.hom (K.hom (F.hom ((setVariableCoefficient A₀ deg hdeg).hom a))) = f a
      rw [hKF,hg.1]
    · intro j
      change g.hom (K.hom (F.hom (setVariableGenerator A₀ deg hdeg j))) = t j
      rw [hKF,hg.2]
    · intro k hk
      let k₀ : GradedDPHom C D₀ := ⟨k,hk.2.2.1,hk.2.2.2⟩
      have heq : k₀.comp F = g := hu (k₀.comp F) ⟨hk.1,hk.2.1⟩
      ext x
      have h := congrArg (fun l => l.hom (K.hom x)) heq
      change k (F.hom (K.hom x)) = G.hom x at h
      rwa [hFK] at h

end DividedPowers.TateResolution
