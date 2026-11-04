module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit

/-!
# Descent of linear maps, idempotent complexes and flatness

Simultaneous descent of finite families of linear maps to a stage, complexes built from
idempotent endomorphisms of a total module, and descent of flatness of a finitely presented
module to a stage.

This is part 3 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

section FiniteSimultaneousDescent

universe u v w t s k

private lemma baseChange_proj_piRight {A : Type u} [CommRing A]
    (R : Type v) [CommRing R] [Algebra A R] {ι : Type t} [Fintype ι] [DecidableEq ι]
    (N : Type w) [AddCommGroup N] [Module A N] (a : ι) (x : R ⊗[A] (ι → N)) :
    (LinearMap.proj a : (ι → N) →ₗ[A] N).baseChange R x =
      TensorProduct.piRight A R R (fun _ : ι ↦ N) x a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r n => rfl
  | add x y hx hy => simp [hx, hy]

private lemma rTensor_baseChange {A : Type u} [CommRing A]
    {R : Type v} [CommRing R] [Algebra A R]
    {S : Type w} [CommRing S] [Algebra A S]
    {M : Type t} [AddCommGroup M] [Module A M]
    {N : Type s} [AddCommGroup N] [Module A N]
    (f : R →ₐ[A] S) (g : M →ₗ[A] N) (x : R ⊗[A] M) :
    g.baseChange S (LinearMap.rTensor M f.toLinearMap x) =
      LinearMap.rTensor N f.toLinearMap (g.baseChange R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => rfl
  | add x y hx hy => simp [hx, hy]

private theorem exists_linearMap_family_baseChange
    {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]
    {J : Type k} {S : J → Type w} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    (f : ∀ j, S j →ₐ[A] R)
    {M : Type t} [AddCommGroup M] [Module A M]
    {N : Type s} [AddCommGroup N] [Module A N]
    {ι : Type*} [Finite ι]
    (h : ∀ φ : R ⊗[A] M →ₗ[R] R ⊗[A] (ι → N),
      ∃ (j : J) (φj : S j ⊗[A] M →ₗ[S j] S j ⊗[A] (ι → N)),
        ∀ x, φ (LinearMap.rTensor M (f j).toLinearMap x) =
          LinearMap.rTensor (ι → N) (f j).toLinearMap (φj x))
    (φ : ι → R ⊗[A] M →ₗ[R] R ⊗[A] N) :
    ∃ (j : J) (φj : ι → S j ⊗[A] M →ₗ[S j] S j ⊗[A] N),
      ∀ a x, φ a (LinearMap.rTensor M (f j).toLinearMap x) =
        LinearMap.rTensor N (f j).toLinearMap (φj a x) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let e := TensorProduct.piRight A R R (fun _ : ι ↦ N)
  obtain ⟨j, ψ, hψ⟩ := h (e.symm.toLinearMap.comp (LinearMap.pi φ))
  refine ⟨j, fun a ↦ ((LinearMap.proj a : (ι → N) →ₗ[A] N).baseChange (S j)).comp ψ, ?_⟩
  intro a x
  have h₁ := congrArg ((LinearMap.proj a : (ι → N) →ₗ[A] N).baseChange R) (hψ x)
  rw [rTensor_baseChange, baseChange_proj_piRight] at h₁
  simpa [e] using h₁

private theorem exists_baseChange_family_eq
    {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]
    {J : Type k} {S : J → Type w} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    {M : Type t} [AddCommGroup M] [Module A M]
    {N : Type s} [AddCommGroup N] [Module A N]
    {ι : Type*} [Finite ι]
    (h : ∀ u u' : M →ₗ[A] (ι → N), u.baseChange R = u'.baseChange R →
      ∃ j, u.baseChange (S j) = u'.baseChange (S j))
    (u u' : ι → M →ₗ[A] N)
    (hu : ∀ a, (u a).baseChange R = (u' a).baseChange R) :
    ∃ j, ∀ a, (u a).baseChange (S j) = (u' a).baseChange (S j) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hpi : (LinearMap.pi u).baseChange R = (LinearMap.pi u').baseChange R := by
    ext m
    apply (TensorProduct.piRight A R R (fun _ : ι ↦ N)).injective
    ext a
    show (1 : R) ⊗ₜ[A] u a m = (1 : R) ⊗ₜ[A] u' a m
    exact LinearMap.congr_fun (hu a) ((1 : R) ⊗ₜ[A] m)
  obtain ⟨j, hj⟩ := h _ _ hpi
  refine ⟨j, fun a ↦ ?_⟩
  have hc := congrArg (fun f ↦
    (LinearMap.proj a : (ι → N) →ₗ[A] N).baseChange (S j) ∘ₗ f) hj
  simpa only [← LinearMap.baseChange_comp, LinearMap.proj_pi] using hc


private lemma cancelBaseChange_tmul_eq_smul_rTensor
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    {R : Type w} [CommRing R] [Algebra A R] [Algebra S R] [IsScalarTower A S R]
    {M : Type t} [AddCommGroup M] [Module A M] (r : R) (x : S ⊗[A] M) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A S R R M (r ⊗ₜ[S] x) =
      r • LinearMap.rTensor M (IsScalarTower.toAlgHom A S R).toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp [TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]

private lemma baseChange_eq_conjugate_of_rTensor_comm
    {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
    {R : Type w} [CommRing R] [Algebra A R] [Algebra S R] [IsScalarTower A S R]
    {M : Type t} [AddCommGroup M] [Module A M]
    {N : Type s} [AddCommGroup N] [Module A N]
    (f : S ⊗[A] M →ₗ[S] S ⊗[A] N) (g : R ⊗[A] M →ₗ[R] R ⊗[A] N)
    (h : ∀ x, g (LinearMap.rTensor M (IsScalarTower.toAlgHom A S R).toLinearMap x) =
      LinearMap.rTensor N (IsScalarTower.toAlgHom A S R).toLinearMap (f x)) :
    f.baseChange R =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A S R R N).symm.toLinearMap ∘ₗ
        g ∘ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange A S R R M).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro r x
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A S R R N).injective
  simp only [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, cancelBaseChange_tmul_eq_smul_rTensor, map_smul]
  exact congrArg (fun y ↦ r • y) (h x).symm

theorem exists_baseChange_complex_relations
    {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]
    {J : Type k} {S : J → Type w} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    {M : Type t} [AddCommGroup M] [Module A M]
    (h : ∀ (N : Type t) [AddCommGroup N] [Module A N] (u u' : M →ₗ[A] N),
      u.baseChange R = u'.baseChange R → ∃ j, u.baseChange (S j) = u'.baseChange (S j))
    (s : Finset ℤ) (e : ℤ → M →ₗ[A] M) (d : M →ₗ[A] M)
    (hs : ∀ n ∉ s, e n = 0)
    (he : ∀ n, IsIdempotentElem ((e n).baseChange R))
    (hd : ∀ n, d.baseChange R ∘ₗ (e n).baseChange R =
      (e (n + 1)).baseChange R ∘ₗ d.baseChange R)
    (hdd : d.baseChange R ∘ₗ d.baseChange R = 0) :
    ∃ j, (∀ n, IsIdempotentElem ((e n).baseChange (S j))) ∧
      (∀ n, d.baseChange (S j) ∘ₗ (e n).baseChange (S j) =
        (e (n + 1)).baseChange (S j) ∘ₗ d.baseChange (S j)) ∧
      d.baseChange (S j) ∘ₗ d.baseChange (S j) = 0 := by
  classical
  let t := s ∪ s.image (fun n ↦ n - 1)
  let T := Option (Bool × ↥t)
  let lhs : T → M →ₗ[A] M
    | none => d ∘ₗ d
    | some (false, n) => e n ∘ₗ e n
    | some (true, n) => d ∘ₗ e n
  let rhs : T → M →ₗ[A] M
    | none => 0
    | some (false, n) => e n
    | some (true, n) => e (n + 1) ∘ₗ d
  have hlim : ∀ a, (lhs a).baseChange R = (rhs a).baseChange R := by
    rintro (_ | ⟨_ | _, n⟩)
    · simpa [lhs, rhs, LinearMap.baseChange_comp] using hdd
    · simpa [lhs, rhs, LinearMap.baseChange_comp, IsIdempotentElem, Module.End.mul_eq_comp]
        using he n
    · simpa [lhs, rhs, LinearMap.baseChange_comp] using hd n
  obtain ⟨j, hj⟩ := exists_baseChange_family_eq (h (T → M)) lhs rhs hlim
  have he' : ∀ n ∈ t, IsIdempotentElem ((e n).baseChange (S j)) := by
    intro n hn
    simpa [lhs, rhs, LinearMap.baseChange_comp, IsIdempotentElem, Module.End.mul_eq_comp]
      using hj (some (false, ⟨n, hn⟩))
  have hd' : ∀ n ∈ t, d.baseChange (S j) ∘ₗ (e n).baseChange (S j) =
      (e (n + 1)).baseChange (S j) ∘ₗ d.baseChange (S j) := by
    intro n hn
    simpa [lhs, rhs, LinearMap.baseChange_comp] using hj (some (true, ⟨n, hn⟩))
  have hz : ∀ n, n ∉ t → e n = 0 ∧ e (n + 1) = 0 := fun n hn ↦
    ⟨hs n fun hns ↦ hn (Finset.mem_union_left _ hns),
      hs _ fun hns ↦ hn (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n + 1, hns, by omega⟩))⟩
  refine ⟨j, fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · by_cases hn : n ∈ t
    · exact he' n hn
    · simp [(hz n hn).1, IsIdempotentElem]
  · by_cases hn : n ∈ t
    · exact hd' n hn
    · simp [(hz n hn).1, (hz n hn).2]
  · simpa [lhs, rhs, LinearMap.baseChange_comp] using hj none

private theorem exists_endomorphism_family_baseChange
    {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]
    {J : Type k} {S : J → Type w} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    [∀ j, Algebra (S j) R] [∀ j, IsScalarTower A (S j) R]
    {M : Type t} [AddCommGroup M] [Module A M]
    {N : Type s} [AddCommGroup N] [Module R N]
    {ι : Type*} [Finite ι]
    (h : ∀ φ : R ⊗[A] M →ₗ[R] R ⊗[A] (ι → M),
      ∃ (j : J) (φj : S j ⊗[A] M →ₗ[S j] S j ⊗[A] (ι → M)),
        ∀ x, φ (LinearMap.rTensor M (IsScalarTower.toAlgHom A (S j) R).toLinearMap x) =
          LinearMap.rTensor (ι → M) (IsScalarTower.toAlgHom A (S j) R).toLinearMap (φj x))
    (e : R ⊗[A] M ≃ₗ[R] N) (φ : ι → N →ₗ[R] N) :
    ∃ (j : J) (φj : ι → S j ⊗[A] M →ₗ[S j] S j ⊗[A] M),
      ∀ a, (φj a).baseChange R =
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (S j) R R M).trans e).symm.conj
          (φ a) := by
  obtain ⟨j, ψ, hψ⟩ := exists_linearMap_family_baseChange
    (fun j ↦ IsScalarTower.toAlgHom A (S j) R) h (fun a ↦ e.symm.conj (φ a))
  refine ⟨j, ψ, fun a ↦ ?_⟩
  rw [baseChange_eq_conjugate_of_rTensor_comm (ψ a) (e.symm.conj (φ a)) (hψ a)]
  ext x
  simp [LinearEquiv.conj_apply_apply]

end FiniteSimultaneousDescent

/-- The range of an idempotent endomorphism of a finitely presented module is finitely
presented: it is a quotient by the finitely generated range of `1 - e`. -/
private theorem finitePresentation_range_of_isIdempotentElem {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] {e : M →ₗ[R] M}
    (he : IsIdempotentElem e) : Module.FinitePresentation R (LinearMap.range e) := by
  refine Module.finitePresentation_of_surjective e.rangeRestrict e.surjective_rangeRestrict ?_
  rw [LinearMap.ker_rangeRestrict, LinearMap.IsIdempotentElem.ker_eq_range he]
  exact (Module.Finite.iff_fg).1 inferInstance

/-- The range of an idempotent endomorphism is a retract, hence inherits flatness over any
base of scalars. -/
private theorem flat_range_of_isIdempotentElem {S R M : Type*} [CommRing R] [CommRing S]
    [Algebra S R] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M]
    [Module.Flat S M] {e : M →ₗ[R] M} (he : IsIdempotentElem e) :
    Module.Flat S (LinearMap.range e) :=
  Module.Flat.of_retract ((LinearMap.range e).subtype.restrictScalars S)
    (e.rangeRestrict.restrictScalars S)
    (by
      ext x
      exact congrArg Subtype.val (Subtype.ext
        ((LinearMap.IsIdempotentElem.mem_range_iff he).1 x.2) : e.rangeRestrict x = x))

/-- The cochain complex with terms the ranges of idempotents `eₙ` of `M` and differential
induced by an endomorphism `d` with `d ∘ eₙ = eₙ₊₁ ∘ d` and `d ∘ d = 0`. -/
private def complexOfIdempotents.{u, v} {S : Type u} [Ring S] (M : Type v) [AddCommGroup M]
    [Module S M] (e : ℤ → M →ₗ[S] M) (d : M →ₗ[S] M)
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0) :
    CochainComplex (ModuleCat.{v} S) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of S (LinearMap.range (e n)))
    (fun n ↦ ModuleCat.ofHom
      ((d ∘ₗ (LinearMap.range (e n)).subtype).codRestrict (LinearMap.range (e (n + 1)))
        (fun x ↦ by
          obtain ⟨_, y, rfl⟩ := x
          exact ⟨d y, by simpa using (LinearMap.congr_fun (hd n) y).symm⟩)))
    (fun n ↦ by
      ext ⟨x, hx⟩
      simpa using LinearMap.congr_fun hdd x)

private lemma map_range_eq_of_intertwines {S M N : Type*} [Ring S]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (f : M ≃ₗ[S] N) (e : M →ₗ[S] M) (e' : N →ₗ[S] N)
    (h : ∀ x, f (e x) = e' (f x)) :
    (LinearMap.range e).map f.toLinearMap = LinearMap.range e' := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e (f.symm x), ⟨f.symm x, rfl⟩, by simpa using h (f.symm x)⟩

private def complexOfIdempotentsCongr.{u, v} {S : Type u} [Ring S]
    {M N : Type v} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (f : M ≃ₗ[S] N) {e : ℤ → M →ₗ[S] M} {d : M →ₗ[S] M}
    {e' : ℤ → N →ₗ[S] N} {d' : N →ₗ[S] N}
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0)
    (hd' : ∀ n, d' ∘ₗ e' n = e' (n + 1) ∘ₗ d') (hdd' : d' ∘ₗ d' = 0)
    (he : ∀ n x, f (e n x) = e' n (f x)) (hf : ∀ x, f (d x) = d' (f x)) :
    complexOfIdempotents M e d hd hdd ≅ complexOfIdempotents N e' d' hd' hdd' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (f.ofSubmodules _ _ (map_range_eq_of_intertwines f (e n) (e' n) (he n))).toModuleIso)
    (by
      rintro n _ rfl
      simp only [complexOfIdempotents, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change d' ((f.ofSubmodules _ _ (map_range_eq_of_intertwines f (e n) (e' n) (he n))) x : N) =
        ((f.ofSubmodules _ _ (map_range_eq_of_intertwines f (e (n + 1)) (e' (n + 1)) (he (n + 1))))
          ⟨d x.1, _⟩ : N)
      simpa only [LinearEquiv.ofSubmodules_apply] using (hf x.1).symm)


private lemma isZero_complexOfIdempotents_X.{u, v} {S : Type u} [Ring S]
    {M : Type v} [AddCommGroup M] [Module S M]
    {e : ℤ → M →ₗ[S] M} {d : M →ₗ[S] M}
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0)
    (n : ℤ) (hn : e n = 0) :
    Limits.IsZero ((complexOfIdempotents M e d hd hdd).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  show Subsingleton (LinearMap.range (e n))
  rw [hn, LinearMap.range_zero]
  infer_instance

private lemma isStrictlyGE_complexOfIdempotents.{u, v} {S : Type u} [Ring S]
    {M : Type v} [AddCommGroup M] [Module S M]
    {e : ℤ → M →ₗ[S] M} {d : M →ₗ[S] M}
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0)
    (a : ℤ) (ha : ∀ n < a, e n = 0) :
    (complexOfIdempotents M e d hd hdd).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ _).mpr fun n hn ↦
    isZero_complexOfIdempotents_X hd hdd n (ha n hn)

private lemma isStrictlyLE_complexOfIdempotents.{u, v} {S : Type u} [Ring S]
    {M : Type v} [AddCommGroup M] [Module S M]
    {e : ℤ → M →ₗ[S] M} {d : M →ₗ[S] M}
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0)
    (b : ℤ) (hb : ∀ n, b < n → e n = 0) :
    (complexOfIdempotents M e d hd hdd).IsStrictlyLE b :=
  (CochainComplex.isStrictlyLE_iff _ _).mpr fun n hn ↦
    isZero_complexOfIdempotents_X hd hdd n (hb n hn)


/-- Base change preserves idempotent endomorphisms. -/
private theorem isIdempotentElem_baseChange.{u, v} {S : Type u} [CommRing S]
    (T : Type*) [CommRing T]
    [Algebra S T] {M : Type v} [AddCommGroup M] [Module S M] {e : M →ₗ[S] M}
    (he : IsIdempotentElem e) :
    IsIdempotentElem (e.baseChange T) := by
  unfold IsIdempotentElem at *
  rw [Module.End.mul_eq_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, he]

/-- The comparison from the base change of the range of `e` to the range of `e.baseChange T`. -/
private def baseChangeRange.{u, v} {S : Type u} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] {M : Type v} [AddCommGroup M] [Module S M] (e : M →ₗ[S] M) :
    T ⊗[S] LinearMap.range e →ₗ[T] LinearMap.range (e.baseChange T) :=
  (((LinearMap.range e).subtype.baseChange T)).codRestrict _ (fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      obtain ⟨_, z, rfl⟩ := y
      exact ⟨t ⊗ₜ z, by simp⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy)

/-- For an idempotent `e`, base change commutes with taking the range of `e`. -/
private theorem bijective_baseChangeRange.{u, v} {S : Type u} [CommRing S]
    (T : Type*) [CommRing T]
    [Algebra S T] {M : Type v} [AddCommGroup M] [Module S M] {e : M →ₗ[S] M}
    (he : IsIdempotentElem e) : Function.Bijective (baseChangeRange T e) := by
  let r : T ⊗[S] M →ₗ[T] T ⊗[S] LinearMap.range e := e.rangeRestrict.baseChange T
  have hleft : ∀ x, r (LinearMap.range e |>.subtype.baseChange T x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      obtain ⟨_, z, rfl⟩ := y
      simp only [r, LinearMap.baseChange_tmul, Submodule.coe_subtype]
      congr 1
      exact Subtype.ext (by simpa using LinearMap.congr_fun he z)
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro x y hxy
    have := congrArg (fun z ↦ r z.1) hxy
    simpa [baseChangeRange, hleft] using this
  · rintro ⟨_, w, rfl⟩
    refine ⟨r w, Subtype.ext ?_⟩
    simp only [baseChangeRange, LinearMap.codRestrict_apply, r]
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl

private lemma linearMap_sum_comp {S : Type*} [Ring S] {M N Q : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] [AddCommGroup Q] [Module S Q] {ι : Type*} (t : Finset ι)
    (f : ι → N →ₗ[S] Q) (g : M →ₗ[S] N) : (∑ i ∈ t, f i) ∘ₗ g = ∑ i ∈ t, f i ∘ₗ g := by
  ext x
  simp [LinearMap.sum_apply]

private lemma linearMap_comp_sum {S : Type*} [Ring S] {M N Q : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] [AddCommGroup Q] [Module S Q] {ι : Type*} (t : Finset ι)
    (f : N →ₗ[S] Q) (g : ι → M →ₗ[S] N) : f ∘ₗ (∑ i ∈ t, g i) = ∑ i ∈ t, f ∘ₗ g i := by
  ext x
  simp [LinearMap.sum_apply]

/-- A finite product of flat modules is flat. -/
private theorem flat_pi_of_finite {S : Type*} [CommRing S] {ι : Type*} [Finite ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    [∀ i, Module.Flat S (M i)] : Module.Flat S (∀ i, M i) := by
  classical
  have := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := S) (M := M)).symm

private lemma baseChange_comp_eq_of_comp_eq {S : Type*} [CommRing S] (T : Type*) [CommRing T]
  [Algebra S T]
    {M : Type*} [AddCommGroup M] [Module S M] {e : ℤ → M →ₗ[S] M} {d : M →ₗ[S] M}
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (n : ℤ) :
    d.baseChange T ∘ₗ (e n).baseChange T = (e (n + 1)).baseChange T ∘ₗ d.baseChange T := by
  rw [← LinearMap.baseChange_comp, hd, LinearMap.baseChange_comp]

private lemma baseChange_comp_self_eq_zero {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T]
    {M : Type*} [AddCommGroup M] [Module S M] {d : M →ₗ[S] M} (hdd : d ∘ₗ d = 0) :
    d.baseChange T ∘ₗ d.baseChange T = 0 := by
  rw [← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero]

/-- Extension of scalars of the complex of idempotent ranges. -/
private def extendScalarsComplexOfIdempotentsIso.{u, v} {S T : Type u} [CommRing S]
    [CommRing T] (f : S →+* T) {M : Type (max u v)} [AddCommGroup M] [Module S M]
    {e : ℤ → M →ₗ[S] M}
    {d : M →ₗ[S] M} (he : ∀ n, IsIdempotentElem (e n))
    (hd : ∀ n, d ∘ₗ e n = e (n + 1) ∘ₗ d) (hdd : d ∘ₗ d = 0) :
    letI := f.toAlgebra
    ((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (complexOfIdempotents M e d hd hdd) ≅
    complexOfIdempotents (T ⊗[S] M) (fun n ↦ (e n).baseChange T) (d.baseChange T)
      (baseChange_comp_eq_of_comp_eq T hd) (baseChange_comp_self_eq_zero T hdd) :=
  letI := f.toAlgebra
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (LinearEquiv.ofBijective (baseChangeRange T (e n))
      (bijective_baseChangeRange T (he n))).toModuleIso) (by
      rintro n _ rfl
      simp only [Functor.mapHomologicalComplex_obj_d, complexOfIdempotents, CochainComplex.of_d]
      apply ModuleCat.ExtendScalars.hom_ext
      intro y
      apply Subtype.ext
      rfl)

section TotalModule

universe u v

variable {S : Type u} [Ring S] (P : CochainComplex (ModuleCat.{v} S) ℤ) (s : Finset ℤ)

private abbrev totalModule := ∀ n : s, P.X n

private def totalInc (n : ℤ) : P.X n →ₗ[S] totalModule P s :=
  if h : n ∈ s then LinearMap.single S (fun m : s ↦ P.X m) (⟨n, h⟩ : s) else 0

private def totalPr (n : ℤ) : totalModule P s →ₗ[S] P.X n :=
  if h : n ∈ s then LinearMap.proj (⟨n, h⟩ : s) else 0

variable {P s}

private lemma totalPr_comp_totalInc (hs : ∀ n ∉ s, Subsingleton (P.X n)) (n : ℤ) :
    totalPr P s n ∘ₗ totalInc P s n = LinearMap.id := by
  by_cases h : n ∈ s
  · ext x
    simp [totalPr, totalInc, h]
  · have := hs n h
    ext x
    exact Subsingleton.elim _ _

private lemma totalPr_comp_totalInc_of_ne {n m : ℤ} (hnm : n ≠ m) :
    totalPr P s m ∘ₗ totalInc P s n = 0 := by
  by_cases hn : n ∈ s
  · by_cases hm : m ∈ s
    · ext x
      simp only [totalPr, totalInc, hn, hm, dite_true, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_proj, LinearMap.zero_apply]
      rw [Function.eval_apply, LinearMap.single_apply, Pi.single_eq_of_ne]
      exact fun h ↦ hnm (congrArg Subtype.val h).symm
    · simp [totalPr, hm]
  · simp [totalInc, hn]

variable (P s)

private def totalDiff : totalModule P s →ₗ[S] totalModule P s :=
  ∑ n ∈ s, totalInc P s (n + 1) ∘ₗ (P.d n (n + 1)).hom ∘ₗ totalPr P s n

private def totalIdem (n : ℤ) : totalModule P s →ₗ[S] totalModule P s :=
  totalInc P s n ∘ₗ totalPr P s n

variable {P s}

private lemma totalDiff_comp_totalInc (hs : ∀ n ∉ s, Subsingleton (P.X n)) (n : ℤ) :
    totalDiff P s ∘ₗ totalInc P s n = totalInc P s (n + 1) ∘ₗ (P.d n (n + 1)).hom := by
  rw [totalDiff, linearMap_sum_comp]
  by_cases hn : n ∈ s
  · rw [Finset.sum_eq_single n]
    · rw [LinearMap.comp_assoc, LinearMap.comp_assoc, totalPr_comp_totalInc hs, LinearMap.comp_id]
    · intro m _ hmn
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, totalPr_comp_totalInc_of_ne (Ne.symm hmn)]
      simp
    · exact fun h ↦ (h hn).elim
  · have := hs n hn
    rw [Finset.sum_eq_zero]
    · ext x
      simp [Subsingleton.elim x 0]
    · intro m hm
      have hmn : n ≠ m := fun h ↦ hn (h ▸ hm)
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, totalPr_comp_totalInc_of_ne hmn]
      simp

private lemma totalPr_comp_totalDiff (hs : ∀ n ∉ s, Subsingleton (P.X n)) (n : ℤ) :
    totalPr P s (n + 1) ∘ₗ totalDiff P s = (P.d n (n + 1)).hom ∘ₗ totalPr P s n := by
  rw [totalDiff, linearMap_comp_sum]
  by_cases hn : n ∈ s
  · rw [Finset.sum_eq_single n]
    · rw [← LinearMap.comp_assoc, totalPr_comp_totalInc hs, LinearMap.id_comp]
    · intro m _ hmn
      rw [← LinearMap.comp_assoc, totalPr_comp_totalInc_of_ne (by omega)]
      simp
    · exact fun h ↦ (h hn).elim
  · rw [Finset.sum_eq_zero]
    · simp [totalPr, hn]
    · intro m hm
      have hmn : m + 1 ≠ n + 1 := fun h ↦ hn (by rw [show n = m by omega]; exact hm)
      rw [← LinearMap.comp_assoc, totalPr_comp_totalInc_of_ne hmn]
      simp

private lemma totalDiff_comp_totalIdem (hs : ∀ n ∉ s, Subsingleton (P.X n)) (n : ℤ) :
    totalDiff P s ∘ₗ totalIdem P s n = totalIdem P s (n + 1) ∘ₗ totalDiff P s := by
  rw [totalIdem, totalIdem, ← LinearMap.comp_assoc, totalDiff_comp_totalInc hs,
    LinearMap.comp_assoc, LinearMap.comp_assoc, totalPr_comp_totalDiff hs]

private lemma totalDiff_comp_totalDiff (hs : ∀ n ∉ s, Subsingleton (P.X n)) :
    totalDiff P s ∘ₗ totalDiff P s = 0 := by
  have h : totalDiff P s ∘ₗ totalDiff P s = totalDiff P s ∘ₗ
      ∑ n ∈ s, totalInc P s (n + 1) ∘ₗ (P.d n (n + 1)).hom ∘ₗ totalPr P s n := rfl
  rw [h, linearMap_comp_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [← LinearMap.comp_assoc, totalDiff_comp_totalInc hs, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc (f := totalPr P s n), ← ModuleCat.hom_comp, P.d_comp_d]
  simp

private lemma isIdempotentElem_totalIdem (hs : ∀ n ∉ s, Subsingleton (P.X n)) (n : ℤ) :
    IsIdempotentElem (totalIdem P s n) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, totalIdem, LinearMap.comp_assoc,
    ← LinearMap.comp_assoc (f := totalPr P s n) (g := totalInc P s n), totalPr_comp_totalInc hs,
    LinearMap.id_comp]

private lemma totalInc_eq_zero {n : ℤ} (hn : n ∉ s) : totalInc P s n = 0 := by
  simp [totalInc, hn]

private lemma totalPr_totalInc_apply (hs : ∀ n ∉ s, Subsingleton (P.X n)) {n : ℤ} (y : P.X n) :
    totalPr P s n (totalInc P s n y) = y :=
  LinearMap.congr_fun (totalPr_comp_totalInc hs n) y

private lemma totalInc_totalPr_of_mem_range (hs : ∀ n ∉ s, Subsingleton (P.X n)) {n : ℤ}
    {x : totalModule P s} (hx : x ∈ LinearMap.range (totalIdem P s n)) :
    totalInc P s n (totalPr P s n x) = x := by
  obtain ⟨z, rfl⟩ := hx
  simp only [totalIdem, LinearMap.comp_apply]
  rw [totalPr_totalInc_apply hs]

/-- The range of the `n`-th idempotent is the `n`-th term of the complex. -/
private def rangeTotalIdemEquiv (hs : ∀ n ∉ s, Subsingleton (P.X n)) (n : ℤ) :
    LinearMap.range (totalIdem P s n) ≃ₗ[S] P.X n where
  toFun x := totalPr P s n x.1
  map_add' x y := by simp
  map_smul' r x := by simp
  invFun y := ⟨totalInc P s n y, totalInc P s n y, by
    simp only [totalIdem, LinearMap.comp_apply]
    rw [totalPr_totalInc_apply hs]⟩
  left_inv x := Subtype.ext (totalInc_totalPr_of_mem_range hs x.2)
  right_inv y := totalPr_totalInc_apply hs y

/-- The complex rebuilt from the total module, its differential and its idempotents is
isomorphic to the original complex. -/
private def complexOfIdempotentsTotalIso (hs : ∀ n ∉ s, Subsingleton (P.X n)) :
    complexOfIdempotents (totalModule P s) (totalIdem P s) (totalDiff P s)
      (totalDiff_comp_totalIdem hs) (totalDiff_comp_totalDiff hs) ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (rangeTotalIdemEquiv hs n).toModuleIso) (by
      rintro n _ rfl
      ext x
      simp only [complexOfIdempotents, CochainComplex.of_d]
      change P.d n (n + 1) (totalPr P s n x.1) = totalPr P s (n + 1) (totalDiff P s x.1)
      rw [← LinearMap.comp_apply (totalPr P s (n + 1)), totalPr_comp_totalDiff hs]
      rfl)

end TotalModule

section EventualFlatness

universe uK

private theorem directLimit_algebra_lift_bijective_iff
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J] {A : Type*} [CommRing A]
    {S : J → Type*} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S fun i j h ↦ ⇑(f i j h)]
    {R : Type*} [CommRing R] [Algebra A R] (g : ∀ j, S j →ₐ[A] R)
    (hf : ∀ i j (h : i ≤ j) (x : S i), g j (f i j h x) = g i x) :
    Function.Bijective (DirectLimit.Algebra.lift S f R g hf) ↔
      (∀ r : R, ∃ (j : J) (s : S j), g j s = r) ∧
      (∀ (j : J) (s : S j), g j s = 0 → ∃ (k : J) (hjk : j ≤ k), f j k hjk s = 0) := by
  constructor
  · intro h
    constructor
    · intro r
      obtain ⟨z, hz⟩ := h.2 r
      obtain ⟨j, s, rfl⟩ := DirectLimit.exists_eq_mk f z
      exact ⟨j, s, hz⟩
    · intro j s hs
      have hz : DirectLimit.Algebra.lift S f R g hf (DirectLimit.Algebra.of S f j s) =
          DirectLimit.Algebra.lift S f R g hf (DirectLimit.Algebra.of S f j 0) := by
        simpa only [DirectLimit.Algebra.lift_of, map_zero] using hs
      obtain ⟨k, hjk, _, heq⟩ := Quotient.exact (h.1 hz)
      exact ⟨k, hjk, by simpa using heq⟩
  · rintro ⟨hsurj, hinj⟩
    exact directLimit_algebra_lift_bijective f g hf hsurj hinj

private theorem exists_directed_stage_element {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    (k : K) (x : c.pt) :
    ∃ (l : K) (_ : k ≤ l) (y : F.obj (G.obj l)), (c.ι.app (G.obj l)).hom y = x := by
  obtain ⟨i, y, rfl⟩ := exists_stage_element hc x
  obtain ⟨l, ⟨t⟩⟩ := ((Functor.final_iff_of_isFiltered G).1 inferInstance).1 i
  obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k l
  refine ⟨m, hkm, (F.map (t ≫ G.map (homOfLE hlm))).hom y, ?_⟩
  exact congrArg (fun q : F.obj i ⟶ c.pt ↦ q.hom y) (c.w (t ≫ G.map (homOfLE hlm)))

private theorem exists_directed_stage_eq_zero {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    {K : Type*} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    {k : K} (y : F.obj (G.obj k)) (hy : (c.ι.app (G.obj k)).hom y = 0) :
    ∃ (k' : K) (h : k ≤ k'), (F.map (G.map (homOfLE h))).hom y = 0 := by
  obtain ⟨i, f, g, hf⟩ := (stage_elements_eq_iff hc y (0 : F.obj (G.obj k))).mp
    (by simpa using hy)
  obtain ⟨k₁, ⟨t⟩⟩ := ((Functor.final_iff_of_isFiltered G).1 inferInstance).1 i
  obtain ⟨k₂, hk₁, hk₂⟩ := directed_of (· ≤ ·) k k₁
  obtain ⟨k', h', he⟩ := final_exists_coeq_le G (f ≫ t ≫ G.map (homOfLE hk₂))
    (G.map (homOfLE hk₁))
  refine ⟨k', hk₁.trans h', ?_⟩
  have hmap : G.map (homOfLE (hk₁.trans h')) = G.map (homOfLE hk₁) ≫ G.map (homOfLE h') := by
    rw [← G.map_comp]; rfl
  rw [hmap, ← he]
  simp [Functor.map_comp, hf]


/-- `rTensor` of a composite of maps agreeing pointwise with a third map. -/
private lemma rTensor_rTensor_of_comp_eq {A : Type*} [CommRing A] {X Y Z : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (M : Type*) [AddCommGroup M] [Module A M] (p : X →ₗ[A] Y) (q : Y →ₗ[A] Z) (r : X →ₗ[A] Z)
    (h : ∀ x, q (p x) = r x) (x : X ⊗[A] M) :
    LinearMap.rTensor M q (LinearMap.rTensor M p x) = LinearMap.rTensor M r x := by
  rw [← LinearMap.rTensor_comp_apply, (LinearMap.ext h : q ∘ₗ p = r)]

private def tensorProductMapSemilinear {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (f : S →ₐ[A] T)
    (M : Type*) [AddCommGroup M] [Module A M] : S ⊗[A] M →ₛₗ[f.toRingHom] T ⊗[A] M where
  __ := (LinearMap.rTensor M f.toLinearMap).toAddHom
  map_smul' r x := by
    change LinearMap.rTensor M f.toLinearMap (r • x) =
      f r • LinearMap.rTensor M f.toLinearMap x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy

-- elaborating the composite natural transformations of derived functors below
private theorem exists_stage_flat_baseChange {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I] {F : I ⥤ CommAlgCat.{uR} R₀}
    {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    [Algebra.FinitePresentation R₀ A₀]
    {K : Type uK} [PartialOrder K] [IsDirectedOrder K] [Nonempty K] (G : K ⥤ I) [G.Final]
    (k : K) (M : Type uM) [AddCommGroup M] [Module (stageAlgebra F A₀ (G.obj k)) M]
    [Module.FinitePresentation (stageAlgebra F A₀ (G.obj k)) M] :
    letI := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
    Module.Flat c.pt ((c.pt ⊗[R₀] A₀) ⊗[stageAlgebra F A₀ (G.obj k)] M) →
    ∃ (l : K) (h : k ≤ l),
      letI := (stageDirectedMap F A₀ G k l h).toRingHom.toAlgebra
      Module.Flat (F.obj (G.obj l)) (stageAlgebra F A₀ (G.obj l) ⊗[stageAlgebra F A₀ (G.obj k)] M)
        := by
  classical
  let R := c.pt ⊗[R₀] A₀
  let Bk := stageAlgebra F A₀ (G.obj k)
  let := (stageToLimitMap c A₀ (G.obj k)).toAlgebra
  intro hflat
  let := hflat
  let := isDirectedOrder_upperSet k
  let J := {l : K // k ≤ l}
  let : Nonempty J := ⟨⟨k, le_rfl⟩⟩
  let A : J → Type uR := fun l ↦ F.obj (G.obj l.1)
  let B := fun l : J ↦ stageAlgebra F A₀ (G.obj l.1)
  let := fun l : J ↦ (stageDirectedMap F A₀ G k l.1 l.2).toRingHom.toAlgebra
  obtain ⟨f, hf₀, hsys, g, hg₀, hfg, hbij⟩ := stage_above_directLimit_lift_bijective hc A₀ G k
  let := hsys
  let : ∀ l : J, Algebra (B l) R := fun l ↦ (g l).toRingHom.toAlgebra
  let : ∀ l : J, IsScalarTower Bk (B l) R := fun l ↦
    IsScalarTower.of_algebraMap_eq fun x ↦ ((g l).commutes x).symm
  obtain ⟨hBsurj, hBinj⟩ := (directLimit_algebra_lift_bijective_iff f g hfg).mp hbij
  have hN := Stacks.ColimitPresentation.FPModules.isModuleColimit f hfg hBsurj hBinj M
  let N := fun l : J ↦ B l ⊗[Bk] M
  let a := fun (i j : J) (h : i ≤ j) ↦ (F.map (G.map (homOfLE h))).hom.toRingHom
  let b := fun (i j : J) (h : i ≤ j) ↦ (f i j h).toRingHom
  let n := fun (i j : J) (h : i ≤ j) ↦ tensorProductMapSemilinear (f i j h) M
  let ν : ∀ i : J, N i →+ R ⊗[Bk] M := fun i ↦
    (tensorProductMapSemilinear (g i) M).toAddMonoidHom
  let ρ : ∀ i : J, A i →+* c.pt := fun i ↦ (c.ι.app (G.obj i.1)).hom.toRingHom
  let σ := fun i : J ↦ (g i).toRingHom
  let γ := fun i : J ↦ (Algebra.TensorProduct.includeLeftRingHom : A i →+* B i)
  have ha : DirectedSystem A (fun i j h ↦ a i j h) := by
    constructor
    · intro i x
      simp [a]
    · intro i j l hij hjl x
      show (F.map (G.map (homOfLE hjl))).hom ((F.map (G.map (homOfLE hij))).hom x) = _
      rw [← CommAlgCat.comp_apply, ← F.map_comp, ← G.map_comp]
      rfl
  have hg : ∀ i j (h : i ≤ j), (γ j).comp (a i j h) = (b i j h).comp (γ i) := by
    intro i j h
    ext x
    simp [γ, a, b, hf₀, stageDirectedMap]
  have hσγ : ∀ i, (algebraMap c.pt R).comp (ρ i) = (σ i).comp (γ i) := by
    intro i
    ext x
    simp [R, ρ, σ, γ, hg₀, stageToLimitMap]
  have hγ : ∀ i, (γ i).toAlgebra = (Algebra.TensorProduct.leftAlgebra : Algebra (A i) (B i)) := by
    intro i
    apply Algebra.algebra_ext
    intro x
    rfl
  have hν : ∀ i x, Stacks.FinitePresentation.ColimitDescent.canonMod
      (fun j : J ↦ IsScalarTower.toAlgHom Bk (B j) R) M i x = ν i x := by
    intro i x
    rfl
  have hn : ∀ i j (h : i ≤ j) x,
      Stacks.FinitePresentation.ColimitDescent.transMod (fun i j h ↦ f i j h) M h x = n i j h x :=
        by
    intro i j h x
    rfl
  have h02 := (Module.Flat.exists_flat_models_and_eventually_flat.{uR, max uR uA, max uR uA uM,
    uK, uR, max uR uA, max uR uA uM, uR, max uR uA, max uR uA uM}
    (R := c.pt) (S := R) (M := R ⊗[Bk] M)).2.2
  obtain ⟨i, hi⟩ := h02 J inferInstance inferInstance inferInstance A B N
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    a b ha hsys γ n ρ σ ν hg
    (by
      intro i x
      show LinearMap.rTensor M (f i i le_rfl).toLinearMap x = x
      have hf : f i i le_rfl = AlgHom.id Bk (B i) := AlgHom.ext fun x ↦
        DirectedSystem.map_self (f := fun i j h ↦ ⇑(f i j h)) x
      rw [hf]
      show LinearMap.rTensor M (LinearMap.id : B i →ₗ[Bk] B i) x = x
      simp)
    (by
      intro i j l hij hjl x
      show LinearMap.rTensor M (f j l hjl).toLinearMap
        (LinearMap.rTensor M (f i j hij).toLinearMap x) =
          LinearMap.rTensor M (f i l (hij.trans hjl)).toLinearMap x
      exact rTensor_rTensor_of_comp_eq M _ _ _
        (DirectedSystem.map_map (f := fun i j h ↦ ⇑(f i j h)) hij hjl) x)
    (by
      intro i j h
      funext x
      exact congrArg (fun q : F.obj (G.obj i.1) ⟶ c.pt ↦ q.hom x) (c.w (G.map (homOfLE h))))
    (by intro i j h; funext x; exact hfg i j h x)
    (by
      intro i j h x
      show LinearMap.rTensor M (g j).toLinearMap (LinearMap.rTensor M (f i j h).toLinearMap x) =
        LinearMap.rTensor M (g i).toLinearMap x
      exact rTensor_rTensor_of_comp_eq M _ _ _ (hfg i j h) x)
    hσγ
    (by
      intro i x m
      calc
        ν i (γ i x • m) = σ i (γ i x) • ν i m :=
          (tensorProductMapSemilinear (g i) M).map_smulₛₗ _ _
        _ = (algebraMap c.pt R) (ρ i x) • ν i m :=
          congrArg (fun z : R ↦ z • ν i m) (RingHom.congr_fun (hσγ i) x).symm
        _ = ρ i x • ν i m := IsScalarTower.algebraMap_smul R _ _)
    (by intro i y m; exact (tensorProductMapSemilinear (g i) M).map_smulₛₗ y m)
    (by
      intro x
      obtain ⟨l, hl, y, hy⟩ := exists_directed_stage_element hc G k x
      exact ⟨⟨l, hl⟩, y, hy⟩)
    (by
      intro i y hy
      obtain ⟨j, hij, hj⟩ := exists_directed_stage_eq_zero hc G y hy
      exact ⟨⟨j, i.2.trans hij⟩, hij, hj⟩)
    hBsurj hBinj
    (by intro x; obtain ⟨i, y, hy⟩ := hN.jointly_surjective x; exact ⟨i, y, (hν i y).symm.trans hy⟩)
    (by
      intro i y hy
      obtain ⟨j, hij, hj⟩ := hN.exists_eq_of_canonMod_eq i y 0 (by rw [hν, map_zero]; exact hy)
      exact ⟨j, hij, by rw [hn, hn] at hj; exact hj.trans ((n i j hij).map_zero)⟩)
    (by intro i; rw [hγ]; infer_instance)
    (by intro i; infer_instance)
    (by
      intro i j h
      let := (a i j h).toAlgebra
      let : IsScalarTower R₀ (A i) (A j) :=
        IsScalarTower.of_algebraMap_eq fun r ↦ ((F.map (G.map (homOfLE h))).hom.commutes r).symm
      let := (b i j h).toAlgebra
      have ht : IsScalarTower (A i) (B i) (B j) :=
        IsScalarTower.of_algebraMap_eq fun x ↦ by
          show (algebraMap (A i) (B j)) x = b i j h ((algebraMap (A i) (B i)) x)
          show (a i j h x) ⊗ₜ[R₀] 1 = b i j h (x ⊗ₜ[R₀] 1)
          exact RingHom.congr_fun (hg i j h) x
      let := ht
      have hp := @Algebra.IsPushout.tensorProduct_tensorProduct R₀ A₀ (A i) (A j)
        _ _ _ _ _ _ _ _ _ ((b i j h).toAlgebra) ht (by
        ext x
        show f i j h (1 ⊗ₜ[R₀] x) = 1 ⊗ₜ[R₀] x
        simp [hf₀, stageDirectedMap])
      convert! hp using 1 <;> first
      | rfl
      | (apply Algebra.algebra_ext; intro x; rfl))
    (by
      intro i j h
      let := (b i j h).toAlgebra
      let : IsScalarTower Bk (B i) (B j) :=
        IsScalarTower.of_algebraMap_eq fun x ↦ ((f i j h).commutes x).symm
      let : Module (B i) (N j) := Module.compHom (N j) (b i j h)
      let htN : IsScalarTower (B i) (B j) (N j) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let u : N i →ₗ[B i] N j :=
        ⟨(n i j h).toAddHom, fun x y ↦ (n i j h).map_smul' x y⟩
      show @IsBaseChange (B i) (N i) (N j) (B j) _ _ _ _ _ _ _ _ htN u
      refine @IsBaseChange.of_equiv (B i) (N i) (N j) (B j) _ _ _ _ _ _ _ _ htN u
        (TensorProduct.AlgebraTensorModule.cancelBaseChange Bk (B i) (B j) (B j) M) ?_
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r m =>
        show (TensorProduct.AlgebraTensorModule.cancelBaseChange Bk (B i) (B j) (B j) M)
          (1 ⊗ₜ[B i] (r ⊗ₜ[Bk] m)) = f i j h r ⊗ₜ[Bk] m
        simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def,
          mul_one]
        rfl
      | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy)
  have hm : Module.compHom (N i) (γ i) = (inferInstance : Module (A i) (N i)) := by
    apply Module.ext'
    intro r x
    exact IsScalarTower.algebraMap_smul (B i) r x
  have hfi := hi i le_rfl
  rw [hm] at hfi
  exact ⟨i.1, i.2, hfi⟩


end EventualFlatness

end PseudoCoherence

end
