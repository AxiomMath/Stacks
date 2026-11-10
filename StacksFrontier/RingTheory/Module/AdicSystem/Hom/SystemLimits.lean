module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.Presentation.Finite
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow

@[expose] public section

/-!
# The `Hom` and `Isom` systems of adic reductions and their limits

For finite modules `M`, `N` over a Noetherian ring `A` with ideal `I`, this file builds the
inverse systems `n ↦ Hom_A(Mₙ, Nₙ)` and `n ↦ Isom_A(Mₙ, Nₙ)` of the adic reductions, the
comparison map from the adic quotients of `Hom_A(M, N)`, and identifies the inverse limits with
the homomorphisms and isomorphisms between the `I`-adic completions (part of Tag 09BB).
-/

/-! ## Tag 09BB -/

section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AdicSystem.HomComparison

universe u v w x

/-- **Stacks 00MB for a module of homomorphisms.** For finite modules `M`, `N` over a Noetherian
ring `A`, the `I`-adic completion of `Hom_A(M, N)` is the module of `A^∧`-linear maps between the
completions of `M` and `N`.

Over a Noetherian ring a finite module is finitely presented, so `M^∧ = A^∧ ⊗_A M` is a base
change (`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`) and the identification is the
base-change isomorphism for `Hom` out of a finitely presented module. -/
@[ega "0 7.3.4", ega "IV 2.5.8.6" "partial"]
public noncomputable def completedHomEquiv
    {A M N : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) :
    AdicCompletion I (M →ₗ[A] N) ≃ₗ[AdicCompletion I A]
      (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) := by
  let : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  let eM := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M
  let eN := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N
  let eH := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (M →ₗ[A] N)
  let eB := (Module.FinitePresentation.isBaseChange_map A M N (AdicCompletion I A)).equiv
  exact eH.symm.trans (eB.trans (eM.arrowCongr eN))

/-- The identification of `completedHomEquiv` carries the completion of a homomorphism `f` to the
map extending `f`: it agrees with `f` on the image of `M`. Since that image generates `M^∧`
topologically, this characterises the identification. -/
public lemma completedHomEquiv_of_apply
    {A M N : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) (f : M →ₗ[A] N) (m : M) :
    completedHomEquiv I (AdicCompletion.of I (M →ₗ[A] N) f)
        (AdicCompletion.of I M m) = AdicCompletion.of I N (f m) := by
  let : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  simp [completedHomEquiv, LinearEquiv.arrowCongr_apply,
    LinearMap.baseChangeHom_apply]

private noncomputable def completedHomEquivGeneral
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) :
    AdicCompletion I (M →ₗ[A] N) ≃ₗ[AdicCompletion I A]
      (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) := by
  letI : Small.{u} M := Module.Finite.small A M
  letI : Small.{u} N := Module.Finite.small A N
  let M₀ := Shrink.{u} M
  let N₀ := Shrink.{u} N
  letI : SMul A M₀ := (Shrink.addEquiv (α := M)).smul A
  letI : Module A M₀ := inferInstance
  letI : SMul A N₀ := (Shrink.addEquiv (α := N)).smul A
  letI : Module A N₀ := inferInstance
  letI : SMulCommClass A A N₀ := ⟨by
    intro a b n
    calc
      a • b • n = (a * b) • n := (mul_smul a b n).symm
      _ = (b * a) • n := by rw [mul_comm]
      _ = b • a • n := mul_smul b a n⟩
  let eM : M₀ ≃ₗ[A] M := Shrink.linearEquiv A M
  let eN : N₀ ≃ₗ[A] N := Shrink.linearEquiv A N
  let eH : (M₀ →ₗ[A] N₀) ≃ₗ[A] (M →ₗ[A] N) :=
    LinearEquiv.arrowCongr (σ₁₁' := RingHom.id A) (σ₂₂' := RingHom.id A) eM eN
  exact (AdicCompletion.congr I eH).symm.trans
    ((completedHomEquiv (A := A) (M := M₀) (N := N₀) I).trans
      ((AdicCompletion.congr I eM).arrowCongr (AdicCompletion.congr I eN)))

private lemma completedHomEquivGeneral_of_apply
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) (f : M →ₗ[A] N) (m : M) :
    completedHomEquivGeneral I (AdicCompletion.of I (M →ₗ[A] N) f)
        (AdicCompletion.of I M m) = AdicCompletion.of I N (f m) := by
  simp [completedHomEquivGeneral, AdicCompletion.map_of,
    completedHomEquiv_of_apply]

private lemma ideal_le_annihilator_quotient
    {A : Type u} {N : Type v} [CommRing A] [AddCommGroup N] [Module A N]
    (J : Ideal A) :
    J ≤ Module.annihilator A (N ⧸ J • (⊤ : Submodule A N)) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change r • (Submodule.Quotient.mk y : N ⧸ J • (⊤ : Submodule A N)) = 0
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero (J • (⊤ : Submodule A N))).mpr
      (Submodule.smul_mem_smul hr (Submodule.mem_top : y ∈ (⊤ : Submodule A N)))

/-- A linear map into a module annihilated by `J` kills `J • ⊤`. -/
private lemma smul_top_le_ker_of_le_annihilator
    {A : Type u} {X : Type v} {Y : Type w} [CommRing A]
    [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y]
    {J : Ideal A} (hJ : J ≤ Module.annihilator A Y) (F : X →ₗ[A] Y) :
    J • (⊤ : Submodule A X) ≤ F.ker := by
  rw [Submodule.smul_le]
  intro a ha z _
  change F (a • z) = 0
  rw [map_smul]
  exact (Module.mem_annihilator.mp (hJ ha)) (F z)

private noncomputable def homQuotientEquiv
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (J : Ideal A) :
    ((M ⧸ J • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ J • (⊤ : Submodule A N))) ≃ₗ[A]
      (M →ₗ[A] (N ⧸ J • (⊤ : Submodule A N))) := by
  let p : Submodule A M := J • ⊤
  let q : Submodule A N := J • ⊤
  let F : ((M ⧸ p) →ₗ[A] (N ⧸ q)) →ₗ[A] (M →ₗ[A] (N ⧸ q)) :=
    LinearMap.lcomp A (N ⧸ q) p.mkQ
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro f g h
    exact Submodule.linearMap_qext _ h
  · intro g
    exact ⟨p.liftQ g (smul_top_le_ker_of_le_annihilator (ideal_le_annihilator_quotient J) g),
      LinearMap.ext fun _ => rfl⟩

private lemma homQuotientEquiv_apply_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (J : Ideal A) (f : (M ⧸ J • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ J • (⊤ : Submodule A N))) (m : M) :
    homQuotientEquiv J f m = f (Submodule.Quotient.mk m) := rfl

private lemma homQuotientEquiv_symm_apply_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (J : Ideal A) (f : M →ₗ[A] (N ⧸ J • (⊤ : Submodule A N))) (m : M) :
    (homQuotientEquiv J).symm f (Submodule.Quotient.mk m) = f m := by
  rw [← homQuotientEquiv_apply_mk, LinearEquiv.apply_symm_apply]

private noncomputable def homTransition
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ) :
    ((M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N))) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
  (homQuotientEquiv (I ^ n)).symm.toLinearMap ∘ₗ
    LinearMap.compRight A (AdicCompletion.transitionMap I N (Nat.le_succ n)) ∘ₗ
    (homQuotientEquiv (I ^ (n + 1))).toLinearMap

private lemma homTransition_apply_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (f : (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N))) (m : M) :
    homTransition I n f (Submodule.Quotient.mk m) =
      AdicCompletion.transitionMap I N (Nat.le_succ n)
        (f (Submodule.Quotient.mk m)) := by
  simp [homTransition, homQuotientEquiv_symm_apply_mk,
    homQuotientEquiv_apply_mk]

private lemma homTransition_apply_transition
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (f : (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N)))
    (x : M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) :
    homTransition I n f (AdicCompletion.transitionMap I M (Nat.le_succ n) x) =
      AdicCompletion.transitionMap I N (Nat.le_succ n) (f x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ m => simpa using homTransition_apply_mk I n f m

private lemma homTransition_comp
    {A : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (I : Ideal A) (n : ℕ)
    (f : (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N)) →ₗ[A]
      (P ⧸ I ^ (n + 1) • (⊤ : Submodule A P)))
    (g : (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N))) :
    homTransition I n (f.comp g) =
      (homTransition I n f).comp (homTransition I n g) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    simp only [LinearMap.comp_apply, homTransition_apply_mk]
    exact (homTransition_apply_transition I n f (g (Submodule.Quotient.mk m))).symm

private lemma homTransition_id
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) :
    homTransition I n (LinearMap.id :
      (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) →ₗ[A]
      (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M))) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m => simp [homTransition_apply_mk]

private noncomputable def isoTransition
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (e : (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N))) :
    (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N)) :=
  LinearEquiv.ofLinearMap (homTransition I n e.toLinearMap)
    (homTransition I n e.symm.toLinearMap)
    (by rw [← homTransition_comp, e.comp_symm, homTransition_id])
    (by rw [← homTransition_comp, e.symm_comp, homTransition_id])

private lemma isoTransition_apply_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (e : (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N))) (m : M) :
    isoTransition I n e (Submodule.Quotient.mk m) =
      AdicCompletion.transitionMap I N (Nat.le_succ n)
        (e (Submodule.Quotient.mk m)) :=
  homTransition_apply_mk I n e.toLinearMap m

private lemma isoTransition_symm
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (e : (M ⧸ I ^ (n + 1) • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ (n + 1) • (⊤ : Submodule A N))) :
    isoTransition I n e.symm = (isoTransition I n e).symm := by
  apply LinearEquiv.ext
  intro x
  rfl

private lemma hom_quotient_annihilator
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (J : Ideal A) :
    J ≤ Module.annihilator A
      ((M ⧸ J • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ J • (⊤ : Submodule A N))) := by
  intro a ha
  rw [Module.mem_annihilator]
  exact fun f ↦ LinearMap.ext fun x ↦
    (Module.mem_annihilator.mp (ideal_le_annihilator_quotient (N := N) J ha)) (f x)

private noncomputable def comparison
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ) :
    ((M →ₗ[A] N) ⧸ I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))) := by
  let f : (M →ₗ[A] N) →ₗ[A]
    ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
    (LinearMap.restrictScalarsₗ A (A ⧸ I ^ n)
      (M ⧸ I ^ n • (⊤ : Submodule A M))
      (N ⧸ I ^ n • (⊤ : Submodule A N)) A).comp
      (LinearMap.reduceModIdeal (I ^ n))
  exact (I ^ n • (⊤ : Submodule A (M →ₗ[A] N))).liftQ f
    (smul_top_le_ker_of_le_annihilator (hom_quotient_annihilator (I ^ n)) f)

private noncomputable def mapCompletionOfCompatible
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : ∀ n, (M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N)))
    (hf : ∀ n, homTransition I n (f (n + 1)) = f n) :
    AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N := by
  let F : AdicCompletion I M → AdicCompletion I N := fun x =>
    ⟨fun n => f n (AdicCompletion.eval I M n x), by
      intro m n hmn
      symm
      apply Submodule.eq_factor_of_eq_factor_succ
        (fun _ _ h => Submodule.pow_smul_top_le I N h) _ (fun k => ?_) hmn
      have hx : AdicCompletion.transitionMap I M (Nat.le_succ k)
          (AdicCompletion.eval I M (k + 1) x) = AdicCompletion.eval I M k x :=
        AdicCompletion.transitionMap_comp_eval_apply I M (Nat.le_succ k) x
      rw [← hx, ← hf k]
      exact homTransition_apply_transition I k (f (k + 1))
        (AdicCompletion.eval I M (k + 1) x)⟩
  refine {
    toFun := F
    map_add' := ?_
    map_smul' := ?_ }
  · exact fun x y ↦ AdicCompletion.ext fun n ↦ map_add (f n) (x.val n) (y.val n)
  · refine fun r x ↦ AdicCompletion.ext fun n ↦ ?_
    change f n ((r • x).val n) = (r • F x).val n
    rw [AdicCompletion.smul_eval, AdicCompletion.smul_eval]
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_surjective
      (I ^ n • (⊤ : Submodule A A))) (r.val n)
    rw [← ha]
    change f n (a • x.val n) = a • f n (x.val n)
    exact map_smul (f n) a (AdicCompletion.eval I M n x)

private noncomputable def isoLimitToCompletion
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (e : { e : ∀ n, (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N)) //
      ∀ n, isoTransition I n (e (n + 1)) = e n }) :
    AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N := by
  let F := mapCompletionOfCompatible I (fun n => (e.val n).toLinearMap) (by
    intro n
    exact congrArg LinearEquiv.toLinearMap (e.property n))
  let G := mapCompletionOfCompatible I (fun n => (e.val n).symm.toLinearMap) (by
    intro n
    have h : isoTransition I n ((e.val (n + 1)).symm) = (e.val n).symm := by
      rw [isoTransition_symm, e.property n]
    exact congrArg LinearEquiv.toLinearMap h)
  refine LinearEquiv.ofLinearMap F G ?_ ?_
  · exact LinearMap.ext fun x ↦ AdicCompletion.ext fun n ↦ (e.val n).apply_symm_apply (x.val n)
  · exact LinearMap.ext fun x ↦ AdicCompletion.ext fun n ↦ (e.val n).symm_apply_apply (x.val n)

private noncomputable def completedIsoAtLevel
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) :
    (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N)) := by
  let hI : I.FG := IsNoetherian.noetherian I
  let eA : AdicCompletion I M ≃ₗ[A] AdicCompletion I N := e.restrictScalars A
  have hmap : Submodule.map eA.toLinearMap
      (I ^ n • (⊤ : Submodule A (AdicCompletion I M))) =
      I ^ n • (⊤ : Submodule A (AdicCompletion I N)) := by
    rw [Submodule.map_smul'']
    congr 1
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr eA.surjective
  exact (AdicCompletion.quotPowSMulTopEquiv hI M n).symm.trans
    ((Submodule.Quotient.equiv _ _ eA hmap).trans
      (AdicCompletion.quotPowSMulTopEquiv hI N n))

private noncomputable def completedHomAtLevel
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) :
    (M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N)) := by
  let hI : I.FG := IsNoetherian.noetherian I
  let fA : AdicCompletion I M →ₗ[A] AdicCompletion I N := f.restrictScalars A
  have h : I ^ n • (⊤ : Submodule A (AdicCompletion I M)) ≤
      (I ^ n • (⊤ : Submodule A (AdicCompletion I N))).comap fA :=
    Submodule.smul_top_le_comap_smul_top (I ^ n) fA
  exact (AdicCompletion.quotPowSMulTopEquiv hI N n).toLinearMap ∘ₗ
    (I ^ n • (⊤ : Submodule A (AdicCompletion I M))).mapQ
      (I ^ n • (⊤ : Submodule A (AdicCompletion I N))) fA h ∘ₗ
    (AdicCompletion.quotPowSMulTopEquiv hI M n).symm.toLinearMap

private lemma completedHomAtLevel_eval
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) (x : AdicCompletion I M) :
    completedHomAtLevel I f n (AdicCompletion.eval I M n x) =
      AdicCompletion.eval I N n (f x) := by
  let hI : I.FG := IsNoetherian.noetherian I
  have hx : AdicCompletion.eval I M n x =
      (AdicCompletion.quotPowSMulTopEquiv hI M n) (Submodule.Quotient.mk x) := rfl
  rw [hx]
  unfold completedHomAtLevel
  simp only [LinearMap.comp_apply]
  change (AdicCompletion.quotPowSMulTopEquiv hI N n)
    (((I ^ n • (⊤ : Submodule A (AdicCompletion I M))).mapQ
      (I ^ n • (⊤ : Submodule A (AdicCompletion I N)))
      (f.restrictScalars A) (Submodule.smul_top_le_comap_smul_top (I ^ n) _))
      ((AdicCompletion.quotPowSMulTopEquiv hI M n).symm
        ((AdicCompletion.quotPowSMulTopEquiv hI M n) (Submodule.Quotient.mk x)))) =
      AdicCompletion.eval I N n (f x)
  rw [LinearEquiv.symm_apply_apply]
  rfl

private lemma completedHomAtLevel_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) (m : M) :
    completedHomAtLevel I f n (Submodule.Quotient.mk m) =
      AdicCompletion.eval I N n (f (AdicCompletion.of I M m)) :=
  completedHomAtLevel_eval I f n (AdicCompletion.of I M m)

private lemma completedHomAtLevel_transition
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) :
    homTransition I n (completedHomAtLevel I f (n + 1)) =
      completedHomAtLevel I f n := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    rw [homTransition_apply_mk, completedHomAtLevel_mk,
      completedHomAtLevel_mk]
    exact AdicCompletion.transitionMap_comp_eval_apply I N (Nat.le_succ n)
      (f (AdicCompletion.of I M m))

private noncomputable def completedHomAtLevelLinear
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ) :
    (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))) where
  toFun := fun f => completedHomAtLevel I f n
  map_add' f g := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := AdicCompletion.eval_surjective I M n x
    simp only [completedHomAtLevel_eval, LinearMap.add_apply, map_add]
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := AdicCompletion.eval_surjective I M n x
    simp only [completedHomAtLevel_eval, LinearMap.smul_apply, map_smul]
    rfl

private noncomputable abbrev homSystem
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) : ℕᵒᵖ ⥤ ModuleCat A :=
  Functor.ofOpSequence
    (X := fun n => ModuleCat.of A
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))))
    (fun n => ModuleCat.ofHom (homTransition I n))

private noncomputable def completedHomCone
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) : Cone (homSystem (M := M) (N := N) I) := by
  refine Cone.mk
    (ModuleCat.of A (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N)) ?_
  refine NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (completedHomAtLevelLinear I n)) ?_
  intro n
  ext f
  dsimp only [homSystem]
  simp only [Functor.ofOpSequence_map_homOfLE_succ]
  change completedHomAtLevel I f n =
    homTransition I n (completedHomAtLevel I f (n + 1))
  exact (completedHomAtLevel_transition I f n).symm

private noncomputable def homLimitProjection
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ) :
    ↥(limit (homSystem (M := M) (N := N) I)) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
  (limit.π (homSystem (M := M) (N := N) I) (op n)).hom

private lemma limitHom_compatible
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (x : ↥(limit (homSystem (M := M) (N := N) I))) (n : ℕ) :
    homTransition I n (homLimitProjection I (n + 1) x) =
      homLimitProjection I n x := by
  have h := congrArg (fun g => (ModuleCat.Hom.hom g) x)
    (limit.w (homSystem (M := M) (N := N) I)
      ((homOfLE (Nat.le_succ n)).op))
  dsimp only [homSystem] at h
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  change homTransition I n (homLimitProjection I (n + 1) x) =
    homLimitProjection I n x at h
  exact h

private noncomputable def limitToCompletedHom
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) :
    ↥(limit (homSystem (M := M) (N := N) I)) →ₗ[A]
      (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) := by
  let F : ↥(limit (homSystem (M := M) (N := N) I)) →
      (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) :=
    fun x => mapCompletionOfCompatible I
      (fun n => homLimitProjection I n x)
      (limitHom_compatible I x)
  refine {
    toFun := F
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    apply LinearMap.ext
    intro z
    apply AdicCompletion.ext
    intro n
    change (homLimitProjection I n (x + y))
        (z.val n) =
      (homLimitProjection I n x + homLimitProjection I n y) (z.val n)
    rw [map_add]
  · intro a x
    apply LinearMap.ext
    intro z
    apply AdicCompletion.ext
    intro n
    change (homLimitProjection I n (a • x))
        (z.val n) =
      a • (homLimitProjection I n x) (z.val n)
    rw [map_smul, LinearMap.smul_apply]

private noncomputable def completedHomToLimit
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) :
    (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) →ₗ[A]
      ↥(limit (homSystem (M := M) (N := N) I)) :=
  (limit.lift (homSystem (M := M) (N := N) I) (completedHomCone I)).hom

private lemma completedHomToLimit_projection
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) :
    homLimitProjection I n (completedHomToLimit I f) =
      completedHomAtLevel I f n := by
  have h := limit.lift_π_apply
    (completedHomCone (A := A) (M := M) (N := N) I) (op n)
    (show ↥(completedHomCone (A := A) (M := M) (N := N) I).pt from f)
  exact h

private lemma limitToCompletedHom_comp_completedHomToLimit
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (f : AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) :
    limitToCompletedHom I (completedHomToLimit I f) = f := by
  refine LinearMap.ext fun x ↦ AdicCompletion.ext fun n ↦ ?_
  change (homLimitProjection I n (completedHomToLimit I f)) (x.val n) = (f x).val n
  rw [completedHomToLimit_projection]
  exact completedHomAtLevel_eval I f n x

private lemma completedHomToLimit_comp_limitToCompletedHom
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A)
    (x : ↥(limit (homSystem (M := M) (N := N) I))) :
    completedHomToLimit I (limitToCompletedHom I x) = x := by
  apply Concrete.limit_ext (homSystem (M := M) (N := N) I)
  intro j
  cases j with
  | op n =>
    change homLimitProjection I n (completedHomToLimit I (limitToCompletedHom I x)) =
      homLimitProjection I n x
    rw [completedHomToLimit_projection]
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      rw [completedHomAtLevel_mk]
      rfl

private noncomputable def limitCompletedHomIso
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) :
    limit (homSystem (M := M) (N := N) I) ≅
      ModuleCat.of A
        (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N) where
  hom := ModuleCat.ofHom (limitToCompletedHom I)
  inv := ModuleCat.ofHom (completedHomToLimit I)
  hom_inv_id :=
    ModuleCat.hom_ext <| LinearMap.ext fun x ↦ completedHomToLimit_comp_limitToCompletedHom I x
  inv_hom_id :=
    ModuleCat.hom_ext <| LinearMap.ext fun f ↦ limitToCompletedHom_comp_completedHomToLimit I f

private noncomputable def homLimitIso
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) :
    limit (homSystem (M := M) (N := N) I) ≅
      ModuleCat.of A (AdicCompletion I (M →ₗ[A] N)) :=
  limitCompletedHomIso I ≪≫
    ((completedHomEquivGeneral I).symm.restrictScalars A).toModuleIso

private lemma completedIsoAtLevel_eval
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) (x : AdicCompletion I M) :
    completedIsoAtLevel I e n (AdicCompletion.eval I M n x) =
      AdicCompletion.eval I N n (e x) := by
  let hI : I.FG := IsNoetherian.noetherian I
  have hx : AdicCompletion.eval I M n x =
      (AdicCompletion.quotPowSMulTopEquiv hI M n) (Submodule.Quotient.mk x) := rfl
  rw [hx]
  unfold completedIsoAtLevel
  simp only [LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_apply]
  simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    AdicCompletion.eval_apply]
  rfl

private lemma completedIsoAtLevel_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) (m : M) :
    completedIsoAtLevel I e n (Submodule.Quotient.mk m) =
      AdicCompletion.eval I N n (e (AdicCompletion.of I M m)) :=
  completedIsoAtLevel_eval I e n (AdicCompletion.of I M m)

private lemma completedIsoAtLevel_transition
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N)
    (n : ℕ) :
    isoTransition I n (completedIsoAtLevel I e (n + 1)) =
      completedIsoAtLevel I e n := by
  apply LinearEquiv.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    rw [isoTransition_apply_mk, completedIsoAtLevel_mk,
      completedIsoAtLevel_mk]
    exact AdicCompletion.transitionMap_comp_eval_apply I N (Nat.le_succ n)
      (e (AdicCompletion.of I M m))

private noncomputable def completedIsoFamily
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) :
    { a : ∀ n, (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N)) //
      ∀ n, isoTransition I n (a (n + 1)) = a n } :=
  ⟨fun n => completedIsoAtLevel I e n, completedIsoAtLevel_transition I e⟩

private noncomputable def isoLimitEquiv
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) :
    { a : ∀ n, (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N)) //
      ∀ n, isoTransition I n (a (n + 1)) = a n } ≃
      (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) where
  toFun := isoLimitToCompletion I
  invFun := completedIsoFamily I
  left_inv e := by
    apply Subtype.ext
    funext n
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ m =>
      change completedIsoAtLevel I (isoLimitToCompletion I e) n
        (Submodule.Quotient.mk m) = e.val n (Submodule.Quotient.mk m)
      rw [completedIsoAtLevel_mk]
      rfl
  right_inv e :=
    LinearEquiv.ext fun x ↦ AdicCompletion.ext fun n ↦ completedIsoAtLevel_eval I e n x

private lemma comparison_apply_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ) (f : M →ₗ[A] N) (m : M) :
    comparison I n (Submodule.Quotient.mk f) (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (f m) := by
  simp [comparison]

private lemma linearMap_eq_of_mem_smul_top
    {A : Type u} {X : Type v} {Y : Type w} [CommRing A]
    [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y]
    (J : Ideal A) (hJ : J ≤ Module.annihilator A Y)
    (F : X →ₗ[A] Y) {x y : X}
    (hxy : x - y ∈ J • (⊤ : Submodule A X)) : F x = F y := by
  have hzero : F (x - y) = 0 := smul_top_le_ker_of_le_annihilator hJ F hxy
  simpa only [map_sub, sub_eq_zero] using hzero

private lemma comparison_completedHomAtLevel
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) (n : ℕ) (c : AdicCompletion I (M →ₗ[A] N)) :
    comparison I n (AdicCompletion.eval I (M →ₗ[A] N) n c) =
      completedHomAtLevel I (completedHomEquivGeneral I c) n := by
  let F : AdicCompletion I (M →ₗ[A] N) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
    (comparison I n).comp (AdicCompletion.eval I (M →ₗ[A] N) n)
  let G : AdicCompletion I (M →ₗ[A] N) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
    (completedHomAtLevelLinear I n).comp
      ((completedHomEquivGeneral I).restrictScalars A).toLinearMap
  obtain ⟨f, hf⟩ :=
    Submodule.Quotient.mk_surjective
      (I ^ n • (⊤ : Submodule A (M →ₗ[A] N)))
      (AdicCompletion.eval I (M →ₗ[A] N) n c)
  have hdiff : c - AdicCompletion.of I (M →ₗ[A] N) f ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I (M →ₗ[A] N))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian I)]
    change AdicCompletion.eval I (M →ₗ[A] N) n
      (c - AdicCompletion.of I (M →ₗ[A] N) f) = 0
    rw [map_sub]
    simp [hf]
  have hconst : ∀ H : AdicCompletion I (M →ₗ[A] N) →ₗ[A]
      ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N))),
      H c = H (AdicCompletion.of I (M →ₗ[A] N) f) := fun H =>
    linearMap_eq_of_mem_smul_top (I ^ n)
      (hom_quotient_annihilator (M := M) (N := N) (I ^ n)) H hdiff
  change F c = G c
  rw [hconst F, hconst G]
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    change comparison I n (Submodule.Quotient.mk f) (Submodule.Quotient.mk m) =
      completedHomAtLevel I
        (completedHomEquivGeneral I (AdicCompletion.of I (M →ₗ[A] N) f)) n
        (Submodule.Quotient.mk m)
    rw [comparison_apply_mk, completedHomAtLevel_mk,
      completedHomEquivGeneral_of_apply]
    rfl

private lemma homLimitIso_projection
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A)
    (x : ↥(limit (homSystem (M := M) (N := N) I))) (n : ℕ) :
    comparison I n
        (AdicCompletion.eval I (M →ₗ[A] N) n ((homLimitIso I).hom.hom x)) =
      homLimitProjection I n x := by
  rw [comparison_completedHomAtLevel]
  change completedHomAtLevel I
      (completedHomEquivGeneral I
        ((completedHomEquivGeneral I).symm (limitToCompletedHom I x))) n =
      homLimitProjection I n x
  rw [LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
    rw [completedHomAtLevel_mk]
    rfl

end Stacks.AdicSystem.HomComparison

end

end
