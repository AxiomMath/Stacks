module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Flat base change of an equalizer, compared with a second equalizer

Let `A → A'` be a flat ring map.  Base change along it preserves equalizers of `A`-modules:
`A' ⊗_A (-)` is exact.  This file records the form of that statement which compares a base
changed equalizer with an equalizer of `A'`-modules: if `N → P ⇉ Q` is an equalizer of
`A`-modules, `M' → P' ⇉ Q'` an equalizer of `A'`-modules, the comparison `A' ⊗_A P → P'` is
bijective, the comparison `A' ⊗_A Q → Q'` is injective and both commute with the two pairs of
parallel arrows, then every `A`-linear map `N → M'` compatible with the first comparison has a
bijective `A'`-linear extension `A' ⊗_A N → M'`.

This is the algebraic step of the flat base change theorem for the degree-zero direct image
(Stacks 073K), where `N`, `P`, `Q` are the sections of a quasi-coherent module over a space, an
affine étale chart of it and a finite affine cover of the relation, and `M'`, `P'`, `Q'` are the
same after base change.

## Main results

* `LinearMap.bijective_liftBaseChange_of_equalizer`: the comparison statement above.
-/

@[expose] public section

open TensorProduct

namespace LinearMap

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [Module.Flat A A']
  {N P Q : Type*} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q]
  {M' P' Q' : Type*} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
  [AddCommGroup P'] [Module A' P'] [AddCommGroup Q'] [Module A' Q']

/-- Two `A'`-linear maps out of `A' ⊗[A] N` agreeing on the elements `1 ⊗ₜ n` are equal. -/
private theorem ext_of_one_tmul {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A' M]
    {f g : A' ⊗[A] N →ₗ[A'] M} (h : ∀ n, f (1 ⊗ₜ n) = g (1 ⊗ₜ n)) : f = g :=
  LinearMap.ext fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul r n => rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul, h]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Flat base change of an equalizer, compared with a second equalizer.**  Let `N → P ⇉ Q` be
an equalizer of `A`-modules (`i` injective with image the equalizer of `a` and `b`) and
`M' → P' ⇉ Q'` an equalizer of `A'`-modules, for a flat `A`-algebra `A'`.  Let
`θP : A' ⊗_A P → P'` be bijective and `θQ : A' ⊗_A Q → Q'` injective, compatible with the two
pairs of parallel arrows.  Then an `A`-linear map `μ : N → M'` with `i' ∘ μ = θP ∘ (1 ⊗ i)` has a
bijective `A'`-linear extension `A' ⊗_A N → M'`. -/
theorem bijective_liftBaseChange_of_equalizer (i : N →ₗ[A] P) (a b : P →ₗ[A] Q)
    (hi : Function.Injective i) (hab : a ∘ₗ i = b ∘ₗ i)
    (heq : ∀ p, a p = b p → ∃ n, i n = p)
    (i' : M' →ₗ[A'] P') (a' b' : P' →ₗ[A'] Q') (hi' : Function.Injective i')
    (hab' : a' ∘ₗ i' = b' ∘ₗ i')
    (θP : A' ⊗[A] P →ₗ[A'] P') (θQ : A' ⊗[A] Q →ₗ[A'] Q')
    (hθP : Function.Bijective θP) (hθQ : Function.Injective θQ)
    (ha : ∀ z, a' (θP z) = θQ (a.baseChange A' z))
    (hb : ∀ z, b' (θP z) = θQ (b.baseChange A' z))
    (μ : N →ₗ[A] M') (hμ : ∀ n, i' (μ n) = θP (1 ⊗ₜ i n)) :
    Function.Bijective (μ.liftBaseChange A') := by
  have hcomp : ∀ z, i' (μ.liftBaseChange A' z) = θP (i.baseChange A' z) :=
    LinearMap.congr_fun <| ext_of_one_tmul (f := i' ∘ₗ μ.liftBaseChange A')
      (g := θP ∘ₗ i.baseChange A') fun n => by simpa using hμ n
  have hiA : Function.Injective (i.baseChange A') :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hexact : Function.Exact i (a - b) := fun p =>
    ⟨fun hp => heq p (sub_eq_zero.mp hp),
      fun ⟨n, hn⟩ => hn ▸ sub_eq_zero.mpr (LinearMap.congr_fun hab n)⟩
  have hexactA : Function.Exact (i.baseChange A') ((a - b).baseChange A') :=
    Module.Flat.lTensor_exact A' hexact
  refine ⟨fun x y hxy => ?_, fun m => ?_⟩
  · apply hiA
    apply hθP.1
    rw [← hcomp, ← hcomp, hxy]
  · obtain ⟨z, hz⟩ := hθP.2 (i' m)
    have hz0 : (a - b).baseChange A' z = 0 := hθQ <| by
      rw [baseChange_sub, sub_apply, map_sub, map_zero, ← ha, ← hb, hz, sub_eq_zero]
      exact LinearMap.congr_fun hab' m
    obtain ⟨w, rfl⟩ := (hexactA z).mp hz0
    refine ⟨w, hi' ?_⟩
    rw [hcomp, hz]

/-- **Base change along one side of a pushout square of rings.**  If `B = S ⊗_R A` and
`M' = B ⊗_A M` through an `A`-linear map `u : M → M'`, then `M' = S ⊗_R M` through the same map. -/
theorem bijective_liftBaseChange_restrictScalars_of_isPushout {R S A B : Type*} [CommRing R]
    [CommRing S] [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B]
    [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    {M M' : Type*} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup M'] [Module B M'] [Module A M'] [IsScalarTower A B M'] [Module S M']
    [IsScalarTower S B M'] [Module R M'] [IsScalarTower R A M'] [IsScalarTower R S M']
    (u : M →ₗ[A] M') (hu : Function.Bijective (u.liftBaseChange B)) :
    Function.Bijective ((u.restrictScalars R).liftBaseChange S) := by
  have key : ((u.restrictScalars R).liftBaseChange S) =
      ((u.liftBaseChange B).restrictScalars S) ∘ₗ
        (Algebra.IsPushout.cancelBaseChange R S A B M).symm.toLinearMap := by
    ext m
    simp
  rw [key, LinearMap.coe_comp]
  exact hu.comp (Algebra.IsPushout.cancelBaseChange R S A B M).symm.bijective

/-- A compatibility of two extensions of scalars with a pair of maps, checked on pure tensors. -/
theorem map_liftBaseChange_eq_of_tmul {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {P Q P' Q' : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [AddCommGroup P'] [Module A' P'] [AddCommGroup Q'] [Module A' Q']
    (θP : A' ⊗[A] P →ₗ[A'] P') (θQ : A' ⊗[A] Q →ₗ[A'] Q') (uP : P → P') (uQ : Q → Q')
    (hθP : ∀ r p, θP (r ⊗ₜ p) = r • uP p) (hθQ : ∀ r q, θQ (r ⊗ₜ q) = r • uQ q)
    (a : P →ₗ[A] Q) (a' : P' →ₗ[A'] Q') (hnat : ∀ p, uQ (a p) = a' (uP p)) (z : A' ⊗[A] P) :
    a' (θP z) = θQ (a.baseChange A' z) := by
  have := ext_of_one_tmul (f := a' ∘ₗ θP) (g := θQ ∘ₗ a.baseChange A') fun p => by
    simp [hθP, hθQ, hnat]
  exact LinearMap.congr_fun this z

/-- An equality of a composite with an extension of scalars, checked on pure tensors. -/
theorem comp_eq_liftBaseChange_of_tmul {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {N M M' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A' M]
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
    (c : A' ⊗[A] N →ₗ[A'] M) (β : M →ₗ[A'] M') (μ : N →ₗ[A] M')
    (h : ∀ n, β (c (1 ⊗ₜ n)) = μ n) (z : A' ⊗[A] N) :
    β (c z) = μ.liftBaseChange A' z :=
  LinearMap.congr_fun (ext_of_one_tmul (f := β ∘ₗ c) (g := μ.liftBaseChange A') fun n => by
    simpa using h n) z

/-- A linear map which, after a bijective extension of scalars, becomes a bijective extension of
scalars, is bijective. -/
theorem bijective_of_comp_liftBaseChange {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    {N M M' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A' M]
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
    (c : A' ⊗[A] N →ₗ[A'] M) (β : M →ₗ[A'] M') (μ : N →ₗ[A] M')
    (h : ∀ n, β (c (1 ⊗ₜ n)) = μ n) (hc : Function.Bijective c)
    (hμ : Function.Bijective (μ.liftBaseChange A')) : Function.Bijective β := by
  have hfun : β ∘ c = μ.liftBaseChange A' := funext (comp_eq_liftBaseChange_of_tmul c β μ h)
  rw [← hfun] at hμ
  exact (Function.Bijective.of_comp_iff β hc).1 hμ

end LinearMap

end
