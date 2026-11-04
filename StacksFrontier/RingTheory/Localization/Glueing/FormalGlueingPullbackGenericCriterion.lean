module

public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingPullbackDatum

/-!
# A criterion for a map out of a base change to be the generic map of a fibre product

Let `R → S` be a ring map, `N` an `R`-module, `P, Q` two `S`-modules, `a : S ⊗_R N → Q` and
`b : P → Q`.  The fibre product `N ×_Q P` of `n ↦ a(1 ⊗ n)` and `b`,
`FormalGlueing.pullbackSections`, comes with the generic map `S ⊗_R (N ×_Q P) → P`.  This file
recognises that map in disguise: an `S`-linear `T : S ⊗_R K → P` out of the base change of an
`R`-module `K`, together with an `R`-linear `κ : K → N` making `K` the fibre product of
`n ↦ a(1 ⊗ n)` and `b` through `(κ, T(1 ⊗ -))`, is the generic map up to the base change of the
comparison `K ≅ N ×_Q P`.  In particular `T` is bijective as soon as the generic map is.

## Main results

* `FormalGlueing.bijective_of_isFibreProduct`: the criterion.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u v w

namespace FormalGlueing

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

attribute [local instance] restrictFromTarget_isScalarTower

/-- **A map out of a base change which is the generic map of a fibre product in disguise is
bijective once the generic map is.**  Let `K` be an `R`-module with `κ : K → N` and an `S`-linear
`T : S ⊗_R K → P` such that `(κ, T(1 ⊗ -))` exhibits `K` as the fibre product of
`n ↦ a(1 ⊗ n)` and `b`: the square commutes, the pair is jointly injective, and every compatible
pair comes from `K`.  If the generic map `S ⊗_R (N ×_Q P) → P` is bijective, so is `T`. -/
theorem bijective_of_isFibreProduct (N : ModuleCat.{max u v w} R)
    (P Q : ModuleCat.{max u v w} S) (a : ModuleCat.of S (S ⊗[R] N) ⟶ Q) (b : P ⟶ Q)
    {K : Type*} [AddCommGroup K] [Module R K] (κ : K →ₗ[R] N) (T : S ⊗[R] K →ₗ[S] P)
    (hw : ∀ k, a.hom ((1 : S) ⊗ₜ[R] κ k) = b.hom (T ((1 : S) ⊗ₜ[R] k)))
    (hinj : ∀ k k', κ k = κ k' → T ((1 : S) ⊗ₜ[R] k) = T ((1 : S) ⊗ₜ[R] k') → k = k')
    (hsurj : ∀ (n : N) (p : P), a.hom ((1 : S) ⊗ₜ[R] n) = b.hom p →
      ∃ k, κ k = n ∧ T ((1 : S) ⊗ₜ[R] k) = p)
    (h : Function.Bijective (pullbackGenericMap S N P Q a b)) :
    Function.Bijective T := by
  let τ : K →ₗ[R] restrictFromTarget (R := R) S P :=
    { toFun := fun k => T ((1 : S) ⊗ₜ[R] k)
      map_add' := fun k k' => by
        rw [TensorProduct.tmul_add, map_add]
        rfl
      map_smul' := fun c k => by
        rw [TensorProduct.tmul_smul]
        show T (c • ((1 : S) ⊗ₜ[R] k)) = algebraMap R S c • T ((1 : S) ⊗ₜ[R] k)
        rw [← IsScalarTower.algebraMap_smul S c ((1 : S) ⊗ₜ[R] k), LinearMap.map_smul] }
  let Ψ : K →ₗ[R] pullbackSections S N P Q a b :=
    LinearMap.codRestrict (pullbackSections S N P Q a b) (LinearMap.prod κ τ)
      fun k => hw k
  have hΨ : Function.Bijective Ψ := by
    refine ⟨fun k k' hk => hinj k k'
      (congrArg (fun x : pullbackSections S N P Q a b => x.1.1) hk)
      (congrArg (fun x : pullbackSections S N P Q a b => x.1.2) hk), ?_⟩
    rintro ⟨⟨n, p⟩, hp⟩
    obtain ⟨k, hk₁, hk₂⟩ := hsurj n p hp
    exact ⟨k, Subtype.ext (Prod.ext hk₁ hk₂)⟩
  let e := LinearEquiv.ofBijective Ψ hΨ
  have hT : T = (pullbackGenericMap S N P Q a b).comp
      ((e.baseChange R S K (pullbackSections S N P Q a b)).toLinearMap) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s k =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul]
      rw [pullbackGenericMap_tmul]
      show T (s ⊗ₜ[R] k) = s • T ((1 : S) ⊗ₜ[R] k)
      rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact hT ▸ h.comp (e.baseChange R S K (pullbackSections S N P Q a b)).bijective

/-- **The criterion transported along additive identifications.**  The same as
`FormalGlueing.bijective_of_isFibreProduct`, with the fibre product exhibited on additive groups
`K', N', P', Q'` identified with `K, N, P, Q`. -/
theorem bijective_of_isFibreProduct_transport (N : ModuleCat.{max u v w} R)
    (P Q : ModuleCat.{max u v w} S) (a : ModuleCat.of S (S ⊗[R] N) ⟶ Q) (b : P ⟶ Q)
    {K : Type*} [AddCommGroup K] [Module R K] (κ : K →ₗ[R] N) (T : S ⊗[R] K →ₗ[S] P)
    {K' N' P' Q' : Type*} [AddCommGroup K'] [AddCommGroup N'] [AddCommGroup P']
    [AddCommGroup Q'] (fK : K' ≃+ K) (fN : N' ≃+ N) (fP : P' ≃+ P) (fQ : Q' ≃+ Q)
    {fst : K' → N'} {snd : K' → P'} {rr : N' → Q'} {bb : P' → Q'}
    (hκ : ∀ k, κ (fK k) = fN (fst k)) (hT : ∀ k, T ((1 : S) ⊗ₜ[R] fK k) = fP (snd k))
    (ha : ∀ n, a.hom ((1 : S) ⊗ₜ[R] fN n) = fQ (rr n)) (hb : ∀ p, b.hom (fP p) = fQ (bb p))
    (hw0 : ∀ k, rr (fst k) = bb (snd k))
    (hinj0 : ∀ k k', fst k = fst k' → snd k = snd k' → k = k')
    (hsurj0 : ∀ n p, rr n = bb p → ∃ k, fst k = n ∧ snd k = p)
    (h : Function.Bijective (pullbackGenericMap S N P Q a b)) :
    Function.Bijective T := by
  refine bijective_of_isFibreProduct S N P Q a b κ T ?_ ?_ ?_ h
  · intro k
    obtain ⟨k, rfl⟩ := fK.surjective k
    rw [hκ, ha, hT, hb, hw0]
  · intro k k' h₁ h₂
    obtain ⟨k, rfl⟩ := fK.surjective k
    obtain ⟨k', rfl⟩ := fK.surjective k'
    rw [hκ, hκ] at h₁
    rw [hT, hT] at h₂
    exact congrArg fK (hinj0 k k' (fN.injective h₁) (fP.injective h₂))
  · intro n p hnp
    obtain ⟨n, rfl⟩ := fN.surjective n
    obtain ⟨p, rfl⟩ := fP.surjective p
    rw [ha, hb] at hnp
    obtain ⟨k, hk₁, hk₂⟩ := hsurj0 n p (fQ.injective hnp)
    exact ⟨fK k, by rw [hκ, hk₁], by rw [hT, hk₂]⟩

end FormalGlueing

end
