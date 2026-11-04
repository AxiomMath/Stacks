module

public import StacksFrontier.RingTheory.AdicCompletion.ModuleEquivOfQuotientEquiv

/-!
# Semilinearity of an equivalence of adic completions built from linear levels

Let `A` be a ring, `R` and `S` be `A`-algebras with ideals `I` and `J`, and let `M` and `N` be
modules over `R` and `S`. Compatible `A`-linear equivalences
`M ⧸ IⁿM ≃ N ⧸ JⁿN` induce an additive equivalence of the adic completions,
`AdicCompletion.addEquivOfQuotientEquiv`. If a ring map `σ` of the completed rings is computed
level by level by `A`-algebra maps `R ⧸ Iⁿ → S ⧸ Jⁿ`, and every element of `R` is a fraction
`a / s` of elements of `A` whose denominator `s` is invertible in `S`, then the equivalence is
`σ`-semilinear.

This is the form in which a comparison of two completions of localizations, each built from
`A`-linear identifications of the levels, is seen to lie over the comparison of the rings: the
scalars of a localization are fractions, and an `A`-linear map commutes with fractions as soon as
the denominators act injectively on the target.

## Main results

* `AdicCompletion.smul_eq_of_mul_eq` — an `A`-linear map commutes with a fraction.
* `AdicCompletion.addEquivOfQuotientEquiv_smul_of_levels` — the semilinearity of the induced
  equivalence of completions.
-/

@[expose] public noncomputable section

namespace AdicCompletion

/-- If `s * r = a` in an `A`-algebra `R` acting on `M`, then `s • r • x = a • x`. -/
private theorem smul_smul_eq_of_mul_eq {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] {r : R} {a s : A}
    (hrs : algebraMap A R s * r = algebraMap A R a) (x : M) : s • r • x = a • x := by
  rw [← algebraMap_smul R s (r • x), smul_smul, hrs, algebraMap_smul]

/-- **An `A`-linear map commutes with fractions.** If `s • r = a` in an `A`-algebra `R` acting on
`M`, if `ψ` is an `A`-algebra map `R → S` and `s` acts injectively on the `S`-module `N`, then an
`A`-linear map `M → N` carries `r • x` to `ψ r • e x`. -/
public theorem smul_eq_of_mul_eq {A R S M N : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]
    (ψ : R →ₐ[A] S) (e : M →ₗ[A] N) {r : R} {a s : A}
    (hrs : algebraMap A R s * r = algebraMap A R a)
    (hs : Function.Injective fun y : N => s • y) (x : M) :
    e (r • x) = ψ r • e x := by
  apply hs
  dsimp only
  have h2 : algebraMap A S s * ψ r = algebraMap A S a := by
    rw [← ψ.commutes, ← ψ.commutes, ← map_mul, hrs]
  rw [← e.map_smul, smul_smul_eq_of_mul_eq hrs, e.map_smul, smul_smul_eq_of_mul_eq h2]

variable {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R] (I : Ideal R)
  {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
  {S : Type*} [CommRing S] [Algebra A S] (J : Ideal S)
  {N : Type*} [AddCommGroup N] [Module S N] [Module A N] [IsScalarTower A S N]

/-- **The equivalence of completions induced by `A`-linear levels is semilinear** over a ring
map `σ` computed level by level by `A`-algebra maps, as soon as the scalars of `R` are fractions
of elements of `A` whose denominators are units of `S`. -/
public theorem addEquivOfQuotientEquiv_smul_of_levels
    (e : ∀ n : ℕ, (M ⧸ (I ^ n • ⊤ : Submodule R M)) ≃ₗ[A] (N ⧸ (J ^ n • ⊤ : Submodule S N)))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : M ⧸ (I ^ n • ⊤ : Submodule R M)),
      transitionMap J N h ((e n).toAddEquiv x) = (e m).toAddEquiv (transitionMap I M h x))
    (σ : AdicCompletion I R → AdicCompletion J S) (ψ : ∀ n : ℕ, (R ⧸ I ^ n) →ₐ[A] (S ⧸ J ^ n))
    (hσ : ∀ (n : ℕ) (r : AdicCompletion I R), evalₐ J n (σ r) = ψ n (evalₐ I n r))
    (hfrac : ∀ r : R, ∃ a s : A, algebraMap A R s * r = algebraMap A R a ∧
      IsUnit (algebraMap A S s))
    (r : AdicCompletion I R) (x : AdicCompletion I M) :
    addEquivOfQuotientEquiv I J (fun n => (e n).toAddEquiv) he (r • x) =
      σ r • addEquivOfQuotientEquiv I J (fun n => (e n).toAddEquiv) he x := by
  refine addEquivOfQuotientEquiv_smul I J _ he σ (fun n r y => ?_) r x
  rw [val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul, hσ]
  obtain ⟨r₀, hr₀⟩ := Ideal.Quotient.mk_surjective (evalₐ I n r)
  obtain ⟨a, s, hrs, hs⟩ := hfrac r₀
  rw [← hr₀]
  have hrs' : algebraMap A (R ⧸ I ^ n) s * Ideal.Quotient.mk (I ^ n) r₀ =
      algebraMap A (R ⧸ I ^ n) a := by
    simpa using congrArg (Ideal.Quotient.mkₐ A (I ^ n)) hrs
  have hinj : Function.Injective fun z : N ⧸ (J ^ n • ⊤ : Submodule S N) => s • z := by
    intro z₁ z₂ hz
    obtain ⟨u, hu⟩ := hs
    have h := congrArg (fun w => (↑u⁻¹ : S) • w) hz
    simp only at h
    rwa [← algebraMap_smul S s z₁, ← algebraMap_smul S s z₂, ← hu, smul_smul, smul_smul,
      Units.inv_mul, one_smul, one_smul] at h
  exact smul_eq_of_mul_eq (ψ n) (e n).toLinearMap hrs' hinj y

end AdicCompletion

end
