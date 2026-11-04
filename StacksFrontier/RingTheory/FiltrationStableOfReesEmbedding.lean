module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.FiniteType

/-!
# Stability of a filtration from a Rees-linear embedding

Let `A` be Noetherian, `J ⊆ A` an ideal and `F` a `J`-filtration of an `A`-module `M` by finitely
generated submodules.  If the module `⨁ᵢ F.N i · Xⁱ ⊆ M[X]` over the Rees algebra `A[JX]` embeds,
by an injective `A[JX]`-linear map out of `M[X]`, into a finitely generated `A[JX]`-submodule of
some module, then `F` is stable.

## Main results

* `Ideal.Filtration.stable_of_injective_polynomialModule`: a filtration by finitely generated
  submodules is stable if its Rees module embeds injectively into a module over the Rees algebra
  with image inside a finitely generated submodule.
* `Ideal.Filtration.stable_of_reesAction`: a filtration is stable if, in an abelian group with an
  action of `A[X]`, the independent elements `Xᵏ · u(y)` with `y ∈ F.N k` lie in the image of an
  equivariant map out of a finite module over the Rees algebra.
-/

@[expose] public section

open Polynomial PolynomialModule

namespace Ideal.Filtration

variable {A : Type*} [CommRing A] [IsNoetherianRing A] {J : Ideal A} {M : Type*}
  [AddCommGroup M] [Module A M]

/-- **A filtration is stable if its Rees module embeds into a finitely generated module over the
Rees algebra.** -/
theorem stable_of_injective_polynomialModule (F : J.Filtration M) (hF : ∀ i, (F.N i).FG)
    {Q : Type*} [AddCommGroup Q] [Module (reesAlgebra J) Q]
    (θ : PolynomialModule A M →ₗ[reesAlgebra J] Q) (hθ : Function.Injective θ)
    (P : Submodule (reesAlgebra J) Q) (hP : P.FG)
    (hsub : ∀ i, ∀ y ∈ F.N i, θ (single A i y) ∈ P) : F.Stable := by
  have : IsNoetherianRing (reesAlgebra J) := Algebra.FiniteType.isNoetherianRing A _
  have : IsNoetherian (reesAlgebra J) P := isNoetherian_of_fg_of_noetherian P hP
  have hle : F.submodule.map θ ≤ P := by
    rw [← F.submodule_span_single, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
    exact hsub i y hy
  have hfg : (F.submodule.map θ).FG := by
    have h1 : ((F.submodule.map θ).comap P.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map P.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
  exact (F.submodule_fg_iff_stable hF).1 (Submodule.fg_of_fg_map_injective θ hθ hfg)

/-- Let `χ` be an action of `A[X]` on an abelian group `Q` by additive endomorphisms and
`u : M ⟶ Q` an additive map, `A`-linear for the action of the constants, such that the elements
`Xᵏ · u(yₖ)` are independent. If a finitely generated module `P` over the Rees algebra `A[JX]`
maps equivariantly to `Q` and its image contains every `Xᵏ · u(y)` with `y ∈ F.N k`, then `F` is
stable. -/
theorem stable_of_reesAction [Module.Finite A M] (F : J.Filtration M) {Q : Type*}
    [AddCommGroup Q] (χ : Polynomial A →+* AddMonoid.End Q) (u : M →+ Q)
    (hu : ∀ (a : A) (m : M), u (a • m) = χ (Polynomial.C a) (u m))
    (hinj : ∀ v : ℕ →₀ M, (v.sum fun k y => χ (Polynomial.X ^ k) (u y)) = 0 → v = 0)
    {P : Type*} [AddCommGroup P] [Module (reesAlgebra J) P] [Module.Finite (reesAlgebra J) P]
    (Φ : P →+ Q) (hΦ : ∀ (r : reesAlgebra J) (z : P), Φ (r • z) = χ r (Φ z))
    (hsub : ∀ k, ∀ y ∈ F.N k, χ (Polynomial.X ^ k) (u y) ∈ Set.range Φ) : F.Stable := by
  let : Module (Polynomial A) Q := Module.compHom Q χ
  let θ₀ : PolynomialModule A M →+ Q :=
    (Finsupp.liftAddHom fun k => (χ (Polynomial.X ^ k)).comp u).comp
      (PolynomialModule.coeffAddEquiv (R := A)).toAddMonoidHom
  have hθ₀ (k : ℕ) (y : M) :
      θ₀ (PolynomialModule.single A k y) = χ (Polynomial.X ^ k) (u y) :=
    Finsupp.liftAddHom_apply_single (fun k => (χ (Polynomial.X ^ k)).comp u) k y
  have hlin : ∀ (p : Polynomial A) (v : PolynomialModule A M), θ₀ (p • v) = χ p (θ₀ v) := by
    intro p v
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add]; rfl
    | monomial i a =>
      induction v using PolynomialModule.induction_linear with
      | zero => simp
      | add v w hv hw => rw [smul_add, map_add, hv, hw, map_add, map_add]
      | single j y =>
        rw [PolynomialModule.monomial_smul_single, hθ₀, hθ₀, hu,
          ← Polynomial.C_mul_X_pow_eq_monomial]
        show (χ (Polynomial.X ^ (i + j)) * χ (Polynomial.C a)) (u y) =
          (χ (Polynomial.C a * Polynomial.X ^ i) * χ (Polynomial.X ^ j)) (u y)
        rw [← map_mul, ← map_mul, pow_add]
        congr 2
        ring
  let θ : PolynomialModule A M →ₗ[reesAlgebra J] Q :=
    { toFun := θ₀
      map_add' := map_add θ₀
      map_smul' := fun r v => by
        rw [Subalgebra.smul_def, hlin]
        rfl }
  have hθ : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 := hinj v.coeff (by
      have : θ₀ v = 0 := hv
      rw [← this]
      show _ = (Finsupp.liftAddHom fun k => (χ (Polynomial.X ^ k)).comp u) v.coeff
      rw [Finsupp.liftAddHom_apply]
      rfl)
    rw [← PolynomialModule.ofCoeff_coeff v, h0]
    rfl
  let Φ' : P →ₗ[reesAlgebra J] Q :=
    { toFun := Φ
      map_add' := map_add Φ
      map_smul' := fun r z => by
        rw [hΦ]
        rfl }
  have hP : (LinearMap.range Φ').FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map Φ'
  have : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
  refine stable_of_injective_polynomialModule F (fun i => IsNoetherian.noetherian _) θ hθ
    (LinearMap.range Φ') hP (fun k y hy => ?_)
  obtain ⟨z, hz⟩ := hsub k y hy
  exact ⟨z, hz.trans (hθ₀ k y).symm⟩

end Ideal.Filtration
