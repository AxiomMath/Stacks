module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Norm.Transitivity
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# The norm of a finite projective domain with a full group of automorphisms

Let `A` be a domain which is a finite projective algebra over `R`, of constant rank `d`, with
`R ⟶ A` injective, and let `G` be a finite group acting faithfully on `A` by `R`-algebra
automorphisms with `#G = d`. Then the norm of `a ∈ A` is the product of its translates:

  `N_{A/R}(a) = ∏_{g ∈ G} g(a)`   in `A`.

The proof passes to fraction fields. With `K = Frac R` and `L = Frac A`, the square
`R ⟶ A ⟶ L`, `R ⟶ K ⟶ L` is a pushout (`A` is integral over `R`), so the norm of `A` over `R`
maps to the field norm of `L` over `K`, and `[L : K] = d`. The action of `G` extends to `L`
faithfully, so `Gal(L/K)` has at least `d = [L : K]` elements: `L/K` is Galois with group `G`,
and the field norm is the product over the Galois group
(`Algebra.norm_eq_prod_automorphisms`). Since `A ⟶ L` is injective, the identity descends.

This is the algebraic content of the identity on functions that Stacks 0FH9 offers in place of
the omitted computation of `π^*𝒩`: for `π : Xⁿ ⟶ Sⁿ(X)`, the composite of `Norm_π` with `π^♯` is
the product over `σ ∈ Sₙ` of the action of `σ`.

## Main results

* `Algebra.algebraMap_projectiveNorm_eq_prod`: the identity above, for a group acting through a
  monoid homomorphism `G →* (A ≃ₐ[R] A)`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

universe u

namespace Algebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsDomain A] [FaithfulSMul R A]
  [Module.Finite R A] [Module.Projective R A]

/-- **The norm of a finite projective domain is the product over a full group of
automorphisms.** If `A` is a domain, finite projective over `R` of constant rank `#G` with
`R ⟶ A` injective, and `ρ : G →* (A ≃ₐ[R] A)` is injective, then for every `a ∈ A`

  `N_{A/R}(a) = ∏_{g ∈ G} ρ(g)(a)`. -/
theorem algebraMap_projectiveNorm_eq_prod {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (A ≃ₐ[R] A)) (hρ : Function.Injective ρ)
    (hrank : ∀ p, Module.rankAtStalk (R := R) A p = Fintype.card G) (a : A) :
    algebraMap R A (projectiveNorm R a) = ∏ g, ρ g a := by
  classical
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R A).isDomain _
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra K L := FractionRing.liftAlgebra R L
  -- the pushout square `R ⟶ A ⟶ L`, `R ⟶ K ⟶ L`
  let e : K ⊗[R] A ≃ₐ[K] L := Algebra.IsPushout.equiv R K A L
  have : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  -- the degree of `L/K` is the rank of `A`
  have hfr : Module.finrank K L = Fintype.card G := by
    rw [← e.toLinearEquiv.finrank_eq]
    have h1 := Module.rankAtStalk_baseChange (R := R) (M := A) (S := K)
      (⊥ : PrimeSpectrum K)
    rw [Module.rankAtStalk_eq_finrank_of_free] at h1
    exact h1.trans (hrank _)
  -- the action extends to `L`
  let ρ' : G →* Gal(L/K) := (IsFractionRing.fieldEquivOfAlgEquivHom K L).comp ρ
  have hρ' : Function.Injective ρ' :=
    (IsFractionRing.fieldEquivOfAlgEquivHom_injective R A K L).comp hρ
  have hcardG : Fintype.card G ≤ Nat.card Gal(L/K) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective ρ' hρ'
  have hgal : Nat.card Gal(L/K) = Module.finrank K L :=
    le_antisymm ((Nat.card_congr (algEquivEquivAlgHom K L).toEquiv).le.trans
      (card_algHom_le_finrank K L L)) (hfr ▸ hcardG)
  have : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L hgal
  have hbij : Function.Bijective ρ' := by
    have : Fintype Gal(L/K) := Fintype.ofFinite _
    refine (Fintype.bijective_iff_injective_and_card ρ').2 ⟨hρ', ?_⟩
    rw [← Nat.card_eq_fintype_card (α := Gal(L/K)), hgal, hfr]
  -- the norm, computed in `L`
  apply IsFractionRing.injective A L
  have hnorm : algebraMap R K (projectiveNorm R a) = norm K (algebraMap A L a) := by
    rw [← projectiveNorm_baseChange, ← projectiveNorm_algEquiv K e,
      projectiveNorm_eq_norm_of_free]
    congr 1
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K L, hnorm,
    norm_eq_prod_automorphisms, map_prod]
  exact (Fintype.prod_bijective ρ' hbij _ _ fun g ↦
    (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L (ρ g) a).symm).symm

/-- **The norm as a product over a group acting by algebra endomorphisms.** The form of
`Algebra.algebraMap_projectiveNorm_eq_prod` for a family `φ : G → (A →ₐ[R] A)` which is
multiplicative for composition, `φ 1 = id` and `φ (σ * τ) = φ σ ∘ φ τ`, and injective. Each
`φ σ` is then an automorphism, with inverse `φ σ⁻¹`. This is the shape in which pullback of
functions along a group of automorphisms of a scheme over the base arrives. -/
theorem algebraMap_projectiveNorm_eq_prod_of_algHom {G : Type*} [Group G] [Fintype G]
    (φ : G → (A →ₐ[R] A)) (h1 : φ 1 = AlgHom.id R A)
    (hmul : ∀ σ τ, φ (σ * τ) = (φ σ).comp (φ τ)) (hφ : Function.Injective φ)
    (hrank : ∀ p, Module.rankAtStalk (R := R) A p = Fintype.card G) (a : A) :
    algebraMap R A (projectiveNorm R a) = ∏ g, φ g a := by
  have hinv : ∀ σ, (φ σ).comp (φ σ⁻¹) = AlgHom.id R A := fun σ ↦ by
    rw [← hmul, mul_inv_cancel, h1]
  let ρ : G →* (A ≃ₐ[R] A) :=
    { toFun := fun σ ↦ AlgEquiv.ofAlgHom (φ σ) (φ σ⁻¹) (hinv σ)
        (by simpa using hinv σ⁻¹)
      map_one' := AlgEquiv.ext fun x ↦ by simp [h1]
      map_mul' := fun σ τ ↦ AlgEquiv.ext fun x ↦ by simp [hmul] }
  exact algebraMap_projectiveNorm_eq_prod ρ
    (fun σ τ h ↦ hφ (AlgHom.ext fun x ↦ congrArg (fun e : A ≃ₐ[R] A ↦ e x) h)) hrank a

end Algebra
