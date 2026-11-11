module

public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization
public import StacksFrontier.LinearAlgebra.ExteriorPower.Prod
public import StacksFrontier.LinearAlgebra.ExteriorPower.VanishingOfSpan

/-!
# Exterior powers of a product with an invertible module

Let `R` be a commutative ring, `M` an `R`-module and `L` an invertible `R`-module. Since `L` is
locally free of rank one, `⋀ʲ L = 0` for `j ≥ 2`, and the decomposition
`⋀ⁿ (M × L) ≃ ⨁_{p + q = n} ⋀ᵖ M ⊗ ⋀^q L` has only two nonzero summands:

`⋀ᵏ⁺¹ (M × L) ≃ ⋀ᵏ⁺¹ M × (⋀ᵏ M ⊗ L)`.

For `L = R` this reads `⋀ᵏ⁺¹ (M × R) ≃ ⋀ᵏ⁺¹ M × ⋀ᵏ M`; in degree zero `⋀⁰ (M × L) ≃ R` is
`exteriorPower.zeroEquiv`.

## Main definitions

* `DirectSum.linearEquivProdOfSubsingleton`: a direct sum all of whose summands but two are
  zero is the product of those two.
* `exteriorPower.prodEquivOfInvertible`: `⋀ᵏ⁺¹ (M × L) ≃ ⋀ᵏ⁺¹ M × (⋀ᵏ M ⊗ L)` for an
  invertible module `L`.
* `exteriorPower.prodRingEquiv`: `⋀ᵏ⁺¹ (M × R) ≃ ⋀ᵏ⁺¹ M × ⋀ᵏ M`.

## Main results

* `exteriorPower.subsingleton_of_invertible`: `⋀ʲ⁺² L = 0` for an invertible module `L`.

## Implementation notes

The vanishing of `⋀ʲ⁺² L` is checked at the maximal ideals: the exterior powers commute with
localization (`IsLocalization.isLocalizedModule_exteriorPowerMap`), and over a local ring an
invertible module is free of rank one, hence spanned by one element.
-/

@[expose] public section

open scoped DirectSum TensorProduct

namespace DirectSum

variable {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι] (F : ι → Type*)
  [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)]

/-- A direct sum of modules all of whose summands other than `F i₀` and `F i₁` are zero is
the product `F i₀ × F i₁`, through the two projections. -/
noncomputable def linearEquivProdOfSubsingleton (i₀ i₁ : ι) (hne : i₀ ≠ i₁)
    (h : ∀ i, i ≠ i₀ → i ≠ i₁ → Subsingleton (F i)) :
    (⨁ i, F i) ≃ₗ[R] F i₀ × F i₁ :=
  LinearEquiv.ofLinearMap ((component R ι F i₀).prod (component R ι F i₁))
    ((lof R ι F i₀).coprod (lof R ι F i₁))
    (by
      refine LinearMap.ext fun p => ?_
      obtain ⟨x, y⟩ := p
      refine Prod.ext ?_ ?_
      · change component R ι F i₀ (lof R ι F i₀ x + lof R ι F i₁ y) = x
        rw [map_add, component.lof_self, component.of, dite_eq_right hne.symm, add_zero]
      · change component R ι F i₁ (lof R ι F i₀ x + lof R ι F i₁ y) = y
        rw [map_add, component.lof_self, component.of, dite_eq_right hne, zero_add])
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      change lof R ι F i₀ (component R ι F i₀ (lof R ι F i x)) +
          lof R ι F i₁ (component R ι F i₁ (lof R ι F i x)) = lof R ι F i x
      rcases eq_or_ne i i₀ with rfl | h0
      · rw [component.lof_self, component.of, dite_eq_right hne, map_zero, add_zero]
      · rcases eq_or_ne i i₁ with rfl | h1
        · rw [component.lof_self, component.of, dite_eq_right h0, map_zero, zero_add]
        · have := h i h0 h1
          simp only [Subsingleton.elim x 0, map_zero, add_zero])

end DirectSum

namespace exteriorPower

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A module isomorphic to the ring is spanned by one element. -/
private theorem span_range_symm_one_eq_top {A X : Type*} [CommSemiring A] [AddCommMonoid X]
    [Module A X] (e : X ≃ₗ[A] A) :
    Submodule.span A (Set.range fun _ : Fin 1 => e.symm 1) = ⊤ := by
  rw [Set.range_const, Submodule.eq_top_iff']
  intro x
  rw [Submodule.mem_span_singleton]
  refine ⟨e x, ?_⟩
  rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-- **The exterior powers of degree at least two of an invertible module vanish.** -/
theorem subsingleton_of_invertible (L : Type*) [AddCommGroup L] [Module R L]
    [Module.Invertible R L] (j : ℕ) : Subsingleton (⋀[R]^(j + 2) L) := by
  refine Module.subsingleton_of_localization_maximal
    (Mₚ := fun P _ => ⋀[Localization.AtPrime P]^(j + 2) (LocalizedModule P.primeCompl L))
    (f := fun P _ => IsLocalization.exteriorPowerMap (Localization.AtPrime P)
      (LocalizedModule.mkLinearMap P.primeCompl L) (j + 2)) (fun P _ => ?_)
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl L))
  exact subsingleton_of_span_eq_top (fun _ : Fin 1 => e.symm 1)
    (span_range_symm_one_eq_top e) (by omega)

variable {L : Type*} [AddCommGroup L] [Module R L]

/-- In `⋀ᵏ⁺¹ (M × L) ≃ ⨁_{p + q = k + 1} ⋀ᵖ M ⊗ ⋀^q L` every summand other than those of
bidegrees `(k + 1, 0)` and `(k, 1)` vanishes, `L` being invertible. -/
theorem subsingleton_prodSummand [Module.Invertible R L] (k : ℕ)
    (i : {pq : ℕ × ℕ // pq.1 + pq.2 = k + 1})
    (h0 : i ≠ ⟨(k + 1, 0), rfl⟩) (h1 : i ≠ ⟨(k, 1), rfl⟩) :
    Subsingleton (TensorProduct R (⋀[R]^i.1.1 M) (⋀[R]^i.1.2 L)) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  have hpq' : p + q = k + 1 := hpq
  by_cases hq0 : q = 0
  · subst hq0
    obtain rfl : p = k + 1 := by omega
    exact (h0 rfl).elim
  by_cases hq1 : q = 1
  · subst hq1
    obtain rfl : p = k := by omega
    exact (h1 rfl).elim
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 2 := ⟨q - 2, by omega⟩
  have := subsingleton_of_invertible (R := R) L j
  exact (inferInstance : Subsingleton (⋀[R]^p M ⊗[R] ⋀[R]^(j + 2) L))

/-- The bidegrees `(k + 1, 0)` and `(k, 1)` are distinct. -/
theorem prodSummand_ne (k : ℕ) :
    (⟨(k + 1, 0), rfl⟩ : {pq : ℕ × ℕ // pq.1 + pq.2 = k + 1}) ≠ ⟨(k, 1), rfl⟩ := by
  intro h
  have h2 := congrArg (fun x : {pq : ℕ × ℕ // pq.1 + pq.2 = k + 1} => x.1.2) h
  exact absurd h2 Nat.zero_ne_one

/-- **The exterior powers of a product with an invertible module.** For an invertible
`R`-module `L`, `⋀ᵏ⁺¹ (M × L) ≃ ⋀ᵏ⁺¹ M × (⋀ᵏ M ⊗ L)`: the summands of bidegrees `(k + 1, 0)`
and `(k, 1)` of `exteriorPower.prodEquivDirectSum`, with `⋀⁰ L ≃ R` and `⋀¹ L ≃ L`. -/
noncomputable def prodEquivOfInvertible [Module.Invertible R L] (k : ℕ) :
    ⋀[R]^(k + 1) (M × L) ≃ₗ[R] ⋀[R]^(k + 1) M × (⋀[R]^k M ⊗[R] L) :=
  prodEquivDirectSum (R := R) (M := M) (N := L) (k + 1) ≪≫ₗ
    DirectSum.linearEquivProdOfSubsingleton (R := R)
      (fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = k + 1} =>
        TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 L))
      ⟨(k + 1, 0), rfl⟩ ⟨(k, 1), rfl⟩ (prodSummand_ne k)
      (fun i h0 h1 => subsingleton_prodSummand (M := M) (L := L) k i h0 h1) ≪≫ₗ
    LinearEquiv.prodCongr
      (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^(k + 1) M)) (zeroEquiv R L) ≪≫ₗ
        TensorProduct.rid R (⋀[R]^(k + 1) M))
      (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^k M)) (oneEquiv R L))

variable (R M) in
/-- **The exterior powers of `M × R`.** `⋀ᵏ⁺¹ (M × R) ≃ ⋀ᵏ⁺¹ M × ⋀ᵏ M`. -/
noncomputable def prodRingEquiv (k : ℕ) :
    ⋀[R]^(k + 1) (M × R) ≃ₗ[R] ⋀[R]^(k + 1) M × ⋀[R]^k M :=
  prodEquivOfInvertible (R := R) (M := M) (L := R) k ≪≫ₗ
    LinearEquiv.prodCongr (LinearEquiv.refl R (⋀[R]^(k + 1) M)) (TensorProduct.rid R (⋀[R]^k M))

end exteriorPower

end
