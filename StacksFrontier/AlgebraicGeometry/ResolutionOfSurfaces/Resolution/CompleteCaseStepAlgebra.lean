module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown

/-!
# A completed local ring of a finite algebra as a finite algebra over a completion

Let `R₀` be a Noetherian domain, `S` a finite `R₀`-algebra, `p` a prime of `R₀` and `q` a prime
of `S` lying over `p`. Writing `Rₚ` and `S_q` for the local rings, the completion `S_q^` is a
factor of the base change `S ⊗[R₀] Rₚ^` of `S` to the completion of `Rₚ`
([Stacks, Tag 07N9]). This file makes `S_q^` into an algebra over `Rₚ^` through that factor and
records what the inductive step of the proof of [Stacks, Tag 0BGN] needs of it: `S_q^` is
finite over `Rₚ^`, its rank over `Rₚ^` is at most the rank of `S` over `R₀`, and — when `Rₚ^`
and `S_q^` are domains of the same finite dimension — the structure map is injective.

## Main results

* `AlgebraicGeometry.injective_of_isIntegral_of_ringKrullDim_eq_two`: an integral ring map from a
  Noetherian local domain of dimension two into a domain of dimension two is injective.
* `AlgebraicGeometry.exists_algebra_adicCompletion_finite_faithfulSMul_finrank_le`: the
  statement above.

## Implementation notes

The `Rₚ^`-algebra structure on `S_q^` is the one induced by the factor of [Stacks, Tag 07N9],
not the completion of the local map `Rₚ → S_q`; the two agree, but the conclusion is
existential in the algebra structure and the induced one makes the factor map `Rₚ^`-linear by
construction, which is what bounds the rank. The rank of the base change is computed by
`IsBaseChange.finrank_eq`, the map `R₀ → Rₚ^` being injective.

## References

* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u

namespace AlgebraicGeometry

/-- **An integral ring map from a Noetherian local domain of dimension two into a domain of
dimension two is injective.** Its kernel `P` is prime, and the target is integral over the
quotient by `P`, so that quotient has dimension at least two ([Stacks, Tag 00OJ]); a nonzero
element `a ∈ P` would give `dim S/P ≤ dim S/(a) ≤ dim S - 1 = 1`. -/
theorem injective_of_isIntegral_of_ringKrullDim_eq_two {S R : Type*} [CommRing S] [CommRing R]
    [IsNoetherianRing S] [IsLocalRing S] [IsDomain S] [IsDomain R] (F : S →+* R)
    (hF : F.IsIntegral) (hS : ringKrullDim S = 2) (hR : ringKrullDim R = 2) :
    Function.Injective F := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let G : S ⧸ RingHom.ker F →+* R := Ideal.Quotient.lift (RingHom.ker F) F fun _ hb => hb
  have hGF : G.comp (Ideal.Quotient.mk (RingHom.ker F)) = F := rfl
  have hG : G.IsIntegral := fun r => by
    obtain ⟨q, hqm, hq⟩ := hF r
    exact ⟨q.map (Ideal.Quotient.mk (RingHom.ker F)), hqm.map _,
      by rwa [Polynomial.eval₂_map, hGF]⟩
  let T : S ⧸ Ideal.span {a} →+* S ⧸ RingHom.ker F :=
    Ideal.Quotient.lift _ (Ideal.Quotient.mk (RingHom.ker F)) fun _ hb =>
      Ideal.Quotient.eq_zero_iff_mem.2 ((Ideal.span_singleton_le_iff_mem _).2 haP hb)
  have hTsurj : Function.Surjective T := fun y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ z, rfl⟩
  have hsucc : ringKrullDim (S ⧸ Ideal.span {a}) + 1 ≤ 2 :=
    hS ▸ ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero ha0)
  have hge : (2 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.span {a}) :=
    hR ▸ (integral_dim_up G hG).1.trans (ringKrullDim_le_of_surjective T hTsurj)
  have h3 : (2 : WithBot ℕ∞) + 1 ≤ 2 := (add_le_add_left hge 1).trans hsucc
  exact absurd h3 (by decide)

variable {R₀ S : Type u} [CommRing R₀] [CommRing S] [IsDomain R₀] [IsNoetherianRing R₀]
  [Algebra R₀ S] [Module.Finite R₀ S]

/-- **The completion of a local ring of a finite algebra, over the completion of the base.**
Let `R₀` be a Noetherian domain, `S` a finite `R₀`-algebra, `p` a prime of `R₀` with local ring
`Rₚ`, and `q₀` a prime of `S` over `p` with local ring `S_{q₀}`. Suppose the completions `Rₚ^`
and `S_{q₀}^` are domains, `Rₚ` has dimension at most two and `S_{q₀}^` has dimension two. Then
`Rₚ^` has dimension two, and `S_{q₀}^` carries the structure of a finite `Rₚ^`-algebra with
injective structure map and with rank over `Rₚ^` at most the rank of `S` over `R₀`. The
structure is the one induced by the factor `S ⊗[R₀] Rₚ^ → S_{q₀}^` of
[Stacks, Tag 07N9]. -/
theorem exists_algebra_adicCompletion_finite_faithfulSMul_finrank_le (p : Ideal R₀) [p.IsPrime]
    (Rp : Type u) [CommRing Rp] [Algebra R₀ Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    [IsDomain (AdicCompletion (maximalIdeal Rp) Rp)]
    (Sq : p.primesOver S → Type u) [∀ q, CommRing (Sq q)] [∀ q, Algebra S (Sq q)]
    [∀ q, IsLocalization.AtPrime (Sq q) q.1] [∀ q, IsLocalRing (Sq q)] (q₀ : p.primesOver S)
    [IsDomain (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀))]
    (hdimR : ringKrullDim Rp ≤ 2)
    (hdimS : ringKrullDim (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)) = 2) :
    ∃ _ : Algebra (AdicCompletion (maximalIdeal Rp) Rp)
        (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)),
      Module.Finite (AdicCompletion (maximalIdeal Rp) Rp)
          (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)) ∧
        FaithfulSMul (AdicCompletion (maximalIdeal Rp) Rp)
          (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)) ∧
        ringKrullDim (AdicCompletion (maximalIdeal Rp) Rp) = 2 ∧
        Module.finrank (AdicCompletion (maximalIdeal Rp) Rp)
          (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)) ≤ Module.finrank R₀ S := by
  have : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
  let Rh := AdicCompletion (maximalIdeal Rp) Rp
  let Sh := AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver p Rp Sq
  -- the factor of Tag 07N9, precomposed with the symmetry of the tensor product
  let Ψ : Rh ⊗[R₀] S →+* Sh := ((Pi.evalRingHom
      (fun q => AdicCompletion (maximalIdeal (Sq q)) (Sq q)) q₀).comp e.toRingHom).comp
    (Algebra.TensorProduct.comm R₀ Rh S).toRingHom
  have hΨ : Function.Surjective Ψ := by
    intro y
    obtain ⟨t, ht⟩ := e.surjective (Function.update 0 q₀ y)
    refine ⟨(Algebra.TensorProduct.comm R₀ Rh S).symm t, ?_⟩
    change e ((Algebra.TensorProduct.comm R₀ Rh S) ((Algebra.TensorProduct.comm R₀ Rh S).symm t))
      q₀ = y
    rw [AlgEquiv.apply_symm_apply, ht, Function.update_self]
  let alg : Algebra Rh Sh := (Ψ.comp (algebraMap Rh (Rh ⊗[R₀] S))).toAlgebra
  let ΨA : Rh ⊗[R₀] S →ₐ[Rh] Sh := { Ψ with commutes' := fun _ => rfl }
  have hfin : Module.Finite Rh Sh := Module.Finite.of_surjective ΨA.toLinearMap hΨ
  have hint : (algebraMap Rh Sh).IsIntegral :=
    algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite Rh Sh)
  -- the dimension of `Rₚ^` is two: at most two, and at least that of `S_{q₀}^`
  have hdimRh : ringKrullDim Rh = 2 := le_antisymm
    ((ringKrullDim_adicCompletion_maximalIdeal (A := Rp)).symm.trans_le hdimR)
    (hdimS ▸ (integral_dim_up (algebraMap Rh Sh) hint).1)
  refine ⟨alg, hfin, ?_, hdimRh, ?_⟩
  · -- the structure map is injective, by dimension
    rw [faithfulSMul_iff_algebraMap_injective]
    exact injective_of_isIntegral_of_ringKrullDim_eq_two (algebraMap Rh Sh) hint hdimRh hdimS
  · -- the rank is bounded by that of the base change, which is the rank of `S`
    have hinj : Function.Injective (algebraMap R₀ Rh) := by
      have h₁ : Function.Injective (algebraMap R₀ Rp) :=
        IsLocalization.injective Rp p.primeCompl_le_nonZeroDivisors
      have h₂ : Function.Injective (algebraMap Rp Rh) := AdicCompletion.of_injective _ _
      rw [IsScalarTower.algebraMap_eq R₀ Rp Rh]
      exact h₂.comp h₁
    have : FaithfulSMul R₀ Rh := (faithfulSMul_iff_algebraMap_injective R₀ Rh).mpr hinj
    rw [← (TensorProduct.isBaseChange R₀ S Rh).finrank_eq]
    exact LinearMap.finrank_le_finrank_of_surjective (f := ΨA.toLinearMap) hΨ

end AlgebraicGeometry

end
