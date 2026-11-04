module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDottedArrow

/-!
# Vanishing of a map of `Ext¹` groups via the blowup

Let `A` be a Noetherian ring, `I` an ideal, and `q₀ = q(S)`, `d = d(S)` the integers attached to
the blowing up of `Spec(A)` in `I`. For a two-term object `K` of `D(A/Iⁿ)` with finite cohomology
whose `Ext¹` into finite modules is killed by `I^c`, the map
`Ext¹(K, Iⁿ/I^{2n}) → Ext¹(K, I^{n-(1+d)c}/I^{2n-2(1+d)c})` is zero.

## Main results

* `Stacks.LocalCohomology.UniformityIII.ext_one_powQuot_map_eq_zero_blowup`: for
  `n ≥ q₀ + (1 + d)c`, the map `Ext¹(K, Iⁿ/I^{2n}) → Ext¹(K, I^{n-(1+d)c}/I^{2n-2(1+d)c})` is zero.
* `Stacks.LocalCohomology.UniformityIII.ext_one_powQuot_map_eq_zero_blowup_of_eq`: the same with
  the level `f = n - (1 + d)c` as a parameter.

## References

* [Stacks Project, Tag 0GAD](https://stacks.math.columbia.edu/tag/0GAD)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

attribute [local instance high] HasDerivedCategory.standard

/-- For `f + (1 + d(S))c = n` and `q(S) ≤ f`, the map `Ext¹(K, Iⁿ/I^{2n}) → Ext¹(K, I^f/I^{2f})`
is zero, for every `K` as in `ext_one_powQuot_map_eq_zero_blowup`. -/
theorem ext_one_powQuot_map_eq_zero_blowup_of_eq {n c f : ℕ}
    (hf : f + (1 + fibreDim I) * c = n) (hq : qS I ≤ f)
    (K : DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n)))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) i).obj K))
    (hfin₁ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) (-1)).obj K))
    (hfin₀ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj K))
    (hann : ∀ (N : ModuleCat.{u} (A ⧸ I ^ n)), Module.Finite (A ⧸ I ^ n) N →
      ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj N) 1, a • ξ = 0)
    (ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj (powQuotObj I n n)) 1) :
    ξ ≫ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n))) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).map
          (powQuotToOfLe I (Nat.le.intro hf) (by omega) (Nat.le.intro hf))) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : f = 0 := by omega
    have h0 : Subsingleton (powQuot I 0 0) := subsingleton_powQuot_zero I 0
    refine IsZero.eq_of_tgt ?_ _ _
    refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
    exact @ModuleCat.isZero_of_subsingleton _ _ (powQuotObjOfLe I 0 (le_refl 0)) h0
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hcn : c ≤ m + 1 := by
      have := Nat.le_mul_of_pos_left c (show 0 < 1 + fibreDim I by omega)
      omega
    exact (blowupDottedArrowSituationQS I m c hcn).ext_one_powQuot_map_eq_zero hf hq K hK
      hfin₁ hfin₀ hann ξ

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and `q₀ = q(S)`, `d = d(S)` the integers
attached to the blowing up of `Spec(A)` in `I` (`qS I` and `fibreDim I`). Let `c ≥ 0` and
`n ≥ q₀ + (1 + d)c`, and let `K` be an object of `D(A/Iⁿ)` with `Hⁱ(K) = 0` for `i ≠ -1, 0`, with
`H⁻¹(K)` and `H⁰(K)` finite, and such that `Ext¹_{A/Iⁿ}(K, N)` is annihilated by `I^c` for every
finite `A/Iⁿ`-module `N`. Then the map

`Ext¹_{A/Iⁿ}(K, Iⁿ/I^{2n}) ⟶ Ext¹_{A/Iⁿ}(K, I^{n-(1+d)c}/I^{2n-2(1+d)c})`

induced by the canonical map of coefficients is zero.

The target is written `powQuot I f f = I^f/I^{f+f}` with `f = n - (1 + d)c`, as an
`A/Iⁿ`-module (`powQuotObjOfLe`); the map is the one induced by `Iⁿ ⊆ I^f` (`powQuotToOfLe`). -/
@[stacks 0GAD]
theorem ext_one_powQuot_map_eq_zero_blowup {n c : ℕ}
    (hn : qS I + (1 + fibreDim I) * c ≤ n)
    (K : DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n)))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) i).obj K))
    (hfin₁ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) (-1)).obj K))
    (hfin₀ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj K))
    (hann : ∀ (N : ModuleCat.{u} (A ⧸ I ^ n)), Module.Finite (A ⧸ I ^ n) N →
      ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj N) 1, a • ξ = 0)
    (ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj (powQuotObj I n n)) 1) :
    ξ ≫ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n))) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).map
          (powQuotToOfLe I (Nat.sub_le n ((1 + fibreDim I) * c)) (by omega)
            (Nat.sub_le n ((1 + fibreDim I) * c)))) = 0 :=
  ext_one_powQuot_map_eq_zero_blowup_of_eq I (f := n - (1 + fibreDim I) * c) (by omega)
    (by omega) K hK hfin₁ hfin₀ hann ξ

end Stacks.LocalCohomology.UniformityIII

end
