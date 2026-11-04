module

public import StacksFrontier.Algebra.Module.FlatComplexNakayama
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import Mathlib.Algebra.Module.SpanRank

/-!
# Nakayama induction along a regular local ring

Let `A` be a ring and `R` a regular local `A`-algebra. A property `P` of `A`-algebras which is
invariant under isomorphism, holds for the residue field `R/𝔪_R`, and passes from `S/tS` to `S`
for every Noetherian local quotient `S` of `R` and nonzerodivisor `t ∈ 𝔪_S`, holds for `R`
(`Stacks.FlatComplexNakayama.induction_isRegularLocalRing`). Indeed a regular local ring `S` with
`𝔪_S ≠ 0` has an element `t ∈ 𝔪_S \ 𝔪_S²`; it is a nonzerodivisor because `S` is a domain, and
`S/tS` is again regular local with a maximal ideal needing one generator fewer.

Combined with the Nakayama steps of `StacksFrontier/Algebra/Module/FlatComplexNakayama.lean` this
gives: for a complex `E₀ ⟶ E₁ ⟶ E₂` of `A`-modules with `E₂` flat whose cohomology stays finite
after every Noetherian base change, exactness in the middle after base change to the residue field
of `R` implies exactness after base change to `R` (`isExactAt_of_isRegularLocalRing`), and
likewise for injectivity of a single map with flat target (`ker_eq_bot_of_isRegularLocalRing`).
This is how the cohomology-and-base-change arguments of
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2) are run here over a regular base,
one element of a regular system of parameters at a time.

## Main results

* `Stacks.FlatComplexNakayama.induction_isRegularLocalRing`: the induction principle.
* `Stacks.FlatComplexNakayama.isExactAt_of_isRegularLocalRing`.
* `Stacks.FlatComplexNakayama.ker_eq_bot_of_isRegularLocalRing`.
* `Stacks.FlatComplexNakayama.isExactAt_congr` and `ker_eq_bot_congr`: both properties are
  invariant under isomorphisms of `A`-algebras.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public section

open TensorProduct IsLocalRing

universe u v w

namespace Stacks.FlatComplexNakayama

variable {A : Type u} [CommRing A]

section Induction

/-- A regular local ring whose maximal ideal is not zero has an element of the maximal ideal
outside its square. -/
theorem exists_mem_maximalIdeal_notMem_sq (S : Type w) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (h : maximalIdeal S ≠ ⊥) :
    ∃ x ∈ maximalIdeal S, x ∉ maximalIdeal S ^ 2 := by
  by_contra hcon
  push Not at hcon
  apply h
  have hle : maximalIdeal S ≤ maximalIdeal S • maximalIdeal S := by
    intro x hx
    have := hcon x hx
    rwa [pow_two] at this
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S)
    (IsNoetherian.noetherian _) hle (maximalIdeal_le_jacobson ⊥)

/-- **Nakayama induction along a regular local ring.** -/
theorem induction_isRegularLocalRing {R : Type w} [CommRing R] [Algebra A R]
    [IsRegularLocalRing R]
    (P : ∀ (S : Type w) [CommRing S] [Algebra A S], Prop)
    (hiso : ∀ (S S' : Type w) [CommRing S] [CommRing S'] [Algebra A S] [Algebra A S'],
      (S ≃ₐ[A] S') → P S → P S')
    (hbase : P (R ⧸ maximalIdeal R))
    (hstep : ∀ (S : Type w) [CommRing S] [Algebra A S] [IsLocalRing S] [IsNoetherianRing S]
      (t : S), t ∈ maximalIdeal S → IsSMulRegular S t → P (S ⧸ Ideal.span {t}) → P S) :
    P R := by
  suffices key : ∀ n : ℕ, ∀ (S : Type w) [CommRing S] [Algebra A S] [IsRegularLocalRing S]
      (π : R →ₐ[A] S), Function.Surjective π → (maximalIdeal S).spanFinrank ≤ n → P S from
    key _ R (AlgHom.id A R) Function.surjective_id le_rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ _ π hπ hn
    have hfg : (maximalIdeal S).FG := IsNoetherian.noetherian _
    have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp (Nat.le_zero.mp hn)
    have hfield : IsField S := (isField_iff_maximalIdeal_eq).mpr hbot
    have hker : RingHom.ker π.toRingHom = maximalIdeal R := by
      let : Field S := hfield.toField
      exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π.toRingHom hπ)
    refine hiso _ _ ((Ideal.quotientEquivAlgOfEq A hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hπ)) hbase
  | succ n ih =>
    intro S _ _ _ π hπ hn
    by_cases hbot : maximalIdeal S = ⊥
    · exact ih S π hπ (by
        rw [hbot, Submodule.spanFinrank_bot]; exact Nat.zero_le _)
    obtain ⟨x, hx, hx2⟩ := exists_mem_maximalIdeal_notMem_sq S hbot
    have hdom : IsDomain S := IsRegularLocalRing.isDomain S
    have hx0 : x ≠ 0 := fun h => hx2 (h ▸ Submodule.zero_mem _)
    have hreg : IsSMulRegular S x := fun a b hab => mul_left_cancel₀ hx0 hab
    have hS' : IsRegularLocalRing (S ⧸ Ideal.span {x}) :=
      Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton hx hx2
    have hle := Stacks.RegularLocalRing.SpanFinrank.spanFinrank_maximalIdeal_succ_le_of_surjective
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective hx hx2
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x))
    have hP' : P (S ⧸ Ideal.span {x}) :=
      ih _ ((Ideal.Quotient.mkₐ A (Ideal.span {x})).comp π)
        ((Ideal.Quotient.mkₐ_surjective A _).comp hπ) (by omega)
    exact hstep S x hx hreg hP'

end Induction

section Homology

variable {E₀ E₁ E₂ : Type v} [AddCommGroup E₀] [AddCommGroup E₁] [AddCommGroup E₂]
  [Module A E₀] [Module A E₁] [Module A E₂] (d₀ : E₀ →ₗ[A] E₁) (d₁ : E₁ →ₗ[A] E₂)

/-- For an isomorphism of `A`-algebras `e : S ≃ₐ[A] S'` and an `A`-linear map `f : E → F`, the
base change of `f` to `S'` commutes with the maps `S ⊗[A] E → S' ⊗[A] E` and
`S ⊗[A] F → S' ⊗[A] F` induced by `e`. -/
theorem baseChange_rTensor_algEquiv_apply {E F : Type v} [AddCommGroup E] [AddCommGroup F]
    [Module A E] [Module A F] (f : E →ₗ[A] F) {S S' : Type w} [CommRing S] [CommRing S']
    [Algebra A S] [Algebra A S'] (e : S ≃ₐ[A] S') (x : S ⊗[A] E) :
    f.baseChange S' (e.toLinearMap.rTensor E x) = e.toLinearMap.rTensor F (f.baseChange S x) :=
  (rTensor_baseChange_apply f e.toAlgHom x).symm

/-- If the base change of `f` to `S'` kills `x`, then the base change of `f` to `S` kills the
preimage of `x` under the isomorphism `S ⊗[A] E ≃ S' ⊗[A] E` induced by `e : S ≃ₐ[A] S'`. -/
private theorem baseChange_symm_rTensor_eq_zero {E F : Type v} [AddCommGroup E] [AddCommGroup F]
    [Module A E] [Module A F] (f : E →ₗ[A] F) {S S' : Type w} [CommRing S] [CommRing S']
    [Algebra A S] [Algebra A S'] (e : S ≃ₐ[A] S') {x : S' ⊗[A] E} (hx : f.baseChange S' x = 0) :
    f.baseChange S ((LinearEquiv.rTensor E e.toLinearEquiv).symm x) = 0 := by
  have := baseChange_rTensor_algEquiv_apply f e.symm x
  rwa [hx, map_zero] at this

/-- Exactness in the middle after base change is invariant under isomorphisms of algebras. -/
theorem isExactAt_congr {S S' : Type w} [CommRing S] [CommRing S'] [Algebra A S]
    [Algebra A S'] (e : S ≃ₐ[A] S') (h : IsExactAt d₀ d₁ S) : IsExactAt d₀ d₁ S' := by
  intro x hx
  obtain ⟨y, hy⟩ := h _ (baseChange_symm_rTensor_eq_zero d₁ e hx)
  refine ⟨e.toLinearMap.rTensor E₀ y, ?_⟩
  rw [baseChange_rTensor_algEquiv_apply, hy]
  exact (LinearEquiv.rTensor E₁ e.toLinearEquiv).apply_symm_apply x

/-- Injectivity after base change is invariant under isomorphisms of algebras. -/
theorem ker_eq_bot_congr {S S' : Type w} [CommRing S] [CommRing S'] [Algebra A S]
    [Algebra A S'] (e : S ≃ₐ[A] S') (h : LinearMap.ker (d₀.baseChange S) = ⊥) :
    LinearMap.ker (d₀.baseChange S') = ⊥ := by
  rw [LinearMap.ker_eq_bot'] at h ⊢
  intro x hx
  exact (LinearEquiv.rTensor E₀ e.toLinearEquiv).symm.map_eq_zero_iff.mp
    (h _ (baseChange_symm_rTensor_eq_zero d₀ e hx))

/-- **Exactness propagates from the residue field to a regular local ring.** For a complex
`E₀ ⟶ E₁ ⟶ E₂` of `A`-modules with `E₂` flat whose middle cohomology is finite after every
Noetherian base change, exactness after base change to the residue field of a regular local
`A`-algebra `R` implies exactness after base change to `R`. -/
theorem isExactAt_of_isRegularLocalRing [Module.Flat A E₂] (hd : d₁ ∘ₗ d₀ = 0)
    {R : Type w} [CommRing R] [Algebra A R] [IsRegularLocalRing R]
    (hfin : ∀ (S : Type w) [CommRing S] [Algebra A S] [IsNoetherianRing S],
      Module.Finite S (homology d₀ d₁ S))
    (hbase : IsExactAt d₀ d₁ (R ⧸ maximalIdeal R)) : IsExactAt d₀ d₁ R :=
  induction_isRegularLocalRing (fun (S : Type w) [CommRing S] [Algebra A S] => IsExactAt d₀ d₁ S)
    (by intro S S' _ _ _ _ e h; exact isExactAt_congr d₀ d₁ e h) hbase (by
      intro S _ _ _ _ t ht hreg h
      exact isExactAt_of_quotient d₀ d₁ hd t ht hreg (hfin S) h)

/-- **Injectivity propagates from the residue field to a regular local ring.** For a map
`d : E₀ ⟶ E₁` of `A`-modules with `E₁` flat whose kernel is finite after every Noetherian base
change, injectivity after base change to the residue field of a regular local `A`-algebra `R`
implies injectivity after base change to `R`. -/
theorem ker_eq_bot_of_isRegularLocalRing [Module.Flat A E₁]
    {R : Type w} [CommRing R] [Algebra A R] [IsRegularLocalRing R]
    (hfin : ∀ (S : Type w) [CommRing S] [Algebra A S] [IsNoetherianRing S],
      Module.Finite S (LinearMap.ker (d₀.baseChange S)))
    (hbase : LinearMap.ker (d₀.baseChange (R ⧸ maximalIdeal R)) = ⊥) :
    LinearMap.ker (d₀.baseChange R) = ⊥ :=
  induction_isRegularLocalRing
    (fun (S : Type w) [CommRing S] [Algebra A S] => LinearMap.ker (d₀.baseChange S) = ⊥)
    (by intro S S' _ _ _ _ e h; exact ker_eq_bot_congr d₀ e h) hbase (by
      intro S _ _ _ _ t ht hreg h
      exact ker_eq_bot_of_quotient d₀ t ht hreg (hfin S) h)

end Homology

end Stacks.FlatComplexNakayama

end
