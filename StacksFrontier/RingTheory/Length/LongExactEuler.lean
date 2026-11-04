module

public import StacksFrontier.RingTheory.Length.IndexAdditivity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of a long exact sequence of three families

The proof of Tag 0B0W needs that the alternating sum of lengths

`χ(ℱ) = ∑ₚ (-1)ᵖ length_A Torₚ(ℱ, 𝒢)`

is additive along a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`, and the reason is the long
exact sequence of `Tor`s

`⋯ → T₁ₚ₊₁ → T₂ₚ₊₁ → T₃ₚ₊₁ →δ T₁ₚ → T₂ₚ → T₃ₚ → ⋯ → T₁₀ → T₂₀ → T₃₀ → 0`

together with additivity of length. This file proves exactly that implication, as a statement
about three families of modules and the maps of such a sequence, with no reference to `Tor` or
to sheaves: `χ(T₂) = χ(T₁) + χ(T₃)`.

## Main results

* `Module.sum_range_alternating_length_add_of_exact` — `χ(T₂) = χ(T₁) + χ(T₃)`, with the three
  alternating sums truncated at a degree `d`.
* `Module.finsum_alternating_length_add_of_exact` — the same with the sums taken as `finsum`s
  over all of `ℕ`, which is the shape the cycle of an alternating sum of `Tor` sheaves is
  written in. This is the `Module.length` analogue of
  `Module.finsum_alternating_finrank_add_of_exact`, the same statement over a field.
* `Module.lengthToNat_sub_add_eq_ker_of_longExact_zero` and
  `Module.lengthToNat_sub_add_eq_add_range_of_longExact` — the single-degree identities
  `length T₁ₚ - length T₂ₚ + length T₃ₚ = length (ker (T₁ₚ → T₂ₚ)) + length (im δₚ₋₁)` that
  drive it, in the two forms the induction needs.

## Implementation notes

The three sums are truncated at a degree `d`, and the only hypothesis about the top of the
sequence is `Subsingleton (T₃ (d + 1))`: that one module being zero kills the connecting map
`δ d` out of it, which is exactly what makes the telescoping sum collapse. Nothing is assumed
about `T₁` or `T₂` above `d`, and nothing about `T₃` above `d + 1`. In the application `d` is
the dimension of the ambient regular scheme, above which every `Tor` sheaf vanishes, so the
truncated sums are the honest ones.

The engine is `Module.lengthToNat_eq_ker_add_range`, which splits the length of a finite-length
module into the lengths of the kernel and the range of a map out of it, packaged as
`Module.length_alternating_exact_six` applied to

`0 → ker(T₁ₚ → T₂ₚ) → T₁ₚ → T₂ₚ → T₃ₚ → im δₚ₋₁ → 0`.

Writing `aₚ = length (im δₚ)`, exactness at `T₁ₚ` turns `length (ker (T₁ₚ → T₂ₚ))` into `aₚ`, so
each degree contributes `aₚ + aₚ₋₁` and the alternating sum telescopes to `± a_d`, which is zero
because `δ d` leaves a zero module. The zero module closing the six-term sequence is spelled as
the bottom submodule of a module already in play rather than as `PUnit`, so no instances have to
be supplied for it.

Lengths are `ℕ∞`-valued and `ENat.toNat` is additive only on finite values, which is why finite
length of each term is a hypothesis; the identities are then stated in `ℤ`, where the
subtractions of the alternating sum are honest.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 00IV](https://stacks.math.columbia.edu/tag/00IV)
-/

@[expose] public section

namespace Module

universe u

variable {A : Type u} [CommRing A]
  {T₁ T₂ T₃ : ℕ → Type u}
  [∀ p, AddCommGroup (T₁ p)] [∀ p, Module A (T₁ p)]
  [∀ p, AddCommGroup (T₂ p)] [∀ p, Module A (T₂ p)]
  [∀ p, AddCommGroup (T₃ p)] [∀ p, Module A (T₃ p)]
  (u : ∀ p, T₁ p →ₗ[A] T₂ p) (v : ∀ p, T₂ p →ₗ[A] T₃ p)
  (δ : ∀ p, T₃ (p + 1) →ₗ[A] T₁ p)

/-! ### The zero module closing a six-term sequence -/

private theorem isFiniteLength_bot (M : Type u) [AddCommGroup M] [Module A M] :
    IsFiniteLength A (⊥ : Submodule A M) :=
  isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩

private theorem lengthToNat_bot (M : Type u) [AddCommGroup M] [Module A M] :
    (Module.length A (⊥ : Submodule A M)).toNat = 0 := by
  simp

/-- The zero map into the bottom submodule is surjective. -/
private theorem surjective_toBot {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] :
    Function.Surjective (0 : M →ₗ[A] (⊥ : Submodule A N)) :=
  fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- A zero module has length zero. -/
private theorem lengthToNat_eq_zero_of_subsingleton (M : Type u) [AddCommGroup M] [Module A M]
    [Subsingleton M] : (Module.length A M).toNat = 0 := by
  simp

/-- Two equal submodules have the same length. -/
private theorem lengthToNat_congr {M : Type u} [AddCommGroup M] [Module A M]
    {N₁ N₂ : Submodule A M} (h : N₁ = N₂) :
    (Module.length A N₁).toNat = (Module.length A N₂).toNat := by subst h; rfl

/-! ### The single-degree identities -/

/-- The alternating sum of lengths along `0 → ker f → M₁ → M₂ → M₃ → C → 0` vanishes. -/
private theorem lengthToNat_sub_add_eq_ker_add_of_exact {M₁ M₂ M₃ C : Type u}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    [AddCommGroup M₃] [Module A M₃] [AddCommGroup C] [Module A C]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (h : M₃ →ₗ[A] C)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h) (hh : Function.Surjective h)
    (hf₁ : IsFiniteLength A M₁) (hf₂ : IsFiniteLength A M₂) (hf₃ : IsFiniteLength A M₃)
    (hfC : IsFiniteLength A C) :
    ((Module.length A M₁).toNat : ℤ) - ((Module.length A M₂).toNat : ℤ) +
        ((Module.length A M₃).toNat : ℤ) =
      ((Module.length A (LinearMap.ker f)).toNat : ℤ) + ((Module.length A C).toNat : ℤ) := by
  have hsix := Module.length_alternating_exact_six
    (LinearMap.ker f).subtype f g h (0 : C →ₗ[A] (⊥ : Submodule A C))
    (Submodule.subtype_injective _) surjective_toBot
    (LinearMap.exact_iff.2 (by simp)) hfg hgh
    ((LinearMap.exact_zero_iff_surjective _ _).2 hh)
    (IsFiniteLength.of_injective hf₁ (Submodule.subtype_injective _)) hf₁ hf₂ hf₃ hfC
  have hb := lengthToNat_bot (A := A) C
  omega

/-- **The single-degree identity in degree zero.** For the tail `T₁ 0 → T₂ 0 → T₃ 0 → 0` of the
sequence, `length (T₁ 0) - length (T₂ 0) + length (T₃ 0) = length (ker (u 0))`. -/
theorem lengthToNat_sub_add_eq_ker_of_longExact_zero
    (hv : ∀ p, Function.Exact (u p) (v p)) (hv0 : Function.Surjective (v 0))
    (hf₁ : IsFiniteLength A (T₁ 0)) (hf₂ : IsFiniteLength A (T₂ 0))
    (hf₃ : IsFiniteLength A (T₃ 0)) :
    ((Module.length A (T₁ 0)).toNat : ℤ) - ((Module.length A (T₂ 0)).toNat : ℤ) +
        ((Module.length A (T₃ 0)).toNat : ℤ) =
      ((Module.length A (LinearMap.ker (u 0))).toNat : ℤ) := by
  have h := lengthToNat_sub_add_eq_ker_add_of_exact (u 0) (v 0)
    (0 : T₃ 0 →ₗ[A] (⊥ : Submodule A (T₃ 0))) (hv 0)
    ((LinearMap.exact_zero_iff_surjective _ _).2 hv0) surjective_toBot hf₁ hf₂ hf₃
    (isFiniteLength_bot (A := A) (T₃ 0))
  rw [h, lengthToNat_bot, Nat.cast_zero, add_zero]

/-- **The single-degree identity in a positive degree.** For the window
`ker (u (p+1)) → T₁ (p+1) → T₂ (p+1) → T₃ (p+1) → im (δ p) → 0` of the sequence,
`length (T₁ (p+1)) - length (T₂ (p+1)) + length (T₃ (p+1))
  = length (ker (u (p+1))) + length (im (δ p))`. -/
theorem lengthToNat_sub_add_eq_add_range_of_longExact
    (hv : ∀ p, Function.Exact (u p) (v p))
    (hδ : ∀ p, Function.Exact (v (p + 1)) (δ p)) (p : ℕ)
    (hf₁ : IsFiniteLength A (T₁ (p + 1))) (hf₂ : IsFiniteLength A (T₂ (p + 1)))
    (hf₃ : IsFiniteLength A (T₃ (p + 1))) :
    ((Module.length A (T₁ (p + 1))).toNat : ℤ) - ((Module.length A (T₂ (p + 1))).toNat : ℤ) +
        ((Module.length A (T₃ (p + 1))).toNat : ℤ) =
      ((Module.length A (LinearMap.ker (u (p + 1)))).toNat : ℤ) +
        ((Module.length A (LinearMap.range (δ p))).toNat : ℤ) := by
  exact lengthToNat_sub_add_eq_ker_add_of_exact (u (p + 1)) (v (p + 1)) (δ p).rangeRestrict
    (hv (p + 1))
    (LinearMap.exact_iff.2 (by
      rw [LinearMap.ker_rangeRestrict]
      exact LinearMap.exact_iff.1 (hδ p)))
    (δ p).surjective_rangeRestrict hf₁ hf₂ hf₃
    (IsFiniteLength.of_surjective hf₃ (δ p).surjective_rangeRestrict)

/-! ### Additivity of the Euler characteristic -/

/-- **The Euler characteristic of a long exact sequence of three families is additive.** Let

`⋯ → T₁ₚ₊₁ → T₂ₚ₊₁ → T₃ₚ₊₁ →δₚ T₁ₚ → T₂ₚ → T₃ₚ → ⋯ → T₁₀ → T₂₀ → T₃₀ → 0`

be exact, with every term of finite length and `T₃ (d + 1) = 0`. Then

`∑ₚ₌₀..d (-1)ᵖ length (T₂ p) = ∑ₚ₌₀..d (-1)ᵖ length (T₁ p) + ∑ₚ₌₀..d (-1)ᵖ length (T₃ p)`.

This is the additivity of `χ(ℱ) = ∑ₚ (-1)ᵖ length Torₚ(ℱ, 𝒢)` along a short exact sequence,
which is the second of the two additivity steps in the proof of Tag 0B0W. -/
@[ega "0 11.10.2" "special case"]
theorem sum_range_alternating_length_add_of_exact
    (hu : ∀ p, Function.Exact (δ p) (u p)) (hv : ∀ p, Function.Exact (u p) (v p))
    (hδ : ∀ p, Function.Exact (v (p + 1)) (δ p)) (hv0 : Function.Surjective (v 0))
    (hf₁ : ∀ p, IsFiniteLength A (T₁ p)) (hf₂ : ∀ p, IsFiniteLength A (T₂ p))
    (hf₃ : ∀ p, IsFiniteLength A (T₃ p)) (d : ℕ) (hd : Subsingleton (T₃ (d + 1))) :
    ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T₂ p)).toNat : ℤ) =
      ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T₁ p)).toNat : ℤ) +
        ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T₃ p)).toNat : ℤ) := by
  -- The alternating sum of the single-degree identities telescopes to `± length (im δ_P)`.
  have key : ∀ P : ℕ,
      ∑ p ∈ Finset.range (P + 1), (-1 : ℤ) ^ p *
          (((Module.length A (T₁ p)).toNat : ℤ) - ((Module.length A (T₂ p)).toNat : ℤ) +
            ((Module.length A (T₃ p)).toNat : ℤ)) =
        (-1 : ℤ) ^ P * ((Module.length A (LinearMap.range (δ P))).toNat : ℤ) := by
    intro P
    induction P with
    | zero =>
      rw [Finset.sum_range_one,
        lengthToNat_sub_add_eq_ker_of_longExact_zero u v hv hv0 (hf₁ 0) (hf₂ 0) (hf₃ 0),
        lengthToNat_congr (LinearMap.exact_iff.1 (hu 0))]
    | succ P ih =>
      rw [Finset.sum_range_succ, ih,
        lengthToNat_sub_add_eq_add_range_of_longExact u v δ hv hδ P
          (hf₁ (P + 1)) (hf₂ (P + 1)) (hf₃ (P + 1)),
        lengthToNat_congr (LinearMap.exact_iff.1 (hu (P + 1)))]
      ring
  -- At `P = d` the connecting map leaves a zero module, so its image is zero.
  have hzero : ((Module.length A (LinearMap.range (δ d))).toNat : ℤ) = 0 := by
    have hbot : LinearMap.range (δ d) = ⊥ := by
      refine le_antisymm (fun y hy => ?_) bot_le
      obtain ⟨z, rfl⟩ := hy
      rw [Subsingleton.elim z 0, map_zero]
      exact Submodule.zero_mem _
    rw [lengthToNat_congr hbot, lengthToNat_bot]
    rfl
  have hsum := key d
  rw [hzero, mul_zero] at hsum
  have hexp : ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p *
      (((Module.length A (T₁ p)).toNat : ℤ) - ((Module.length A (T₂ p)).toNat : ℤ) +
        ((Module.length A (T₃ p)).toNat : ℤ)) =
      (∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T₁ p)).toNat : ℤ) -
          ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T₂ p)).toNat : ℤ)) +
        ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T₃ p)).toNat : ℤ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hexp] at hsum
  linarith

/-- An alternating sum of lengths over all of `ℕ` is the truncated sum, once the modules vanish
above the truncation degree. -/
private theorem finsum_alternating_length_eq_sum_range {T : ℕ → Type u}
    [∀ p, AddCommGroup (T p)] [∀ p, Module A (T p)] (d : ℕ)
    (hT : ∀ p, d < p → Subsingleton (T p)) :
    (∑ᶠ p : ℕ, (-1 : ℤ) ^ p * ((Module.length A (T p)).toNat : ℤ)) =
      ∑ p ∈ Finset.range (d + 1), (-1 : ℤ) ^ p * ((Module.length A (T p)).toNat : ℤ) := by
  refine finsum_eq_sum_of_support_subset _ (s := Finset.range (d + 1)) fun p hp => ?_
  simp only [Function.mem_support, ne_eq] at hp
  simp only [Finset.coe_range, Set.mem_Iio]
  rcases Nat.lt_or_ge p (d + 1) with h | h
  · exact h
  · have : Subsingleton (T p) := hT p (by omega)
    exact absurd (by simp) hp

/-- **The Euler characteristic of a long exact sequence of three families is additive**, with
the three alternating sums taken over all of `ℕ`. The modules are assumed to vanish above a
degree `d`, which makes each `finsum` the honest finite alternating sum; in the application `d`
is the dimension of the ambient regular scheme.

This is the `Module.length` analogue of `Module.finsum_alternating_finrank_add_of_exact`, which
is the same statement for `Module.finrank` over a field. -/
@[ega "0 11.10.2" "special case"]
theorem finsum_alternating_length_add_of_exact
    (hu : ∀ p, Function.Exact (δ p) (u p)) (hv : ∀ p, Function.Exact (u p) (v p))
    (hδ : ∀ p, Function.Exact (v (p + 1)) (δ p)) (hv0 : Function.Surjective (v 0))
    (hf₁ : ∀ p, IsFiniteLength A (T₁ p)) (hf₂ : ∀ p, IsFiniteLength A (T₂ p))
    (hf₃ : ∀ p, IsFiniteLength A (T₃ p)) (d : ℕ)
    (hT₁ : ∀ p, d < p → Subsingleton (T₁ p)) (hT₂ : ∀ p, d < p → Subsingleton (T₂ p))
    (hT₃ : ∀ p, d < p → Subsingleton (T₃ p)) :
    (∑ᶠ p : ℕ, (-1 : ℤ) ^ p * ((Module.length A (T₂ p)).toNat : ℤ)) =
      (∑ᶠ p : ℕ, (-1 : ℤ) ^ p * ((Module.length A (T₁ p)).toNat : ℤ)) +
        ∑ᶠ p : ℕ, (-1 : ℤ) ^ p * ((Module.length A (T₃ p)).toNat : ℤ) := by
  rw [finsum_alternating_length_eq_sum_range d hT₁, finsum_alternating_length_eq_sum_range d hT₂,
    finsum_alternating_length_eq_sum_range d hT₃]
  exact sum_range_alternating_length_add_of_exact u v δ hu hv hδ hv0 hf₁ hf₂ hf₃ d
    (hT₃ (d + 1) (by omega))

end Module

end
