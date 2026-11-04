module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Agreement of an ideal with a principal ideal along an arc

Two algebraic facts behind the separation of strict transforms over a valuation ring.

Let `φ : R ⟶ A` be a ring map to a local ring and let `I ⊆ (t)` be ideals of `R`, with `φ t` a
nonzerodivisor. If `I` and `(t)` extend to the same ideal of `A`, then `t u ∈ I` for some `u ∈ R`
with `φ u` a unit; only `φ t ∈ I A` is needed. Geometrically: a closed subscheme `C = V(I)`
contains the effective Cartier divisor `E = V(t)`, and if `C` and `E` agree along an arc
`Spec A ⟶ Spec R` whose generic point avoids `E`, then they agree on the basic open `D(u)`, a
neighbourhood of the image of the closed point.

Over a valuation ring, if `Nₐ, N_b ⊆ Iₐ + I_b`, then `Iₐ + Nₐ = Iₐ` or `I_b + N_b = I_b`,
because the ideals of a valuation ring are totally ordered.

## Main results

* `Ideal.exists_isUnit_map_mul_mem_of_mem_map`: the first statement.
* `ValuationRing.sup_eq_left_or_sup_eq_left_of_le_sup`: the second statement.
-/

@[expose] public section

namespace Ideal

variable {R A : Type*} [CommRing R] [CommRing A]

/-- **An ideal inside a principal ideal which agrees with it along an arc agrees with it near
the closed point.** Let `φ : R →+* A` be a ring map to a local ring, let `I ≤ (t)` be an ideal
of `R` and suppose `φ t` is a nonzerodivisor. If `φ t` lies in the extension of `I` (that is,
`I` and `(t)` extend to the same ideal of `A`), then there is `u ∈ R` with `φ u` a unit and
`t * u ∈ I`. -/
theorem exists_isUnit_map_mul_mem_of_mem_map [IsLocalRing A] (φ : R →+* A)
    {I : Ideal R} {t : R} (hI : I ≤ span {t}) (ht : IsLeftRegular (φ t))
    (h : φ t ∈ I.map φ) : ∃ u : R, IsUnit (φ u) ∧ t * u ∈ I := by
  -- the ideal of `u` with `t * u ∈ I`
  let K : Ideal R := I.colon (span {t})
  have hIK : I ≤ span {t} * K := by
    intro x hx
    obtain ⟨u, rfl⟩ := mem_span_singleton'.1 (hI hx)
    refine mem_span_singleton_mul.2 ⟨u, ?_, mul_comm t u⟩
    refine Submodule.mem_colon.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := mem_span_singleton'.1 hy
    rw [smul_eq_mul, mul_left_comm]
    exact I.mul_mem_left c hx
  have htop : K.map φ = ⊤ := by
    have hmem : φ t ∈ span {φ t} * K.map φ := by
      simpa only [Ideal.map_mul, Ideal.map_span, Set.image_singleton] using map_mono (f := φ) hIK h
    obtain ⟨z, hz, hzt⟩ := mem_span_singleton_mul.1 hmem
    exact (eq_top_iff_one _).2 ((ht (show φ t * z = φ t * 1 by rw [hzt, mul_one]) : z = 1) ▸ hz)
  by_contra! hne
  have hle : K.map φ ≤ IsLocalRing.maximalIdeal A := by
    refine map_le_iff_le_comap.2 fun u hu => ?_
    rw [mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    refine hne u hunit ?_
    have hut := Submodule.mem_colon.1 hu t (mem_span_singleton_self t)
    rwa [smul_eq_mul, mul_comm] at hut
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (htop ▸ hle))

end Ideal

namespace ValuationRing

variable {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]

/-- Over a valuation ring, if `Nₐ` and `N_b` both lie in `Iₐ ⊔ I_b`, then `Iₐ ⊔ Nₐ = Iₐ` or
`I_b ⊔ N_b = I_b`. -/
theorem sup_eq_left_or_sup_eq_left_of_le_sup {Ia Ib Na Nb : Ideal A} (hNa : Na ≤ Ia ⊔ Ib)
    (hNb : Nb ≤ Ia ⊔ Ib) : Ia ⊔ Na = Ia ∨ Ib ⊔ Nb = Ib := by
  rcases (ValuationRing.le_total_ideal (A := A)).total Ia Ib with h | h
  · exact Or.inr (sup_eq_left.2 (hNb.trans (sup_eq_right.2 h).le))
  · exact Or.inl (sup_eq_left.2 (hNa.trans (sup_eq_left.2 h).le))

end ValuationRing

end
