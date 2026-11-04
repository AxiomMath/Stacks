module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

/-!
# A nonzero discriminant for a finite separable extension of normal domains

Let `A → B` be an injective finite map of domains with `A` normal, let `K` and `L` be fraction
fields of `A` and `B`, and assume `L/K` is finite separable. Then `L` has a `K`-basis whose
members come from `B`, and the discriminant of such a basis is a *nonzero element of `A`*.

The two halves are independent. That a `K`-basis of `L` can be found inside the image of `B` only
needs `L` to be the fraction field of `B` and finite over `K`: the image of `B` already spans `L`
over `K`, because the inverse of a nonzero element of `B` is a polynomial in that element with
coefficients in `K`. That the discriminant of such a basis lies in `A` and is nonzero is the trace
pairing being `A`-valued on elements integral over `A` — `A` is integrally closed in `K` — and
nondegenerate, which is separability.

## Main results

* `Stacks.Trace.span_range_algebraMap_fractionRing_eq_top`: the image of `B` in its fraction
  field `L` spans `L` over a subfield `K` with `L/K` finite.
* `Stacks.Trace.exists_basis_mem_range_algebraMap`: `L` has a `K`-basis all of whose members lie
  in the image of `B`.
* `Stacks.Trace.exists_ne_zero_algebraMap_eq_discr`: the discriminant of a `K`-basis of `L` made
  of elements integral over a normal domain `A` with fraction field `K` is the image of a nonzero
  element of `A`.
* `Stacks.Trace.exists_basis_mem_range_algebraMap_discr_ne_zero`: the two combined — a `K`-basis
  of `L` inside the image of `B` together with the nonzero element of `A` that is its
  discriminant.

## Implementation notes

The last statement is the opening paragraph of [Stacks, Tag 0AXL], which chooses `b₁, …, bₙ ∈ B`
forming a `K`-basis of `L` and uses `d = det(Trace_{L/K}(bᵢbⱼ))` to annihilate the cokernel of a
trace map. It is stated here as pure commutative algebra and is not tagged: Tag 0AXL is the
transfer of reduction to rational singularities along `A → B`, whose remaining content is
geometric.

Separability is Mathlib's `Algebra.IsSeparable`, the condition on an algebraic extension, rather
than `Algebra.IsSeparableExtension` (Tag 030O(2)), which is the condition on an arbitrary
extension; for the finite extensions considered here the two agree, but the comparison is not in
the library.

Finiteness of `L` over `K` is a hypothesis rather than a consequence of finiteness of `B` over
`A`, since it is the only form in which it is used and the deduction plays no part in the
argument.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0BIL](https://stacks.math.columbia.edu/tag/0BIL)
-/

@[expose] public section

namespace Stacks.Trace

section Span

variable (B K L : Type*) [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Module.Finite K L]

/-- The image of a domain `B` in a fraction field `L` of `B` spans `L` over any subfield `K` for
which `L` is finite over `K`.

A quotient `x / y` of elements of `B` is a `K`-linear combination of elements of `B`: the inverse
of `y` is `p(y)` for some `p ∈ K[X]`, because `y` is algebraic over `K`, so `x / y` is the
corresponding combination of the elements `x * yⁱ` of `B`. -/
theorem span_range_algebraMap_fractionRing_eq_top :
    Submodule.span K (Set.range (algebraMap B L)) = ⊤ := by
  refine le_antisymm le_top fun z _ => ?_
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) (K := L) z
  have hinv : (algebraMap B L y)⁻¹ ∈ Algebra.adjoin K ({algebraMap B L y} : Set L) := by
    simpa using Subalgebra.inv_mem_of_algebraic
      (A := Algebra.adjoin K ({algebraMap B L y} : Set L))
      (x := ⟨algebraMap B L y, Algebra.self_mem_adjoin_singleton K _⟩)
      (Algebra.IsAlgebraic.isAlgebraic (R := K) (algebraMap B L y))
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hinv
  obtain ⟨p, hp⟩ := hinv
  rw [div_eq_mul_inv, ← hp, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mul_smul_comm]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨x * y ^ i, by rw [map_mul, map_pow]⟩)

/-- A fraction field `L` of a domain `B`, finite over a subfield `K`, has a `K`-basis all of whose
members lie in the image of `B`. -/
theorem exists_basis_mem_range_algebraMap :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K L), ∀ i, b i ∈ Set.range (algebraMap B L) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K (Set.range (algebraMap B L))
  rw [span_range_algebraMap_fractionRing_eq_top B K L] at hspan
  let b : Module.Basis t K L := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan])
  have : Fintype t := FiniteDimensional.fintypeBasisIndex b
  refine ⟨Fintype.card t, b.reindex (Fintype.equivFin t), fun i => ?_⟩
  rw [Module.Basis.coe_reindex, Function.comp_apply, Module.Basis.mk_apply]
  exact hts ((Fintype.equivFin t).symm i).2

end Span

section Discriminant

variable (A K L : Type*) [CommRing A] [IsNormalDomain A] [Field K] [Field L] [Algebra A K]
  [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Module.Finite K L]

/-- The discriminant of a `K`-basis of `L` made of elements integral over a normal domain `A` with
fraction field `K` is the image of a nonzero element of `A`.

It lies in `A` because the traces `Trace_{L/K}(bᵢbⱼ)` are integral over `A` and `A` is integrally
closed in `K`, and it is nonzero because the trace pairing of a finite separable extension is
nondegenerate ([Stacks, Tag 0BIL]). -/
theorem exists_ne_zero_algebraMap_eq_discr [Algebra.IsSeparable K L] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K L) (hb : ∀ i, IsIntegral A (b i)) :
    ∃ d : A, d ≠ 0 ∧ algebraMap A K d = Algebra.discr K b := by
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.discr_isIntegral (R := A) (K := K) hb)
  refine ⟨d, fun hd0 => ?_, hd⟩
  rw [hd0, map_zero] at hd
  exact Algebra.discr_not_zero_of_basis K b hd.symm

end Discriminant

/-- **The opening step of [Stacks, Tag 0AXL].** Let `A → B` be a finite map of domains with `A`
normal, let `K` and `L` be fraction fields of `A` and `B` with `L` finite separable over `K`.
Then there is a `K`-basis `b` of `L` whose members lie in the image of `B`, and a nonzero `d ∈ A`
whose image in `K` is the discriminant `det(Trace_{L/K}(bᵢbⱼ))` of that basis.

The basis is found inside `B` by `span_range_algebraMap_fractionRing_eq_top`, and its
discriminant is pinned down in `A` by `exists_ne_zero_algebraMap_eq_discr`, whose integrality
hypothesis holds because `B` is finite, hence integral, over `A`. -/
theorem exists_basis_mem_range_algebraMap_discr_ne_zero (A B K L : Type*) [CommRing A]
    [IsNormalDomain A] [CommRing B] [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Module.Finite A B] [Module.Finite K L]
    [Algebra.IsSeparable K L] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K L) (d : A),
      (∀ i, b i ∈ Set.range (algebraMap B L)) ∧ d ≠ 0 ∧ algebraMap A K d = Algebra.discr K b := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis_mem_range_algebraMap B K L
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_algebraMap_eq_discr A K L b fun i => by
    obtain ⟨c, hc⟩ := hb i
    rw [← hc]
    exact (Algebra.IsIntegral.isIntegral (R := A) c).map (IsScalarTower.toAlgHom A B L)
  exact ⟨n, b, d, hb, hd0, hd⟩

end Stacks.Trace

end
