module

public import StacksFrontier.RingTheory.GradedAlgebra.ModuleTruncation
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading

/-!
# Splitting a truncated graded module into residue classes over the Veronese subring

Let `S = ⨁_{i ≥ 0} 𝒮 i` be a graded ring, `d ≥ 1`, `B = S⁽ᵈ⁾` the Veronese subring, and let `M`
be a `ℤ`-graded `S`-module. Over `B` the truncation `M_{≥ k}` splits into the `d` residue classes
of the degrees modulo `d`:

`M_{≥ k} = ⨁_{q < d} (M_{≥ k})_{≡ q}`.

This file proves the half of that splitting which finiteness arguments consume: **a finite
generating family over `B` for each residue class gives one for the whole truncation.** It is
the degree bookkeeping of the source's proof of Stacks 0B5Q clause (4) — "using the finiteness of
congruence classes once more" — separated from the geometry, so that the geometric input is
applied once per residue class and the assembly is uniform.

## Main definitions

* `Stacks.Veronese.residuePart`: the part of an element supported in the degrees congruent to
  `q` modulo `d`.
* `Stacks.Veronese.ResidueSupported`: the property of having all homogeneous components in
  degrees congruent to `q` modulo `d`.

## Main results

* `Stacks.Veronese.sum_residuePart`: the `d` residue parts of an element sum to it.
* `Stacks.Veronese.residuePart_mem_truncationAbove`: each residue part of an element of the
  truncation lies in the truncation.
* `Stacks.Veronese.residueSupported_residuePart`: each residue part is supported in its own
  residue class.
* `Stacks.Veronese.mem_span_of_mem_truncationAbove`: **the assembly** — if every element of
  the truncation which is supported in the residue class of `q` lies in the `B`-span of a set
  `G q`, for each `q < d`, then every element of the truncation lies in the `B`-span of
  `⋃ q, G q`.
* `Stacks.Veronese.finite_iUnion_range`: the union of the `d` generating families is finite, so
  the conclusion names a finite generating family for the whole truncation.

## Implementation notes

The residue part is the sum of the homogeneous components over the part of the support lying in
one class, so `Stacks.Veronese.sum_residuePart` is `Finset.sum_fiberwise_of_maps_to` along
`i ↦ (i % d).toNat`, which lands in `Finset.range d` because `d` is positive. Nothing here needs
the residue parts to be `B`-*submodules*, and they are not shown to be: the conclusion is phrased
with `Submodule.span B`, which is a `B`-submodule by construction, so the induction over
`Subring.closure` that the submodule property would need is avoided.

The truncation, its grading and the `B`-action are
`Stacks.GradedModule.truncationAbove`, `Stacks.GradedModule.truncationAboveGrading` and
`Stacks.Veronese.veroneseModule`; none of them is restated.

## What this is not

This is only the residue bookkeeping. The geometric half — that each residue class of
`⨁_{n ≥ k} Γ(Proj S, ℱ(n))` is finite over `B`, via the Veronese comparison on twisted global
sections and clause (4) of Stacks 0AG6 upstairs — is not here, and needs the comparison as a
semilinear map rather than as a bijection of underlying types.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open DirectSum
open Stacks.GradedModule

namespace Stacks.Veronese

universe u v w t

attribute [local instance] Classical.propDecidable

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [AddCommGroup M] [Module S M] [SetLike τ M] [AddSubgroupClass τ M]
  (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- The residue class of a degree modulo `d`, as a natural number below `d`. -/
public def degreeResidue (d : ℕ) (i : ℤ) : ℕ := (i % (d : ℤ)).toNat

/-- The remainder of an integer modulo a positive `d` is nonnegative and below `d`. -/
private theorem emod_nonneg_and_lt {d : ℕ} (hd : 0 < d) (i : ℤ) :
    0 ≤ i % (d : ℤ) ∧ i % (d : ℤ) < d :=
  ⟨Int.emod_nonneg i (by omega), Int.emod_lt_of_pos i (by exact_mod_cast hd)⟩

public theorem degreeResidue_lt {d : ℕ} (hd : 0 < d) (i : ℤ) : degreeResidue d i < d := by
  have := emod_nonneg_and_lt hd i
  rw [degreeResidue]
  omega

public theorem coe_degreeResidue {d : ℕ} (hd : 0 < d) (i : ℤ) :
    ((degreeResidue d i : ℕ) : ℤ) = i % (d : ℤ) :=
  Int.toNat_of_nonneg (emod_nonneg_and_lt hd i).1

/-- Taking one homogeneous component commutes with a finite sum. -/
public theorem coe_decompose_sum (i : ℤ) (s : Finset ℤ) (f : ℤ → M) :
    ((decompose 𝒨 (∑ j ∈ s, f j)) i : M) = ∑ j ∈ s, ((decompose 𝒨 (f j)) i : M) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add,
      ih, Finset.sum_insert hj]

/-- **The part of `x` supported in the degrees congruent to `q` modulo `d`.** -/
public def residuePart (d q : ℕ) (x : M) : M :=
  ∑ i ∈ (decompose 𝒨 x).support.filter (fun i => degreeResidue d i = q),
    ((decompose 𝒨 x) i : M)

/-- **The `d` residue parts of an element sum to it.** -/
public theorem sum_residuePart {d : ℕ} (hd : 0 < d) (x : M) :
    ∑ q ∈ Finset.range d, residuePart 𝒨 d q x = x := by
  have hmaps : ∀ i ∈ (decompose 𝒨 x).support, degreeResidue d i ∈ Finset.range d :=
    fun i _ => Finset.mem_range.2 (degreeResidue_lt hd i)
  exact (Finset.sum_fiberwise_of_maps_to hmaps fun i => ((decompose 𝒨 x) i : M)).trans
    (DirectSum.sum_support_decompose 𝒨 x)

/-- **Each residue part of an element of the truncation lies in the truncation**: it is a sum of
homogeneous components of degree at least the cut. -/
public theorem residuePart_mem_truncationAbove {k : ℤ} (d q : ℕ) {x : M}
    (hx : x ∈ truncationAbove 𝒮 𝒨 k) :
    residuePart 𝒨 d q x ∈ truncationAbove 𝒮 𝒨 k := by
  refine Submodule.sum_mem _ fun i _ => ?_
  rcases le_or_gt k i with hik | hik
  · exact mem_truncationAbove_of_mem 𝒮 𝒨 k hik ((decompose 𝒨 x) i).2
  · rw [(mem_truncationAbove_iff 𝒮 𝒨 k x).mp hx i hik]
    exact Submodule.zero_mem _

/-- The property of having every homogeneous component in a degree congruent to `q` modulo
`d`. -/
public def ResidueSupported (d q : ℕ) (x : M) : Prop :=
  ∀ i : ℤ, degreeResidue d i ≠ q → ((decompose 𝒨 x) i : M) = 0

/-- **Each residue part is supported in its own residue class.** -/
public theorem residueSupported_residuePart (d q : ℕ) (x : M) :
    ResidueSupported 𝒨 d q (residuePart 𝒨 d q x) := by
  intro i hi
  rw [residuePart, coe_decompose_sum 𝒨 i]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjq : degreeResidue d j = q := (Finset.mem_filter.mp hj).2
  exact DirectSum.decompose_of_mem_ne 𝒨 ((decompose 𝒨 x) j).2 (fun h => hi (h ▸ hjq))

/-- **The assembly.** If for each `q < d` every element of the truncation supported in the
residue class of `q` lies in the `B`-span of `G q`, then every element of the truncation lies in
the `B`-span of the union of the `G q`.

The conclusion is a membership rather than an inequality of submodules because the truncation is
an `S`-submodule while the span is a `B`-submodule, and the two live in different types; the
consumer wants the membership in any case. -/
public theorem mem_span_of_mem_truncationAbove {d : ℕ} (hd : 0 < d) (k : ℤ)
    (G : ℕ → Set M)
    (hG : ∀ q ∈ Finset.range d, ∀ y ∈ truncationAbove 𝒮 𝒨 k,
      ResidueSupported 𝒨 d q y → y ∈ Submodule.span (veroneseSubring 𝒮 d) (G q))
    {x : M} (hx : x ∈ truncationAbove 𝒮 𝒨 k) :
    x ∈ Submodule.span (veroneseSubring 𝒮 d) (⋃ q ∈ Finset.range d, G q) := by
  rw [← sum_residuePart 𝒨 hd x]
  refine Submodule.sum_mem _ fun q hq => ?_
  refine Submodule.span_mono (fun z hz => Set.mem_biUnion hq hz)
    (hG q hq _ (residuePart_mem_truncationAbove 𝒮 𝒨 d q hx)
      (residueSupported_residuePart 𝒨 d q x))

omit [AddCommGroup M] in
/-- The union of the `d` generating families is finite, so the assembly names a finite generating
family for the whole truncation. -/
public theorem finite_iUnion_range (d : ℕ) (G : ℕ → Set M) (hG : ∀ q, (G q).Finite) :
    (⋃ q ∈ Finset.range d, G q).Finite :=
  Set.Finite.biUnion (Finset.range d).finite_toSet fun q _ => hG q

end Stacks.Veronese

end
