module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections

/-!
# Locally principal closed subschemes of an integral scheme

On an integral scheme every locally principal closed subscheme other than the whole scheme is an
effective Cartier divisor. The reason is that the local generator is automatically a
nonzerodivisor: the sections of the structure sheaf over a nonempty open of an integral scheme
form a domain, so a generator fails to be a nonzerodivisor only by being zero, and a zero
generator would put the whole affine open inside the support of the subscheme. The support is
closed and a nonempty open of an irreducible space is dense, so the support would be everything,
which on a reduced scheme happens only for the whole scheme.

This is the step that turns local principality into the hypothesis of the forward direction of
Stacks Tag 01WS, `Stacks.Divisors.isEffectiveCartierDivisor_of_forall_mem_support`, which asks
for a *nonzerodivisor* generator near every point of the support.

## Main results

* `Stacks.IdealSheaf.coe_le_support_of_ideal_eq_bot`: an affine open on which the ideal is zero
  lies in the support.
* `Stacks.IdealSheaf.ideal_ne_bot`: on an integral scheme, a closed subscheme other than the
  whole scheme cuts out a nonzero ideal on every nonempty affine open.
* `Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal`: a locally principal closed
  subscheme of an integral scheme which is not the whole scheme is an effective Cartier divisor.

## Implementation notes

The hypothesis "not the whole scheme" is `I ≠ ⊥`, since `⊥ : X.IdealSheafData` is the zero ideal
sheaf, cutting out `X` itself; this is the spelling the nondegeneracy statements of Stacks Tag
02S4 produce (`Stacks.Chow.zeroDivisor_ne_bot`).

No finiteness, Noetherian or quasi-compactness hypothesis is needed, and no affine cover is
taken: irreducibility replaces a cover argument, because a single nonempty affine open is already
dense.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X : Scheme.{u}}

namespace Stacks.IdealSheaf

/-- **An affine open on which the ideal is zero lies in the support.** Over such an open every
section of the ideal vanishes everywhere, so every point of the open is in the zero locus. -/
theorem coe_le_support_of_ideal_eq_bot (I : X.IdealSheafData) {U : X.affineOpens}
    (hU : I.ideal U = ⊥) : (U : Set X) ⊆ (I.support : Set X) := fun _ hy =>
  (Scheme.IdealSheafData.mem_support_iff_of_mem hy).2 (by rw [hU]; simp)

/-- **On an integral scheme a closed subscheme other than the whole scheme cuts out a nonzero
ideal on every nonempty affine open.** A zero ideal would place the affine open inside the
support, which is closed; a nonempty open of an irreducible space is dense, so the support would
be the whole space, and on a reduced scheme that happens only for the whole scheme. -/
theorem ideal_ne_bot [IsIntegral X] (I : X.IdealSheafData) (hI : I ≠ ⊥)
    {U : X.affineOpens} {y : X} (hy : y ∈ (U : Set X)) : I.ideal U ≠ ⊥ := fun hU => by
  refine hI (Scheme.IdealSheafData.support_eq_top_iff.1 (Closeds.coe_eq_univ.1 ?_))
  have hdense : Dense (I.support : Set X) :=
    ((U : X.Opens).isOpen.dense ⟨y, hy⟩).mono (coe_le_support_of_ideal_eq_bot I hU)
  rw [← I.support.isClosed.closure_eq, hdense.closure_eq]

end Stacks.IdealSheaf

namespace Stacks.Divisors

/-- **A locally principal closed subscheme of an integral scheme which is not the whole scheme is
an effective Cartier divisor.** On an integral scheme the local generator is a nonzerodivisor for
free: the sections over a nonempty open form a domain, and the generator is nonzero by
`Stacks.IdealSheaf.ideal_ne_bot`. So the hypothesis of the forward direction of Stacks Tag 01WS,
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_mem_support`, is met at every point. -/
theorem isEffectiveCartierDivisor_of_isLocallyPrincipal [IsIntegral X] (I : X.IdealSheafData)
    (hI : I ≠ ⊥) (hprin : IsLocallyPrincipal I) :
    IsEffectiveCartierDivisor I := by
  refine isEffectiveCartierDivisor_of_forall_mem_support I fun x _ => ?_
  obtain ⟨U, hxU, t, ht⟩ := hprin x
  have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  refine ⟨U, t, hxU, ht, mem_nonZeroDivisors_of_ne_zero fun h => ?_⟩
  exact Stacks.IdealSheaf.ideal_ne_bot I hI hxU
    (by rw [ht, h, Ideal.span_singleton_eq_bot])

end Stacks.Divisors

end
