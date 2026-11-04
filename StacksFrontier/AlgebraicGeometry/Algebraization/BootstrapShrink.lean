module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapDepth

/-!
# Shrinking the locus of a bootstrap situation

The hypotheses of a bootstrap situation persist when its specialization-stable locus `T` is
replaced by a smaller specialization-stable subset `T'`. Only the chain-of-primes depth
estimate needs an argument: for a chain `p ⊆ r ⊆ q` whose middle prime leaves `T'` but not
`T`, either some prime of `V(I) \ T` already lies between `p` and `q`, and the original
estimate applies to it, or none does, and the strict bound of Tag 0EID applies.

## Main results

* `Stacks.Algebraization.depth_or_depth_add_dimension_of_subset` — the depth estimate for the
  smaller locus.
* `Stacks.Algebraization.BootstrapSituation.shrink` — the resulting bootstrap situation.

## Implementation notes

The other assumptions are inherited from the original situation, so `shrink` is a structure
update and leaves the ring, the ideal, the module and both bounds definitionally unchanged.

## References

* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EFV (shrinking `T`).** The chain-of-primes depth estimate of a
bootstrap situation persists after restricting its locus to any subset. -/
@[stacks 0EFV "shrinking_t"]
public theorem depth_or_depth_add_dimension_of_subset
    (S : BootstrapSituation.{u, v, w})
    (T' : Set (PrimeSpectrum S.A)) (hsub : T' ⊆ S.T) :
    ∀ p r q : PrimeSpectrum S.A,
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus (S.I : Set S.A) →
      r ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) → r ∉ T' → q ∈ T' →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.M)) ≥ (S.s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl S.M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))) >
        ((S.d + S.s : ℤ) : EInt)) := by
  intro p r q hpr hrq hp _ _ hq
  by_cases hx : ∃ x : PrimeSpectrum S.A, p.asIdeal ≤ x.asIdeal ∧ x.asIdeal ≤ q.asIdeal ∧
      x ∈ PrimeSpectrum.zeroLocus (S.I : Set S.A) ∧ x ∉ S.T
  · rcases hx with ⟨x, hpx, hxq, hxI, hxnot⟩
    exact S.depth_or_depth_add_dimension p x q hpx hxq hp hxI hxnot (hsub hq)
  · exact Or.inl (le_of_lt (depth_localized_gt_of_no_intermediate_prime
      S p q (hpr.trans hrq) hp (hsub hq) hx))

/-- **Stacks Project, Tag 0EFV, part (E).** The bootstrap situation obtained by restricting the
locus of `S` to a smaller specialization-stable subset: `A, I, T', M` with `T' ⊆ T` again
satisfies every assumption of Situation 0EFU, with the same bounds `s` and `d`. -/
@[stacks 0EFV "part (E): for a smaller specialization-stable T' ⊆ T the quadruple A, I, T', M \
is again a situation as in Stacks 0EFU"]
public def BootstrapSituation.shrink
    (S : BootstrapSituation.{u, v, w})
    (T' : Set (PrimeSpectrum S.A)) (hsub : T' ⊆ S.T)
    (hstable : StableUnderSpecialization T') :
    BootstrapSituation.{u, v, w} :=
  { S with
    T := T'
    subset_adicLocus := fun _ hp => S.subset_adicLocus (hsub hp)
    stableUnderSpecialization := hstable
    depth_or_depth_add_dimension := depth_or_depth_add_dimension_of_subset S T' hsub
    completedLocalDepth := fun q hq => S.completedLocalDepth q (hsub hq) }

end Stacks.Algebraization

end
