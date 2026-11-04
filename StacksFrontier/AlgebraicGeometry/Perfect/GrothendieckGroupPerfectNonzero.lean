module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupAffine.Perfect

/-!
# `K₀(X)` is not the zero group

The Grothendieck group `AlgebraicGeometry.PerfectKZero` of [Stacks, Tag 0FDG] (1) is nonzero on
an affine scheme over a nontrivial local ring, and in particular on `Spec ℚ`.

## Main results

* `AlgebraicGeometry.exists_ne_zero_perfectKZero_spec`: `K₀(Spec R) ≠ 0` for `R` a local ring.
* `AlgebraicGeometry.exists_ne_zero_perfectKZero_specRat`: the hypothesis is satisfied by a
  ring, so the statement above is not vacuous.

## Implementation notes

`K₀(X) = K₀(D_perf(𝒪_X))` is a definition, so no check on it can detect that the subcategory
`D_perf(𝒪_X)` is inhabited by anything other than the zero object, nor that the quotient
defining its `K`-group is not the whole free abelian group. These two statements supply that
missing check: the group is nonzero for a genuine scheme.

The witness travels along the identification `K₀(Spec R) ≅ K₀(R)` of [Stacks, Tag 0FDH]
(`Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_addEquiv_K0_perfectDerivedCategory_spec`)
and is detected by the rank homomorphism `K0.rank : K₀(R) →+ ℤ`, which is available over a local
ring and sends the class of the free module of rank one to `1`. Transporting the class back gives
a nonzero element of `K₀(Spec R)` itself; nothing here needs `D_perf(𝒪_{Spec R})` to be described
by hand.

The instance priority on `HasDerivedCategory.standard` matches the one in
`StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupAffine.Perfect`: at equal priority the
locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` wins and the two spellings of
the derived category no longer agree.

## References

* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
* [Stacks Project, Tag 0FDH](https://stacks.math.columbia.edu/tag/0FDH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`K₀(Spec R)` is nonzero** for every nontrivial local ring `R`: the class of the free
module of rank one has rank `1` in `K₀(R)`, and the identification of [Stacks, Tag 0FDH] carries
it back to a nonzero element of `K₀(Spec R) = K₀(D_perf(𝒪_{Spec R}))`. -/
theorem exists_ne_zero_perfectKZero_spec (R : CommRingCat.{u}) [IsLocalRing (R : Type u)] :
    ∃ x : PerfectKZero (Spec R), x ≠ 0 := by
  obtain ⟨e, -⟩ :=
    Stacks.AlgebraicGeometry.GrothendieckGroupAffine.exists_addEquiv_K0_perfectDerivedCategory_spec
      R
  refine ⟨e.symm (K0.mk (FGProj.free (R : Type u) 1)), e.symm.map_ne_zero_iff.2 fun hx => ?_⟩
  simpa [K0.rank_mk, FGProj.rank_free] using congrArg (K0.rank (R : Type u)) hx

/-- **`K₀(Spec ℚ)` is nonzero.** The hypothesis of
`AlgebraicGeometry.exists_ne_zero_perfectKZero_spec` is satisfied by a ring, so that statement
is about a scheme that exists. -/
theorem exists_ne_zero_perfectKZero_specRat :
    ∃ x : PerfectKZero (Spec (CommRingCat.of ℚ)), x ≠ 0 :=
  exists_ne_zero_perfectKZero_spec (CommRingCat.of ℚ)

end AlgebraicGeometry

end
