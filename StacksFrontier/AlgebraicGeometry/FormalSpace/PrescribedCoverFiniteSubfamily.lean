module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaRefined

/-!
# A finite subfamily of a prescribed covering of an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `U₀` be an affine formal algebraic
space over `S`. This file cuts an arbitrary covering `{Wᵢ ⟶ U₀}` of `U₀` as in Definition
**Stacks 0AIM** down to a *finite jointly surjective subfamily*: there are a finite type `K` and
a reindexing `k : K → I` for which `{W_{k j} ⟶ U₀}` is again a covering as in Definition 0AIM.

## Main results

* `FormalSpace.exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`:
  the finite subfamily, for an affine formal algebraic space.

## Why the subfamily, and not just some finite covering

The members of the subfamily are members of the family *given*, indexed by `k j`. So every
datum the given family carries — in particular a map of each member into some prescribed
object, as in the refinement of a covering constructed by the proof of **Stacks 0ANG** — is
carried by the subfamily too, by composing with `k`. A finite covering of `U₀` obtained by any
other route, for instance the one that the implication (1) ⇒ (2) of **Stacks 0AJ9** extracts
from the atlas which `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` supplies
(`AlgebraicGeometry.FormalSpace.hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction`),
has no such maps and does not serve.

## What is assumed

Nothing. The covering is an argument rather than something read off a hypothesis that `U₀` be a
formal algebraic space, and the two inputs are both proved in this library:

* quasi-compactness of the reduction of an affine formal algebraic space,
  `AlgebraicGeometry.FormalSpace.affineReductionsQuasiCompact`;
* the finite subfamily of a prescribed covering whose base changes cover a compact point,
  `AlgebraicGeometry.FormalSpace.exists_finite_subfamily_pullback_cover_of_compactSpace`,
  through
  `exists_finite_subfamily_jointly_surjective_of_isQuasiCompactSpaceULift_reduction`.

In particular nothing here routes through
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, which is unproved: joint
surjectivity of the subfamily is checked on points, by
`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointly_surjective_points`.

## No tag

**Stacks 0AJ9** asserts the existence of *some* finite covering of a formal algebraic space with
quasi-compact reduction, and that assertion is registered on
`AlgebraicGeometry.FormalSpace.hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction`. The
statement below is strictly stronger — the finite covering is a subfamily of a covering handed
in — and the Stacks project states no lemma to that effect, so it carries no `@[stacks]`
registration.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite subfamily of a prescribed covering of an affine formal algebraic space.** Let
`U₀` be an affine formal algebraic space over `S` and let `{Wᵢ ⟶ U₀}` be a covering as in
Definition **Stacks 0AIM** — the sources affine formal algebraic spaces, each arrow
representable étale, the arrow out of the coproduct a surjection of sheaves. Then finitely many
members of that covering already form one: there are a finite type `K` and a reindexing
`k : K → I` with `{W_{k j} ⟶ U₀}` again a covering as in Definition 0AIM.

Since the members are members of the family given, so is anything that family carries. This is
the form in which the refinement of a covering in the proof of **Stacks 0ANG** needs the
finiteness step: each member of the refinement keeps its map into the covering of the source
that is being refined.

An affine formal algebraic space has a reduction
(`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace`) and that
reduction is a quasi-compact algebraic space
(`AlgebraicGeometry.FormalSpace.affineReductionsQuasiCompact`), so
`exists_finite_subfamily_jointly_surjective_of_isQuasiCompactSpaceULift_reduction`
applies to the given covering. -/
theorem exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace
    {U₀ : FppfSheaf B S hS} (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    {I : Type (u + 1)} (W : I → FppfSheaf B S hS) (p : ∀ i, W i ⟶ U₀)
    (hcover : IsAffineEtaleCover B S hS W p) :
    ∃ (K : Type (u + 1)) (_ : Finite K) (k : K → I),
      IsAffineEtaleCover B S hS (fun j ↦ W (k j)) (fun j ↦ p (k j)) := by
  obtain ⟨haffine, hetale, hsurjective⟩ := hcover
  obtain ⟨Ured, ι, hι⟩ := exists_isReduction_of_isAffineFormalAlgebraicSpace B S hS U₀ hU₀
  obtain ⟨K, hKfin, k, hsubcover⟩ :=
    exists_finite_subfamily_jointly_surjective_of_isQuasiCompactSpaceULift_reduction B S hS hι
      (affineReductionsQuasiCompact B S hS U₀ Ured ι hU₀ hι) p haffine hetale hsurjective
  exact ⟨K, hKfin, k, fun j ↦ haffine (k j), fun j ↦ hetale (k j), hsubcover⟩

end AlgebraicGeometry.FormalSpace

end
