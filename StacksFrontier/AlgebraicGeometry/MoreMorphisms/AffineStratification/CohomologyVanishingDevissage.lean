module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CohomologyVanishing

/-!
# Vanishing above the affine stratification number

On a nonempty quasi-compact quasi-separated scheme `X` with affine stratification number `n` the
cohomology `Hᵖ(X, F)` of a quasi-coherent `𝒪_X`-module vanishes for `p > n`. The statement is
proved here relative to two conditions, each a named `Prop`: affineness of a scheme carrying a
surjective immersion from an affine scheme, and the cohomological dévissage step of the source's
induction.

## Main definitions

* `AlgebraicGeometry.CohomologicalDevissageStep`: the inductive step of the source's proof, the
  passage from vanishing above `m` on the complement of an affine open to vanishing above
  `m + 1`.

## Main results

* `AlgebraicGeometry.isZero_cohomology_of_affineStratificationNumber_lt`: the vanishing, relative
  to `AlgebraicGeometry.IsAffineOfSurjectiveImmersion` and
  `AlgebraicGeometry.CohomologicalDevissageStep`.

## Implementation notes

Both conditions are discharged elsewhere, so the vanishing holds outright:
`AlgebraicGeometry.isAffineOfSurjectiveImmersion` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/AffineStratification/Peeling.lean` and
`AlgebraicGeometry.cohomologicalDevissageStep` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/AffineStratification/CohomologyVanishingProof.lean`,
which is where the unconditional statement carries the `@[stacks 0F2Y]` attribute. Nothing in
this file carries it.

`IsAffineOfSurjectiveImmersion` is [Stacks, Tag 06AD] in the general, non-nilpotent form the
source uses: an affine stratification records affineness of the reduced induced scheme on a
stratum, while the induction needs the open top stratum affine as an open subscheme, and the
ideal cutting out the reduced structure is nil but not nilpotent. `CohomologicalDevissageStep`
is the four-term exact sequence `0 → K → F → j_*(F|_U) → Q → 0` for the inclusion `j` of the top
stratum, together with the vanishing of the cohomology of `j_*(F|_U)` in positive degrees, the
presentation of `K` and `Q` as filtered colimits of their finite type quasi-coherent submodules,
and the passage to the scheme-theoretic support of such a submodule, a closed subscheme with the
same underlying space as the complement of the top stratum.

## References

* [Stacks Project, Tag 0F2Y](https://stacks.math.columbia.edu/tag/0F2Y)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The cohomological dévissage step of [Stacks, Tag 0F2Y]: if `U` is an affine open of `Y` with
affine inclusion, the complement of `U` carries a closed subscheme with an affine stratification
indexed by `Fin (m + 1)`, and cohomology vanishes above `m` on every scheme with such a
stratification, then cohomology on `Y` vanishes above `m + 1`. -/
def CohomologicalDevissageStep : Prop :=
  ∀ (m : ℕ) (Y : Scheme.{u}) (U : Y.Opens), IsAffineOpen U → IsAffineHom U.ι →
    ∀ (V : Scheme.{u}) (j : V ⟶ Y), IsClosedImmersion j →
      Set.range j.base = (U : Set Y)ᶜ →
      Nonempty (AffineStratification V (Fin (m + 1))) →
      (∀ W : Scheme.{u}, Nonempty (AffineStratification W (Fin (m + 1))) →
        QuasicoherentCohomologyVanishesAbove W m) →
      QuasicoherentCohomologyVanishesAbove Y (m + 1)

/-- Let `X` be a nonempty quasi-compact quasi-separated scheme with affine stratification number
`n`. Then `Hᵖ(X, F) = 0` for `p > n` and every quasi-coherent `𝒪_X`-module `F`, relative to the
two conditions `haffine` ([Stacks, Tag 06AD]) and `hdevissage` (the inductive step of the
source's proof).

This is the assembly of the induction from the two conditions, not a formalization of
[Stacks, Tag 0F2Y], and it carries no tag: both conditions are discharged in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/AffineStratification/CohomologyVanishingProof.lean`,
where `AlgebraicGeometry.isZero_cohomology_of_affineStratificationNumber` states the vanishing
with no hypothesis beyond the tag's own. -/
theorem isZero_cohomology_of_affineStratificationNumber_lt
    (haffine : IsAffineOfSurjectiveImmersion.{u})
    (hdevissage : CohomologicalDevissageStep.{u})
    (X : Scheme.{u}) [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : affineStratificationNumber X < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  isZero_cohomology_of_affineStratificationNumber_lt_of_devissage haffine hdevissage X F p hp

end AlgebraicGeometry

end
