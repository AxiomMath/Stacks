module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyColimitReduction.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-affine scheme with no higher structure-sheaf cohomology is affine

[Stacks, Tag 0EBE](https://stacks.math.columbia.edu/tag/0EBE): a quasi-affine scheme `X` with
`Hᵖ(X, 𝒪_X) = 0` for every `p > 0` is affine.

## The source's proof

The Stacks proof is two lines: `𝒪_X` is ample on a quasi-affine scheme by
[Stacks, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE), so
[Stacks, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD) -- affineness from the vanishing of
`Hᵖ(X, L^{⊗ -n})` for an ample `L`, all `n ≥ n₀` and all `p > 0` -- applies with `L = 𝒪_X`.  What
the source leaves silent is that every integer tensor power of `𝒪_X` is again `𝒪_X`, so the
single hypothesis `Hᵖ(X, 𝒪_X) = 0` already supplies Tag 0EBD's whole family of hypotheses, in
every degree `n` at once; `n₀` may therefore be taken to be `0`, or indeed anything.

Both inputs are proved in this repository with no hypothesis beyond the tag's own:
`Stacks.Ample.isAmple_unitModule_of_isQuasiAffine` is Tag 01QE, and Tag 0EBD is
`isAffine_of_isZero_cohomology_negative_tensorPower` of the enclosing namespace
`Stacks.AlgebraicGeometry.CohomologyColimitReduction`, in the sibling file `Basic.lean`.  The
identification of the powers of `𝒪_X` with
`𝒪_X` is `Stacks.Ample.unitTensorPowIso`, which is stated for every integer exponent, and it is
transported to cohomology by functoriality of `Hᵖ(X, -)`.

## Main results

* `isZero_hgroup_tensorPowModule_unitModule`: the vanishing of `Hᵖ(X, 𝒪_X)` propagates to every
  integer tensor power of `𝒪_X`.
* `isAffine_of_isZero_hgroup_unitModule`: **[Stacks, Tag 0EBE]**, for an arbitrary quasi-affine
  scheme and vanishing in every positive degree.
* `isZero_hgroup_unitModule_of_isAffine`: the hypothesis of the tag holds on an affine scheme,
  which is [Stacks, Tag 01XB] at `𝒪_X`.  This witnesses that the tag is not vacuous.

## Implementation notes

`H^p(X, 𝒪_X)` is `Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf)`: the `p`-th
right derived functor of `Γ(⊤, -)` on `𝒪_X`-modules, valued in abelian groups, evaluated at the
structure sheaf regarded as a module over itself.  This is the cohomology the whole ample/affine
cluster is stated at, and `Stacks.Ample.unitModule X` is a reducible abbreviation for the module
argument.  Vanishing is the categorical `CategoryTheory.Limits.IsZero`.

Quasi-affineness is Mathlib's `AlgebraicGeometry.Scheme.IsQuasiAffine`, a class, so it is taken as
an instance hypothesis and is not named in the declaration names.

**Non-vacuity.** An affine scheme is quasi-affine (Mathlib's low-priority instance on
`AlgebraicGeometry.Scheme.IsQuasiAffine`) and satisfies the vanishing hypothesis by Tag 01XB, so
the two hypotheses of the tag are jointly satisfiable; the `example` after
`isZero_hgroup_unitModule_of_isAffine` checks that composition. The hypothesis of
quasi-affineness is a genuine restriction and not an artefact: Tag 01QE is a biconditional, so a
scheme whose structure sheaf fails to be ample -- for instance one that is not quasi-compact --
is outside the statement's scope.

## References

* [Stacks Project, Tag 0EBE](https://stacks.math.columbia.edu/tag/0EBE)
* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CohomologyColimitReduction

/-- **The vanishing of `Hᵖ(X, 𝒪_X)` propagates to every integer tensor power of `𝒪_X`.**  This is
the step the source performs silently when it feeds `L = 𝒪_X` to [Stacks, Tag 0EBD], whose
hypothesis is about the negative twists `L^{⊗ -n}`: every integer tensor power of `𝒪_X` is `𝒪_X`
again (`Stacks.Ample.unitTensorPowIso`), and `Hᵖ(X, -)` carries that isomorphism of modules to an
isomorphism of cohomology groups.

The exponent is arbitrary -- no positivity, and no lower bound -- which is why the tag needs only
one hypothesis rather than a family indexed by `n`. -/
theorem isZero_hgroup_tensorPowModule_unitModule (X : Scheme.{u}) (p : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf))) (n : ℤ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p
      (Stacks.Ample.tensorPowModule X (Stacks.Ample.unitModule X) n)) :=
  h.of_iso (((Hfunctor X.ringCatSheaf ⊤ p).mapIso (Stacks.Ample.unitTensorPowIso X n)).symm)

/-- **[Stacks, Tag 0EBE].** Let `X` be a quasi-affine scheme.  If `Hᵖ(X, 𝒪_X) = 0` for every
`p > 0`, then `X` is affine.

The source's argument verbatim: `𝒪_X` is an ample invertible module on a quasi-affine scheme
([Stacks, Tag 01QE], `Stacks.Ample.isAmple_unitModule_of_isQuasiAffine`), so affineness follows
from the vanishing of the higher cohomology of the negative twists of an ample module
([Stacks, Tag 0EBD], `isAffine_of_isZero_cohomology_negative_tensorPower`).  Tag 0EBD's family of
hypotheses collapses to this single one because the twists of `𝒪_X` are all `𝒪_X`, by
`isZero_hgroup_tensorPowModule_unitModule`; the threshold `n₀` is taken to be `0` and is
immaterial. -/
@[stacks 0EBE]
theorem isAffine_of_isZero_hgroup_unitModule (X : Scheme.{u}) [X.IsQuasiAffine]
    (hvan : ∀ p : ℕ, 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf))) :
    IsAffine X :=
  isAffine_of_isZero_cohomology_negative_tensorPower (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isQuasiAffine X inferInstance) 0
    fun n p _ hp => isZero_hgroup_tensorPowModule_unitModule X p (hvan p hp) (-n)

/-- **The hypothesis of [Stacks, Tag 0EBE] holds on an affine scheme.**  `𝒪_X` is quasi-coherent,
so this is [Stacks, Tag 01XB] -- the vanishing of the higher cohomology of a quasi-coherent module
on an affine scheme -- read at the structure sheaf.

Recorded as the non-vacuity witness for the tag: an affine scheme is quasi-affine, so together
with this lemma it satisfies both hypotheses of
`isAffine_of_isZero_hgroup_unitModule` at once. -/
@[sga "1 XI 6.9" "partial", sga "3 XVII 5.4.1" "partial"]
theorem isZero_hgroup_unitModule_of_isAffine (X : Scheme.{u}) [IsAffine X] (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf)) :=
  Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine X _ p hp

/-- Both hypotheses of [Stacks, Tag 0EBE] are satisfiable simultaneously: an affine scheme is
quasi-affine and has no higher structure-sheaf cohomology, and the tag returns its affineness. -/
example (X : Scheme.{u}) [IsAffine X] : IsAffine X :=
  isAffine_of_isZero_hgroup_unitModule X fun p hp => isZero_hgroup_unitModule_of_isAffine X p hp

end Stacks.AlgebraicGeometry.CohomologyColimitReduction

end
