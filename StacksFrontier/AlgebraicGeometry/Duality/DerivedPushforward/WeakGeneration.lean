module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# The twisted inverse image from a generating family, without compact generation

Let `f : X ⟶ Y` be a morphism of schemes. The Stacks proof of [Stacks, Tag 0A9E] obtains the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` from Brown representability in the form
[Stacks, Tag 0A8G], whose hypothesis is that `D_QCoh(𝒪_X)` be *compactly* generated — which is
[Stacks, Tag 09IS], for `X` quasi-compact and quasi-separated. There is a second form of Brown
representability, [Stacks, Tag 0GYH], which asks for much less: a family `E : ι → D_QCoh(𝒪_X)`
such that

1. every nonzero object receives a nonzero morphism from some `E i`, and
2. every morphism from some `E i` into a countable direct sum `∐ K` factors as a direct sum of
   morphisms `E (j n) ⟶ K n` preceded by a morphism `E i ⟶ ∐ₙ E (j n)`,

with no compactness of the `E i`. This file runs the Stacks proof of Tag 0A9E against that
hypothesis instead.

The point of doing so is that the weaker hypothesis has a route in the literature which does not
pass through Tag 09IS: [Stacks, Tag 0GZ0] part (3) produces it for the cartesian objects of the
small affine site of a scheme with no hypothesis at all, and [Stacks, Tag 0GZZ] is the comparison
of those with `D_QCoh(𝒪_X)`. Neither Tag 09IS nor that comparison is available here, so nothing
below is Tag 0A9E; what the statements do is name the single hypothesis each of the two routes
has to discharge.

## Main results

* `Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating`
  — the Stacks proof of [Stacks, Tag 0A9E] with [Stacks, Tag 09IS] replaced by a generating
  family in the sense of [Stacks, Tag 0GYG], and every other input except [Stacks, Tag 08DZ]
  discharged. The morphism is arbitrary here, which is why Tag 08DZ stays a hypothesis: it is a
  theorem only for a quasi-compact quasi-separated morphism.
* `isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating_of_qcqs`, in the same namespace
  — the same for a quasi-compact quasi-separated morphism, where [Stacks, Tag 08DZ] is discharged
  as well, leaving the generating family and part (1) of [Stacks, Tag 08D5].
* `isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating`, in the same namespace
  — the same for a quasi-compact quasi-separated morphism with quasi-compact target, where
  [Stacks, Tag 08D5] part (1) is discharged as well, leaving exactly one hypothesis: the
  generating family.

## Implementation notes

The index type `ι` is in the scheme universe `u`, which is also the morphism universe of the
derived category in force (`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`), so the direct
sums [Stacks, Tag 0GYH] asks for are the `HasCoproducts.{max u u} = HasCoproducts.{u}` of
[Stacks, Tag 08DT], available as
`Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory`. Unlike
[Stacks, Tag 0A8G], Tag 0GYH leaves the index universe of the family free of the morphism
universe, so this is not forced; it is the choice that makes the hypothesis the one Tag 08DT
supplies.

**What is still carried, and why.** Exactness of the restricted functor is discharged by the
instances of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/Exactness.lean`, and triangulatedness
and direct sums of `D_QCoh(𝒪_X)` by
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated` and
`hasCoproducts_quasiCoherentDerivedCategory`. The direct-sum hypothesis on the restricted functor
is [Stacks, Tag 08DZ]; for a quasi-compact quasi-separated morphism it is discharged by
`LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`, which is that
tag at the locally small model these statements live at. It survives as a hypothesis only in the
statement for an arbitrary morphism, where it is not a theorem.

**No `@[stacks]` attribute is attached.** Tag 0A9E asserts the existence of the right adjoint for
a morphism of quasi-compact quasi-separated schemes with no further hypothesis, and no statement
below reaches that: each carries the generating family, which is Tag 09IS in the source and
Tags 0GZ0 and 0GZZ on the other route. A tag here would report an open tag as formalized.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0GYH](https://stacks.math.columbia.edu/tag/0GYH)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The Stacks proof of [Stacks, Tag 0A9E] with the generating family of
[Stacks, Tag 0GYG] in place of compact generation.** Let `f : X ⟶ Y` be a morphism of schemes and
suppose derived direct image preserves quasi-coherent cohomology. If the restricted functor
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums ([Stacks, Tag 08DZ]) and
`D_QCoh(𝒪_X)` carries a family `E` which detects nonzero objects and through which morphisms into
countable direct sums factor, then `Rf_*` has a right adjoint — the twisted inverse image `f^×`.

The members of `E` are **not** assumed compact. Everything else the source uses is discharged:
`D_QCoh` is a triangulated subcategory on either side, `D_QCoh(𝒪_X)` has direct sums
([Stacks, Tag 08DT]), and the restricted functor is exact. The proof is one application of
[Stacks, Tag 0GYH]. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)]
    {ι : Type u} (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X)
    (hE : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, ¬ IsZero K →
      ∃ (i : ι) (g : E i ⟶ K), g ≠ 0)
    (hE' : ∀ (K : ℕ → Stacks.Duality.quasiCoherentDerivedCategory X) (i : ι) (α : E i ⟶ ∐ K),
      ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint := by
  have hsum := hasCoproducts_quasiCoherentDerivedCategory X
  obtain ⟨_, adj, _, _⟩ :=
    Pretriangulated.exists_isTriangulated_rightAdjoint_of_generating_of_factorsThroughSigma
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush) E hE hE'
  exact adj.isLeftAdjoint

/-- **[Stacks, Tag 0A9E] for a quasi-compact quasi-separated morphism, with the generating family
of [Stacks, Tag 0GYG] as its only hypothesis beyond part (1) of [Stacks, Tag 08D5].** Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and suppose derived direct
image preserves quasi-coherent cohomology. If `D_QCoh(𝒪_X)` carries a family `E` which detects
nonzero objects and through which morphisms into countable direct sums factor, then `Rf_*` has a
right adjoint.

Compared with `isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating` this discharges
[Stacks, Tag 08DZ] — that the restricted functor commutes with direct sums — by
`LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`,
which is where quasi-compactness and quasi-separatedness of `f` are used. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating_of_qcqs
    [QuasiCompact f] [QuasiSeparated f]
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    {ι : Type u} (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X)
    (hE : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, ¬ IsZero K →
      ∃ (i : ι) (g : E i ⟶ K), g ≠ 0)
    (hE' : ∀ (K : ℕ → Stacks.Duality.quasiCoherentDerivedCategory X) (i : ι) (α : E i ⟶ ∐ K),
      ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush) := fun α ↦
    LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward f hpush α
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating f hpush E hE hE'

/-- **[Stacks, Tag 0A9E] reduced to one hypothesis.** Let `f : X ⟶ Y` be a quasi-compact
quasi-separated morphism of schemes with `Y` quasi-compact. If `D_QCoh(𝒪_X)` carries a generating
family in the sense of [Stacks, Tag 0GYG], then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right
adjoint.

Compared with `isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating` this discharges two
inputs: part (1) of [Stacks, Tag 08D5], that `Rf_*` preserves quasi-coherence of cohomology, by
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`, and [Stacks, Tag 08DZ],
that the restricted functor commutes with direct sums, by
`isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating_of_qcqs`. The generating family is
all that is left. -/
theorem isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_generating
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    {ι : Type u} (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X)
    (hE : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X, ¬ IsZero K →
      ∃ (i : ι) (g : E i ⟶ K), g ≠ 0)
    (hE' : ∀ (K : ℕ → Stacks.Duality.quasiCoherentDerivedCategory X) (i : ι) (α : E i ⟶ ∐ K),
      ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ K n) (γ : E i ⟶ ∐ fun n ↦ E (j n)),
        α = γ ≫ Limits.Sigma.map β) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_generating_of_qcqs f _ E hE hE'

end Stacks.Duality.DerivedPushforward

end
