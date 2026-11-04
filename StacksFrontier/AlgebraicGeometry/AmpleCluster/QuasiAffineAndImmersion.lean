module

public import StacksFrontier.AlgebraicGeometry.AmpleCluster.Basic

/-!
# Finite sets in a common affine open: the quasi-affine and affine-immersion cases

Stacks Tag 01ZY gives four hypotheses, each of which puts a finite set of points of a scheme into
a single affine open: the scheme is quasi-affine; it immerses into an affine scheme; it carries an
ample invertible module; it immerses into a `Proj`. This file proves the first two.

Both come from the prime-avoidance lemma of the sibling file
`StacksFrontier/AlgebraicGeometry/AmpleCluster/Basic.lean`, which already treats the general
shape "a scheme with an open immersion into an affine scheme".

* **Quasi-affine.** Mathlib's `AlgebraicGeometry.Scheme.IsQuasiAffine` makes `X.toSpecΓ` an open
  immersion into `Spec Γ(X, ⊤)`, so the lemma applies verbatim with the ambient open taken to be
  `⊤`.
* **Immersion into an affine scheme.** An immersion factors as a closed immersion
  `i.liftCoborder : X ⟶ i.coborderRange` followed by the open immersion `i.coborderRange.ι`
  (Mathlib's `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`). Composing that open
  immersion with `Y.isoSpec` puts `i.coborderRange` in the shape the lemma wants, giving an affine
  open `V ⊆ i.coborderRange` around the image of the finite set; its preimage in `X` is affine
  because a closed immersion is an affine morphism, and it contains the finite set.

Note that neither statement needs `X` to be quasi-compact: the open produced is a *single* basic
open, not a finite union, so no compactness enters. In particular the second case is not derived
from the first, which would need `X` quasi-compact to even state the hypothesis.

## Main results

* `Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine`: part (1).
* `Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_affine`: part (2).

## Implementation notes

`IsAffineOpen.preimage` wants `[IsAffineHom f]`; for `f = i.liftCoborder` that instance is found
through Mathlib's `IsClosedImmersion` instance on `liftCoborder`, which is in turn why the
closed-then-open factorization is the useful one here rather than the open-then-closed one (the
latter is available only for quasi-compact immersions).

No transparency workaround is needed in this file. The two in the sibling file are about the two
descriptions of the points of `Spec R` and are described there.

## References

* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)

## What is not done

Parts (3) and (4) of the tag are not proved here; this file carries the part (1) and part (2)
labels and no other. Both of the remaining parts are proved elsewhere in the library.

Part (3), the ample case, is
`Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample`
(`../AmpleAffineAvoidance/AmpleFiniteSet.lean`). It does **not** go through `Proj`, which is why
it is available: the source's route — an ample invertible module presents the scheme as an open
subscheme of a `Proj`, by Stacks Tag 01Q3 — is still not formalized here, and the graded ring
`Γ_*(X, L) = ⨁_n Γ(X, L ^⊗ n)` of Stacks Tag 01CV is available only as a plain commutative ring with
no `GradedRing` instance. The proof of part (3) uses part (1) of this file instead: an ample `L` puts
the finite set inside a single `X_a`, that `X_a` is quasi-affine, and part (1) shrinks it to an
affine open. So the obstruction recorded here — that
`Stacks.Ample.nonvanishingLocus_add_subset` bounds `X_{s + t}` above by `X_s ∪ X_t` and so points
the wrong way, and that `Stacks.Ample.IsAmple` may serve two points by sections of two different
tensor powers, which cannot be added without the multiplication of that graded ring — is real,
but is not on the path actually taken.

Part (4), the `Proj` case, is
`Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj`
(`ProjImmersion.lean`). It needs the homogeneous form of prime avoidance (Stacks, Algebra, Lemma
10.57.6); Mathlib has no such lemma at the pin, but this repository proves it, as
`Stacks.GradedAvoidance.exists_homogeneous_pos_forall_notMem` (`../GradedSections/Avoidance.lean`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AmpleCluster

/-- **Stacks Tag 01ZY, part (1).** A finite set of points of a quasi-affine scheme lies in an
affine open. -/
@[stacks 01ZY "part (1)"]
theorem exists_affineOpen_containing_finite_of_isQuasiAffine {X : Scheme.{u}} [X.IsQuasiAffine]
    {E : Set X} (hE : E.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U := by
  obtain ⟨g, haff, hEU, -⟩ :=
    exists_affine_preimage_basicOpen_of_finite X.toSpecΓ hE ⊤ (fun _ _ => trivial)
  exact ⟨_, haff, hEU⟩

/-- **Stacks Tag 01ZY, part (2).** A finite set of points of a locally closed subscheme of an
affine scheme lies in an affine open. -/
@[stacks 01ZY "part (2)"]
theorem exists_affineOpen_containing_finite_of_immersion_affine {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsImmersion i] [IsAffine Y] {E : Set X} (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U := by
  obtain ⟨g, haff, hEV, -⟩ := exists_affine_preimage_basicOpen_of_finite
    (i.coborderRange.ι ≫ Y.isoSpec.hom) (hE.image i.liftCoborder) ⊤ (fun _ _ => trivial)
  exact ⟨i.liftCoborder ⁻¹ᵁ _, haff.preimage i.liftCoborder, fun x hx => hEV ⟨x, hx, rfl⟩⟩

end Stacks.AmpleCluster

end
