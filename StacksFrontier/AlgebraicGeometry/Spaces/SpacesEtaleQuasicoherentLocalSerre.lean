module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.QuasicoherenceSliceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.LocalSerreFamily
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules on the slices of the spaces-étale site

Let `S` be a scheme and let `X` be an algebraic space over `S`.  Let `C = X_{spaces, étale}` be the
étale site on the category of algebraic spaces étale over `X`, with its structure sheaf
`U ↦ Γ(U, 𝒪_U)`, and for an object `U` of `C` let `A_U` be the category of quasi-coherent
`𝒪_U`-modules on the slice `C/U`.  This family satisfies the first of the three conditions the
unbounded cohomological descent of Tag 0DC1 imposes on a family of subcategories of the
categories of modules on the slices of a ringed site: restriction along a morphism of `C` sends
`A_V` into `A_U`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleQuasicoherentSlices`: the family `A_U`, quasi-coherence of
  modules on the slice of the spaces-étale site at `U`, as a
  `Stacks.Cohomology.CohomologicalDescent.SliceProperties` of the ringed site
  `(X_{spaces, étale}, 𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isStableUnderRestriction_spacesEtaleQuasicoherentSlices`: the family
  of quasi-coherent modules on the slices of the spaces-étale site is stable under restriction,
  which is condition `Stacks.Cohomology.CohomologicalDescent.IsStableUnderRestriction` of
  Tag 0DC2.

## What of Tag 0DC5 is *not* here

Tag 0DC5 asserts that all three of the conditions of Tag 0DC1 — Tags 0DC2, 0DC3 and 0DC4 — hold
for this family. Only the first is proved here, and no
`Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily` is assembled.

* **Condition (2), Tag 0DC3**, that membership in `A_U` is local on coverings of `U`, is not
  proved. Its forward implication is the result below; its converse needs the comparison of the
  iterated slice `(C/U)/V` with the slice `C/V.left` for quasi-coherence, which is not available.

* **Condition (3), Tag 0DC4**, with `B = Ob(C)`, `d_V = 0` and `Cov_V` the coverings of `V` by
  affine objects, is not proved. It needs the vanishing `H^p(V, F) = 0` for `p > 0` on an affine
  object `V` of the étale site and quasi-coherent `F` (the clause of Tag 03DW in positive degrees)
  and the cofinality of the affine coverings, neither of which is available.

* **The standing assumption** of Tag 0DC1, that each `A_U` is a weak Serre subcategory, is not
  established.

Nothing below is stated with the vanishing, the cofinality or the weak Serre property as a
hypothesis.

## Implementation notes

The ringed site is `AlgebraicGeometry.Space.spacesEtaleRingedSite`, whose objects, morphisms and
sections of the structure sheaf all live in the universe `u + 1` above the base scheme.
Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, Tag 03DL (6).

## References

* [Stacks Project, Tag 0DC5](https://stacks.math.columbia.edu/tag/0DC5)
* [Stacks Project, Tag 0DC2](https://stacks.math.columbia.edu/tag/0DC2)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The family `A_U`.**  For an algebraic space `X`, the family which assigns to
an object `U` of the spaces-étale site `X_{spaces, étale}` the quasi-coherent modules on the slice
`C/U`, read as a family of properties of sheaves of modules on the slices of the ringed site
`(X_{spaces, étale}, 𝒪_X)`. -/
noncomputable def spacesEtaleQuasicoherentSlices :
    Stacks.Cohomology.CohomologicalDescent.SliceProperties
      (spacesEtaleRingedSite B S hS X) :=
  fun U ↦ SheafOfModules.isQuasicoherentOnSite
    ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over U)

/-- **Stability under restriction.**  Let `X` be an algebraic space over a scheme `S` and let
`C = X_{spaces, étale}` be the étale site on the algebraic spaces étale over `X`, with its
structure sheaf.  Then the family which assigns to an object `U` of `C` the quasi-coherent modules
on `C/U` is stable under restriction: for a morphism `f : U ⟶ V` of `C`, the restriction functor
from modules on `C/V` to modules on `C/U` sends quasi-coherent modules to quasi-coherent modules.

This is condition (1) of Tag 0DC1, i.e. the condition
`Stacks.Cohomology.CohomologicalDescent.IsStableUnderRestriction` of Tag 0DC2, for this family. -/
@[stacks 0DC5 "property (1), i.e. condition 0DC2 for the family A_U of quasi-coherent modules on \
the slices of the spaces-etale site of an algebraic space: restriction along a morphism U -> V of \
the site sends A_V into A_U. NOT covered by this declaration: property (2) (condition 0DC3, \
locality on coverings), property (3) (condition 0DC4, the set B = Ob(C) with d_V = 0 and the \
cofinal affine coverings), and the standing assumption that each A_U is a weak Serre \
subcategory; no LocalSerreFamily is assembled. See the module documentation for why each of those \
is unreachable in this development -- in particular the positive-degree vanishing of the \
cohomology of a quasi-coherent module on an affine object of the etale site, the clause of \
Stacks 03DW that the source's reference to Stacks 01XB and Stacks 071Y supplies, is proved \
nowhere here and also blocks Stacks 0720 and Stacks 08EX"]
theorem isStableUnderRestriction_spacesEtaleQuasicoherentSlices :
    Stacks.Cohomology.CohomologicalDescent.IsStableUnderRestriction
      (spacesEtaleRingedSite B S hS X) (spacesEtaleQuasicoherentSlices B S hS X) := by
  intro U V f F hF
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_overMap _ f F hF

end AlgebraicGeometry.Space

end
