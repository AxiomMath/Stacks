module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Basic

/-!
# The fibrewise criterion for a syntomic morphism

A flat morphism of schemes which is locally of finite presentation and all of whose fibres are
local complete intersections over the residue fields of their base points is syntomic.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.syntomic_of_lci_fibers`: **Stacks 01UF**.

## Implementation notes

The fibre over a point `s` is `AlgebraicGeometry.Scheme.Hom.fiber`, presented by its structure
morphism `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` to the spectrum of the residue
field at `s`; being a local complete intersection over that field is
`AlgebraicGeometry.IsLocalCompleteIntersectionOverField`, which unfolds to syntomicity of the
structure morphism.

The proof is a single application of base change for the syntomic locus,
`AlgebraicGeometry.syntomicLocus_eq_preimage` (Tag 02V3): the fibre square is cartesian, so the
locus where the fibre is syntomic is the preimage of the locus where the morphism is syntomic,
and every point of the source lies in its own fibre. No local computation is needed, and the
flatness and finite-presentation hypotheses enter only through that lemma.

`AlgebraicGeometry.IsSyntomicAt` and `AlgebraicGeometry.SyntomicAt` are two names for one
predicate; `AlgebraicGeometry.isSyntomicAt_iff_syntomicAt` records this, and Tag 02V3 is stated
with the former while `AlgebraicGeometry.Syntomic` is defined by the latter.

## References

* [Stacks Project, Tag 01UF](https://stacks.math.columbia.edu/tag/01UF)
* [Stacks Project, Tag 02V3](https://stacks.math.columbia.edu/tag/02V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01UF.** A flat morphism of schemes which is locally of finite
presentation and whose every fibre is a local complete intersection over the residue field of
its base point is syntomic. -/
@[stacks 01UF]
theorem syntomic_of_lci_fibers {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f]
    (hlci : ∀ s : S, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField s)) :
    Syntomic f := by
  intro x
  have hmem : f.asFiber x ∈ {z | IsSyntomicAt (f.fiberToSpecResidueField (f x)) z} :=
    hlci (f x) (f.asFiber x)
  rw [syntomicLocus_eq_preimage (f.fiberι (f x)) (f.fiberToSpecResidueField (f x)) f
    (S.fromSpecResidueField (f x)) (IsPullback.of_hasPullback ..)] at hmem
  have hx : IsSyntomicAt f (f.fiberι (f x) (f.asFiber x)) := hmem
  rw [Scheme.Hom.fiberι_asFiber] at hx
  exact hx

end AlgebraicGeometry

end
