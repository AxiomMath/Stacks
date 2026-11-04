module

public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
/-!
# The two spellings of `Ass(F)` agree

The tree carries two declarations for the set of associated points of an `𝒪_X`-module: the one
the source's definition [Stacks, Tag 02OJ] is formalised as,
`Stacks.Divisors.associatedPoints`, and the one that [Stacks, Tag 0AVL] is stated against,
`Stacks.AlgebraicGeometry.AssociatedPointsMono.associatedPoints`. They are the same set: both
say that the maximal ideal of `𝒪_{X, x}` is an associated prime of the stalk of `F` at `x`, both
read that stalk as the stalk of the underlying presheaf of abelian groups of `F.val`, and both
give it the module structure that `PresheafOfModules` puts on such a stalk — the only difference
is that one introduces it as a `letI` from a definition and the other as an instance. So the two
predicates are the same proposition up to unfolding, and `Stacks.Divisors` is the spelling to
use.

This file records the identification and restates Tag 0AVL against
`Stacks.Divisors.associatedPoints`, so that a consumer phrasing its hypotheses with the Tag
02OJ definition — for instance [Stacks, Tag 0BJZ], whose hypothesis is a condition at every
point of `Ass(F)` — can apply Tag 0AVL without carrying the second spelling around.

## Main results

* `Stacks.Divisors.associatedPoints_eq_associatedPointsMono`: the two sets are equal.
* `Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints`: Tag 0AVL, with its hypothesis
  phrased using `Stacks.Divisors.associatedPoints`.

## Implementation notes

The equality holds by `rfl`, so nothing is bridged: no transport of the hypothesis of Tag 0AVL
is needed and the restatement below is the original theorem with its statement re-elaborated.
The tag `0AVL` stays on
`Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints`,
which is where the proof is; this file adds no tag.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The associated point predicate of [Stacks, Tag 02OJ] and the one Tag 0AVL is stated against
are the same predicate. -/
theorem isAssociatedPoint_iff_associatedPointsMono (F : X.Modules) (x : X) :
    IsAssociatedPoint F x ↔
      Stacks.AlgebraicGeometry.AssociatedPointsMono.IsAssociatedPoint F x :=
  Iff.rfl

/-- `Ass(F)` as defined in [Stacks, Tag 02OJ] is the set of associated points that
[Stacks, Tag 0AVL] is stated against. -/
theorem associatedPoints_eq_associatedPointsMono (F : X.Modules) :
    associatedPoints F = Stacks.AlgebraicGeometry.AssociatedPointsMono.associatedPoints F :=
  rfl

/-- **[Stacks, Tag 0AVL].** A morphism of quasi-coherent modules on a locally Noetherian scheme
is a monomorphism as soon as, at every point, either the induced map of stalks is injective or
the point is not in `Ass(F)`.

This is
`Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints` with
`Ass(F)` spelled as in [Stacks, Tag 02OJ]. -/
theorem mono_of_stalk_injective_on_associatedPoints [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ x : X,
      Function.Injective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)).hom ∨
        x ∉ associatedPoints F) :
    CategoryTheory.Mono f :=
  Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints f hf

end Stacks.Divisors
