module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# A scheme covered by two disjoint affine opens is affine

If a scheme is the union of two disjoint affine opens then it is affine: the two opens form a
finite pairwise disjoint family of affine opens whose supremum is the whole scheme, and such a
supremum is an affine open.

## Main results

* `Stacks.ZariskiAndSeparation.AffineDisjointUnion.isAffine_of_sup_eq_top_of_disjoint`:
  [Stacks Project, Tag 01I5].

## Implementation notes

The source states this for a locally ringed space `X = U ⨿ V`, which is then a scheme because it
has an affine open cover; the statement below assumes that `X` is a scheme, and the attribute
records the difference.

## References

* [Stacks Project, Tag 01I5](https://stacks.math.columbia.edu/tag/01I5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ZariskiAndSeparation.AffineDisjointUnion

/-- **A scheme covered by two disjoint affine opens is affine.** -/
@[stacks 01I5 "for a scheme; a locally ringed space with an affine open cover is one"]
theorem isAffine_of_sup_eq_top_of_disjoint {X : Scheme.{u}} (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (hd : Disjoint U V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffine X := by
  have hpair : Pairwise (Function.onFun Disjoint (fun b : Bool => cond b U V)) := by
    rintro (_ | _) (_ | _) hij
    exacts [absurd rfl hij, hd.symm, hd, absurd rfl hij]
  have h := IsAffineOpen.iSup_of_disjoint (fun b => by cases b <;> assumption) hpair
  rw [iSup_bool_eq] at h
  have : IsAffine (⊤ : X.Opens).toScheme := hUV ▸ (h : IsAffineOpen (U ⊔ V))
  exact IsAffine.of_isIso (Scheme.topIso X).inv

end Stacks.ZariskiAndSeparation.AffineDisjointUnion

end
