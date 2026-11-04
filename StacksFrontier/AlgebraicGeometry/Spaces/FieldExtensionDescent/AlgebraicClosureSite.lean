module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase

/-!
# The algebraic closure of a field of a big fppf site lies in that site

A big fppf site holds the schemes whose size is below its cutoff, and base change along a
field extension `K/k` is only defined inside the site, so a statement about the base change of
an algebraic space over `k` to the algebraic closure of `k` needs `Spec (k̄)` to be an object of
the site. It is: the size of `Spec R` is `max ℵ₀ #R`, the algebraic closure of `k` has
cardinality at most `max #k ℵ₀`, and the cutoff is uncountable. No closure property of the
cutoff beyond that is used — in particular the strong prelimit hypothesis, which the
constructions of [Stacks, Tag 000R] generally need, is not.

With that in hand the base change of an algebraic space over `k` to `k̄`, which is restriction
along the induced morphism of spectra, is an algebraic space over `k̄` by [Stacks, Tag 03I5]
part (1), and base change of morphisms is the action of that restriction functor on morphisms.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_algebraicClosure`: the spectrum of the algebraic
  closure of a field whose spectrum lies in the site lies in the site.
* `AlgebraicGeometry.Space.algebraicClosureMap`: the morphism `Spec k̄ ⟶ Spec k` of the site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relocalizeRestrict_algebraicClosureMap`: the base
  change to `k̄` of an algebraic space over `k` is an algebraic space over `k̄`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- **The spectrum of the algebraic closure of a field of the site is in the site.** The size of
an affine scheme is the maximum of `ℵ₀` and the cardinality of its ring, the algebraic closure
of `k` has cardinality at most the maximum of `#k` and `ℵ₀`, and the site's cutoff is
uncountable. -/
theorem BigFppfSite.contains_spec_algebraicClosure (B : BigFppfSite.{u}) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) :
    B.Contains (Spec (.of (AlgebraicClosure k))) := by
  have hk' : max ℵ₀ (Cardinal.mk k) < B.cutoff := by
    rw [← Scheme.size_Spec (CommRingCat.of k)]
    exact hk
  show (Spec (CommRingCat.of (AlgebraicClosure k))).size < B.cutoff
  rw [Scheme.size_Spec]
  refine max_lt B.aleph0_lt_cutoff (lt_of_le_of_lt ?_ hk')
  exact (Algebra.IsAlgebraic.cardinalMk_le_max k (AlgebraicClosure k)).trans
    (le_of_eq (max_comm _ _))

namespace Space

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))

/-- The morphism `Spec k̄ ⟶ Spec k` of the big fppf site attached to the algebraic closure of a
field of the site. -/
abbrev algebraicClosureMap : B.obj (B.contains_spec_algebraicClosure k hk) ⟶ B.obj hk :=
  fieldExtensionMap B k (AlgebraicClosure k) hk (B.contains_spec_algebraicClosure k hk)

/-- **The base change of an algebraic space to the algebraic closure of the ground field is an
algebraic space.** This is [Stacks, Tag 03I5] part (1) for
`AlgebraicGeometry.Space.algebraicClosureMap`; base change of a *morphism* of algebraic spaces
is the action of the same restriction functor on morphisms. -/
theorem isAlgebraicSpace_relocalizeRestrict_algebraicClosureMap
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsAlgebraicSpace B (Spec (.of (AlgebraicClosure k))) (B.contains_spec_algebraicClosure k hk)
      ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj X) :=
  isAlgebraicSpace_relocalizeRestrict B (Spec (.of (AlgebraicClosure k))) (Spec (.of k))
    (B.contains_spec_algebraicClosure k hk) hk (algebraicClosureMap B k hk) X hX

end Space

end AlgebraicGeometry

end
