module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FlatPushforwardPreservesKInjectives
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact

/-! # The two spellings of K-injectivity agree

K-injectivity of a cochain complex is stated twice in this development, at two different
levels:

* `IsKInjectiveHomotopyCategory`, the spelling used by Stacks Tag 093Y, is a `Prop`-valued
  `def` at the level of the **homotopy category**: every morphism `Q(M) ⟶ Q(I)` out of an
  acyclic `M` is zero;
* `CochainComplex.IsKInjective` (Mathlib) is a **class** at the level of **complexes**: every
  chain map `M ⟶ I` out of an acyclic `M` admits a homotopy to zero.

They say the same thing, because a chain map becomes zero in the homotopy category exactly when
it is null-homotopic, but they are different Lean terms and neither is usable where the other
is expected. This file supplies the equivalence, so that the result tagged Stacks 093Y —
`rightAdjoint_preserves_isKInjective`, stated with the first spelling — can be cited where the
second is required, which is everywhere else: the K-injective resolutions of Stacks 079P, the
computation of right derived functors on K-injective complexes, and Mathlib's own API all use
the class.

## Main results

* `Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective`: the two predicates are
  equivalent.

## References

* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Cohomology

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The homotopy-category spelling of K-injectivity used by `rightAdjoint_preserves_isKInjective`
(Stacks 093Y) agrees with Mathlib's complex-level class `CochainComplex.IsKInjective`.

Left to right, a morphism out of an acyclic complex is zero in the homotopy category, hence
null-homotopic by `CategoryTheory.HomotopyCategory.homotopyOfEq`. Right to left, the quotient
functor is full, so such a morphism of the homotopy category is the class of a chain map, which
is null-homotopic and therefore zero. -/
alias isKInjectiveHomotopyCategory_iff_isKInjective :=
  Stacks.Injectives.isKInjectiveHomotopyCategory_iff_isKInjective

end Stacks.Cohomology

end
