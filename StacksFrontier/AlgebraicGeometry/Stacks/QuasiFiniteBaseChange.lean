module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiFiniteAlgebraicStack

/-!
# Base change of quasi-finite 1-morphisms of algebraic stacks (Stacks 0G2P)

A base change of a quasi-finite 1-morphism of algebraic stacks over `S` is quasi-finite.
Quasi-finiteness (**Stacks 0G2M**) is the conjunction of local quasi-finiteness (**Stacks 06PU**)
and quasi-compactness (**Stacks 050U**), and each conjunct is separately stable under base change:
the first by **Stacks 06UB** and the second by **Stacks 050V**. Both are stated at an arbitrary
recognised 2-fibre product of the cospan, with the conclusion about the first projection, so the
conjunction of the two is the whole of Stacks 0G2P.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiFinite_baseChange`: **Stacks 0G2P**.

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiFinite` is an `abbrev` for a conjunction, so the
hypothesis projects to its two conjuncts and the conclusion is built by `And.intro`; the two
components are the two base-change lemmas applied to the same square and the same recognition
hypothesis. Nothing further is needed, and in particular the 2-fibre product is not re-recognised
and the field-valued fibres are not revisited — that work is inside Stacks 06UB.

The quasi-compactness conjunct is spelled `AlgebraicGeometry.Stack.IsQuasiCompactMorphism`, the
arm over `AlgebraicGeometry.Stack.AlgebraicStacks`, and not the Stacks 04XB relative property
`AlgebraicGeometry.Stack.IsQuasiCompact`, which takes a 1-morphism of categories fibred in
groupoids. The two are type-incomparable.

## References

* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 06UB](https://stacks.math.columbia.edu/tag/06UB)
* [Stacks Project, Tag 0G2M](https://stacks.math.columbia.edu/tag/0G2M)
* [Stacks Project, Tag 0G2P](https://stacks.math.columbia.edu/tag/0G2P)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0G2P.** A base change of a quasi-finite 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over `S` is quasi-finite: the first projection of any 2-fibre product of the cospan `(g, f)` is
quasi-finite as soon as `f` is.

Quasi-finiteness is local quasi-finiteness together with quasi-compactness, and the two conjuncts
are inherited by **Stacks 06UB** and **Stacks 050V** respectively. -/
@[stacks 0G2P]
theorem isQuasiFinite_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsQuasiFinite B S hS f) :
    IsQuasiFinite B S hS P.fst :=
  ⟨isLocallyQuasiFinite_baseChange B S hS f g P hP hf.1,
    Stack.isQuasiCompactMorphism_baseChange B S hS f g P hP hf.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
