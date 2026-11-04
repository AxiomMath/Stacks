module

public import StacksFrontier.RingTheory.LocalCohomology.StrictProCategory
public import StacksCore.Tactic.StacksAttribute

/-!
# The strict pro-category, in the `CategoryTheory` namespace

The strict pro-category of a category has inverse sequences as objects and uniformly shifted,
eventual morphisms as arrows: the quotient of the path category on representatives of strict
pro-morphisms by `Stacks.LocalCohomology.strictProRelations`.

## Main definitions

* `CategoryTheory.StrictProCategory`: the strict pro-category, as presented by
  `Stacks.LocalCohomology.strictProRelations`.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

namespace CategoryTheory

universe v u

@[expose] public section

/-- The strict pro-category of `C`. Its objects are inverse sequences in `C`; its morphisms are
uniformly shifted compatible maps modulo eventual agreement after passing to a common shift. -/
@[stacks 0GA5 "strict_pro_category"]
abbrev StrictProCategory (C : Type u) [Category.{v} C] :=
  CategoryTheory.Quotient (Stacks.LocalCohomology.strictProRelations (C := C))

end

end CategoryTheory
