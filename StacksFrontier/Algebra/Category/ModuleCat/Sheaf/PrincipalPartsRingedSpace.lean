module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
import StacksCore.Tactic.StacksAttribute

/-!
# The module of principal parts on a topological space

Let `O₁ ⟶ O₂` be a map of sheaves of rings on a topological space `X` and let `F` be a sheaf
of `O₂`-modules. The sheaf of `O₂`-modules corepresenting the differential operators of order
at most `k` out of `F` is the *module of principal parts of order `k`* of `F`, written
`Pᵏ_{O₂/O₁}(F)`. This is Tag 0G3T, the naming of the object whose existence is Tag 0G3S.

The site of opens of a topological space is a site, so this is the same object as in the
site-theoretic Tag 09CU, and `moduleOfPrincipalParts` needs no hypotheses beyond those already
carried by the general statement: this file records the tag on that declaration rather than on
a restricted copy, exactly as Tags 0G3Q, 0G3R and 0G3S are recorded.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.moduleOfPrincipalParts` (Tag 09CU) also realizes
  Tag 0G3T.

## References

* [Stacks Project, Tag 0G3T](https://stacks.math.columbia.edu/tag/0G3T)
* [Stacks Project, Tag 09CU](https://stacks.math.columbia.edu/tag/09CU), the module of
  principal parts on an arbitrary site.
-/

@[expose] public section

add_to_stacks 0G3T "the ringed-space case of 09CU"
  AlgebraicGeometry.SheafOfModules.moduleOfPrincipalParts

end
