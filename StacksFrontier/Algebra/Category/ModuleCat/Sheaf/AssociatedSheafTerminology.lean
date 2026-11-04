module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf associated to a module, as a Stacks tag

Construction (3) of Stacks 01BH — for a ringed space `(X, 𝒪_X)`, a ring map
`α : R → Γ(X, 𝒪_X)` and an `R`-module `M`, the sheaf of `𝒪_X`-modules obtained by sheafifying
the presheaf `U ↦ 𝒪_X(U) ⊗_R M` — is built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison`, together with its
universal property and its comparison with construction (1), pullback along the morphism
`X ⟶ ({*}, R)`. This file records the tag on that construction.

## Main results

* `Stacks.AssociatedSheaf.associatedSheaf` realizes the associated-sheaf construction of
  Tag 01BH.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public section

add_to_stacks 01BH "associated_sheaf_construction" Stacks.AssociatedSheaf.associatedSheaf

end

-- ===== merged from StacksDraft.Ch17.Sec10.AssociatedSheafTerminology =====

/-!
# The sheaf associated to a module: terminology

Stacks 01BI fixes the terminology for construction (3) of Stacks 01BH: for a ringed space
`(X, 𝒪_X)`, a ring map `α : R → Γ(X, 𝒪_X)` and an `R`-module `M`, the sheafification of the
presheaf `U ↦ 𝒪_X(U) ⊗_R M` is called *the sheaf associated to `M`* (and to `α`). Taking `R`
to be the global sections of the structure sheaf and `α` the identity gives the sheaf
associated to `M` alone.

It introduces no new object: the construction is
`Stacks.AssociatedSheaf.associatedSheaf`, built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison` and already
registered against Stacks 01BH. This file records Stacks 01BI on the same construction.

## References

* [Stacks Project, Tag 01BI](https://stacks.math.columbia.edu/tag/01BI)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public section

add_to_stacks 01BI Stacks.AssociatedSheaf.associatedSheaf

end
