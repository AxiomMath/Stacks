module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksCore.Tactic.StacksAttribute

/-!
# Presheaf functors attached to a pair of adjoint functors

Stacks 09VQ says that for `u : C ⥤ D` with right adjoint `v : D ⥤ C`, restriction along `u`
carries the representable presheaf `h_V` to `h_{v V}` (1), the index category
`I^v_U = StructuredArrow U v` has an initial object (2) and `{}^u_V I = CostructuredArrow u V`
has a final one (3), and the presheaf functors satisfy `{}_p u = v^p` (4) and `u^p = v_p` (5).

Nothing is reproved here. Clause (1) is Mathlib's `CategoryTheory.Adjunction.compYonedaIso`,
which exhibits the isomorphism naturally in `V`; clauses (2) and (3) are
`CategoryTheory.mkInitialOfLeftAdjoint` and `CategoryTheory.mkTerminalOfRightAdjoint`, which
moreover name the initial and final objects as the unit and the counit; and clauses (4) and (5)
are `CategoryTheory.Functor.ranIsoRestrictionOfAdjunction` and `restrictionIsoLanOfAdjunction`
of `StacksFrontier.CategoryTheory.Sites.CoverLifting`, stated there for an arbitrary category of
values rather than only for presheaves of types.

## References

* [Stacks Project, Tag 09VQ](https://stacks.math.columbia.edu/tag/09VQ)
-/

@[expose] public section

add_to_stacks 09VQ "(1) `u^p h_V = h_{v V}`, naturally in `V`"
  CategoryTheory.Adjunction.compYonedaIso
add_to_stacks 09VQ "(2) `I^v_U` has the initial object `(u U, η_U)`"
  CategoryTheory.mkInitialOfLeftAdjoint
add_to_stacks 09VQ "(3) `{}^u_V I` has the final object `(v V, ε_V)`"
  CategoryTheory.mkTerminalOfRightAdjoint
add_to_stacks 09VQ "(4) `{}_p u = v^p`"
  CategoryTheory.Functor.ranIsoRestrictionOfAdjunction
add_to_stacks 09VQ "(5) `u^p = v_p`"
  CategoryTheory.Functor.restrictionIsoLanOfAdjunction
