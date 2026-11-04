module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Free abelian sheaves

The free abelian sheaf `Z_G^#` on a sheaf of sets `G` is
`Sheaf.composeAndSheafify J AddCommGrpCat.free` applied to `G`, left adjoint to the forgetful
functor `sheafCompose J (forget AddCommGrpCat)` by `Sheaf.adjunction J AddCommGrpCat.adj`.
The Yoneda and sheafification adjunctions identify maps from the free abelian sheaf on a
representable, and the free functor preserves sheafification.

## References

* [Stacks Project, Tag 03AB](https://stacks.math.columbia.edu/tag/03AB)
* [Stacks Project, Tag 05NY](https://stacks.math.columbia.edu/tag/05NY)
* [Stacks Project, Tag 03AC](https://stacks.math.columbia.edu/tag/03AC)
-/

@[expose] public section

-- Tag 03AB: `Mor(h_U^#, F) = F(U)`, `Mor(Z_G^#, A) = Mor(G, A)`, `Mor(Z_U^#, A) = A(U)`.
add_to_stacks 03AB "(1) sheafification adj" CategoryTheory.sheafificationAdjunction
add_to_stacks 03AB "(1) Yoneda" CategoryTheory.yonedaEquiv
add_to_stacks 03AB "(2) Z_G^#" CategoryTheory.Sheaf.composeAndSheafify
add_to_stacks 03AB "(2) Z_G^# ⊣ forget" CategoryTheory.Sheaf.adjunction
add_to_stacks 03AB "(3) Mor(Z_U^#, A)" CategoryTheory.Sheaf.freeYonedaHomEquiv
add_to_stacks 05NY "Mor_{Ab(C)}(Z_X^#, G) = G(X)" CategoryTheory.Sheaf.freeYonedaHomEquiv

-- Tag 03AC: `Z_G^# ≅ (Z_{G^#})^#`, naturally in `G`, because the left adjoint
-- `AddCommGrpCat.free` preserves sheafification.
add_to_stacks 03AC "free preserves (-)^#"
  CategoryTheory.Sheaf.preservesSheafification_of_adjunction
add_to_stacks 03AC "Z_G^# ≅ (Z_{G^#})^#" CategoryTheory.presheafToSheafCompComposeAndSheafifyIso
add_to_stacks 03AC "free ⊣ forget on Ab" AddCommGrpCat.adj
