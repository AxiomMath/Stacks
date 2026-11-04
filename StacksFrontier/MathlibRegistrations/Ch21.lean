module

public import Mathlib.CategoryTheory.Yoneda
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 21 (Cohomology on Sites) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

## Tags

* 071D: the global sections `Γ(C, F) = Mor_{PSh(C)}(e, F)` of a presheaf of sets are the
  morphisms from a final presheaf; the constant presheaf on a singleton is final.
-/

add_to_stacks 071D "global sections of a presheaf of sets as morphisms from the final presheaf \
(the constant presheaf on a singleton)" CategoryTheory.Functor.sectionsEquivHom
