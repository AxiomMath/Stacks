module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Sheafified Yoneda for a subcanonical topology

On a subcanonical site the representable presheaves are already sheaves, so sheafifying one
changes nothing. Consequently the sheafified Yoneda embedding `U ↦ h_U^#` agrees with
Mathlib's `CategoryTheory.GrothendieckTopology.uliftYoneda`, the Yoneda embedding into
sheaves available for a subcanonical topology, and inherits its full faithfulness.

This module gathers the imports that provide these results:
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, the comparison isomorphism between the
sheafified Yoneda embedding and the Yoneda embedding into sheaves, and
`CategoryTheory.Sheaf.fullyFaithfulSheafifiedYoneda`, the full faithfulness of the sheafified
Yoneda embedding of a subcanonical site.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
  [HasSheafify J (Type max u v)]

end CategoryTheory.Sheaf
