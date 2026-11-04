module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import StacksCore.Tactic.StacksAttribute

/-!
# Free abelian presheaves

The free abelian presheaf `Z_G = G ⋙ AddCommGrpCat.free` and its adjunction with the forgetful
functor `PAb(C) ⥤ PSh(C)` are `AddCommGrpCat.adj.whiskerRight Cᵒᵖ`.
-/

@[expose] public section

-- Tag 03A8: `Mor(h_U, F) = F(U)`, `Mor(Z_G, A) = Mor(G, A)`, and their composite
-- `Mor(Z_U, A) = A(U)`, all natural.
add_to_stacks 03A8 "(1) Yoneda" CategoryTheory.yonedaEquiv
add_to_stacks 03A8 "(2), (3) Z_G ⊣ forget" CategoryTheory.Adjunction.whiskerRight
add_to_stacks 03A8 "free ⊣ forget on Ab" AddCommGrpCat.adj

-- Tag 03A9: `Z_(-)` is a left adjoint, so `⊕ Z_{G_i} → Z_{∐ G_i}` is an isomorphism.
add_to_stacks 03A9 "Z_(-) is a left adjoint" CategoryTheory.Adjunction.whiskerRight
add_to_stacks 03A9 "preserves coproducts" CategoryTheory.Adjunction.leftAdjoint_preservesColimits
add_to_stacks 03A9 "Z_{∐ G_i} ≅ ⊕ Z_{G_i}" CategoryTheory.Limits.PreservesCoproduct.iso
