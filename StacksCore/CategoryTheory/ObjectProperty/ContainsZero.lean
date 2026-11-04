module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import StacksCore.Tactic.StacksAttribute

/-! ## The kernel of a functor. -/

add_to_stacks 02MR "`Ker F`, the full subcategory of objects killed by `F`. Reducibly
`ObjectProperty.inverseImage IsZero F`, hence the very object property that 02MQ is stated for in
`StacksCore.CategoryTheory.Abelian.SerreClass.Basic`: one definition seen twice, with
`F.kernel X ↔ IsZero (F.obj X)` by `rfl`."
  CategoryTheory.Functor.kernel
