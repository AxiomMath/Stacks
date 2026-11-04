module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCore.Tactic.EgaSgaAttribute

/-! # Pushforward along a point of a site

## Main results

* `pushforwardPoint`: the pushforward `p_* E` of an object `E` along a point `p` of a site,
  i.e. the skyscraper sheaf at `p` with value `E` (Stacks 00Y9).
* `pushforwardPoint_obj`, `pushforwardPoint_obj_obj`: the underlying presheaf of `p_* E`, and
  its value on an object as a product of copies of `E` indexed by the fibre of `p`.

Tags covered: 00Y9.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

/-- **Stacks 00Y9.** The pushforward `p_* E` of an object `E` along a point `p` of the site
`(C, J)`: the skyscraper sheaf at `p` with value `E`. -/
@[stacks 00Y9, ega "IV 21.9.1" "more general"]
noncomputable def pushforwardPoint
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : J.Point) {A : Type*} [Category A] [Limits.HasProducts A] (E : A) :
    Sheaf J A :=
  p.skyscraperSheaf E

/-- The sections of `p_* E` over `V` form the product of copies of `E` indexed by the fibre
of `p` over `V`. -/
theorem pushforwardPoint_obj_obj
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : J.Point) {A : Type*} [Category A] [Limits.HasProducts A] (E : A) (V : C) :
    ((pushforwardPoint p E).obj).obj (op V) =
      ∏ᶜ (fun (_ : p.fiber.obj V) => E) :=
  rfl

/-- The presheaf underlying `p_* E` is the skyscraper presheaf at `p` with value `E`. -/
theorem pushforwardPoint_obj
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : J.Point) {A : Type*} [Category A] [Limits.HasProducts A] (E : A) :
    (pushforwardPoint p E).obj = p.skyscraperPresheaf E :=
  rfl
