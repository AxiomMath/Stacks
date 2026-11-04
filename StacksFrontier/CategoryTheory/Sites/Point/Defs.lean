module

public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of a topos

The site `pt` has a single object, a single morphism and a single covering, so that its topos
of sheaves of sets is the category of sets, `Sh(pt) = Sets`. Accordingly `Sh(pt)` is modelled
here by `Type w`, and a point of a topos is a morphism of topoi out of `Type w`.

## Main definitions

* `PointOfTopos`: a point of the topos `Sh(C, J)`.
-/

@[expose] public section

open CategoryTheory

/-- A *point of the topos* `Sh(C, J)` is a morphism of topoi `p : Sh(pt) → Sh(C, J)`, where
`Sh(pt) = Sets` is modelled by `Type w`. Concretely, a point is an adjoint pair `p⁻¹ ⊣ p_*` with
`p⁻¹ : Sh(C, J) ⥤ Type w` (the stalk functor) and `p_* : Type w ⥤ Sh(C, J)` (the skyscraper
functor), such that `p⁻¹` is left exact. -/
@[stacks 00Y4, sga "4 IV 6.1"]
def PointOfTopos.{w, v, u} {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) : Type _ :=
  MorphismOfTopoi (Type w) (Sheaf J (Type w))
