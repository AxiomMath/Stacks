module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-! # Topoi and morphisms of topoi

A *topos* is the category `Sheaf J (Type w)` of sheaves of sets on a site `(C, J)`. Mathlib has
no notion of geometric morphism; the library's `MorphismOfTopoi E F` packages the data
`(f_*, f⁻¹, f⁻¹ ⊣ f_*, f⁻¹ left exact)` for arbitrary categories `E`, `F`, and this file
specialises it to sheaf topoi on sites.

## Main definitions

* `SheafToposMorphism J K`: a morphism of topoi `f : Sh(D) → Sh(C)` (Stacks 00XA (1)).
* `SheafToposMorphism.comp`: the composition `f ∘ g` with `(f ∘ g)_* = f_* ∘ g_*` and
  `(f ∘ g)⁻¹ = g⁻¹ ∘ f⁻¹` (Stacks 00XA (2)).
* `LeftAdjointsPreserveFiniteLimits`: the (in general false) proposition that every left adjoint
  between two sheaf categories is left exact; not the definition of a morphism of topoi.

Tags covered: 00XA.
-/

@[expose] public section

open CategoryTheory

universe w v₁ u₁ v₂ u₂ v₃ u₃

/-- **Stacks 00XA (1).** Let `(C, J)` and `(D, K)` be sites. A *morphism of topoi* `f` from
`Sh(D)` to `Sh(C)` is a pair of functors `f_* : Sh(D) ⥤ Sh(C)` and `f⁻¹ : Sh(C) ⥤ Sh(D)`
together with an adjunction `f⁻¹ ⊣ f_*` (that is, `Mor(f⁻¹ G, F) = Mor(G, f_* F)` bifunctorially)
such that `f⁻¹` commutes with finite limits. Here `Sh(C)` is the category of sheaves of sets
`Sheaf J (Type w)`; the fields are `pushforward` (`f_*`), `inverseImage` (`f⁻¹`), `adj` and
`preservesFiniteLimits` of `MorphismOfTopoi`. -/
@[stacks 00XA "(1); the composition (2) is `SheafToposMorphism.comp`"]
abbrev SheafToposMorphism {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) :=
  MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))

namespace SheafToposMorphism

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}

/-- **Stacks 00XA (2).** Given morphisms of topoi `f : Sh(D) → Sh(C)` and `g : Sh(E) → Sh(D)`,
the composition `f ∘ g : Sh(E) → Sh(C)` is the morphism of topoi given by the functors
`(f ∘ g)_* = f_* ∘ g_*` and `(f ∘ g)⁻¹ = g⁻¹ ∘ f⁻¹` (see `pushforward_comp` and
`inverseImage_comp`). -/
@[stacks 00XA "(2)"]
abbrev comp (f : SheafToposMorphism.{w} J K) (g : SheafToposMorphism.{w} K L) :
    SheafToposMorphism.{w} J L :=
  MorphismOfTopoi.comp f g

/-- The pushforward of a composite is `(f ∘ g)_* = f_* ∘ g_*`. -/
theorem pushforward_comp (f : SheafToposMorphism.{w} J K) (g : SheafToposMorphism.{w} K L) :
    (f.comp g).pushforward = g.pushforward ⋙ f.pushforward :=
  rfl

/-- The inverse image of a composite is `(f ∘ g)⁻¹ = g⁻¹ ∘ f⁻¹`. -/
theorem inverseImage_comp (f : SheafToposMorphism.{w} J K) (g : SheafToposMorphism.{w} K L) :
    (f.comp g).inverseImage = f.inverseImage ⋙ g.inverseImage :=
  rfl

end SheafToposMorphism

/-- The proposition that every left adjoint `f_inv` of a functor `f_star : Sheaf K A ⥤ Sheaf J A`
preserves finite limits. This is *not* the definition of a morphism of topoi (Stacks 00XA, which is
`SheafToposMorphism`): there left exactness is a requirement on a given adjoint pair, not a claim
about all adjoint pairs. It is false in general: for `A = Type` on the one-point site, `X × -` is
left adjoint to `X ⟹ -` but does not preserve the terminal object unless `X` is a singleton. -/
def LeftAdjointsPreserveFiniteLimits (C : Type*) [Category C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] (K : GrothendieckTopology D)
    (A : Type*) [Category A] : Prop :=
  ∀ (f_star : Sheaf K A ⥤ Sheaf J A) (f_inv : Sheaf J A ⥤ Sheaf K A),
    (f_inv ⊣ f_star) → Limits.PreservesFiniteLimits f_inv
