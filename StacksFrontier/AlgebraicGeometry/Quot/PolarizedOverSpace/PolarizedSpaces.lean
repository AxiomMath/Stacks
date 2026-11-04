module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.ModulesPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange

/-!
# Polarized families of algebraic spaces over an algebraic space (left side of Stacks 0E94)

Let `T` be an algebraic space over `Spec(ℤ)`. The left-hand category of Stacks 0E94 has for
objects the pairs `(X ⟶ T, L)` of a morphism of algebraic spaces which is proper, flat and of
finite presentation, and an invertible `𝒪_X`-module `L` which is ample on `X/T` in the sense of
Stacks 0D31 (`AlgebraicGeometry.Space.IsRelativelyAmple`). Its morphisms are the isomorphisms of
such pairs: an isomorphism `f : X ≅ X'` over `T` together with an isomorphism `L ≅ f^*L'`. The
category is a groupoid because the right-hand side of Stacks 0E94 is one (Stacks 0D3Z: the
category `Polarized` is fibred in groupoids), exactly as for Stacks 0E93.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.familyModules`: the pseudofunctor `X ↦ Modules(𝒪_X)` on
  the finitely presented, flat and proper algebraic spaces over `T` of Stacks 0E93.
* `AlgebraicGeometry.PolarizedOverSpace.IsPolarization`: invertibility and relative ampleness.
* `AlgebraicGeometry.PolarizedOverSpace.PolarizedSpacesOver`: **the left-hand category of
  Stacks 0E94**, the core of the full subcategory of the Grothendieck construction of
  `familyModules` on the polarizations.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

variable (B : BigFppfSite.{u})

/-- The ambient base scheme `Spec(ℤ)` lies in every big fppf site. -/
abbrev hZ : B.Contains integerBase := B.contains_integerBase

variable (T : AlgebraicSpaces B integerBase (hZ B))

/-- The finitely presented, flat and proper algebraic spaces over `T`, with isomorphisms over
`T`, as in Stacks 0E93. -/
abbrev ProperFlatOver :=
  SpacesOverSpace.SpacesOver B integerBase (hZ B)
    (SpacesOverSpace.properFlatProperty B integerBase (hZ B)) T

/-- The total space of a family over `T`. -/
abbrev familyFunctor : ProperFlatOver B T ⥤ AlgebraicSpaces B integerBase (hZ B) :=
  ObjectProperty.ι _ ⋙ Core.inclusion _ ⋙ Over.forget T

/-- The modules on the total spaces of the families over `T`, with their inverse images. -/
abbrev familyModules :
    Pseudofunctor (LocallyDiscrete (ProperFlatOver B T)ᵒᵖ) Cat :=
  (familyFunctor B T).op.toPseudofunctor.comp (Space.modulesPseudofunctor B integerBase (hZ B))

/-- A module on an algebraic space `X` over `T` is a *polarization* of `X/T` when it is
invertible (Stacks 01CS) and ample on `X/T` (Stacks 0D31). -/
def IsPolarization {X : AlgebraicSpaces B integerBase (hZ B)} (x : X ⟶ T)
    (L : Space.Modules.{u, u} B integerBase (hZ B) X.1 X.2) : Prop :=
  Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase (hZ B) X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase (hZ B) X.1 X.2).O)).property L ∧
    Space.IsRelativelyAmple B integerBase (hZ B) x L

/-- The pairs `(X ⟶ T, L)` whose module is a polarization. -/
abbrev polarizationProperty : ObjectProperty (Pseudofunctor.CoGrothendieck (familyModules B T)) :=
  fun X => IsPolarization B T X.base.1.of.hom X.fiber

/-- **The left-hand category of Stacks 0E94**: pairs `(X ⟶ T, L)` of a finitely presented, flat
and proper morphism of algebraic spaces and an invertible module ample on `X/T`, with their
isomorphisms. -/
abbrev PolarizedSpacesOver := Core (polarizationProperty B T).FullSubcategory

end AlgebraicGeometry.PolarizedOverSpace

end
