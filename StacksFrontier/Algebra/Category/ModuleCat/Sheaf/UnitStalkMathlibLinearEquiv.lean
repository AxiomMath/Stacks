module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearEquiv

/-!
# The stalk of the structure sheaf as a module over itself, at Mathlib's stalk module structure

The stalk at `x` of the structure sheaf of a ringed space `X`, viewed as a sheaf of modules over
itself, is free of rank one over the local ring `𝒪_{X,x}`.  That is
`Stacks.SheafOfModules.unitStalkLinearEquiv`, and it is stated for the `𝒪_{X,x}`-module
structure `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, which is built from germ
representatives.

A statement about a stalk whose `Module` instance came from instance search instead carries
Mathlib's `PresheafOfModules` stalk module structure,
`Stacks.SheafOfModules.FlatShortExact.stalkModule`.  The two structures are equal
(`Stacks.SheafOfModules.stalkModule_eq`) but not definitionally so; this module transports the
rank-one equivalence along that equality.

## Main definitions

* `Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquiv`: `(𝒪_X)_x ≃ₗ 𝒪_{X,x}` at
  Mathlib's stalk module structure, for a ringed space.
* `Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquivScheme`: the same for a scheme and
  its `AlgebraicGeometry.Scheme.ringCatSheaf`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.SheafOfModules.FlatShortExact

/-- A linear equivalence transported along an equality of `Module` structures on its source. -/
def linearEquivOfInstanceEq {R M N : Type u} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R N] {i₁ i₂ : Module R M} (h : i₁ = i₂)
    (e : @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ M N _ _ i₁ _) :
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ M N _ _ i₂ _ :=
  h ▸ e

/-- **The stalk of the structure sheaf of a ringed space, as a module over itself, is free of
rank one**, at Mathlib's `PresheafOfModules` stalk module structure.

This is `Stacks.SheafOfModules.unitStalkLinearEquiv` carried across the equality of module
structures `Stacks.SheafOfModules.stalkModule_eq`. -/
noncomputable def unitAbStalkLinearEquiv {X : RingedSpace.{u, u}} (x : X.carrier) :
    letI := stalkModule (_root_.SheafOfModules.unit (structureSheafRing X)) x
    abStalk (_root_.SheafOfModules.unit (structureSheafRing X)) x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x :=
  linearEquivOfInstanceEq
    (Stacks.SheafOfModules.stalkModule_eq X
      (_root_.SheafOfModules.unit (structureSheafRing X)).val x)
    (Stacks.SheafOfModules.unitStalkLinearEquiv X x).symm

/-- **The stalk of the structure sheaf of a scheme, as a module over itself, is free of rank
one**, at Mathlib's `PresheafOfModules` stalk module structure and at the spelling
`AlgebraicGeometry.Scheme.ringCatSheaf` of the structure sheaf of rings. -/
noncomputable def unitAbStalkLinearEquivScheme (X : Scheme.{u}) (x : X) :
    letI := stalkModule (X := X.toRingedSpace) (_root_.SheafOfModules.unit X.ringCatSheaf) x
    abStalk (X := X.toRingedSpace) (_root_.SheafOfModules.unit X.ringCatSheaf) x
        ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  unitAbStalkLinearEquiv (X := X.toRingedSpace) x

end Stacks.SheafOfModules.FlatShortExact

end
