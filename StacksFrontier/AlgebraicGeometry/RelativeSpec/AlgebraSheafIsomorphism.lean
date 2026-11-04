module

public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# Quasi-coherence of an algebra sheaf is invariant under isomorphism

Let `X` be a scheme.  An algebra sheaf `A : AlgebraSheaf X` is quasi-coherent when its
underlying `𝒪_X`-module `AlgebraSheaf.underlyingModule A` is, and that module is defined as the
restriction of scalars, along the structure morphism `𝒪_X ⟶ A`, of `A` viewed as a module over
itself.  Neither `AlgebraSheaf.underlyingModule` nor `AlgebraSheaf.IsQuasicoherent` comes with
any functoriality, so quasi-coherence could not be transported along an isomorphism of algebra
sheaves.  This file supplies that transport.

The ingredient that is missing from Mathlib is the comparison, for a morphism of sheaves of
rings `ε : R ⟶ R'`, between `R` as a module over itself and `R'` as a module over `R`; it is
constructed here as `SheafOfModules.unitRestrictScalarsMap`, and shown to be an isomorphism
when `ε` is.  This is a statement about an arbitrary site, not about schemes.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.unitRestrictScalarsMap` is the morphism of `R`-modules
  `R ⟶ ε_*(R')` attached to a morphism of sheaves of rings `ε : R ⟶ R'`, where `ε_*` denotes
  restriction of scalars, and `Stacks.RelativeSpec.AlgebraSheaf.unitRestrictScalarsIso` promotes
  it to an isomorphism when `ε` is one, with
  `Stacks.RelativeSpec.AlgebraSheaf.unitRestrictScalarsInv` for its inverse.  They live in this
  namespace rather than `SheafOfModules` because
  `StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech` already
  uses that namespace for the same construction in the generality of a map `A ⟶ B` of sheaves of
  rings over `R`, as `SheafOfModules.unitRestrictScalarsMapOfComp` with its lemmas
  `SheafOfModules.unitRestrictScalarsMap_congr`, `…_id` and `…_comp`, and two declarations of one
  fully-qualified name make the whole-library build fail.
* `Stacks.RelativeSpec.AlgebraSheaf.ringSheafIso` is the isomorphism of sheaves of rings
  underlying an isomorphism of algebra sheaves, the counterpart for isomorphisms of
  `Stacks.RelativeSpec.AlgebraSheaf.ringSheafMap`.
* `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso` is the isomorphism of `𝒪_X`-modules
  underlying an isomorphism of algebra sheaves.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.restrictScalars_unit_eq`: restricting the target of a
  morphism of algebra sheaves, viewed as a module over itself, along the two structure
  morphisms in turn gives the underlying module of the target.

Quasi-coherence is invariant under isomorphism of algebra sheaves by
`Stacks.RelativeSpec.AlgebraSheaf.isQuasicoherent_of_iso`, which is stated and proved in
`StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic`; the isomorphism of
underlying modules it needs is `Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso` below.

## Implementation notes

The components of `unitRestrictScalarsMap` are written with their source and target given as
`(unit R).val.obj U` and `((restrictScalars ε).obj (unit R')).val.obj U` rather than as
`ModuleCat.of _ _`: the module structure on the latter is the one induced by restriction of
scalars, and spelling the target as `ModuleCat.of _ (R'.obj.obj U)` leaves the scalar ring as a
metavariable, so that the `Module` instance needed by the `LinearMap` constructor cannot be
synthesized.

The two scalar conditions are the two ring axioms: `ε` is `R`-linear because it is
multiplicative, and `ε⁻¹` is `R`-linear because `ε⁻¹ ∘ ε` is the identity on sections.

`underlyingModuleIso` is assembled from `unitRestrictScalarsIso` by applying restriction of
scalars along the structure morphism of the source.  The transport that identifies the result
with the underlying module of the target is `restrictScalars_unit_eq`, which is
`structureMap_comp_ringSheafMap` transported by `congrArg`; this uses that restriction of
scalars along a composite is the composite of the restrictions, which holds definitionally
because the scalar action of `r` through `α ≫ β` is by definition the action of `β (α r)`.

## References

* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open SheafOfModules (unit restrictScalars)

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (ε : R ⟶ R')

/-- The morphism of `R`-modules from `R`, viewed as a module over itself, to `R'`, viewed as an
`R`-module by restriction of scalars along `ε : R ⟶ R'`.  On sections it is `ε` itself, which
is `R`-linear because it is multiplicative. -/
public noncomputable def unitRestrictScalarsMap :
    unit.{u} R ⟶ (restrictScalars.{u} ε).obj (unit.{u} R') where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := (unit.{u} R).val.obj U)
        (Y := ((restrictScalars.{u} ε).obj (unit.{u} R')).val.obj U)
        { toFun := (ε.hom.app U).hom
          map_add' := map_add _
          map_smul' := fun r x => (ε.hom.app U).hom.map_mul r x }
      naturality := fun {U V} f => ModuleCat.hom_ext (LinearMap.ext fun x =>
        congrArg (fun k : R.obj.obj U ⟶ R'.obj.obj V => k.hom x) (ε.hom.naturality f)) }

/-- The inverse of `unitRestrictScalarsMap` for an isomorphism `ε : R ≅ R'` of sheaves of
rings.  On sections it is `ε⁻¹`, which is `R`-linear because `ε⁻¹ (ε r · x) = r · ε⁻¹ x`. -/
public noncomputable def unitRestrictScalarsInv (ε : R ≅ R') :
    (restrictScalars.{u} ε.hom).obj (unit.{u} R') ⟶ unit.{u} R where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := ((restrictScalars.{u} ε.hom).obj (unit.{u} R')).val.obj U)
        (Y := (unit.{u} R).val.obj U)
        { toFun := (ε.inv.hom.app U).hom
          map_add' := map_add _
          map_smul' := fun r x => Eq.trans ((ε.inv.hom.app U).hom.map_mul _ x)
            (congrArg (fun k : R.obj.obj U => k * (ε.inv.hom.app U).hom x)
              (congrArg (fun k : R ⟶ R => (k.hom.app U).hom r) ε.hom_inv_id)) }
      naturality := fun {U V} f => ModuleCat.hom_ext (LinearMap.ext fun x =>
        congrArg (fun k : R'.obj.obj U ⟶ R.obj.obj V => k.hom x) (ε.inv.hom.naturality f)) }

/-- For an isomorphism `ε : R ≅ R'` of sheaves of rings, `R` as a module over itself is
isomorphic to `R'` with its `R`-module structure obtained by restricting scalars along `ε`. -/
public noncomputable def unitRestrictScalarsIso (ε : R ≅ R') :
    unit.{u} R ≅ (restrictScalars.{u} ε.hom).obj (unit.{u} R') where
  hom := unitRestrictScalarsMap ε.hom
  inv := unitRestrictScalarsInv ε
  hom_inv_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      congrArg (fun k : R ⟶ R => (k.hom.app U).hom x) ε.hom_inv_id))
  inv_hom_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      congrArg (fun k : R' ⟶ R' => (k.hom.app U).hom x) ε.inv_hom_id))

variable {X : Scheme.{u}}

/-- The isomorphism of sheaves of rings underlying an isomorphism of algebra sheaves. -/
public noncomputable def ringSheafIso {A A' : AlgebraSheaf X} (e : A ≅ A') :
    ringSheaf A ≅ ringSheaf A' :=
  (sheafCompose (_root_.Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).mapIso ((Under.forget X.sheaf).mapIso e)

/-- Restricting scalars along the structure morphism of `A` of the target of a morphism
`u : A ⟶ A'`, viewed as a module over `A` through `u`, gives the underlying module of `A'`. -/
public theorem restrictScalars_unit_eq {A A' : AlgebraSheaf X} (u : A ⟶ A') :
    (SheafOfModules.restrictScalars (structureMap A)).obj
        ((SheafOfModules.restrictScalars (ringSheafMap u)).obj
          (SheafOfModules.unit (ringSheaf A'))) = underlyingModule A' :=
  congrArg (fun α : X.ringCatSheaf ⟶ ringSheaf A' =>
    (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit (ringSheaf A')))
    (structureMap_comp_ringSheafMap u)

/-- The isomorphism of `𝒪_X`-modules underlying an isomorphism of algebra sheaves. -/
public noncomputable def underlyingModuleIso {A A' : AlgebraSheaf X} (e : A ≅ A') :
    underlyingModule A ≅ underlyingModule A' :=
  (SheafOfModules.restrictScalars (structureMap A)).mapIso
      (unitRestrictScalarsIso (ringSheafIso e)) ≪≫
    eqToIso (restrictScalars_unit_eq e.hom)

end Stacks.RelativeSpec.AlgebraSheaf

end
