module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# The module underlying an algebra sheaf on an algebraic space, by restriction of scalars

Let `A` be a sheaf of commutative `𝒪_F`-algebras on the small étale site of an algebraic space
`F`.  `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` builds the `𝒪_F`-module underlying
`A` by hand, from the sectionwise structure-algebra maps.  This file identifies it with the
sheaf of rings `A` regarded as a module over itself and restricted along the structure morphism.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.ringSheafOfSite`: the sheaf of not necessarily
  commutative rings underlying an algebra sheaf.
* `AlgebraicGeometry.Space.AlgebraSheaf.structureMapOfSite`: its structure morphism, as a
  morphism of sheaves of rings out of the structure sheaf of `F`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars`: **the module
  underlying an algebra sheaf is the restriction of scalars along its structure morphism of the
  free module of rank one over its own sheaf of rings.**

## Implementation notes

The identification is an equality, holding by `rfl`. Only the single-universe case is stated, the
structure morphism of an algebra sheaf being a morphism of sheaves of rings only when the algebra
sections and the schemes live in the same universe.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space.AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The sheaf of not necessarily commutative rings underlying an algebra sheaf on the small
étale site of an algebraic space: its sheaf of commutative rings with commutativity forgotten. -/
abbrev ringSheafOfSite (A : AlgebraSheaf.{u, m} B S hS F hF) :
    Sheaf (SmallEtale.topology B S hS F) RingCat.{m} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf A.right)

/-- The structure morphism of an algebra sheaf, as a morphism of sheaves of rings out of the
structure sheaf of the algebraic space. -/
def structureMapOfSite (A : AlgebraSheaf.{u, u} B S hS F hF) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⟶
      ringSheafOfSite A :=
  (@sheafCompose _ _ _ _ _ _ (smallEtaleRingedSite B S hS F hF).J
    (forget₂ CommRingCat.{u} RingCat.{u})
    (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat).map A.hom

/-- Restriction of scalars along the structure morphism of an algebra sheaf, from its own
sheaves of modules to the `𝒪_F`-modules of the algebraic space. -/
abbrev restrictScalarsStructureMap (A : AlgebraSheaf.{u, u} B S hS F hF) :
    SheafOfModules.{u} (ringSheafOfSite A) ⥤ Modules.{u, u} B S hS F hF :=
  SheafOfModules.restrictScalars (structureMapOfSite A)

/-- **The module underlying an algebra sheaf is the restriction of scalars along its structure
morphism of the free module of rank one over its own sheaf of rings.** -/
theorem underlyingModule_eq_restrictScalars (A : AlgebraSheaf.{u, u} B S hS F hF) :
    A.underlyingModule =
      (restrictScalarsStructureMap A).obj (SheafOfModules.unit (ringSheafOfSite A)) :=
  rfl

end AlgebraicGeometry.Space.AlgebraSheaf

end
