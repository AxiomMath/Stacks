module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage

/-!
# Modules of an algebraic space in the two spellings, and the derived functors between them

For an algebraic space `X`, the identity functor from `AlgebraicGeometry.Space.Modules X.1 X.2`
(the site spelling) to the sheaves of modules over
`AlgebraicGeometry.Space.ringedToposStructureRingSheaf X` (the topos spelling), and the identity
isomorphisms identifying `M[0]` and `Rf_*` in the two spellings.

## Main definitions

* `AlgebraicGeometry.Space.spaceToToposModules`: the identity from `Modules X.1 X.2` to the
  sheaves of modules over `ringedToposStructureRingSheaf X`.
* `AlgebraicGeometry.Space.singleSpaceToToposIso`: `M[0]` in the two spellings.
* `AlgebraicGeometry.Space.derivedPushforwardSpaceToToposIso`: `Rf_*` in the two spellings.

## Main results

* `AlgebraicGeometry.Space.singleSpaceToToposIso_hom_app`,
  `AlgebraicGeometry.Space.singleSpaceToToposIso_inv_app`: the components of
  `singleSpaceToToposIso` are identities.
* `AlgebraicGeometry.Space.derivedPushforwardSpaceToToposIso_hom_app`,
  `AlgebraicGeometry.Space.derivedPushforwardSpaceToToposIso_inv_app`: the components of
  `derivedPushforwardSpaceToToposIso` are identities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The identity functor from the site spelling `Modules X.1 X.2` to the topos spelling. -/
def spaceToToposModules (X : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
  𝟭 _

/-- `spaceToToposModules X` sends a module `M` to itself. -/
@[simp]
theorem spaceToToposModules_obj (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2) :
    (spaceToToposModules X).obj M = M :=
  rfl

/-- `spaceToToposModules X` sends a morphism `g` to itself. -/
@[simp]
theorem spaceToToposModules_map (X : AlgebraicSpaces B S hS) {M M' : Modules.{u, u} B S hS X.1 X.2}
    (g : M ⟶ M') : (spaceToToposModules X).map g = g :=
  rfl

/-- `M[0]` in the two spellings. -/
def singleSpaceToToposIso (X : AlgebraicSpaces B S hS) :
    spaceDerivedSingle B S hS X 0 ⋙ spaceToToposDerived X ≅
      spaceToToposModules X ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0 :=
  Iso.refl _

/-- `Rf_*` in the two spellings. -/
def derivedPushforwardSpaceToToposIso (f : X ⟶ Y) :
    derivedModulePushforward B S hS f ⋙ spaceToToposDerived Y ≅
      spaceToToposDerived X ⋙ derivedPushforward (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) :=
  Iso.refl _


/-- The components of the forward map of `singleSpaceToToposIso X` are identities. -/
@[simp]
theorem singleSpaceToToposIso_hom_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (singleSpaceToToposIso X).hom.app M = 𝟙 _ :=
  rfl

/-- The components of the inverse map of `singleSpaceToToposIso X` are identities. -/
@[simp]
theorem singleSpaceToToposIso_inv_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (singleSpaceToToposIso X).inv.app M = 𝟙 _ :=
  rfl

/-- The components of the forward map of `derivedPushforwardSpaceToToposIso f` are identities. -/
@[simp]
theorem derivedPushforwardSpaceToToposIso_hom_app (f : X ⟶ Y) (K : spaceDerivedCategory B S hS X) :
    (derivedPushforwardSpaceToToposIso f).hom.app K = 𝟙 _ :=
  rfl

/-- The components of the inverse map of `derivedPushforwardSpaceToToposIso f` are identities. -/
@[simp]
theorem derivedPushforwardSpaceToToposIso_inv_app (f : X ⟶ Y) (K : spaceDerivedCategory B S hS X) :
    (derivedPushforwardSpaceToToposIso f).inv.app K = 𝟙 _ :=
  rfl

end AlgebraicGeometry.Space
