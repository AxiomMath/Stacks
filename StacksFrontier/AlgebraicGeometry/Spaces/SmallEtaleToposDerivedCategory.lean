module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback

/-!
# `D(𝒪_X)` on the small étale ringed topos, and its bridge to `spaceDerivedCategory`

For an algebraic space `X` the derived category of `𝒪_X`-modules has two spellings in the
library, definitionally equal:

* `AlgebraicGeometry.Space.spaceDerivedCategory X`, on the modules
  `AlgebraicGeometry.Space.Modules X.1 X.2` over the ring sheaf of the small étale ringed
  *site*, which is the user-facing spelling of the statements about `D(𝒪_X)`;
* `AlgebraicGeometry.Space.smallEtaleToposDerivedCategory X`, on the sheaves of modules over
  `AlgebraicGeometry.Space.ringedToposStructureRingSheaf X`, the ring sheaf of the small étale
  ringed *topos*: the spelling the derived pullbacks, direct images, tensor products and base
  change maps of algebraic spaces are stated with.

Each crossing between the two spellings is checked cheaply on its own, but a term that crosses
them at many implicit positions can make definitional unfolding blow up. Lemmas about those
derived functors should therefore be stated in the topos spelling, and statements in the
user-facing spelling should cross to it only through the named identity functors of this file.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleToposDerivedCategory X`, with its abelian structure and model
  `toposModulesAbelian X`, `toposHasDerivedCategory X` as terms.
* `AlgebraicGeometry.Space.spaceToToposDerived X`, `AlgebraicGeometry.Space.toposToSpaceDerived X`:
  the identity functors between the two spellings.

## Main results

* `…spaceToToposDerived_obj`, `…spaceToToposDerived_map`, `…toposToSpaceDerived_obj`,
  `…toposToSpaceDerived_map`: they are the identity on objects and morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The abelian structure of the sheaves of modules over the ring sheaf of the small étale ringed
topos of `X`, as a term. -/
abbrev toposModulesAbelian (X : AlgebraicSpaces B S hS) :
    Abelian (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  SheafOfModules.instAbelian _

/-- The standard model of the derived category of those sheaves of modules, as a term. -/
abbrev toposHasDerivedCategory (X : AlgebraicSpaces B S hS) :
    @HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _
      (toposModulesAbelian X) :=
  @HasDerivedCategory.standard _ _ (toposModulesAbelian X)

/-- **`D(𝒪_X)` on the small étale ringed topos of `X`**, at the standard model: the derived
category of sheaves of modules over `AlgebraicGeometry.Space.ringedToposStructureRingSheaf X`. -/
abbrev smallEtaleToposDerivedCategory (X : AlgebraicSpaces B S hS) :=
  @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _
    (toposModulesAbelian X) (toposHasDerivedCategory X)

/-- The identity functor from the site spelling `spaceDerivedCategory X` to the topos spelling
`smallEtaleToposDerivedCategory X`. -/
def spaceToToposDerived (X : AlgebraicSpaces B S hS) :
    spaceDerivedCategory B S hS X ⥤ smallEtaleToposDerivedCategory X :=
  𝟭 _

/-- The identity functor from the topos spelling `smallEtaleToposDerivedCategory X` to the site
spelling `spaceDerivedCategory X`. -/
def toposToSpaceDerived (X : AlgebraicSpaces B S hS) :
    smallEtaleToposDerivedCategory X ⥤ spaceDerivedCategory B S hS X :=
  𝟭 _

/-- `spaceToToposDerived X` is the identity on objects. -/
@[simp]
theorem spaceToToposDerived_obj (X : AlgebraicSpaces B S hS) (E : spaceDerivedCategory B S hS X) :
    (spaceToToposDerived X).obj E = E :=
  rfl

/-- `spaceToToposDerived X` is the identity on morphisms. -/
@[simp]
theorem spaceToToposDerived_map (X : AlgebraicSpaces B S hS) {E E' : spaceDerivedCategory B S hS X}
    (φ : E ⟶ E') : (spaceToToposDerived X).map φ = φ :=
  rfl

/-- `toposToSpaceDerived X` is the identity on objects. -/
@[simp]
theorem toposToSpaceDerived_obj (X : AlgebraicSpaces B S hS)
    (E : smallEtaleToposDerivedCategory X) :
    (toposToSpaceDerived X).obj E = E :=
  rfl

/-- `toposToSpaceDerived X` is the identity on morphisms. -/
@[simp]
theorem toposToSpaceDerived_map (X : AlgebraicSpaces B S hS)
    {E E' : smallEtaleToposDerivedCategory X} (φ : E ⟶ E') : (toposToSpaceDerived X).map φ = φ :=
  rfl

end AlgebraicGeometry.Space

end
