module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk.ModuleStalk
public import Mathlib.Topology.Sheaves.CommRingCat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsComparisonMap

/-!
# Sheafification of a presheaf of modules does not change the stalks

Let `O` be a sheaf of commutative rings on a topological space and let `P` be a presheaf of
`O`-modules. Sheafifying `P` gives a sheaf of `O`-modules together with a canonical morphism
`P ⟶ P^#`, and this file records that the induced map on stalks is a linear isomorphism: the
underlying map of abelian groups is the stalk map of the sheafification unit, which is an
isomorphism because sheafification is computed stalkwise.

## Main definitions

* `Stacks.ModuleStalk.ringSheafOn`: the sheaf of rings underlying a sheaf of commutative rings,
  together with the instance `Stacks.ModuleStalk.moduleStalkSheafOfModules` giving the module
  structure on the stalks of a sheaf of modules over it.
* `Stacks.ModuleStalk.sheafifyModules`: the sheafification of a presheaf of `O`-modules.
* `Stacks.ModuleStalk.toSheafifyModules`: the canonical morphism to it.
* `Stacks.ModuleStalk.sheafifyModulesStalkEquiv`: the induced linear equivalence of stalks.

## Main results

* `Stacks.ModuleStalk.bijective_stalkMap_toSheafifyModules`: the map induced on stalks by the
  sheafification unit is bijective.

## Implementation notes

The sheafification used is Mathlib's `PresheafOfModules.sheafification` at the identity of the
underlying presheaf of rings, which is the form taken by the library's extension-of-scalars
functor for sheaves of modules. Its underlying presheaf of abelian groups is, by definition, the
sheafification of the underlying presheaf of abelian groups of `P`, and the morphism to it is
`CategoryTheory.toSheafify`; the two statements of this file are those two facts combined with
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.ModuleStalk

variable {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)
  (P : PresheafOfModules.{u} (O.presheaf ⋙ forget₂ CommRingCat RingCat))

/-- The sheaf of rings underlying a sheaf of commutative rings on a topological space. This is
`Stacks.Sheaves.Differentials.ringSheaf` with the site arguments supplied, which is needed: left to
  instance
search they are metavariables and the `GrothendieckTopology.HasSheafCompose` instance is not
found. -/
abbrev ringSheafOn : TopCat.Sheaf RingCat.{u} X :=
  Stacks.Sheaves.Differentials.ringSheaf (C := Opens X) (J := Opens.grothendieckTopology X) O

/-- The stalk of a sheaf of `O`-modules is a module over the stalk of `O`. Instance search does
not find this on its own: a `SheafOfModules (ringSheafOn O)` is indexed by `(ringSheafOn O).obj`,
which search does not reduce to the form `O.presheaf ⋙ forget₂ CommRingCat RingCat` that
Mathlib's instance is stated for. -/
instance moduleStalkSheafOfModules (G : SheafOfModules.{u} (ringSheafOn O)) (x : X) :
    Module ↑(O.presheaf.stalk x) ↑((presheafOn G.val).stalk x) :=
  moduleStalk (O := O.presheaf) G.val x

/-- The sheafification of a presheaf of `O`-modules, as a sheaf of modules over the sheaf of
rings underlying `O`. -/
abbrev sheafifyModules : SheafOfModules.{u} (ringSheafOn O) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheafOn O).obj)).obj P

/-- The canonical morphism from a presheaf of `O`-modules to its sheafification. -/
def toSheafifyModules :
    P ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheafOn O).obj)).obj
      (sheafifyModules O P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOn O).obj)).unit.app P

/-- The map induced on stalks by the sheafification unit of a presheaf of modules is bijective:
sheafification does not change stalks. -/
theorem bijective_stalkMap_toSheafifyModules (x : X) :
    Function.Bijective (stalkMap (toSheafifyModules O P) x) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.presheaf
  exact ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))

/-- Sheafification of a presheaf of modules does not change the stalks: the sheafification unit
induces a linear isomorphism on the stalk at every point. -/
def sheafifyModulesStalkEquiv (x : X) :
    ↑((presheafOn P).stalk x) ≃ₗ[O.presheaf.stalk x]
      ↑((presheafOn (sheafifyModules O P).val).stalk x) :=
  LinearEquiv.ofBijective (stalkMap (toSheafifyModules O P) x)
    (bijective_stalkMap_toSheafifyModules O P x)

/-- The stalk isomorphism of a sheafification sends the germ of a section to the germ of its
image. -/
theorem sheafifyModulesStalkEquiv_germ (x : X) (W : Opens X) (hx : x ∈ W)
    (m : ↑(P.obj (op W))) :
    sheafifyModulesStalkEquiv O P x (germ P W x hx m) =
      germ (sheafifyModules O P).val W x hx
        (((toSheafifyModules O P).app (op W)).hom m) :=
  stalkMap_germ (toSheafifyModules O P) x W hx m

end Stacks.ModuleStalk

end
