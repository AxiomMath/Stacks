module

public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Virtual normal bundles of an immersion

Let `i : Z ⟶ X` be an immersion of schemes. A *virtual normal bundle* for `i` is a finite
locally free `𝒪_Z`-module `𝒩` together with a surjection `𝒩^∨ ⟶ 𝒞_{Z/X}` onto the conormal
sheaf of `i`. Here the dual is `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf` and the
conormal sheaf is `Stacks.Thickenings.immersionConormalSheaf`. When `i` is a regular immersion
the conormal sheaf is itself finite locally free and its dual is the normal bundle.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle`: a virtual normal bundle for an immersion.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- A *virtual normal bundle* for an immersion `i : Z ⟶ X`: a finite locally free `𝒪_Z`-module
together with a surjection from its dual onto the conormal sheaf `𝒞_{Z/X}` of `i`. -/
@[stacks 0FBQ "(2): a virtual normal bundle for an immersion"]
structure VirtualNormalBundle {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] where
  /-- The finite locally free module `𝒩` on the source of the immersion. -/
  bundle : Z.Modules
  /-- `𝒩` is finite locally free. -/
  [isFiniteLocallyFree : SheafOfModules.IsFiniteLocallyFree.{u, u, u} bundle]
  /-- The map `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` onto the conormal sheaf. -/
  surjection :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf bundle ⟶
      Stacks.Thickenings.immersionConormalSheaf i
  /-- `σ` is surjective. -/
  [epi : Epi surjection]

attribute [instance] VirtualNormalBundle.isFiniteLocallyFree VirtualNormalBundle.epi

end Stacks.Chow

end
