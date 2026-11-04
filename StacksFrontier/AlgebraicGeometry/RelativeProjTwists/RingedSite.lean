module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Ringed sites, and the ringed site of a scheme

A *ringed site* is a site together with a sheaf of commutative rings on it. This file defines
that notion, the underlying sheaf of (not necessarily commutative) rings over which sheaves of
modules on it are taken, and the ringed site attached to a scheme: the site of its open subsets
with the Zariski topology and its structure sheaf. The sheaf of rings of the ringed site of a
scheme `X` is `AlgebraicGeometry.Scheme.ringCatSheaf` on the nose, so sheaves of modules on it are
objects of `X.Modules`.

## Main definitions

* `Stacks.CategoryTheory.RingedSite`: a site with a sheaf of commutative rings.
* `Stacks.CategoryTheory.RingedSite.ringSheaf`: its structure sheaf with commutativity
  forgotten, over which sheaves of modules on it are indexed.
* `Stacks.CategoryTheory.RingedSite.ofScheme`: the ringed site of a scheme.

## Main results

* `Stacks.CategoryTheory.RingedSite.ringSheaf_ofScheme`: the sheaf of rings of the ringed site
  of a scheme is `AlgebraicGeometry.Scheme.ringCatSheaf`, by `rfl`.
* `Stacks.CategoryTheory.RingedSite.modulesEq_ofScheme`: consequently the type of sheaves of
  modules on the ringed site of `X` is the type `X.Modules`, again by `rfl`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory

universe u v w

/-- A ringed site: a category with a Grothendieck topology and a sheaf of commutative rings. -/
@[sga "4 IV 11.1.1" "special case"]
public structure RingedSite where
  /-- The underlying category. -/
  C : Type u
  [category : Category.{v} C]
  /-- The Grothendieck topology on the underlying category. -/
  J : GrothendieckTopology C
  /-- The structure sheaf. -/
  O : Sheaf J CommRingCat.{w}

attribute [instance] RingedSite.category

namespace RingedSite

/-- The structure sheaf of a ringed site with commutativity forgotten, the sheaf of rings over
which sheaves of modules on the ringed site are indexed. -/
public abbrev ringSheaf (X : RingedSite.{u, v, w}) : Sheaf X.J RingCat.{w} := by
  let : PreservesLimitsOfSize.{v, max u v}
      (forget₂ CommRingCat.{w} RingCat.{w}) := {
    preservesLimitsOfShape := fun {J} _ ↦ {
      preservesLimit := fun {F} ↦ {
        preserves := fun {c} hc ↦ by
          have : HasLimit (F ⋙ forget CommRingCat.{w}) :=
            ⟨_, isLimitOfPreserves (forget CommRingCat.{w}) hc⟩
          have : Small.{w} (F ⋙ forget CommRingCat.{w}).sections :=
            (Types.hasLimit_iff_small_sections _).mp inferInstance
          have : Small.{w} ((F ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⋙
              forget RingCat.{w}).sections := ‹Small.{w} (F ⋙ forget CommRingCat.{w}).sections›
          exact (preservesLimit_of_createsLimit_and_hasLimit F
            (forget₂ CommRingCat.{w} RingCat.{w})).preserves hc } } }
  let : X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
    hasSheafCompose_of_preservesLimitsOfSize X.J
  exact (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O

/-- The ringed site of a scheme: the site of its open subsets with the Zariski topology,
carrying its structure sheaf. -/
public abbrev ofScheme (X : AlgebraicGeometry.Scheme.{u}) : RingedSite.{u, u, u} where
  C := X.Opens
  J := Opens.grothendieckTopology X
  O := X.sheaf

/-- The sheaf of rings of the ringed site of a scheme is the scheme's own `ringCatSheaf`. -/
public theorem ringSheaf_ofScheme (X : AlgebraicGeometry.Scheme.{u}) :
    (ofScheme X).ringSheaf = X.ringCatSheaf := rfl

/-- Sheaves of modules on the ringed site of a scheme are exactly the scheme's sheaves of
modules. -/
public theorem modulesEq_ofScheme (X : AlgebraicGeometry.Scheme.{u}) :
    SheafOfModules.{u} (ofScheme X).ringSheaf = X.Modules := rfl

end RingedSite

end Stacks.CategoryTheory

end
