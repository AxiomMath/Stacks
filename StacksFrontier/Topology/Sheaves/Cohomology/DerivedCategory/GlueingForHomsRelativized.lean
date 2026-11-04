module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumFromGlueingAtTheOverlap

/-!
# An object given over an open is the restriction of one given over the whole space

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67. An object `K : OpenDerivedCategory X O` given over an open
`O` extends by zero along `O` to a sheaf of modules on `X`, and the restriction of that extension
to any open `W ≤ O` — read in the open-subspace model — is the object's own restriction from `O`
to `W`. The comparison is the counit of extension by zero along `⊤`, which is invertible by
[Stacks, Tag 00AB].

Taking `W = O` gives the statement of the title: every object over `O` is isomorphic to the
restriction from `⊤` of an object over `⊤`, namely of its own extension by zero read in the
`⊤`-model.

## Main definitions

* `Stacks.DerivedGlueing.extendToTop`: extension by zero along `O`, read in the open-subspace
  model of the whole space — the functor from modules over `O` to modules over `⊤`.
* `Stacks.DerivedGlueing.extendToTopRestrictionIso`: its restriction to `W ≤ O` is restriction
  from `O` to `W`, as an isomorphism of functors on modules.
* `Stacks.DerivedGlueing.derivedExtendToTopRestrictionIso`: the same, on derived categories and
  in the system's own displayed restriction.

## Main results

* `Stacks.DerivedGlueing.derivedExtendToTopSelfIso`: the restriction from `⊤` to `O` of the
  extension of an object over `O` is that object.
* `Stacks.DerivedGlueing.exists_restriction_top_iso`: every object over `O` is the restriction
  from `⊤` of an object over `⊤`, up to isomorphism.

## Implementation notes

`Stacks.DerivedGlueing.openModuleRestriction_eq` and
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension` compare the restrictions of an
object over `O` with the restrictions of its extension by zero read on the *slice site* over `W`,
through `Stacks.DerivedGlueing.sliceToSubspace`.  The comparison here stays in the open-subspace
model throughout and therefore needs no passage between the two models: both sides are values of
`Stacks.DerivedGlueing.openModuleRestriction`, which is extension by zero followed by restriction
by definition, so the whole content is the invertibility of the counit at `⊤`.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### Extension by zero, read in the open-subspace model of the whole space -/

/-- **Extension by zero along `O`, read in the open-subspace model of `⊤`.** A module given over
the open `O` is extended by zero to the whole of `X` and the result is read as a module over the
open subspace `⊤`.  Composed with restriction from `⊤` to an open `W ≤ O` it is restriction from
`O` to `W`, by `Stacks.DerivedGlueing.extendToTopRestrictionIso`. -/
abbrev extendToTop (O : Opens X.carrier) :
    SheafOfModules.{u} (restrictedRingSheaf X O) ⥤
      SheafOfModules.{u} (restrictedRingSheaf X ⊤) :=
  jShriek O (underlyingRingSheaf X) ⋙ jStar (⊤ : Opens X.carrier) (underlyingRingSheaf X)

/-- **The restriction to `W ≤ O` of the extension of a module over `O` is its restriction from
`O`.** Restriction from `U` to `W` is by definition extension by zero along `U` followed by
restriction to `W`, so both sides are `j_!^O` followed by `j^{*W}`, the left-hand side with the
composite `j^{*⊤} j_!^⊤` inserted in the middle.  That composite is the counit of the adjunction
at `⊤`, which is invertible, `Stacks.DerivedGlueing.jStarTopCompJShriekTopIso`. -/
def extendToTopRestrictionIso (O W : Opens X.carrier) (hWO : W ≤ O) :
    extendToTop O ⋙ openModuleRestriction X W ⊤ le_top ≅
      openModuleRestriction X W O hWO :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (jShriek O (underlyingRingSheaf X))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (jStarTopCompJShriekTopIso (underlyingRingSheaf X))
          (jStar W (underlyingRingSheaf X)) ≪≫
        Functor.leftUnitor _)

/-- **The restriction to `O` of the extension of a module over `O` is that module.**
`Stacks.DerivedGlueing.extendToTopRestrictionIso` at `W = O`, followed by
`Stacks.DerivedGlueing.openModuleRestrictionSelfIso`. -/
def extendToTopSelfIso (O : Opens X.carrier) :
    extendToTop O ⋙ openModuleRestriction X O ⊤ le_top ≅
      𝟭 (SheafOfModules.{u} (restrictedRingSheaf X O)) :=
  extendToTopRestrictionIso O O le_rfl ≪≫ openModuleRestrictionSelfIso X O le_rfl

/-! ### The same on derived categories -/

/-- Extension by zero along an open, read in the open-subspace model of `⊤`, is additive. -/
instance extendToTop_additive (O : Opens X.carrier) : (extendToTop (X := X) O).Additive :=
  inferInstance

/-- **The displayed restriction to `W ≤ O` of the extension of an object over `O` is its
displayed restriction from `O`.** The functor-level isomorphism
`Stacks.DerivedGlueing.extendToTopRestrictionIso`, carried to derived categories and read in the
system's own displayed restriction through
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`. -/
def derivedExtendToTopRestrictionIso (S : LocallyGiven X) (O W : Opens X.carrier)
    (hWO : W ≤ O) :
    (extendToTop O).mapDerivedCategory ⋙ S.restriction W ⊤ le_top ≅
      S.restriction W O hWO :=
  Functor.isoWhiskerLeft (extendToTop O).mapDerivedCategory
      (restrictionIsoMapDerivedCategory S W ⊤ le_top) ≪≫
    mapDerivedCategoryCompIso (extendToTop O) (openModuleRestriction X W ⊤ le_top) ≪≫
    mapDerivedCategoryCongr (extendToTopRestrictionIso O W hWO) ≪≫
    (restrictionIsoMapDerivedCategory S W O hWO).symm

/-- **The displayed restriction from `⊤` to `O` of the extension of an object over `O` is that
object.** `Stacks.DerivedGlueing.derivedExtendToTopRestrictionIso` at `W = O`, followed by
`Stacks.DerivedGlueing.restrictionSelfIso`. -/
def derivedExtendToTopSelfIso (S : LocallyGiven X) (O : Opens X.carrier) :
    (extendToTop O).mapDerivedCategory ⋙ S.restriction O ⊤ le_top ≅
      𝟭 (OpenDerivedCategory X O) :=
  derivedExtendToTopRestrictionIso S O O le_rfl ≪≫ restrictionSelfIso S O le_rfl

/-- **Every object given over an open is the restriction from the whole space of an object given
over the whole space.** The witness is the object's own extension by zero along `O`, read in the
open-subspace model of `⊤`. -/
theorem exists_restriction_top_iso (S : LocallyGiven X) (O : Opens X.carrier)
    (K : OpenDerivedCategory X O) :
    ∃ K' : OpenDerivedCategory X ⊤,
      Nonempty ((S.restriction O ⊤ le_top).obj K' ≅ K) :=
  ⟨(extendToTop O).mapDerivedCategory.obj K, ⟨(derivedExtendToTopSelfIso S O).app K⟩⟩

end Stacks.DerivedGlueing

end
