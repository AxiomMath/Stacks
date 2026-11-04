module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SubsingletonSpaceModuleEquivalence
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedIsomorphismTransport

/-!
# The derived category of a ringed space with at most one point

Let `(Z, 𝒪_Z)` be a ringed space whose underlying space has at most one point.  Sections on the
whole space are an equivalence of abelian categories
(`Stacks.Cohomology.SubsingletonSections.subsingletonSectionsEquivalence`), hence exact, so they
lift to an equivalence of unbounded derived categories

`D(Mod(Γ(Z, 𝒪_Z))) ≌ D(Mod(𝒪_Z))`.

Applied to the one-point ringed space `({x}, 𝒪_X|_{\{x\}})` on a point of a ringed space `X`,
whose sections ring is `𝒪_{X,x}` by
`Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso`, this is the
identification

`D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))`

that the proof of [Stacks, Tag 0G02] uses to move a comparison performed over the local ring onto
the one-point space, where
`Stacks.Cohomology.SupportedComplexes.isoOfDerivedSupportedSectionsIso` turns it into a global
isomorphism.  Its quasi-inverse direction is what that transport consumes: an isomorphism of
complexes of `𝒪_{X,x}`-modules between the two sides' images is reflected back to an isomorphism
on the one-point space, by `Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIso`.

## Main definitions

* `Stacks.Cohomology.SubsingletonSections.subsingletonDerivedEquivalence`: the derived lift
  `D(Mod(Γ(Z, 𝒪_Z))) ≌ D(Mod(𝒪_Z))` on a space with at most one point.
* `Stacks.Cohomology.SupportedComplexes.pointBaseRingEquiv`: the sections ring of the one-point
  space on `x`, as a ring, is `𝒪_{X,x}`.
* `Stacks.Cohomology.SupportedComplexes.stalkModuleEquivalence`:
  `Mod(𝒪_{X,x}) ≌ Mod(𝒪_X|_{\{x\}})`.
* `Stacks.Cohomology.SupportedComplexes.stalkModuleDerivedEquivalence`: **the derived
  identification** `D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))`.
* `Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIso`: the isomorphism on the
  one-point space produced from an isomorphism of the images in `D(Mod(𝒪_{X,x}))`.
* `Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIsoOfSupported`: **the transport
  end to end** — a comparison over `𝒪_{X,x}` of two complexes supported at a closed point `x` is
  an isomorphism of those complexes on `X`.

## Implementation notes

The derived lift is `Dualizing.mapDerivedCategoryEquivalenceOfEquivalence`, which asks for both
functors of the abelian equivalence to be additive and exact.  Exactness is free — a functor with
both adjoints preserves all limits and colimits — and additivity follows from preservation of
binary products, as for
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` — on both halves, the
`Additive` instance already registered for
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` not being found through the
quasi-inverse's definition.

The ring is carried by `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` along the ring
isomorphism `Γ({x}, 𝒪_X|_{\{x\}}) ≅ 𝒪_{X,x}`, which is
`Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso` read as a `RingEquiv`.
The stalk here is the `CommRingCat`-valued stalk of the structure sheaf of `X`, the spelling
`AlgebraicGeometry.RingedSpace.inverseImageStalkIso` and the ringed-space stalk maps are written
in; the `RingCat`-valued stalk that the stalk functor on sheaves of modules produces is a
different object, and no comparison of the two is made here.

The reflection statement is phrased with the two objects of `D(Mod(𝒪_X|_{\{x\}}))` given and the
isomorphism between their images supplied, rather than as a bare isomorphism of complexes of
`𝒪_{X,x}`-modules: an isomorphism between arbitrary objects of `D(Mod(𝒪_{X,x}))` says nothing
about any particular pair upstairs, and it is the pair
`R𝓗_{\{x\}}(K), R𝓗_{\{x\}}(L)` that
`Stacks.Cohomology.SupportedComplexes.isoOfDerivedSupportedSectionsIso` demands.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.SubsingletonSections

attribute [local instance] HasDerivedCategory.standard

variable (Z : RingedSpace.{u, u}) [Subsingleton Z.carrier]

/-- The identification of modules over the global functions with modules on a space with at most
one point is additive, being one half of an equivalence of additive categories. -/
public instance subsingletonSectionsEquivalence_functor_additive :
    (subsingletonSectionsEquivalence Z).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Its quasi-inverse — sections on the whole space, on the nose — is additive for the same
reason. -/
public instance subsingletonSectionsEquivalence_inverse_additive :
    (subsingletonSectionsEquivalence Z).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The derived lift of the identification on a space with at most one point**:

`D(Mod(Γ(Z, 𝒪_Z))) ≌ D(Mod(𝒪_Z))`.

Both functors of
`Stacks.Cohomology.SubsingletonSections.subsingletonSectionsEquivalence` are exact, being halves
of an equivalence of abelian categories, so the equivalence descends to unbounded derived
categories. -/
public def subsingletonDerivedEquivalence :
    DerivedCategory (ModuleCat.{u} (baseRing Z)) ≌
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (subsingletonSectionsEquivalence Z)

end Stacks.Cohomology.SubsingletonSections

/-! ### The one-point space at a point of a ringed space -/

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (x : X.carrier)

/-- **The sections ring of the one-point ringed space on `x` is the local ring `𝒪_{X,x}`**, as a
ring isomorphism: this is
`Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso` read as a `RingEquiv`. -/
public def pointBaseRingEquiv :
    baseRing (closedSubsetRingedSpace X ({x} : Set X.carrier)) ≃+* X.presheaf.stalk x :=
  (sectionsAtPointStructureSheafIso X x).commRingCatIsoToRingEquiv

/-- **Modules on the one-point ringed space on `x` are `𝒪_{X,x}`-modules**:

`Mod(𝒪_{X,x}) ≌ Mod(𝒪_X|_{\{x\}})`.

The space `{x}` has one point, so modules on it are modules over its global functions by
`Stacks.Cohomology.SubsingletonSections.subsingletonSectionsEquivalence`, and that ring is
`𝒪_{X,x}` by `Stacks.Cohomology.SupportedComplexes.pointBaseRingEquiv`. -/
public def stalkModuleEquivalence :
    ModuleCat.{u} (X.presheaf.stalk x) ≌
      SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier))) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (pointBaseRingEquiv X x)).trans
    (Stacks.Cohomology.SubsingletonSections.subsingletonSectionsEquivalence
      (closedSubsetRingedSpace X ({x} : Set X.carrier)))

/-- The identification at a point is additive, being one half of an equivalence of additive
categories. -/
public instance stalkModuleEquivalence_functor_additive :
    (stalkModuleEquivalence X x).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Its quasi-inverse is additive for the same reason. -/
public instance stalkModuleEquivalence_inverse_additive :
    (stalkModuleEquivalence X x).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The derived identification at a point**:

`D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))`.

Both functors of `Stacks.Cohomology.SupportedComplexes.stalkModuleEquivalence` are exact, being
halves of an equivalence of abelian categories. -/
public def stalkModuleDerivedEquivalence :
    DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)) ≌
      DerivedCategory (SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (stalkModuleEquivalence X x)

/-- **An isomorphism over the local ring is an isomorphism on the one-point space.** For `P` and
`Q` in `D(Mod(𝒪_X|_{\{x\}}))`, an isomorphism of their images in `D(Mod(𝒪_{X,x}))` yields an
isomorphism `P ≅ Q`.

This is what feeds `Stacks.Cohomology.SupportedComplexes.isoOfDerivedSupportedSectionsIso`: that
transport consumes an isomorphism on the one-point space, while a comparison carried out over the
local ring produces one in `D(Mod(𝒪_{X,x}))`. -/
public def isoOfStalkModuleDerivedIso
    (P Q : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))))
    (φ : (stalkModuleDerivedEquivalence X x).inverse.obj P ≅
      (stalkModuleDerivedEquivalence X x).inverse.obj Q) : P ≅ Q :=
  (stalkModuleDerivedEquivalence X x).inverse.preimageIso φ

/-- **A comparison over the local ring at a closed point is a global isomorphism.** For `K` and
`L` in `D(𝒪_X)` whose cohomology sheaves are supported on the closed point `x`, an isomorphism
over `𝒪_{X,x}` of the images of `R𝓗_{\{x\}}(K)` and `R𝓗_{\{x\}}(L)` yields `K ≅ L`.

This is
`Stacks.Cohomology.SupportedComplexes.isoOfDerivedSupportedSectionsIso` — which consumes an
isomorphism on the one-point space `({x}, 𝒪_X|_{\{x\}})` — fed through
`Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIso`, so that a comparison carried
out in `D(Mod(𝒪_{X,x}))`, where a local duality argument produces it, suffices.  The hypotheses
are exactly those of the transport: `x` closed, and `K` and `L` supported there. -/
public def isoOfStalkModuleDerivedIsoOfSupported
    (hx : IsClosed ({x} : Set X.carrier))
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) L)
    (φ : (stalkModuleDerivedEquivalence X x).inverse.obj
          ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K) ≅
        (stalkModuleDerivedEquivalence X x).inverse.obj
          ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj L)) :
    K ≅ L :=
  isoOfDerivedSupportedSectionsIso X ({x} : Set X.carrier) hx K L hK hL
    (isoOfStalkModuleDerivedIso X x _ _ φ)

end Stacks.Cohomology.SupportedComplexes

end
