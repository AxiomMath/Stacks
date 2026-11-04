module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOnASubsingletonSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence

/-!
# Derived global sections of a complex supported at a closed point

Let `(X, 𝒪_X)` be a ringed space and let `x ∈ X` be a point whose singleton is closed. For an
object `K` of `D(𝒪_X)` whose cohomology sheaves are supported on `{x}`, derived global sections
on `X` are the ordinary sections at the point:

`RΓ(X, K) ≅ Γ({x}, R𝓗_{\{x\}}(K))`,

the right-hand side being sections on the one-point ringed space `({x}, 𝒪_X|_{\{x\}})` read as a
module over `Γ(X, 𝒪_X)`, with no derived functor left on it.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.sectionsAtPoint`: sections on the closed subset `{x}`
  with scalars in `Γ(X, 𝒪_X)`.

## Main results

* `Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoSectionsAtClosedPoint`: the
  isomorphism above.
* `Stacks.Cohomology.SupportedComplexes.homologyIsoSectionsAtClosedPoint`: its degree-`n`
  cohomology, `H^n(X, K) ≅ H^n(Γ({x}, R𝓗_{\{x\}}(K)))`.

## References

* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.SubsingletonSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (x : X.carrier)

/-- The carrier of the ringed space on a one-point closed subset is a subsingleton. -/
public instance subsingleton_carrier_closedSubsetRingedSpace_singleton :
    Subsingleton (closedSubsetRingedSpace X ({x} : Set X.carrier)).carrier :=
  inferInstanceAs (Subsingleton ({x} : Set X.carrier))

/-- **Sections at the closed point**: sections on `{x}` of a sheaf of `𝒪_X|_{\{x\}}`-modules, read
as a module over `Γ(X, 𝒪_X)` by restriction of scalars along the inclusion. This is
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections` at the inclusion of `{x}` and at the
open `⊤`, with the module universe pinned to that of the space. -/
public abbrev sectionsAtPoint :
    SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier))) ⥤
      ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier))) :=
  preimageSections (closedSubsetInclusion X ({x} : Set X.carrier)) ⊤

/-- Sections at the closed point preserve finite limits. -/
public instance preservesFiniteLimits_sectionsAtPoint :
    PreservesFiniteLimits (sectionsAtPoint X x) :=
  comp_preservesFiniteLimits
    (sectionsOverOpen (closedSubsetRingedSpace X ({x} : Set X.carrier))
      ((opensMap (closedSubsetInclusion X ({x} : Set X.carrier))).obj ⊤))
    (ModuleCat.restrictScalars.{u}
      (RingCat.Hom.hom ((structureSheafHom
        (closedSubsetInclusion X ({x} : Set X.carrier))).hom.app (op (⊤ : Opens X.carrier)))))

/-- Sections at the closed point preserve finite colimits. -/
public instance preservesFiniteColimits_sectionsAtPoint :
    PreservesFiniteColimits (sectionsAtPoint X x) :=
  comp_preservesFiniteColimits
    (sectionsOverOpen (closedSubsetRingedSpace X ({x} : Set X.carrier))
      ((opensMap (closedSubsetInclusion X ({x} : Set X.carrier))).obj ⊤))
    (ModuleCat.restrictScalars.{u}
      (RingCat.Hom.hom ((structureSheafHom
        (closedSubsetInclusion X ({x} : Set X.carrier))).hom.app (op (⊤ : Opens X.carrier)))))

/-- **Derived global sections of a complex supported at a closed point are its sections at that
point.** For `x` a point of a ringed space `X` whose singleton is closed and `K` an object of
`D(𝒪_X)` whose cohomology sheaves are supported on `{x}`,

`RΓ(X, K) ≅ Γ({x}, R𝓗_{\{x\}}(K))`

in `D(Γ(X, 𝒪_X))`. -/
public def derivedSectionsIsoSectionsAtClosedPoint
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) :
    (baseSections X).obj K ≅
      (sectionsAtPoint X x).mapDerivedCategory.obj
        ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K) :=
  letI := pushforward_preservesFiniteLimits X ({x} : Set X.carrier)
  letI := pushforward_preservesFiniteColimits X ({x} : Set X.carrier) hx
  let i := closedSubsetInclusion X ({x} : Set X.carrier)
  let G := (derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K
  let e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i).obj G ≅ K :=
    (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory i).app G ≪≫
      derivedPushforwardSupportedSectionsIso X ({x} : Set X.carrier) hx K hK
  (baseSections X).mapIso e.symm ≪≫ (lerayIso i).app G ≪≫
    (derivedPreimageSectionsIso i ⊤).app G

/-- **The reduction to the point in each degree**: `H^n(X, K) ≅ H^n(Γ({x}, R𝓗_{\{x\}}(K)))` for
`K` with cohomology sheaves supported on the closed point `x`. -/
public def homologyIsoSectionsAtClosedPoint
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) (n : ℤ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        ((baseSections X).obj K) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        ((sectionsAtPoint X x).mapDerivedCategory.obj
          ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
    (derivedSectionsIsoSectionsAtClosedPoint X x hx K hK)

end Stacks.Cohomology.SupportedComplexes

end
