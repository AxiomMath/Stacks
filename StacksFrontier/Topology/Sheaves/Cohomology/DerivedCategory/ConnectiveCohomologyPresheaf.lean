module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ConnectiveHypercohomology

/-!
# The cohomology presheaf of a complex with no negative cohomology

Let `X` be a ringed space and let `M` be an object of the unbounded derived category `D(𝒪_X)`
whose cohomology sheaves vanish in negative degrees.  Its degree-zero *cohomology presheaf*
`U ↦ H^0(U, M)` is then the presheaf of sections of its degree-zero cohomology sheaf, with all
restriction maps included.

This is the presheaf-level form of
`Stacks.Cohomology.Connective.nonempty_zerothDerivedSectionsIsoSections`, which gives the same
identification one open at a time.

## Main results

* `Stacks.Cohomology.Connective.nonempty_zerothCohomologyPresheafIsoSections`: `H^0` of the
  hypercohomology presheaf of a complex with no negative cohomology is the underlying presheaf of
  its degree-zero cohomology sheaf.

## Implementation notes

Taking sections on every open at once is the forgetful functor
`SheafOfModules.forget`, which is additive and left exact
(`SheafOfModules.Finite.forgetPreservesFiniteLimits`), and the hypercohomology presheaf of
Tag 0BKZ is by construction its unbounded right derived functor, so the statement is
`Stacks.Cohomology.Connective.nonempty_zerothHomologyRightDerivedIso` at that functor.

## References

* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HypercohomologyEdge (derivedSectionsPresheaf homotopySectionsPresheaf)

namespace Stacks.Cohomology.Connective

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Sheaves of modules on a ringed space form a Grothendieck abelian category, in the one module
universe available there. -/
local instance isGrothendieckAbelian_moduleSheaves (X : RingedSpace.{u, u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) :=
  SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X)

/-- **The degree-zero cohomology presheaf of a complex with no negative cohomology is the presheaf
of sections of its degree-zero cohomology sheaf.**  For `M` in `D(𝒪_X)` with vanishing cohomology
sheaves in negative degrees, the presheaf `U ↦ H^0(U, M)` is the underlying presheaf of `H^0(M)`,
restriction maps included. -/
theorem nonempty_zerothCohomologyPresheafIsoSections (X : RingedSpace.{u, u})
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hM : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) i).obj
        M)) :
    Nonempty
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{u} (structureSheafRing X).obj) 0).obj
          ((derivedSectionsPresheaf (structureSheafRing X)).obj M) ≅
        (SheafOfModules.forget (structureSheafRing X)).obj
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            M)) :=
  nonempty_zerothHomologyRightDerivedIso (SheafOfModules.forget (structureSheafRing X))
    (derivedSectionsPresheaf (structureSheafRing X))
    ((homotopySectionsPresheaf (structureSheafRing X)).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    M hM

end Stacks.Cohomology.Connective

end
