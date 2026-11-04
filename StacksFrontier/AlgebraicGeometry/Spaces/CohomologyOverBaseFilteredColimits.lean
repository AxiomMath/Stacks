module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import
  StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsSpaceTypeU

/-!
# Cohomology read over a base commutes with filtered colimits

On a quasi-compact and absolutely quasi-separated algebraic space `X` over a scheme `S`, the
cohomology of `𝒪_X`-modules at module universe `u` commutes with filtered colimits
(**Stacks 073E**, available as
`AlgebraicGeometry.Space.preservesColimit_smallEtaleModuleCohomology_typeU`).  Reading that
cohomology as a module over the global functions of a base `Y` through a morphism
`f : X ⟶ Y` — which is what `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBase`
does for **Stacks 073K**, part (2) — is restriction of scalars along the ring map of
**Stacks 0732**, and that does not disturb the colimit: restriction of scalars is a *left*
adjoint, to coextension of scalars, so it preserves all colimits.

## Main results

* `AlgebraicGeometry.Space.preservesColimitsOfSize_globalSectionsRestrictScalars`: restriction of
  scalars along the comparison of global function rings preserves colimits.
* `AlgebraicGeometry.Space.preservesColimit_cohomologyOverBase`: **cohomology read over a base
  preserves filtered colimits of `𝒪_X`-modules at module universe `u`.**

## Implementation notes

Restriction of scalars has adjoints on both sides — extension of scalars on the left and
coextension of scalars on the right — so it is exact and preserves all limits and colimits.  The
exactness is already recorded, at this very seating, as
`AlgebraicGeometry.Space.preservesHomology_globalSectionsRestrictScalars`; what is needed here is
the colimit half, and it comes from `CategoryTheory.ModuleCat.restrictCoextendScalarsAdj`, the
adjunction in which restriction of scalars is the *left* adjoint.

The two hypotheses of Stacks 073E are absolute conditions on `X` rather than conditions on `f`:
quasi-compactness of the space and quasi-separatedness in the absolute sense.  For the `f` of
Stacks 073K they follow from `f` being quasi-compact and quasi-separated over an affine base, by
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace` and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace`.

## References

* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction of scalars along the comparison of global function rings preserves colimits.**
It is the left adjoint of coextension of scalars. -/
theorem preservesColimitsOfSize_globalSectionsRestrictScalars {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    PreservesColimitsOfSize.{u + 1, u + 1} (globalSectionsRestrictScalars B S hS f) :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
    (globalSectionsRingHomSite B S hS f)).leftAdjoint_preservesColimits

/-- **Stacks 073E for cohomology read over a base.**  On a quasi-compact and absolutely
quasi-separated algebraic space `X`, the degree-`p` cohomology of `𝒪_X`-modules at module
universe `u`, read as a module over the global functions of a base `Y` through `f : X ⟶ Y`,
preserves filtered colimits.

This is the form in which the proof of **Stacks 073K**, part (2) uses Stacks 073E: the left hand
side of part (2) is cohomology on `X` read over `Γ(Y, 𝒪_Y)`, and the dévissage along Lazard's
theorem needs that functor to commute with the filtered colimit of free finite modules. -/
theorem preservesColimit_cohomologyOverBase (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (p : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Modules.{u, u} B S hS X.1 X.2) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    PreservesColimit D
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p ⋙
        globalSectionsRestrictScalars B S hS f) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := preservesColimit_smallEtaleModuleCohomology_typeU B S hS hZ X.1 X.2 hqc hqs p D
  have := preservesColimitsOfSize_globalSectionsRestrictScalars B S hS f
  infer_instance

end AlgebraicGeometry.Space

end

end
