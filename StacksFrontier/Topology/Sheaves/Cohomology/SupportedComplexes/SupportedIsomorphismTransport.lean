module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence

/-!
# Complexes supported on a closed subset are compared on that subset

Let `Z` be a closed subset of a ringed space `X`, let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion and let `RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` be the right derived functor of sections supported
on `Z`.  By [Stacks, Tag 0AEF] part (2), `i_*` on derived categories is an equivalence of
`D(𝒪_X|_Z)` with the full subcategory `D_Z(𝒪_X)` of complexes whose cohomology sheaves are
supported on `Z`, with quasi-inverse `RH_Z`.  This file records the two consequences one uses
when comparing two complexes that are both supported on `Z`:

* an isomorphism `RH_Z(K) ≅ RH_Z(L)` is the image of an isomorphism `K ≅ L`, and
* a morphism `K ⟶ L` is invertible as soon as `RH_Z` of it is.

The first is the step "both sides are supported on `Z`, so it suffices to compare them on `Z`"
in the proof of a global isomorphism between two complexes that are only known to agree near
`Z` — for instance the identification of the derived dual of a coherent module supported at a
closed point with the shifted Matlis dual, where the two sides carry no canonical map to one
another and the isomorphism has to be produced from the comparison on `{x}`.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.isoOfDerivedSupportedSectionsIso`: an isomorphism
  `K ≅ L` of complexes supported on `Z` out of an isomorphism `RH_Z(K) ≅ RH_Z(L)`.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isIso_of_isIso_derivedSupportedSectionsOnClosed_map`:
  `RH_Z` reflects invertibility of morphisms between complexes supported on `Z`.
* `AlgebraicGeometry.cohomologySupportedOn_shift`: cohomological support is unchanged by
  translation, so that a shift of a supported complex may be fed to the two statements above.

## Implementation notes

Both statements are formal consequences of the counit of the adjunction `i_*^D ⊣ RH_Z` being
invertible at a complex supported on `Z`, which is
`Stacks.Cohomology.SupportedComplexes.derivedPushforwardSupportedSectionsIso`; no further
property of `RH_Z` is used, and in particular neither statement needs the full equivalence of
Tag 0AEF or any identification of `D(𝒪_X|_Z)` with modules over a ring.  The hypotheses that
`K` and `L` are supported on `Z` cannot be dropped from either: `RH_Z` of a complex supported on
the complement of `Z` vanishes.

The reflection statement is phrased for a morphism rather than deduced from full faithfulness of
`i_*^D`, because what is wanted downstream is invertibility of a given comparison map, and the
counit square of the adjunction provides it directly.

## References

* [Stacks Project, Lemma 20.34.4 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
  (K L : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))

/-- **Two complexes supported on a closed subset are isomorphic as soon as their sections
supported there are.**  For `K` and `L` in `D(𝒪_X)` whose cohomology sheaves are supported on the
closed subset `Z`, an isomorphism `RH_Z(K) ≅ RH_Z(L)` in `D(𝒪_X|_Z)` yields an isomorphism
`K ≅ L` in `D(𝒪_X)`: push it forward along the inclusion of `Z` and compose with the two
canonical isomorphisms `i_* RH_Z(K) ≅ K` and `i_* RH_Z(L) ≅ L` of [Stacks, Tag 0AEF] part (2).

This is what makes a comparison performed on `Z` — at a closed point, say — produce a global
isomorphism, for two complexes between which no canonical morphism is given. -/
def isoOfDerivedSupportedSectionsIso
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z K)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z L)
    (ψ : (derivedSupportedSectionsOnClosed X Z hZ).obj K ≅
      (derivedSupportedSectionsOnClosed X Z hZ).obj L) :
    K ≅ L :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  (derivedPushforwardSupportedSectionsIso X Z hZ K hK).symm ≪≫
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.mapIso ψ ≪≫
    derivedPushforwardSupportedSectionsIso X Z hZ L hL

/-- **Sections supported on a closed subset reflect invertibility between complexes supported
there.**  If `K` and `L` in `D(𝒪_X)` have cohomology sheaves supported on the closed subset `Z`
and `φ : K ⟶ L` is such that `RH_Z(φ)` is invertible, then `φ` is invertible.

The counit square of the adjunction `i_*^D ⊣ RH_Z` of [Stacks, Tag 0A3B] reads
`i_* RH_Z(φ) ≫ ε_L = ε_K ≫ φ`, and both counit components are invertible by [Stacks, Tag 0AEF]
part (2), so `ε_K ≫ φ` is invertible and hence so is `φ`. -/
theorem isIso_of_isIso_derivedSupportedSectionsOnClosed_map
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z K)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z L)
    (φ : K ⟶ L) (hφ : IsIso ((derivedSupportedSectionsOnClosed X Z hZ).map φ)) :
    IsIso φ := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  let := isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ K hK
  let := isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ L hL
  let := hφ
  have hnat := (derivedPushforwardAdjunction X Z hZ).counit.naturality φ
  rw [Functor.comp_map, Functor.id_map] at hnat
  have hcomp : IsIso ((derivedPushforwardAdjunction X Z hZ).counit.app K ≫ φ) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedPushforwardAdjunction X Z hZ).counit.app K) φ

end Stacks.Cohomology.SupportedComplexes

/-! ### Cohomological support and translation -/

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **Cohomological support is unchanged by translation.**  If the cohomology sheaves of `E` are
supported on `T`, then so are those of `E⟦n⟧`.

Read off the derived stalks by
`AlgebraicGeometry.cohomologySupportedOn_iff_forall_isZero_derivedStalk`: the derived stalk
functor commutes with the translation, and the translation of a zero object is zero. -/
theorem cohomologySupportedOn_shift {X : TopCat.{u}}
    (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X) (n : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} O)) (hE : CohomologySupportedOn O T E) :
    CohomologySupportedOn O T (E⟦n⟧) := by
  rw [cohomologySupportedOn_iff_forall_isZero_derivedStalk] at hE ⊢
  intro y hy
  refine IsZero.of_iso ?_
    (((SheafOfModules.stalkFunctor O y).mapDerivedCategory.commShiftIso n).app E)
  exact Functor.map_isZero (CategoryTheory.shiftFunctor _ n) (hE y hy)

end AlgebraicGeometry

end
