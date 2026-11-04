module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsSheafTriangle
public import StacksCore.Tactic.StacksAttribute

/-!
# Canonical terms for the derived functor of sections supported on a closed subset

Let `Z` be a closed subset of a ringed space `X`, let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion and let `RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` be the total right derived functor of sections
supported on `Z`. The adjunction `i_* ⊣ RH_Z` and the distinguished triangle
`i_* RH_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ (i_* RH_Z(K))⟦1⟧` are available as existence statements; a
canonical map out of either of them — for instance the factorization of a map `i_* L ⟶ K`
through `i_* RH_Z(K)` — cannot be built through an existential. This file provides both as
*terms*.

Nothing here is a new theorem about `RH_Z`: the adjunction is Mathlib's
`CategoryTheory.Adjunction.derived`, whose four derived-functor hypotheses are discharged from
exactness of `i_*` on one side and from K-injective resolutions on the other, and the connecting
map of the triangle is the one that
`Stacks.Cohomology.RestrictionCover.derivedTriangleOfShortExactOnInjectives` already
constructs. The existing existence statements remain the stated forms of Stacks 0A3B (1) and
Stacks 0G72; the terms below are chosen refinements of them.

## Main definitions

* `derivedAdjunctionOfExactLeftAdjoint`: for an adjunction `G₀ ⊣ H₀` with `G₀` exact and a right
  derived functor `RF` of `H₀`, the adjunction `G₀.mapDerivedCategory ⊣ RF` as a term.
* `derivedPushforwardAdjunction`: **Stacks 0A3B (1)** as a term, the adjunction `i_* ⊣ RH_Z`.
* `derivedPushforwardCompDerivedSupportedSectionsIsoId`: **Stacks 0A3B (2)** as a term, the
  natural isomorphism `i_* ⋙ RH_Z ≅ 𝟭` inverse to the unit.
* `derivedSupportedSectionsTriangleδ`: **Stacks 0G72** as a term, the connecting map `δ` of the
  triangle, and `derivedSupportedSectionsTriangle`, the triangle itself.
* `derivedSupportedSectionsLift`: the canonical factorization of a map `i_* L ⟶ K` through
  `i_* RH_Z(K)`, that is, its adjoint transpose.
* `localCohomologySheafOfComplex`: the degree-`c` local cohomology sheaf `ℋ ᶜ_Z(K)` of a complex
  `K` in `D(𝒪_X)`, and `localCohomologySheafLift`, the degree-`c` cohomology sheaf of the
  factorization above.

## Main results

* `derivedPushforwardAdjunction_unit_app`: the unit of the chosen adjunction satisfies the same
  compatibility with the underived unit that
  `exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit` asserts of an unspecified
  one, which is what identifies it as the canonical comparison `K ⟶ RH_Z(i_* K)`.
* `unit_eq_of_unit_app_eq` and `unit_eq_derivedPushforwardAdjunction_unit`: that compatibility
  determines the unit, so every adjunction the existence statement could produce has the unit of
  the adjunction chosen here.
* `derivedSupportedSectionsTriangle_distinguished`: the triangle built from the chosen `δ` is
  distinguished at every object.
* `modulePushforward_map_derivedSupportedSectionsLift_comp_counit`: the factorization property,
  `i_*(lift u) ≫ counit = u`, which is the commutative triangle of Stacks 0G7L.

## Implementation notes

`CategoryTheory.Adjunction.derived` asks for four derived-functor properties: each of the two
derived functors must be one, and each must remain one after post-composition with the other
(*absoluteness*). Here the left adjoint `i_*` is exact, so `i_*.mapDerivedCategory` has an
invertible comparison `Functor.mapDerivedCategoryFactorsh` and both of its two properties are
free, by `CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts`; this is the mirror image of
`CategoryTheory.Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact`. On the right, that
`RH_Z` is a right derived functor is the instance
`derivedSupportedSectionsOnClosed_isRightDerivedFunctor`, and its absoluteness is
`CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions` applied to the K-injective
resolutions of `Mod(𝒪_X)`, which `exists_isKInjective_quasiIso_moduleSheaves` supplies: a
K-injective complex is precisely one into which `DerivedCategory.Qh` is bijective on morphisms,
by `CochainComplex.IsKInjective.Qh_map_bijective`.

Because the adjunction is a term, the unit compatibility of
`exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit` becomes a lemma about it,
`CategoryTheory.Adjunction.derivedη_fac_app`, and invertibility of the unit is then the already
general `isIso_unit_of_fullyFaithful_of_isKInjective_map` applied to the term. So Stacks
0A3B (2) is also upgraded to a chosen natural isomorphism.

For the triangle only the statement of Stacks 0G72 is existential: its proof obtains `δ` from
`derivedTriangleOfShortExactOnInjectives`, which returns the connecting map *in a subtype*
together with its distinguishedness, so `δ` is read off the first component with no choice at
all. The two other maps of the triangle are already the natural transformations
`derivedSupportedSectionsToId` and `idToDerivedRestrictPush`.

The degree-`c` local cohomology sheaf of a complex is taken in the unbounded model, as the
degree-`c` cohomology sheaf of `RH_Z(K)`; its identification with the bounded-below
`localCohomologySheafFunctorInt` at a module placed in degree `0` is not available as a term,
because the comparison of the two models,
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`, is itself an
existence statement resting on a chosen injective resolution.

## References

* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Remark 36.6.6 (Tag 0G7L)](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Lemma 13.30.3 (Tag 09T5)](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### A chosen derived adjunction when the left adjoint is exact -/

section Derived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {G₀ : B ⥤ A} {H₀ : A ⥤ B} [G₀.Additive] [H₀.Additive]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]

/-- K-injective resolutions of cochain complexes are coresolutions in the sense that the
absoluteness criterion of `CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions`
consumes: every object of the homotopy category admits a quasi-isomorphism into an object into
which `DerivedCategory.Qh` is bijective on morphisms. Bijectivity at a K-injective complex is
`CochainComplex.IsKInjective.Qh_map_bijective`. -/
theorem exists_quasiIso_qh_map_bijective
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    ∃ (I : HomotopyCategory A (ComplexShape.up ℤ)) (s : M ⟶ I),
      HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s ∧
        ∀ N : HomotopyCategory A (ComplexShape.up ℤ),
          Function.Bijective (DerivedCategory.Qh.map :
            (N ⟶ I) → (DerivedCategory.Qh.obj N ⟶ DerivedCategory.Qh.obj I)) := by
  obtain ⟨Mc, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨J, q, hJ, hq⟩ := hres Mc
  have : J.IsKInjective := hJ
  exact ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J,
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq,
    fun N => CochainComplex.IsKInjective.Qh_map_bijective N J⟩

/-- The functor induced by an exact functor on unbounded derived categories is the *left* derived
functor of its degreewise action on the homotopy category: the comparison
`Functor.mapDerivedCategoryFactorsh` is an isomorphism, which is all that is needed.

This is the mirror image of
`CategoryTheory.Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact`. -/
theorem isLeftDerivedFunctor_mapDerivedCategory_of_exact :
    G₀.mapDerivedCategory.IsLeftDerivedFunctor G₀.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ G₀.mapDerivedCategoryFactorsh

/-- The left derived functor of an exact functor is **absolute**: it remains a left derived
functor after post-composition with an arbitrary functor, the comparison being the whiskered
one. The whiskered comparison is still an isomorphism, and the functor being derived still
inverts quasi-isomorphisms. -/
theorem isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact {H : Type*} [Category H]
    (Ψ : DerivedCategory A ⥤ H) :
    (G₀.mapDerivedCategory ⋙ Ψ).IsLeftDerivedFunctor
      ((DerivedCategory.Qh.associator G₀.mapDerivedCategory Ψ).inv ≫
        Functor.whiskerRight G₀.mapDerivedCategoryFactorsh.hom Ψ)
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) :=
  (Functor.isLeftDerivedFunctor_iff_of_inverts _ _
    (MorphismProperty.IsInvertedBy.of_comp _ _
      (Functor.isInvertedBy_mapHomotopyCategory_comp_Qh_of_exact G₀) _)).2 inferInstance

/-- **A chosen derived adjunction, Stacks 09T5 for an exact left adjoint.** Let `G₀ ⊣ H₀` be an
adjunction of additive functors between abelian categories with `G₀` exact, and let `RF` with
comparison `β` be a right derived functor of `H₀` on the unbounded derived category. If every
complex in the source of `H₀` admits a K-injective resolution, then the functor induced by `G₀`
on unbounded derived categories is left adjoint to `RF`.

Unlike `exists_derivedAdjunction_unit_compat_of_exact`, this is the adjunction itself; the unit
compatibility that pins it down is `derivedAdjunctionOfExactLeftAdjoint_unit_app`. The four
derived-functor hypotheses of `CategoryTheory.Adjunction.derived` are discharged by
`isLeftDerivedFunctor_mapDerivedCategory_of_exact` and
`isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact` on the left, and by the ambient instance
and `CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions` on the right. -/
noncomputable def derivedAdjunctionOfExactLeftAdjoint (adj : G₀ ⊣ H₀)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q) :
    G₀.mapDerivedCategory ⊣ RF :=
  letI := isLeftDerivedFunctor_mapDerivedCategory_of_exact (G₀ := G₀)
  letI := isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact (G₀ := G₀) RF
  letI := Functor.isRightDerivedFunctor_comp_of_coresolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) β G₀.mapDerivedCategory
    (exists_quasiIso_qh_map_bijective hres)
  (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    G₀.mapDerivedCategoryFactorsh.hom β

/-- **The unit of the chosen derived adjunction is the canonical comparison.** At the image of a
complex `M` the unit of `derivedAdjunctionOfExactLeftAdjoint` is computed from the unit
`M ⟶ H₀(G₀ M)` of the underived adjunction and the two derivation units, which is the
compatibility that `exists_derivedAdjunction_unit_compat_of_exact` asserts of an unspecified
adjunction. -/
theorem derivedAdjunctionOfExactLeftAdjoint_unit_app (adj : G₀ ⊣ H₀)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (M : HomotopyCategory B (ComplexShape.up ℤ)) :
    (derivedAdjunctionOfExactLeftAdjoint adj RF β hres).unit.app
          (DerivedCategory.Qh.obj M) ≫ RF.map (G₀.mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
        β.app ((G₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  have := isLeftDerivedFunctor_mapDerivedCategory_of_exact (G₀ := G₀)
  have := isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact (G₀ := G₀) RF
  have := Functor.isRightDerivedFunctor_comp_of_coresolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) β G₀.mapDerivedCategory
    (exists_quasiIso_qh_map_bijective hres)
  (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    G₀.mapDerivedCategoryFactorsh.hom β M

/-- **The compatibility determines the unit, so the chosen adjunction is canonical.** Any
adjunction between the same two functors whose unit satisfies the compatibility of
`derivedAdjunctionOfExactLeftAdjoint_unit_app` has *that* unit: transformations into the
composite `G₀.mapDerivedCategory ⋙ RF` are determined by their composites with the comparison,
that composite being a left derived functor by
`isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact`.

So nothing is chosen in `derivedAdjunctionOfExactLeftAdjoint`: the adjunction whose existence
`exists_derivedAdjunction_unit_compat_of_exact` asserts has the same unit as it. -/
theorem unit_eq_of_unit_app_eq (adj : G₀ ⊣ H₀)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (Ad : G₀.mapDerivedCategory ⊣ RF)
    (hAd : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      Ad.unit.app (DerivedCategory.Qh.obj M) ≫
          RF.map (G₀.mapDerivedCategoryFactorsh.hom.app M) =
        DerivedCategory.Qh.map
            ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app M) ≫
          β.app ((G₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) :
    Ad.unit = (derivedAdjunctionOfExactLeftAdjoint adj RF β hres).unit := by
  let _ := isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact (G₀ := G₀) RF
  refine Functor.leftDerived_ext (G₀.mapDerivedCategory ⋙ RF)
    ((DerivedCategory.Qh.associator G₀.mapDerivedCategory RF).inv ≫
      Functor.whiskerRight G₀.mapDerivedCategoryFactorsh.hom RF)
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _ _ _ ?_
  ext M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp, Category.assoc,
    derivedAdjunctionOfExactLeftAdjoint_unit_app adj RF β hres M] using hAd M

end Derived

/-! ### Stacks 0A3B as a term -/

/-- **Stacks 0A3B (1), as a term.** Let `Z` be a closed subset of a ringed space `X` and let
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. The functor `D(𝒪_X|_Z) ⥤ D(𝒪_X)` induced by
`i_*` is left adjoint to the right derived functor `RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` of sections
supported on `Z`.

This is the adjunction whose mere existence is
`derivedPushforward_adj_derivedSupportedSectionsOnClosed`, and its unit is the canonical
comparison by `derivedPushforwardAdjunction_unit_app`. -/
@[stacks 0A3B "the adjunction i_*^D ⊣ RℋZ as a term, not an existence statement"]
noncomputable def derivedPushforwardAdjunction (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⊣
      derivedSupportedSectionsOnClosed X Z hZ :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  derivedAdjunctionOfExactLeftAdjoint
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
    (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ)
    (exists_isKInjective_quasiIso_moduleSheaves X)

/-- **The unit of the chosen adjunction of Stacks 0A3B (1) is the canonical comparison**
`K ⟶ RH_Z(i_* K)`: at the image of a complex `M` of `𝒪_X|_Z`-modules it is computed from the
unit `M ⟶ H_Z(i_* M)` of the underived adjunction and the derivation units of the two derived
functors. This is the compatibility of
`exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit`, now for a specific
adjunction. -/
theorem derivedPushforwardAdjunction_unit_app (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z)
    (M : HomotopyCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (derivedPushforwardAdjunction X Z hZ).unit.app (DerivedCategory.Qh.obj M) ≫
          (derivedSupportedSectionsOnClosed X Z hZ).map
            ((modulePushforward
              (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
            (ComplexShape.up ℤ)).unit.app M) ≫
        (derivedSupportedSectionsOnClosedUnit X Z hZ).app
          (((modulePushforward (closedSubsetInclusion X Z)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) :=
  have := pushforward_preservesFiniteLimits X Z
  have := pushforward_preservesFiniteColimits X Z hZ
  derivedAdjunctionOfExactLeftAdjoint_unit_app
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
    (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ)
    (exists_isKInjective_quasiIso_moduleSheaves X) M

/-- **The chosen adjunction of Stacks 0A3B (1) is the canonical one.** Every adjunction
`i_* ⊣ RH_Z` whose unit satisfies the compatibility of
`exists_derivedPushforward_adj_derivedSupportedSectionsOnClosed_unit` — the property pinning the
unit down as the comparison `K ⟶ RH_Z(i_* K)` — has the unit of `derivedPushforwardAdjunction`.

In particular the adjunction produced by the existence statement is not more general than this
one, and no choice distinguishes them. -/
theorem unit_eq_derivedPushforwardAdjunction_unit (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    ∀ Ad : (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⊣
        derivedSupportedSectionsOnClosed X Z hZ,
      (∀ M : HomotopyCategory (_root_.SheafOfModules.{u}
          (structureSheafRing (closedSubsetRingedSpace X Z))) (ComplexShape.up ℤ),
        Ad.unit.app (DerivedCategory.Qh.obj M) ≫
            (derivedSupportedSectionsOnClosed X Z hZ).map
              ((modulePushforward
                (closedSubsetInclusion X Z)).mapDerivedCategoryFactorsh.hom.app M) =
          DerivedCategory.Qh.map
              ((Adjunction.mapHomotopyCategoryAdjunction
                (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
                (ComplexShape.up ℤ)).unit.app M) ≫
            (derivedSupportedSectionsOnClosedUnit X Z hZ).app
              (((modulePushforward (closedSubsetInclusion X Z)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj M)) →
      Ad.unit = (derivedPushforwardAdjunction X Z hZ).unit :=
  have := pushforward_preservesFiniteLimits X Z
  have := pushforward_preservesFiniteColimits X Z hZ
  fun Ad hAd => unit_eq_of_unit_app_eq
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
    (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ)
    (exists_isKInjective_quasiIso_moduleSheaves X) Ad hAd

/-- **Stacks 0A3B (2), as a term.** The unit of the chosen adjunction `i_* ⊣ RH_Z` is an
isomorphism, so `RH_Z(i_* K) = K` for every `K` in `D(𝒪_X|_Z)`.

The proof is the general `isIso_unit_of_fullyFaithful_of_isKInjective_map`, applied to the term
`derivedPushforwardAdjunction` and its unit compatibility: on a K-injective complex the three
factors of that compatibility are invertible. -/
instance isIso_unit_derivedPushforwardAdjunction (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    IsIso (derivedPushforwardAdjunction X Z hZ).unit :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  isIso_unit_of_fullyFaithful_of_isKInjective_map
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ)
    (isKInjective_modulePushforward_closedSubsetInclusion X Z)
    (exists_isKInjective_quasiIso_moduleSheaves X)
    (exists_isKInjective_quasiIso_moduleSheaves_closedSubset X Z)
    (derivedPushforwardAdjunction X Z hZ) (derivedPushforwardAdjunction_unit_app X Z hZ)

/-- **Stacks 0A3B (2) as a natural isomorphism.** Composing `RH_Z` with the derived pushforward
from the closed subset is the identity on `D(𝒪_X|_Z)`, the isomorphism being the inverse of the
unit of `derivedPushforwardAdjunction`. -/
@[stacks 0A3B "RℋZ ∘ i_*^D ≅ 𝟭, as a chosen natural isomorphism"]
noncomputable def derivedPushforwardCompDerivedSupportedSectionsIsoId (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory ⋙
        derivedSupportedSectionsOnClosed X Z hZ ≅
      𝟭 (DerivedCategory (_root_.SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z)))) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  (asIso (derivedPushforwardAdjunction X Z hZ).unit).symm

/-! ### Stacks 0G72 as a term -/

section Triangle

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
  (RH RJ : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
  (aH : (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
  (aJ : (restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RJ)
  [RH.IsRightDerivedFunctor aH
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))]
  [RJ.IsRightDerivedFunctor aJ
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))]

/-- The connecting map of the triangle of Stacks 0G72, as a subtype element: it is
`Stacks.Cohomology.RestrictionCover.derivedTriangleOfShortExactOnInjectives` applied to the
short exact sequence `0 ⟶ i_* ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` of an injective sheaf of modules,
with the three chosen derived functors identified on the functorial K-injective resolution. -/
noncomputable def derivedSupportedSectionsTriangleδData :
    {δ : RJ ⟶ RH ⋙ shiftFunctor
        (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) (1 : ℤ) //
      ∀ K, Triangle.mk ((derivedSupportedSectionsToId X Z RH aH).app K)
          ((idToDerivedRestrictPush X Z hZ RJ aJ).app K) (δ.app K) ∈
        distTriang (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))} :=
  derivedTriangleOfShortExactOnInjectives (structureSheafRing X)
    (supportedSectionsFunctor X Z) (Functor.id _)
    (restrictPush (structureSheafRing X) (openComplement Z hZ))
    (supportedSectionsSubsheafInclusion X Z)
    (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit
    (supportedSectionsSubsheafInclusion_comp_unit X Z hZ)
    (fun I _ => supportedSectionsRestrictPushShortExact X Z hZ I)
    RH (Functor.id _) RJ
    (resolutionDerivedIso (structureSheafRing X) (supportedSectionsFunctor X Z) RH aH)
    (resolutionDerivedIso (structureSheafRing X) (Functor.id _) (Functor.id _)
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh))
    (resolutionDerivedIso (structureSheafRing X)
      (restrictPush (structureSheafRing X) (openComplement Z hZ)) RJ aJ)
    (derivedSupportedSectionsToId X Z RH aH) (idToDerivedRestrictPush X Z hZ RJ aJ)
    (fun K => resolutionDerivedIso_fac (structureSheafRing X)
      (F := supportedSectionsFunctor X Z) (G := Functor.id _) (RF := RH)
      (RG := Functor.id _) aH
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh)
      (supportedSectionsSubsheafInclusion X Z) (derivedSupportedSectionsToId X Z RH aH)
      (derivedSupportedSectionsToId_fac X Z RH aH) K)
    (fun K => resolutionDerivedIso_fac (structureSheafRing X)
      (F := Functor.id _) (G := restrictPush (structureSheafRing X) (openComplement Z hZ))
      (RF := Functor.id _) (RG := RJ)
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh) aJ
      (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit
      (idToDerivedRestrictPush X Z hZ RJ aJ)
      (idToDerivedRestrictPush_fac X Z hZ RJ aJ) K)

/-- **The connecting map of Stacks 0G72, as a term.** For chosen right derived functors `RH` of
`ℱ ↦ i_* ℋ_Z(ℱ)` and `RJ` of `ℱ ↦ j_*(ℱ|_U)`, this is the natural transformation
`δ : RJ ⟶ RH⟦1⟧` completing the two canonical maps `RH ⟶ 𝟭` and `𝟭 ⟶ RJ` to a distinguished
triangle, by `derivedSupportedSectionsTriangle_distinguished`.

The existence statement `exists_derivedSupportedSectionsTriangle` is this map with the quantifier
in front: the connecting map is constructed by
`Stacks.Cohomology.RestrictionCover.derivedTriangleOfShortExactOnInjectives` as the connecting
map of the short exact sequence of complexes obtained by applying the three functors to the
functorial K-injective resolution, descended along the localization. -/
@[stacks 0G72 "the connecting morphism δ of the triangle, as a term"]
noncomputable def derivedSupportedSectionsTriangleδ :
    RJ ⟶ RH ⋙ shiftFunctor
      (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) (1 : ℤ) :=
  (derivedSupportedSectionsTriangleδData X Z hZ RH RJ aH aJ).1

/-- **Stacks 0G72, as a term.** The triangle
`i_* Rℋ_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ (i_* Rℋ_Z(K))⟦1⟧` in the unbounded derived category of
`𝒪_X`-modules, built from the two canonical natural transformations and the chosen connecting
map. It is distinguished by `derivedSupportedSectionsTriangle_distinguished`, and all three of
its maps are components of natural transformations, so it is functorial in `K`. -/
noncomputable abbrev derivedSupportedSectionsTriangle
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    Triangle (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :=
  Triangle.mk ((derivedSupportedSectionsToId X Z RH aH).app K)
    ((idToDerivedRestrictPush X Z hZ RJ aJ).app K)
    ((derivedSupportedSectionsTriangleδ X Z hZ RH RJ aH aJ).app K)

/-- **Stacks 0G72.** The triangle of `derivedSupportedSectionsTriangle` is distinguished at every
object `K` of `D(𝒪_X)`. -/
@[stacks 0G72 "the triangle i_*RℋZ(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ [1] is distinguished"]
theorem derivedSupportedSectionsTriangle_distinguished
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    derivedSupportedSectionsTriangle X Z hZ RH RJ aH aJ K ∈
      distTriang (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :=
  (derivedSupportedSectionsTriangleδData X Z hZ RH RJ aH aJ).2 K

end Triangle

/-! ### The canonical factorization through derived supported sections -/

section Factorization

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The canonical factorization of Stacks 0G7L.** A map `i_* L ⟶ K` in `D(𝒪_X)` out of a
complex pushed forward from `Z` has a canonical lift `L ⟶ RH_Z(K)`, its adjoint transpose under
`derivedPushforwardAdjunction`. Pushing the lift forward and composing with the counit
`i_* RH_Z(K) ⟶ K` returns the original map, by
`modulePushforward_map_derivedSupportedSectionsLift_comp_counit`: this is the commutative
triangle of Stacks 0G7L, for the chosen adjunction. -/
@[stacks 0G7L "the canonical factorisation through derived supported sections"]
noncomputable def derivedSupportedSectionsLift
    {L : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    {K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))}
    (u : letI := pushforward_preservesFiniteLimits X Z
      letI := pushforward_preservesFiniteColimits X Z hZ
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj L ⟶ K) :
    L ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj K :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  (derivedPushforwardAdjunction X Z hZ).homEquiv L K u

/-- **The triangle of Stacks 0G7L commutes.** The canonical lift of `u : i_* L ⟶ K` through
`i_* RH_Z(K)`, pushed forward and followed by the counit of the adjunction, is `u` again. -/
@[stacks 0G7L "the commuting triangle of the factorisation"]
theorem modulePushforward_map_derivedSupportedSectionsLift_comp_counit
    {L : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    {K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))}
    (u : letI := pushforward_preservesFiniteLimits X Z
      letI := pushforward_preservesFiniteColimits X Z hZ
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj L ⟶ K) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (derivedSupportedSectionsLift X Z hZ u) ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app K = u := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  exact ((derivedPushforwardAdjunction X Z hZ).homEquiv L K).symm_apply_apply u

/-- **The local cohomology sheaf of a complex.** For `K` in `D(𝒪_X)` and `c : ℤ` this is the
degree-`c` cohomology sheaf `ℋ ᶜ_Z(K)` of `RH_Z(K)`, a sheaf of `𝒪_X|_Z`-modules.

For a module placed in degree `0` this is the unbounded-model avatar of
`localCohomologySheafFunctorInt`; the two are not identified here, because the comparison of the
two models is only available as an existence statement. -/
noncomputable abbrev localCohomologySheafOfComplex (c : ℤ)
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
    _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)) :=
  (DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) c).obj
    ((derivedSupportedSectionsOnClosed X Z hZ).obj K)

/-- **The degree-`c` cohomology sheaf of the comparison of Stacks 0G7L, as a term.** The
canonical lift `L ⟶ RH_Z(K)` of a map `u : i_* L ⟶ K` induces, on degree-`c` cohomology sheaves,
a map `H ᶜ(L) ⟶ ℋ ᶜ_Z(K)` of sheaves of `𝒪_X|_Z`-modules.

This is the map a Gysin-type comparison in degree `c` is read off: with `L` the extended
alternating Čech complex of `c` global equations and `u` its augmentation towards `K`, the
source is the degree-`c` cohomology sheaf of that complex. It is a term precisely because
`derivedPushforwardAdjunction` is one; through the `Nonempty` form of Stacks 0A3B (1) no such
map can be written down. -/
noncomputable def localCohomologySheafLift (c : ℤ)
    {L : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    {K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))}
    (u : letI := pushforward_preservesFiniteLimits X Z
      letI := pushforward_preservesFiniteColimits X Z hZ
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj L ⟶ K) :
    (DerivedCategory.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) c).obj L ⟶
      localCohomologySheafOfComplex X Z hZ c K :=
  (DerivedCategory.homologyFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) c).map
    (derivedSupportedSectionsLift X Z hZ u)

end Factorization

end Stacks.Cohomology.SupportedComplexes

end
