module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedShortExactOnInjectivesTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportLongExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology with support in a closed subscheme: Stacks 0A45

Let `i : Z ⟶ X` be a closed immersion of schemes and let `j : U ⟶ X` be the inclusion of the
open complement.  For an abelian sheaf `F` on `X_étale` there is a distinguished triangle

`i_*Rℋ_Z(F) ⟶ F ⟶ Rj_*(F|_U) ⟶ i_*Rℋ_Z(F)⟦1⟧`

in `D(X_étale)`, hence the sequence

`0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0`

is exact, and for `p ≥ 1` the higher direct images along `j` of the restriction of `F` to the
open complement are the cohomology sheaves with support in `Z`:

`R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)`.

These are the three assertions of [Stacks, Tag 0A45], collected in the structure
`AlgebraicGeometry.CohomologyWithSupportSequences` and inhabited by
`AlgebraicGeometry.cohomologyWithSupportSequences`, which carries the tag.

## Main definitions

* `AlgebraicGeometry.supportedCohomologyPushforward` — the functor `F ↦ i_*ℋ^n_Z(F)`.
* `AlgebraicGeometry.complementHigherDirectImage` — the functor `F ↦ R^n j_*(F|_U)`.
* `AlgebraicGeometry.supportedSectionsDelta` — the connecting natural transformation
  `R^n(j_*(-|_U)) ⟶ R^{n+1}(i_*ℋ_Z)` of the long exact sequence.
* `AlgebraicGeometry.CohomologyWithSupportSequences` — the three assertions of
  [Stacks, Tag 0A45], as a structure.

## Main results

* `AlgebraicGeometry.exact_supportedSections_composableArrows₅` — every six-term window of the
  long exact sequence of right derived functors of `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)` is exact.
* `AlgebraicGeometry.exists_fourTerm_exact_supportedSections` — the four-term exact sequence.
* `AlgebraicGeometry.complementHigherDirectImageIso` — the higher direct images.
* `AlgebraicGeometry.exists_distTriang_supportedSections` — the distinguished triangle.
* `AlgebraicGeometry.cohomologyWithSupportSequences` — **[Stacks, Tag 0A45]**, all three
  assertions.

## Implementation notes

The triangle is the distinguished triangle of the short complex of endofunctors
`i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`, which is short exact on injective objects: applying the three
functors degreewise to a K-injective resolution gives a short exact sequence of complexes,
whose triangle is transported to any chosen triple of right derived functors.  That is the
general `Stacks.ShortExactOnInjectives.exists_derivedTriangle_of_shortExactOnInjectives`, and
it also supplies the two canonical maps of the triangle together with the factorizations that
pin them down as the derived versions of `i_*ℋ_Z ⟶ 𝟭` and `𝟭 ⟶ j_*(-|_U)`.  The triangle is
stated for an *arbitrary* triple of right derived functors, as the same statement for sheaves of
modules on a ringed space is ([Stacks, Tag 0G72],
`Stacks.Cohomology.SupportedComplexes.exists_derivedSupportedSectionsTriangle`), so that it
applies to every model of `i_*Rℋ_Z` and of `Rj_*(-|_U)`.

Both assertions are read off the long exact sequence of right derived functors of the short
complex of endofunctors `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`, which is short exact at every injective
abelian sheaf (`AlgebraicGeometry.supportedSectionsShortComplex_shortExact_of_injective`);
the machine is
`CategoryTheory.longExact_rightDerived_of_shortExact_on_injectives`, whose named connecting
transformation is `CategoryTheory.rightDerivedDelta`.  What makes the sequence collapse to the
two assertions of the source is that the higher right derived functors of the identity functor
vanish (`CategoryTheory.isZero_rightDerived_id_obj`): in degree `0` the window becomes the
four-term sequence, and in degrees `≥ 1` the connecting morphism has zero on both sides, so it
is an isomorphism (`CategoryTheory.ComposableArrows.Exact.isIso_map'`).

The three functors of the sequence are left exact, so in degree zero their right derived
functors are themselves and the derived maps in degree zero are the original maps
`i_*ℋ_Z(F) ⟶ F` and `F ⟶ j_*(F|_U)`; that is
`AlgebraicGeometry.rightDerived_supportedSectionsPushforwardInclusion_zero` and
`AlgebraicGeometry.rightDerived_complementRestriction_zero`.  The two identifications
`R^n(i_*ℋ_Z) ≅ i_*(R^nℋ_Z)` and `R^n(j_*(-|_U)) ≅ (R^n j_*)(-|_U)` are
`AlgebraicGeometry.supportedSectionsPushforwardRightDerivedIso` and
`AlgebraicGeometry.complementRestrictPushRightDerivedIso`.

`R^n` is Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` here; the comparison with
the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus` in which
`AlgebraicGeometry.isZero_rightDerivedPlus_supportedSections_pushforward` ([Stacks, Tag 09XR])
is stated is `Stacks.DerivedIndexing.rightDerivedIso`.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- `i_*ℋ^n_Z`, the `n`-th cohomology sheaf with support in the closed subscheme, pushed
forward to the ambient small étale site. -/
public abbrev supportedCohomologyPushforward (n : ℕ) :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B X :=
  (supportedSections B i).rightDerived n ⋙ smallEtaleClosedPushforward B i

/-- `R^n j_*(-|_U)`, the `n`-th higher direct image along the inclusion of the open complement
of the restriction to that complement. -/
public abbrev complementHigherDirectImage (n : ℕ) :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B X :=
  SmallEtale.openRestriction.{u, u + 1} B (closedComplementInclusion B i) ⋙
    (Stacks.HigherDirectImage.pushforward.{u, u + 1} B
      (closedComplementInclusion B i)).rightDerived n

/-- The connecting natural transformation `R^n(j_*(-|_U)) ⟶ R^{n+1}(i_*ℋ_Z)` of the long exact
sequence of cohomology with support. -/
public abbrev supportedSectionsDelta (n : ℕ) :
    (complementRestrictPush B i).rightDerived n ⟶
      (supportedSectionsPushforward B i).rightDerived (n + 1) :=
  CategoryTheory.rightDerivedDelta (supportedSectionsPushforwardInclusion B i)
    (complementRestriction B i)
    (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
    (supportedShortComplex_shortExact_on_injectives B i) n

/-- The six-term window of the long exact sequence of cohomology with support is exact. -/
public theorem exact_supportedSections_composableArrows₅ (n : ℕ)
    (F : SmallEtaleAbelianSheaf B X) :
    (ComposableArrows.mk₅
      ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) n).app F)
      ((NatTrans.rightDerived (complementRestriction B i) n).app F)
      ((supportedSectionsDelta B i n).app F)
      ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) (n + 1)).app F)
      ((NatTrans.rightDerived (complementRestriction B i) (n + 1)).app F)).Exact :=
  CategoryTheory.exact_rightDerived_composableArrows₅ _ _ _
    (supportedShortComplex_shortExact_on_injectives B i) (injectiveResolution F) n

/-! ### The higher direct images -/

/-- **Stacks 0A45, the higher direct images.**  For `p ≥ 1` the `p`-th higher direct image along
the inclusion `j` of the open complement of the restriction of `F` to that complement is the
direct image along `i` of the `(p+1)`-st cohomology sheaf of `F` with support in the closed
subscheme:

`R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)`,

naturally in `F`.  The comparison is the connecting morphism of the long exact sequence, which
in these degrees has zero on both sides because the higher right derived functors of the
identity vanish. -/
@[sga "4 XIX 3.2" "partial"]
public def complementHigherDirectImageIso (n : ℕ) :
    complementHigherDirectImage B i (n + 1) ≅ supportedCohomologyPushforward B i (n + 2) := by
  haveI hiso : ∀ F : SmallEtaleAbelianSheaf B X,
      IsIso ((supportedSectionsDelta B i (n + 1)).app F) := fun F =>
    (exact_supportedSections_composableArrows₅ B i (n + 1) F).isIso_map' 1 (by omega)
      ((CategoryTheory.isZero_rightDerived_id_obj F n).eq_of_src _ 0)
      ((CategoryTheory.isZero_rightDerived_id_obj F (n + 1)).eq_of_tgt _ 0)
  haveI : IsIso (supportedSectionsDelta B i (n + 1)) := NatIso.isIso_of_isIso_app _
  exact (complementRestrictPushRightDerivedIso B i (n + 1)).symm ≪≫
    asIso (supportedSectionsDelta B i (n + 1)) ≪≫
      supportedSectionsPushforwardRightDerivedIso B i (n + 2)

/-! ### The four-term exact sequence -/

/-- **Stacks 0A45, the four-term exact sequence.**  There is a natural transformation
`δ : j_*(-|_U) ⟶ i_*ℋ¹_Z` for which

`0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0`

is exact at every abelian sheaf `F` on `X_étale`: the first map is a monomorphism, the sequence
is exact at `F` and at `j_*(F|_U)`, and `δ` is an epimorphism. -/
public theorem exists_fourTerm_exact_supportedSections :
    ∃ (δ : complementRestrictPush B i ⟶ supportedCohomologyPushforward B i 1)
      (hz : ∀ F : SmallEtaleAbelianSheaf B X,
        (complementRestriction B i).app F ≫ δ.app F = 0),
      ∀ F : SmallEtaleAbelianSheaf B X,
        Mono ((supportedSectionsPushforwardInclusion B i).app F) ∧
        (supportedSectionsShortComplex B i F).Exact ∧
        (ShortComplex.mk ((complementRestriction B i).app F) (δ.app F) (hz F)).Exact ∧
        Epi (δ.app F) := by
  have hβ := congr_app (rightDerived_complementRestriction_zero B i)
  simp only [NatTrans.comp_app] at hβ
  refine ⟨(complementRestrictPush B i).rightDerivedZeroIsoSelf.inv ≫
      supportedSectionsDelta B i 0 ≫ (supportedSectionsPushforwardRightDerivedIso B i 1).hom,
    fun F => ?_, fun F => ⟨?_, supportedSectionsShortComplex_exact B i F, ?_, ?_⟩⟩
  · have h1 : (complementRestriction B i).app F ≫
        (complementRestrictPush B i).rightDerivedZeroIsoSelf.inv.app F =
          (𝟭 (SmallEtaleAbelianSheaf B X)).rightDerivedZeroIsoSelf.inv.app F ≫
            (NatTrans.rightDerived (complementRestriction B i) 0).app F := by
      rw [← cancel_epi ((𝟭 (SmallEtaleAbelianSheaf B X)).rightDerivedZeroIsoSelf.hom.app F),
        ← Category.assoc, ← hβ F]
      simp
    have h2 : (NatTrans.rightDerived (complementRestriction B i) 0).app F ≫
        (supportedSectionsDelta B i 0).app F = 0 :=
      (exact_supportedSections_composableArrows₅ B i 0 F).toIsComplex.zero' 1 2 3
    simp only [NatTrans.comp_app]
    rw [reassoc_of% h1, reassoc_of% h2]
    simp
  · have hαF := congr_app (rightDerived_supportedSectionsPushforwardInclusion_zero B i) F
    simp only [NatTrans.comp_app] at hαF
    have h : (supportedSectionsPushforwardInclusion B i).app F =
        (supportedSectionsPushforward B i).rightDerivedZeroIsoSelf.inv.app F ≫
          (NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) 0).app F ≫
            (𝟭 (SmallEtaleAbelianSheaf B X)).rightDerivedZeroIsoSelf.hom.app F := by
      rw [hαF]
      simp
    have := CategoryTheory.mono_rightDerived_zero_app
      (supportedSectionsPushforwardInclusion B i) (complementRestriction B i)
      (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
      (supportedShortComplex_shortExact_on_injectives B i) F
    rw [h]
    infer_instance
  · refine ShortComplex.exact_of_iso (ShortComplex.isoMk
      ((𝟭 (SmallEtaleAbelianSheaf B X)).rightDerivedZeroIsoSelf.app F)
      ((complementRestrictPush B i).rightDerivedZeroIsoSelf.app F)
      ((supportedSectionsPushforwardRightDerivedIso B i 1).app F) ?_ ?_)
      ((exact_supportedSections_composableArrows₅ B i 0 F).exact' 1 2 3)
    · exact (hβ F).symm
    · simp
      rfl
  · have : Epi ((supportedSectionsDelta B i 0).app F) :=
      ((exact_supportedSections_composableArrows₅ B i 0 F).exact' 2 3 4).epi_f
        ((CategoryTheory.isZero_rightDerived_id_obj F 0).eq_of_tgt _ 0)
    simp only [NatTrans.comp_app]
    infer_instance

/-! ### The distinguished triangle -/

section Triangle

open CategoryTheory.Pretriangulated

variable [HasDerivedCategory.{u + 1} (SmallEtaleAbelianSheaf B X)]

/-- **Stacks 0A45, the distinguished triangle.**  Let `RH` be a right derived functor of
`F ↦ i_*ℋ_Z(F)` and `RJ` a right derived functor of `F ↦ j_*(F|_U)` on the unbounded derived
category of abelian sheaves on `X_étale`, and let `RI` be one of the identity.  The two
canonical natural transformations `i_*ℋ_Z ⟶ 𝟭` and `𝟭 ⟶ j_*(-|_U)` descend to maps
`rf : RH ⟶ RI` and `rg : RI ⟶ RJ` — pinned down by their composites with the comparison units
— and extend by a connecting map `δ : RJ ⟶ RH⟦1⟧` to a distinguished triangle

`i_*Rℋ_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ i_*Rℋ_Z(K)⟦1⟧`

at every object `K` of the derived category.  All three maps are natural transformations of
functors, so the triangle is functorial in `K`. -/
public theorem exists_distTriang_supportedSections
    (RH RI RJ : DerivedCategory (SmallEtaleAbelianSheaf B X) ⥤
      DerivedCategory (SmallEtaleAbelianSheaf B X))
    (aH : (supportedSectionsPushforward B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (aI : (𝟭 (SmallEtaleAbelianSheaf B X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RI)
    (aJ : (complementRestrictPush B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RJ)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))]
    [RI.IsRightDerivedFunctor aI
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))]
    [RJ.IsRightDerivedFunctor aJ
      (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ))] :
    ∃ (rf : RH ⟶ RI) (rg : RI ⟶ RJ)
      (δ : RJ ⟶ RH ⋙ shiftFunctor (DerivedCategory (SmallEtaleAbelianSheaf B X)) (1 : ℤ)),
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (supportedSectionsPushforwardInclusion B i) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ aI =
        aH ≫ Functor.whiskerLeft DerivedCategory.Qh rf ∧
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (complementRestriction B i) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ aJ =
        aI ≫ Functor.whiskerLeft DerivedCategory.Qh rg ∧
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
        distTriang (DerivedCategory (SmallEtaleAbelianSheaf B X)) :=
  Stacks.ShortExactOnInjectives.exists_derivedTriangle_of_shortExactOnInjectives
    (SmallEtaleAbelianSheaf B X) (supportedSectionsPushforward B i)
    (𝟭 (SmallEtaleAbelianSheaf B X)) (complementRestrictPush B i)
    (supportedSectionsPushforwardInclusion B i) (complementRestriction B i)
    (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
    (fun I _ => supportedSectionsShortComplex_shortExact_of_injective B i I) RH RI RJ aH aI aJ

/-! ### Stacks 0A45 -/

/-- The three assertions of **Stacks 0A45** for a closed immersion `i : Z ⟶ X` of schemes with
open complement `j : U ⟶ X`, on abelian sheaves of the small étale sites:

1. the distinguished triangle `i_*Rℋ_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ i_*Rℋ_Z(K)⟦1⟧` in
   `D(X_étale)`, for arbitrary right derived functors of `i_*ℋ_Z`, of the identity and of
   `j_*(-|_U)`, with the two canonical maps pinned down by their composites with the units;
2. the four-term exact sequence
   `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0`;
3. the isomorphisms `R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)` for `p ≥ 1`. -/
public structure CohomologyWithSupportSequences (B : BigEtaleSite.{u}) {Z X : B.Scheme}
    (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]
    [HasDerivedCategory.{u + 1} (SmallEtaleAbelianSheaf B X)] : Type (u + 2) where
  /-- **The distinguished triangle.**  For arbitrary right derived functors `RH` of
  `F ↦ i_*ℋ_Z(F)`, `RI` of the identity and `RJ` of `F ↦ j_*(F|_U)` on the unbounded derived
  category of abelian sheaves on `X_étale`, the two canonical natural transformations
  `i_*ℋ_Z ⟶ 𝟭` and `𝟭 ⟶ j_*(-|_U)` descend to maps `rf : RH ⟶ RI` and `rg : RI ⟶ RJ`, pinned
  down by their composites with the comparison units, and extend by a connecting map
  `δ : RJ ⟶ RH⟦1⟧` to a distinguished triangle at every object of the derived category. -/
  distinguishedTriangle : ∀ (RH RI RJ : DerivedCategory (SmallEtaleAbelianSheaf B X) ⥤
      DerivedCategory (SmallEtaleAbelianSheaf B X))
      (aH : (supportedSectionsPushforward B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
      (aI : (𝟭 (SmallEtaleAbelianSheaf B X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RI)
      (aJ : (complementRestrictPush B i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RJ),
      RH.IsRightDerivedFunctor aH
          (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ)) →
        RI.IsRightDerivedFunctor aI
          (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ)) →
        RJ.IsRightDerivedFunctor aJ
          (HomotopyCategory.quasiIso (SmallEtaleAbelianSheaf B X) (ComplexShape.up ℤ)) →
        ∃ (rf : RH ⟶ RI) (rg : RI ⟶ RJ)
          (δ : RJ ⟶ RH ⋙
            shiftFunctor (DerivedCategory (SmallEtaleAbelianSheaf B X)) (1 : ℤ)),
          Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (supportedSectionsPushforwardInclusion B i) (ComplexShape.up ℤ))
              DerivedCategory.Qh ≫ aI =
            aH ≫ Functor.whiskerLeft DerivedCategory.Qh rf ∧
          Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (complementRestriction B i) (ComplexShape.up ℤ))
              DerivedCategory.Qh ≫ aJ =
            aI ≫ Functor.whiskerLeft DerivedCategory.Qh rg ∧
          ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
            distTriang (DerivedCategory (SmallEtaleAbelianSheaf B X))
  /-- **The four-term exact sequence.**  There is a natural transformation
  `δ : j_*(-|_U) ⟶ i_*ℋ¹_Z` for which `0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0` is
  exact at every abelian sheaf `F` on `X_étale`. -/
  fourTermExact : ∃ (δ : complementRestrictPush B i ⟶ supportedCohomologyPushforward B i 1)
      (hz : ∀ F : SmallEtaleAbelianSheaf B X,
        (complementRestriction B i).app F ≫ δ.app F = 0),
      ∀ F : SmallEtaleAbelianSheaf B X,
        Mono ((supportedSectionsPushforwardInclusion B i).app F) ∧
        (supportedSectionsShortComplex B i F).Exact ∧
        (ShortComplex.mk ((complementRestriction B i).app F) (δ.app F) (hz F)).Exact ∧
        Epi (δ.app F)
  /-- **The higher direct images.**  For `p ≥ 1`, the `p`-th higher direct image along the
  inclusion of the open complement of the restriction there is the direct image along the closed
  immersion of the `(p+1)`-st cohomology sheaf with support, naturally in the sheaf. -/
  higherDirectImageIso : ∀ n : ℕ,
    complementHigherDirectImage B i (n + 1) ≅ supportedCohomologyPushforward B i (n + 2)

/-- **Stacks 0A45.**  Let `i : Z ⟶ X` be a closed immersion of schemes and let `j : U ⟶ X` be
the inclusion of the complement of `Z`.  For an abelian sheaf `F` on `X_étale` there is a
distinguished triangle

`i_*Rℋ_Z(F) ⟶ F ⟶ Rj_*(F|_U) ⟶ i_*Rℋ_Z(F)⟦1⟧`

in `D(X_étale)`, hence a four-term exact sequence

`0 ⟶ i_*ℋ_Z(F) ⟶ F ⟶ j_*(F|_U) ⟶ i_*ℋ¹_Z(F) ⟶ 0`

and isomorphisms `R^p j_*(F|_U) ≅ i_*ℋ^{p+1}_Z(F)` for `p ≥ 1`.

All three assertions are stated at once, as the three fields of
`AlgebraicGeometry.CohomologyWithSupportSequences`.  The triangle is given for an arbitrary
triple of right derived functors of `i_*ℋ_Z`, of the identity and of `j_*(-|_U)` on the whole
unbounded derived category, so it applies to every model of `i_*Rℋ_Z` and `Rj_*(-|_U)` and is
functorial in the object; the other two assertions are given at every abelian sheaf, naturally
in it.  The open complement `U` and its inclusion `j` are constructed from `i` rather than
assumed.

`R^p` is Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`; the comparison with the
`ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus` of
`AlgebraicGeometry.isZero_rightDerivedPlus_supportedSections_pushforward` ([Stacks, Tag 09XR])
is `Stacks.DerivedIndexing.rightDerivedIso`. -/
@[stacks 0A45]
public def cohomologyWithSupportSequences : CohomologyWithSupportSequences B i where
  distinguishedTriangle RH RI RJ aH aI aJ hH hI hJ :=
    haveI := hH; haveI := hI; haveI := hJ
    exists_distTriang_supportedSections B i RH RI RJ aH aI aJ
  fourTermExact := exists_fourTerm_exact_supportedSections B i
  higherDirectImageIso n := complementHigherDirectImageIso B i n

end Triangle

end AlgebraicGeometry

end
