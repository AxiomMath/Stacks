module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullbackSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticKernelOfFlatRestrictionLargeSections

/-!
# Stacks 07B9 (2)(c), 07BA and 0H11 at module universe `u + 1`

Let `𝒳` be an algebraic stack, `g^*` restriction of modules from the fppf site to the flat-fppf
site at module universe `u + 1` (`AlgebraicGeometry.Stack.FlatFppf.moduleInverseImage`) and
`Lg_!` its derived left adjoint (`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriekSucc`,
**Stacks 07AS** (4) at that universe), and `LQCoh^fbc(𝒪_𝒳)` the faithful class of **Stacks 0762**
at that universe (`AlgebraicGeometry.Stack.FlatFppf.sheafFlatBaseChangeModulesSucc`).

Module universe `u + 1` is where the quasi-coherent objects `QC(𝒳)` of **Stacks 0H0X**, the
derived direct image of **Stacks 07BC** and the module case of **Stacks 07AV** live. This file
gives there the statements which are registered at module universe `u`:

* **Stacks 07B9** (2)(c): `Lg_!` carries `D_QCoh(𝒪_{𝒳_{flat,fppf}})` into `D_{LQCoh^fbc}(𝒪_𝒳)`.
  The dévissage is
  `AlgebraicGeometry.Stack.FlatFppf.derivedCategoryB_derivedModuleLowerShriekSucc_of_single`;
  its inputs are **Stacks 0771** (5) at `u + 1` (in `AlgebraicGeometry.Stack`,
  `isClosedUnderColimitsOfShape_nat_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc`),
  **Stacks 0771** (2) at `u + 1` and **Stacks 07B3** (2) at `u + 1`
  (`AlgebraicGeometry.Stack.FlatFppf.derivedCategoryB_derivedModuleLowerShriekSucc_singleFunctor`).
* **Stacks 07BA**: the orthogonality, the cone and the triangle `Lg_! g^* E ⟶ E ⟶ P ⟶`, as
  instances of the category-theoretic statements of `DerivedCategory.KernelColocalization` (its
  canonicity is `CategoryTheory.Pretriangulated.exists_iso_of_leftOrthogonal`, and its form as
  a colocalization is
  `AlgebraicGeometry.Stack.FlatFppf.hasColocalizations_sheafFlatBaseChangeModulesSucc`).
* **Stacks 0H11**: `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is left admissible in
  `D_{LQCoh^fbc}(𝒪_𝒳)`, its left orthogonal `𝒜` is right admissible, `𝒜 ⟶ D_QCoh(𝒪_𝒳)` is an
  equivalence, and `𝒜` is a strictly full saturated triangulated subcategory of
  `D_{LQCoh^fbc}(𝒪_𝒳)` and of `D(𝒳_{fppf}, 𝒪_𝒳)`.

`D_QCoh(𝒪_𝒳)` is the Verdier quotient `D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of
**Stacks 07B6**, `DerivedCategory.KernelColocalization.quotient`, which is the quotient at which
**Stacks 07BE** and **Stacks 07B7** are stated at module universe `u + 1`.

The statements that use **Stacks 07B3** (2) are at the standard models of the derived categories,
the only models at which it is proved at module universe `u + 1`; they name the models with
`letI`. No `@[stacks]` attribute is claimed: these tags are registered at module universe `u`.

## References

* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 0H11](https://stacks.math.columbia.edu/tag/0H11)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory.KernelColocalization

universe u w t t'

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

-- the abelian structure and enough injectives of the library on sheaves of modules whose
-- sections contain the site would be met first by instance search here, with a universe
-- constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections
  hasSheafify_fppfTopology_largeSections wEqualsLocallyBijective_fppfTopology_largeSections
  hasPointwiseRightKanExtension_inclusion_ringCat_largeSections
  hasPointwiseRightKanExtension_inclusion_addCommGrpCat_largeSections

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-! ### Stacks 07B9 (2)(c) -/

/-- **Stacks 07B9** (2)(c) at module universe `u + 1`: `Lg_!` carries
`D_QCoh(𝒪_{𝒳_{flat,fppf}})` into `D_{LQCoh^fbc}(𝒪_𝒳)`, for the derived lower shriek of
Stacks 07AS (4) and the faithful class of Stacks 0762 at that universe, at the standard models of
the derived categories. The dévissage reduces it to a quasi-coherent module in degree `0`, which is
Stacks 07B3 (2); `LQCoh^fbc(𝒪_𝒳)` is weak Serre and closed under colimits of sequences
(Stacks 0771 (2), (5)). -/
theorem derivedCategoryB_derivedModuleLowerShriekSucc :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ∀ H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳) H →
        DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
          ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H) :=
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  derivedCategoryB_derivedModuleLowerShriekSucc_of_single B S hS 𝒳 _
    (fun F hF => ObjectProperty.prop_colimit _ F hF)
    (derivedCategoryB_derivedModuleLowerShriekSucc_singleFunctor B E h S hS 𝒳)

/-- **Stacks 07B9** (2)(a) followed by (2)(c) at module universe `u + 1`: for `K` in
`D_{LQCoh^fbc}(𝒪_𝒳)`, `Lg_! g^* K` lies in `D_{LQCoh^fbc}(𝒪_𝒳)` again, at the standard models of
the derived categories. -/
theorem derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage_sheafFlatBaseChange :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ∀ K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K →
        DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
          ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
            ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K)) :=
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  fun K hK => derivedCategoryB_derivedModuleLowerShriekSucc B E h S hS 𝒳 _
    (derivedCategoryB_moduleInverseImage_mapDerivedCategory B S hS 𝒳 _
      (fun F hF => isQuasicoherentOnSite_moduleInverseImage_of_sheafFlatBaseChangeModulesSucc
        B E h S hS 𝒳 F hF) K hK)

/-! ### Stacks 07BA -/

section AnyModels

variable [HasDerivedCategory.{t} (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{t'} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))]

/-- **Stacks 07BA** at module universe `u + 1`, the orthogonality:
`Hom(Lg_! g^* E, P') = Hom(g^* E, g^* P') = 0` for every `P'` in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, `g^*` killing it by Stacks 07B9 (2)(b); for any models of the
derived categories. -/
theorem leftOrthogonal_derivedModuleLowerShriekSucc_moduleInverseImage
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) :
    (derivedInter (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).leftOrthogonal
      ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
        ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K)) :=
  leftOrthogonal_obj_counit _ _ (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)
    (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳) K

end AnyModels

/-- **Stacks 07BA** at module universe `u + 1`, the cone: for `E` in `D_{LQCoh^fbc}(𝒪_𝒳)`, every
cone `P` on the counit `Lg_! g^* E ⟶ E` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, at the standard
models of the derived categories. -/
theorem derivedInter_obj₃_of_distTriang_derivedModuleLowerShriekSuccAdjunction_counit :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ∀ K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K →
      ∀ (P : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
        (b : K ⟶ P) (c : P ⟶ ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K))⟦(1 : ℤ)⟧),
        Triangle.mk ((derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).counit.app K) b c ∈
          distTriang
            (DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) →
        derivedInter (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) P :=
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  fun K hK P b c hT => derivedInter_obj₃_of_distTriang _ _
    (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)
    (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳)
    (isIso_derivedModuleLowerShriekSuccAdjunction_unit B S hS 𝒳) K hK
    (derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage_sheafFlatBaseChange
      B E h S hS 𝒳 K hK) P b c hT

/-- **Stacks 07BA** at module universe `u + 1`: every `E` in `D_{LQCoh^fbc}(𝒪_𝒳)` sits in a
distinguished triangle `E' ⟶ E ⟶ P ⟶ E'[1]` with `E' = Lg_! g^* E` and `E' ⟶ E` the counit,
`E'` in `D_{LQCoh^fbc}(𝒪_𝒳)` and left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, and `P` in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, at the standard models of the derived categories. -/
theorem exists_distTriang_derivedModuleLowerShriekSuccAdjunction_counit :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ∀ K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K →
      ∃ (P : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
        (b : K ⟶ P) (c : P ⟶ ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
          ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K))⟦(1 : ℤ)⟧),
        Triangle.mk ((derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).counit.app K) b c ∈
            distTriang
              (DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))) ∧
          DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)
            ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
              ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K)) ∧
          derivedInter (parasiticModulesSucc B S hS 𝒳)
            (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) P ∧
          (derivedInter (parasiticModulesSucc B S hS 𝒳)
            (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).leftOrthogonal
            ((derivedModuleLowerShriekSucc B S hS 𝒳).obj
              ((moduleInverseImage B S hS 𝒳).mapDerivedCategory.obj K)) :=
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  fun K hK => by
    obtain ⟨P, b, c, hT⟩ :=
      distinguished_cocone_triangle ((derivedModuleLowerShriekSuccAdjunction B S hS 𝒳).counit.app K)
    exact ⟨P, b, c, hT,
      derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage_sheafFlatBaseChange
        B E h S hS 𝒳 K hK,
      derivedInter_obj₃_of_distTriang_derivedModuleLowerShriekSuccAdjunction_counit
        B E h S hS 𝒳 K hK P b c hT,
      leftOrthogonal_derivedModuleLowerShriekSucc_moduleInverseImage B E h S hS 𝒳 K⟩

/-! ### Stacks 0H11 -/

/-- The four assertions of Stacks 0H11 at module universe `u + 1`, from the generic statements of
`DerivedCategory.KernelColocalization` at the actual `Lg_!`. -/
private lemma admissibilitySucc :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (interIn (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsLeftAdmissible ∧
      ((interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsRightAdmissible ∧
        interIn (parasiticModulesSucc B S hS 𝒳) (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) =
          (interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
            (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).rightOrthogonal) ∧
      ((interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).ι ⋙
        toQuotient (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsEquivalence ∧
      (interLeftOrthogonalToClass (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) ⋙
        toQuotient (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsEquivalence := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  have hG := isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳
  have hunit := isIso_derivedModuleLowerShriekSuccAdjunction_unit B S hS 𝒳
  have hshriek :=
    derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage_sheafFlatBaseChange
      B E h S hS 𝒳
  exact ⟨isLeftAdmissible_interIn _ _ (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)
      hG hunit hshriek,
    isRightAdmissible_interLeftOrthogonalIn _ _ (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)
      hG hunit hshriek,
    isEquivalence_interLeftOrthogonalIn_ι_comp _ _
      (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳) hG hunit hshriek,
    isEquivalence_interLeftOrthogonalToClass_comp _ _
      (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳) hG hunit hshriek⟩

/-- **Stacks 0H11** at module universe `u + 1`, first assertion:
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊂ D_{LQCoh^fbc}(𝒪_𝒳)` is left admissible. -/
theorem interIn_parasiticModulesSucc_isLeftAdmissible :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (interIn (parasiticModulesSucc B S hS 𝒳)
      (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsLeftAdmissible :=
  (admissibilitySucc B E h S hS 𝒳).1

/-- **Stacks 0H11** at module universe `u + 1`, second assertion: the left orthogonal `𝒜` of
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is right admissible in `D_{LQCoh^fbc}(𝒪_𝒳)`, and
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` is the right orthogonal of `𝒜`. -/
theorem interLeftOrthogonalIn_parasiticModulesSucc_isRightAdmissible :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsRightAdmissible ∧
      interIn (parasiticModulesSucc B S hS 𝒳) (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) =
        (interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
          (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).rightOrthogonal :=
  (admissibilitySucc B E h S hS 𝒳).2.1

/-- **Stacks 0H11** at module universe `u + 1`, third assertion: the composition
`𝒜 ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` of the inclusion with the Verdier quotient functor of
Stacks 07B6 is an equivalence. -/
theorem interLeftOrthogonalIn_parasiticModulesSucc_ι_comp_isEquivalence :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    ((interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).ι ⋙
      toQuotient (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsEquivalence :=
  (admissibilitySucc B E h S hS 𝒳).2.2.1

/-- **Stacks 0H11** at module universe `u + 1`, last assertion inside `D_{LQCoh^fbc}(𝒪_𝒳)`: `𝒜`
is a strictly full saturated triangulated subcategory. -/
theorem interLeftOrthogonalIn_parasiticModulesSucc_isSaturated :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsClosedUnderIsomorphisms ∧
      (interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsSaturated ∧
      (interLeftOrthogonalIn (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsTriangulated :=
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
  isSaturated_interLeftOrthogonalIn _ _ (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳)
    (isZero_moduleInverseImage_mapDerivedCategory_iff_forall_isParasitic B S hS 𝒳)
    (isIso_derivedModuleLowerShriekSuccAdjunction_unit B S hS 𝒳)
    (derivedCategoryB_derivedModuleLowerShriekSucc_moduleInverseImage_sheafFlatBaseChange
      B E h S hS 𝒳)

/-- **Stacks 0H11** at module universe `u + 1`, last assertion inside `D(𝒳_{fppf}, 𝒪_𝒳)`: `𝒜`
read there is a strictly full saturated triangulated subcategory, for any model of the derived
category. -/
theorem interLeftOrthogonal_parasiticModulesSucc_isSaturated
    [HasDerivedCategory.{t'} (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))] :
    (interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsClosedUnderIsomorphisms ∧
      (interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsSaturated ∧
      (interLeftOrthogonal (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsTriangulated :=
  isSaturated_interLeftOrthogonal _ _

/-- **Stacks 0H11** at module universe `u + 1`, the realization of `D_QCoh(𝒪_𝒳)` inside
`D(𝒳_{fppf}, 𝒪_𝒳)`: the inclusion of `𝒜`, presented as a subcategory of `D(𝒳_{fppf}, 𝒪_𝒳)`,
followed by the Verdier quotient functor of Stacks 07B6 is an equivalence. -/
theorem interLeftOrthogonalToClass_parasiticModulesSucc_comp_isEquivalence :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (interLeftOrthogonalToClass (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) ⋙
      toQuotient (parasiticModulesSucc B S hS 𝒳)
        (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳)).IsEquivalence :=
  (admissibilitySucc B E h S hS 𝒳).2.2.2

end AlgebraicGeometry.Stack.FlatFppf

end
