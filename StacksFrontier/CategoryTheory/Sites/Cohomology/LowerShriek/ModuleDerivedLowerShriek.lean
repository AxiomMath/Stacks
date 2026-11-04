module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AdjointExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroLowerShriekModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Cellular
import StacksCore.Tactic.StacksAttribute

/-!
# The derived lower shriek of modules along a continuous and cocontinuous functor

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g : Sh(C) ⟶ Sh(D)` be the
corresponding morphism of topoi, let `O_D` be a sheaf of rings on `D` and set
`O_C = g^{-1} O_D`. Stacks 07AC asserts that `g_! : Mod(O_C) ⥤ Mod(O_D)` has a left derived
functor `Lg_!`, left adjoint to `g^*`, with
`Lg_!(j_{U!} O_U) = g_! j_{U!} O_U = j_{u(U)!} O_{u(U)}`.

The library reduces the existence of `Lg_!` (by the criterion of Stacks 0794) and its adjointness
to one statement, the acyclicity of `g_!` on bounded above acyclic complexes of direct sums of the
`j_{U!} O_U`. As in the source, this file proves it from Stacks 0D6X: for an injective
`O_D`-module `I`, `Ext^n_{O_C}(j_{U!} O_U, g^{-1} I) = 0` for `n ≥ 1`. The Čech form of 0D6X
gives this vanishing on the underlying abelian sheaves, and Stacks 03FD over `U` identifies the
two `Ext` groups.

## Main results

All in the namespace `Stacks.Cohomology.DerivedLowerShriek`:

* `subsingleton_ext_freeAbelianSheaf_restriction`: Stacks 0D6X for an injective module, on the
  underlying abelian sheaves.
* `subsingleton_ext_sectionObject_restriction` and
  `extAcyclic_extensionByZeroUnit`: the same in the category of modules.
* `lowerShriekModules_acyclic`: the acyclicity statement.
* `isIso_derivedLowerShriekComparison_app`: `Lg_!` is computed degreewise on bounded above
  complexes of direct sums of the `j_{U!} O_U`.
* `derivedLowerShriek_spec`: **Stacks 07AC**.

## Implementation notes

The two sites, their morphisms, the sheaf of rings and the module sections are in one universe
`u`, the sites being small, as the sites of the source are. Continuity in the sense of the source
(Stacks 00WV) is `Functor.IsContinuous` together with its covering-pullback clause
`Stacks.Sites.PreservesCoveringPullbacks`; no fibre products are assumed in `D` beyond the ones
this clause provides. The sheaf of rings is commutative, as rings are in the source, and is read
as a sheaf of rings through `AlgebraicGeometry.RingedSite.ringSheaf`.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open StacksDraft.UnboundedLeftDerivedFunctor

universe u

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] [Stacks.Sites.PreservesCoveringPullbacks J f]
  (O : Sheaf K CommRingCat.{u})

/-- The ringed site `(D, O_D)`. -/
abbrev targetRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := D
  J := K
  O := O

omit [f.IsCocontinuous J K] in
/-- **Stacks 0D6X for an injective module, read on the underlying abelian sheaves.** -/
theorem subsingleton_ext_freeAbelianSheaf_restriction (U : C)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
    [Injective I] (n : ℕ)
    (hn : 0 < n) :
    Subsingleton (Ext ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free))
      ((f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).obj
        ((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj I)) n) := by
  set Cov : ∀ U : C, Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ J U } :=
    fun U => { E | (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ U), HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ U), PreservesLimit (cospan (E.1.f j) g) f) } with hCov
  have hProducts : ∀ {U : C} (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun b ↦ Over.mk (E.1.f (i b))) :=
    fun E hE q i => Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hImageProducts : ∀ {U : C}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → (E.1.map f).I₀),
        HasProduct (fun b ↦ Over.mk ((E.1.map f).f (i b))) := fun E hE q i => by
    have := hProducts E hE q i
    have := Stacks.Sites.preservesLimit_fibreProducts_overPost f E.1 hE.1 hE.2 q i
    have : HasLimit (Discrete.functor (fun b ↦ Over.mk (E.1.f (i b))) ⋙ Over.post f) :=
      HasLimit.mk ⟨_, isLimitOfPreserves (Over.post f) (limit.isLimit _)⟩
    exact hasLimit_of_iso
      (F := Discrete.functor (fun b ↦ Over.mk (E.1.f (i b))) ⋙ Over.post f)
      (G := Discrete.functor (fun b ↦ Over.mk ((E.1.map f).f (i b))))
      (Discrete.natIso fun _ => Iso.refl _)
  have hsub := Stacks.CechSite.injective_module_subsingleton_ext_of_functor.{u, u}
    (targetRingedSite K O) J f Set.univ Cov hProducts hImageProducts
    (fun E _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩)
    (fun U _ R hR => by
      obtain ⟨E, hJE, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J f R hR
      exact ⟨⟨E, hJE⟩, ⟨hpb, hpr⟩, hle⟩)
    (fun E hE q i => by
      let := hProducts E hE
      let := hImageProducts E hE
      let := Stacks.Sites.preservesLimit_fibreProducts_overPost f E.1 hE.1 hE.2 q i
      exact Stacks.CechSite.isIso_cechProductMapOfFunctor f E.1 q i)
    I U (Set.mem_univ _) n hn
  refine Stacks.Cohomology.subsingleton_ext_of_iso ?_ n hsub
  exact (presheafToSheaf J AddCommGrpCat.{u}).mapIso (Functor.isoWhiskerRight
    (NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift.symm) (fun _ => rfl))
    AddCommGrpCat.free)

omit [f.IsCocontinuous J K] in
/-- **Stacks 0D6X for an injective module, read in the category of modules.** For an injective
`O_D`-module `I` and an object `U` of `C`, `Ext^n_{O_C}(j_{U!} O_U, g^{-1} I) = 0` for `n ≥ 1`.
The vanishing on the underlying abelian sheaves is
`subsingleton_ext_freeAbelianSheaf_restriction`, and the comparison of the two `Ext` groups is
Stacks 03FD over `U`. -/
theorem subsingleton_ext_sectionObject_restriction (U : C)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
    [Injective I] (n : ℕ)
    (hn : 0 < n) :
    Subsingleton (Ext (Stacks.Cohomology.ObjectSections.sectionObject J
        (inverseImageRing J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U)
      ((restrictionModules J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj I) n) := by
  set R := inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)
  have e := (ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free))
    (Stacks.Cohomology.ObjectSections.sectionObject J R U)
    (fun I _ n e => ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf J R I U n e)
    (ModuleSheafCohomology.tensorSheafHomIso J R _) n).app
      ((restrictionModules J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj I)
  exact e.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
    (subsingleton_ext_freeAbelianSheaf_restriction J K f O U I n hn)

section Spelling

variable (R : Sheaf J RingCat.{u}) (U : C)

/-- Morphisms out of `O ⊗ ℤ[h_U]` are the sections over `U`, as a functor of the module. -/
def sectionObjectCorepresentation :
    coyoneda.obj (op (Stacks.Cohomology.ObjectSections.sectionObject J R U)) ≅
      SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op U) ⋙
        forget AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight (ModuleSheafCohomology.tensorSheafHomIso J R
      (yoneda.obj U ⋙ AddCommGrpCat.free) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
      (ModuleSheafCohomology.evaluationRepresentation J U).symm) (forget AddCommGrpCat.{u})

/-- Morphisms out of `j_{U!} O_U` are the sections over `U`, as a functor of the module
(Stacks 0G1V). -/
def extensionByZeroUnitCorepresentation :
    coyoneda.obj (op (extensionByZeroUnit R U)) ≅
      SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op U) ⋙
        forget AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun M => Equiv.toIso (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U M))
    (fun {M N} g => by
      ext φ
      exact Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality J R U φ g)

/-- The two spellings of `j_{U!} O_U` agree: both corepresent the sections over `U`. -/
def sectionObjectIsoExtensionByZeroUnit :
    Stacks.Cohomology.ObjectSections.sectionObject J R U ≅ extensionByZeroUnit R U :=
  (Coyoneda.fullyFaithful.preimageIso
    (sectionObjectCorepresentation J R U ≪≫
      (extensionByZeroUnitCorepresentation J R U).symm)).unop.symm

end Spelling

omit [f.IsCocontinuous J K] in
/-- **The generators `j_{U!} O_U` are `Ext`-acyclic for `g_! ⊣ g^{-1}`**: `Ext^n_{O_C}(j_{U!} O_U,
g^{-1} I) = 0` for every injective `O_D`-module `I` and every `n ≥ 1`. -/
theorem extAcyclic_extensionByZeroUnit (U : C) :
    (adjunctionModules J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).extAcyclic
      (extensionByZeroUnit (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U) :=
  fun I _ n hn => Stacks.Cohomology.subsingleton_ext_of_iso
    (sectionObjectIsoExtensionByZeroUnit J _ U).symm n
    (subsingleton_ext_sectionObject_restriction J K f O U I n hn)

omit [f.IsCocontinuous J K] in
/-- **The acyclicity statement of Stacks 07AC for modules.** The lower-shriek functor
`g_! : Mod(O_C) ⥤ Mod(O_D)` carries every bounded above acyclic complex whose terms are direct
sums of the `j_{U!} O_U` to an acyclic complex. As in the source, this is the `Ext`-acyclicity of
the generators for the adjunction `g_! ⊣ g^{-1}`, `extAcyclic_extensionByZeroUnit`, which is
Stacks 0D6X. -/
theorem lowerShriekModules_acyclic (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u}
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, IsSumOfExtensionByZeroUnits
      (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (L.X n))
    (hLac : L.Acyclic) :
    (((SheafOfModules.pullback.{u}
      (idRingMap J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).Acyclic := by
  refine (adjunctionModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).map_acyclic_of_extAcyclic
    L a hLac fun n => ?_
  obtain ⟨ι, U, ⟨e⟩⟩ := hLP n
  exact (adjunctionModules J K f _).extAcyclic_of_iso e
    ((adjunctionModules J K f _).extAcyclic_coproduct _
      fun i => extAcyclic_extensionByZeroUnit J K f O (U i))

omit [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The class of direct sums of the `j_{U!} O_U` is closed under isomorphisms. -/
lemma isSumOfExtensionByZeroUnits_of_iso (R : Sheaf J RingCat.{u}) {M M' : SheafOfModules.{u} R}
    (hM : IsSumOfExtensionByZeroUnits R M) (e : M ≅ M') : IsSumOfExtensionByZeroUnits R M' := by
  obtain ⟨ι, U, ⟨e'⟩⟩ := hM
  exact ⟨ι, U, ⟨e' ≪≫ e⟩⟩

omit [Stacks.Sites.PreservesCoveringPullbacks J f] in
/-- The complex `j_{U!} O_U` placed in degree zero has its terms in the class of direct sums of
the `j_{V!} O_V`. -/
lemma isSumOfExtensionByZeroUnits_single (R : Sheaf J RingCat.{u}) (U : C) (n : ℤ) :
    IsSumOfExtensionByZeroUnits R
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (extensionByZeroUnit R U)).X n) := by
  by_cases hn : n = 0
  · subst hn
    exact isSumOfExtensionByZeroUnits_of_iso J R ⟨PUnit, fun _ => U, ⟨coproductUniqueIso _⟩⟩
      (HomologicalComplex.singleObjXSelf _ 0 _).symm
  · obtain ⟨Z, hZ, hPZ⟩ := (IsSumOfExtensionByZeroUnits R).exists_prop_of_containsZero
    exact isSumOfExtensionByZeroUnits_of_iso J R hPZ
      (hZ.iso (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC, existence**: the left derived functor `Lg_!` of lower shriek of modules
exists at every object. -/
instance hasPointwiseLeftDerivedFunctor_lowerShriekOnHomotopy :
    (lowerShriekOnHomotopy J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (sourceQuasiIso J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
  hasPointwiseLeftDerivedLowerShriek_of_acyclic_univLE J K f _ (lowerShriekModules_acyclic J K f O)

/-- `Lg_!` stays a left derived functor after composition with derived restriction, being
constructed by resolutions. -/
instance isLeftDerivedFunctor_derivedLowerShriek_comp_derivedRestriction :
    (derivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
      derivedRestriction J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
          (derivedLowerShriek J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
          (derivedRestriction J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))).inv ≫
        Functor.whiskerRight (derivedLowerShriekComparison J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
          (derivedRestriction J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)))
      (sourceQuasiIso J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic J K f _
    (lowerShriekModules_acyclic J K f O) _

/-- **`Lg_!` is computed degreewise on a bounded above complex of direct sums of the
`j_{U!} O_U`**: the counit `Lg_! ∘ Q ⟶ Q ∘ g_!` is invertible there, these complexes being
cellular for the class with which `Lg_!` is constructed (Stacks 0794). -/
lemma isIso_derivedLowerShriekComparison_app
    (L : CochainComplex (SheafOfModules.{u}
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) ℤ)
    [L.IsStrictlyLE 0]
    (hL : ∀ n, IsSumOfExtensionByZeroUnits
      (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) (L.X n)) :
    IsIso ((derivedLowerShriekComparison J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u}
    (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))) :=
    hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
    hasExactColimitsOfShape_nat _
  have : PreservesColimitsOfShape ℕ (lowerShriekModules J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      (adjunctionModules J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))).preservesColimitsOfShape
  have h := derives_cellularLocalizerMorphism
    (lowerShriekModules J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
    (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)))
    (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
    (fun M => exists_epi_isSumOfExtensionByZeroUnits _ M) (lowerShriekModules_acyclic J K f O)
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism
    _ (hasLeftResolutions_cellularLocalizerMorphism
      (IsSumOfExtensionByZeroUnits (inverseImageRing J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)))
      (fun _ _ => isSumOfExtensionByZeroUnits_biprod _)
      (fun M => exists_epi_isSumOfExtensionByZeroUnits _ M))
  exact CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ h DerivedCategory.Qh _ _
    ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L,
      ⟨L, CochainComplex.isPCellular_of_isStrictlyLE _ L hL, ⟨Iso.refl _⟩⟩⟩

/-- `Lg_!(j_{U!} O_U) = g_! j_{U!} O_U`: the first equality of the displayed chain of Stacks 07AC.
`j_{U!} O_U` placed in degree zero is a bounded above complex of direct sums of the `j_{V!} O_V`,
on which the counit of `Lg_!` is invertible. -/
def derivedLowerShriekSingleExtensionByZeroUnitIso (U : C) :
    (derivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit
          (inverseImageRing J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerShriekModules J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj
          (extensionByZeroUnit (inverseImageRing J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U)) :=
  have := isIso_derivedLowerShriekComparison_app J K f O
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (extensionByZeroUnit
      (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U))
    (isSumOfExtensionByZeroUnits_single J _ U)
  (derivedLowerShriek J K f
    (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
    asIso ((derivedLowerShriekComparison J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (extensionByZeroUnit
          (inverseImageRing J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U)))) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (lowerShriekModules J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
        (ComplexShape.up ℤ) 0).app _)

/-- **Stacks 07AC.** Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let
`g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi, let `O_D` be a sheaf of rings on `D`
and set `O_C = g^{-1} O_D`. Then the functor `g_! : Mod(O_C) ⥤ Mod(O_D)` of Stacks 0797 has a
left derived functor `Lg_! : D(O_C) ⥤ D(O_D)`, which is left adjoint to `g^*`, and for every
object `U` of `C`

`Lg_!(j_{U!} O_U) = g_! j_{U!} O_U = j_{u(U)!} O_{u(U)}`.

Continuity of `u` in the sense of the source (Stacks 00WV) is `Functor.IsContinuous` together with
its covering-pullback clause `Stacks.Sites.PreservesCoveringPullbacks`. The derived functor is
`derivedLowerShriek`, the total left derived functor of `SheafOfModules.pullback` along the
identity of `O_C`, which is the lower shriek of Stacks 0797 up to the canonical isomorphism
`Stacks.SheafOfModules.lowerShriekIsoPullback`; `g^*` on derived categories is
`derivedRestriction`, induced by the exact restriction functor. -/
@[stacks 07AC]
theorem derivedLowerShriek_spec :
    (lowerShriekOnHomotopy J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) ∧
    (derivedLowerShriek J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).IsLeftDerivedFunctor
      (derivedLowerShriekComparison J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O))
      (sourceQuasiIso J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) ∧
    Nonempty (derivedLowerShriek J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⊣
      derivedRestriction J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) ∧
    ∀ U : C,
      Nonempty ((derivedLowerShriek J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit
            (inverseImageRing J K f
              (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U)) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((Stacks.SheafOfModules.lowerShriek.{u} J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj
            (extensionByZeroUnit (inverseImageRing J K f
              (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U))) ∧
      Nonempty ((Stacks.SheafOfModules.lowerShriek.{u} J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).obj
          (extensionByZeroUnit (inverseImageRing J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) U) ≅
        extensionByZeroUnit
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) (f.obj U)) :=
  ⟨inferInstance, inferInstance,
    ⟨derivedLowerShriekAdjunction J K f
      (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)⟩,
    fun U => ⟨⟨derivedLowerShriekSingleExtensionByZeroUnitIso J K f O U ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((Stacks.SheafOfModules.lowerShriekIsoPullback.{u} J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).app _).symm⟩,
      ⟨lowerShriekExtensionByZeroUnitIso J K f
        (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) U⟩⟩⟩

end Derived

end Stacks.Cohomology.DerivedLowerShriek

end
