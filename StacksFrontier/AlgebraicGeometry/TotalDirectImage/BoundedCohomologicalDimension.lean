module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.BasisVanishing
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.PreimageSectionsVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyPresheafSheafification
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# Bounded cohomological dimension of a quasi-compact quasi-separated morphism

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. There is an integer `N`, depending only on `f`, such that for every object `E` of
the unbounded derived category of `𝒪_X`-modules with quasi-coherent cohomology sheaves and
`H^m(E) = 0` for `m > 0` one has `H^m(Rf_* E) = 0` for `m ≥ N`.

## Main results

* `AlgebraicGeometry.isZero_homology_derivedPushforward_of_isBasis`: for an arbitrary morphism
  `f`, if the higher cohomology of quasi-coherent `𝒪_X`-modules over the preimages of a basis of
  the opens of `S` vanishes from degree `N` onwards, then `H^m(Rf_* E) = 0` for `m ≥ b + N` and
  every `E` with quasi-coherent cohomology sheaves and `H^m(E) = 0` for `m > b`.
* `AlgebraicGeometry.exists_isZero_homology_derivedPushforward_of_isLE_zero`: the uniform upper
  bound on the cohomology sheaves of a derived direct image.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.OpenSubspace (derivedSectionsOnOpen)
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedMapDerivedCategoryIso)
open Stacks.Cohomology.CohomologyPresheaf (cohomologyPresheaf cohomologyPresheafEvaluationIso
  sheafificationCohomologyPresheafIso)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- Sections over `f⁻¹ V` of an `𝒪_X`-module, as an abelian group. -/
private abbrev sectionsOnPreimageGroup : X.Modules ⥤ AddCommGrpCat.{u} :=
  secF.{u, u, u} X.ringCatSheaf (f ⁻¹ᵁ V)

private instance sectionsOnPreimageGroup_additive :
    (sectionsOnPreimageGroup f V).Additive :=
  ⟨by intros; rfl⟩

/-- Sections over `f⁻¹ V` commute with countable products. -/
private instance sectionsOnPreimageGroup_preservesCountableProducts :
    PreservesLimitsOfShape (Discrete ℕ) (sectionsOnPreimageGroup f V) :=
  inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
    (SheafOfModules.evaluation X.ringCatSheaf (op (f ⁻¹ᵁ V)) ⋙
      forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V)))) AddCommGrpCat.{u}))

/-- The unbounded total right derived functor `R Γ(f⁻¹ V, -) : D(𝒪_X) ⥤ D(Ab)` of the
abelian-group-valued sections over `f⁻¹ V`. -/
private abbrev derivedSectionsOnPreimageGroup :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  ((sectionsOnPreimageGroup f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- Derived abelian-group-valued sections over `V` of a derived direct image agree with derived
sections over `f⁻¹ V`, as functors `D(𝒪_X) ⥤ D(Ab)`. -/
private def derivedSectionsOnPreimageGroupIso :
    derivedSectionsOnPreimageGroup f V ≅
      derivedPushforward f.toLRSHom.toShHom ⋙ derivedSectionsOnOpen S.ringCatSheaf V :=
  (totalRightDerivedMapDerivedCategoryIso (preimageSections f.toLRSHom.toShHom V)
      (forget₂ (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u})).symm ≪≫
    Functor.isoWhiskerRight (derivedSectionsPushforwardIso f.toLRSHom.toShHom V).symm
      ((forget₂ (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u}).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft (derivedPushforward f.toLRSHom.toShHom)
      (totalRightDerivedMapDerivedCategoryIso (sectionsOverOpen S.toRingedSpace V)
        (forget₂ (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
          AddCommGrpCat.{u}))

/-- Let `f : X ⟶ S` be a morphism of schemes, let `B` be a basis of the opens of `S` and let `N`
be a degree from which the higher cohomology of every quasi-coherent `𝒪_X`-module over `f⁻¹ V`
vanishes, for every `V ∈ B`. Then `H^m(Rf_* E) = 0` for `m ≥ b + N` and every `E` in `D(𝒪_X)`
with quasi-coherent cohomology sheaves living in degrees `≤ b`. -/
theorem isZero_homology_derivedPushforward_of_isBasis {N : ℕ} {B : Set S.Opens}
    (hB : Opens.IsBasis B)
    (hvan : ∀ V ∈ B, ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
      IsZero (((secF.{u, u, u} X.ringCatSheaf (f ⁻¹ᵁ V)).rightDerivedPlus p).obj M))
    (E : DerivedCategory.{u + 1} X.Modules)
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) (m : ℤ) (hm : b + (N : ℤ) ≤ m) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules m).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj E)) := by
  set O := S.ringCatSheaf
  set K := (derivedPushforward f.toLRSHom.toShHom).obj E
  have hPre (W) (hW : W ∈ B) : IsZero ((cohomologyPresheaf O K m).presheaf.obj (op W)) := by
    have h := isLE_rightDerivedFunctor_obj_addCommGrpCat X (sectionsOnPreimageGroup f W)
      (derivedSectionsOnPreimageGroup f W)
      (((sectionsOnPreimageGroup f W).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
      N (fun M hM p hp ↦ hvan W hW M hM p hp) E hcoh b hE
    have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
        ((derivedSectionsOnPreimageGroup f W).obj E)) :=
      DerivedCategory.isZero_of_isLE _ (b + (N : ℤ) - 1) m (by omega)
    exact (hz.of_iso (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).mapIso
      ((derivedSectionsOnPreimageGroupIso f W).app E)).symm)).of_iso
      ((cohomologyPresheafEvaluationIso O W m).app K)
  exact (Stacks.Topology.BasisVanishing.isZero_sheafification_of_isZero_on_basis
    (R := O) (cohomologyPresheaf O K m) hB hPre).of_iso
    ((sheafificationCohomologyPresheafIso O m).app K).symm

/-- Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. There is an integer `N`, depending only on `f`, such that every object `E` of
`D(𝒪_X)` with quasi-coherent cohomology sheaves and vanishing cohomology in positive degrees has
`H^m(Rf_* E) = 0` for all `m ≥ N`. -/
@[stacks 08D5 "bounded_cohomological_dimension"]
theorem exists_isZero_homology_derivedPushforward_of_isLE_zero
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, ∀ E : DerivedCategory.{u + 1} X.Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE 0 → ∀ m : ℤ, N ≤ m →
        IsZero ((DerivedCategory.homologyFunctor S.Modules m).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj E)) := by
  obtain ⟨N, B, hB, hvan⟩ := exists_isBasis_isZero_rightDerivedPlus_sectionsOnPreimage f
  exact ⟨(N : ℤ), fun E hcoh hE m hm ↦
    isZero_homology_derivedPushforward_of_isBasis f hB hvan E hcoh 0 hE m (by omega)⟩

end AlgebraicGeometry

end
