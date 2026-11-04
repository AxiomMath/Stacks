module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineStrictHenselizationFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveVanishingCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveVanishingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReductionUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreProjectiveLineInjective

/-!
# Higher direct images of injective `ℤ/ℓℤ`-modules along base changes of `ℙ¹` vanish

This is the last paragraph of the proof of the proper base change theorem
([Stacks, Tag 095T]): condition (2) of [Stacks, Tag 0A4B] holds for `ℙ¹_S ⟶ S`. For an injective
sheaf `I` of `ℤ/ℓℤ`-modules on `ℙ¹_S`, a base change `f' : X' ⟶ T` of `ℙ¹_S ⟶ S` along
`g : T ⟶ S` and a geometric point `t` of `T`, the stalk at `t` of `R^q f'_* (g')⁻¹I` is
`H^q(X' ×_T Spec(𝒪^{sh}_{T,t}), I|)` ([Stacks, Tag 03Q9]), which vanishes together with the
cohomology of `I` on the geometric fibre of `ℙ¹_S` at `g ∘ t` (Tags 0A5H, 0A5E), which vanishes
together with the stalk at `g ∘ t` of `R^q f_* I` (the same argument over `S` itself), which is
zero because `I` has no higher direct images ([Stacks, Tag 03FD]).

In `higherDirectImagesVanishOnInjectives_projectiveLine` the inputs Tag 03Q9 (`h03Q9`), Tag 0A5H
(`h0A5H`) and Tag 0A5E (`h0A5E`) are hypotheses. In
`isIso_etaleAbelianSheafDerivedBaseChange_of_isProper_of_inputs` Tag 0A5H and Tag 0A3U are
discharged, and only Tags 03Q9 and 0A5E remain as hypotheses.

## Main results

* `Stacks.EtaleCohomology.higherDirectImagesVanishOnInjectives_projectiveLine`
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper_of_inputs`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- `Ext`-groups of abelian sheaves on a small étale site exist in the universe `u + 1`. -/
local instance hasExt_smallEtale (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, 0}

/-- **Condition (2) of [Stacks, Tag 0A4B] for `ℙ¹_S ⟶ S`**, granted [Stacks, Tag 03Q9]
(`h03Q9`), [Stacks, Tag 0A5H] (`h0A5H`) and [Stacks, Tag 0A5E] (`h0A5E`) in the forms of their
developments. -/
theorem higherDirectImagesVanishOnInjectives_projectiveLine
    (h03Q9 : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (s : GeometricPoint Y) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((derivedPushforwardStalkToStrictHenselizationSections (BigEtaleSite.containing Y)
        (BigEtaleSite.contains_containing Y) f s).app ((DerivedCategory.singleFunctor _ 0).obj G)))
    (h0A5H : ∀ (ℓ : ℕ) (_ : ℓ.Prime) (A : Type u) [CommRing A] [HenselianLocalRing A]
      (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1}
        (ProjectiveSpace 1 (Spec (.of A))).smallEtaleTopology ℓ)), Injective J →
      ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (closedFibreInclusion A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)))).obj
          ((SheafOfModules.toSheaf _).obj J)) q))
    (h0A5E : ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k]
      [IsSepClosed k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      (_ : topologicalKrullDim X ≤ 1) (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (_ : Stacks.Torsion.torsionSheafProperty.{u + 1} (smallEtaleTopology X) F) (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' f) F q))
    (S : Scheme.{u}) :
    HigherDirectImagesVanishOnInjectives.{u, 0} (ProjectiveSpace 1 S ↘ S) := by
  intro ℓ hℓ I hI X' Y' g g' f' sq q hq
  set f := ProjectiveSpace 1 S ↘ S
  set G := (SheafOfModules.toSheaf _).obj I
  have hG : (ℓ : ℤ) • 𝟙 G = 0 := by
    rw [zsmul_id_eq_zero_iff]
    intro V x
    rw [natCast_zsmul]
    exact nsmul_toSheaf_eq_zero.{u + 1, u + 1} _ ℓ I V x
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg hq.le).symm⟩
  have hn : 0 < n := by exact_mod_cast hq
  -- the stalk at `g ∘ t` of `R^n f_* G` vanishes
  have hS : ∀ s : GeometricPoint S, Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (strictHenselizationBaseChangeToSource (BigEtaleSite.containing S)
        (BigEtaleSite.contains_containing S) f s)).obj G) n) := by
    intro s
    refine (isZero_stalk_homology_iff_subsingleton_H_strictHenselization _ _ f s G
      (h03Q9 f s G) n).1 ?_
    refine (smallEtaleStalkAb s.hom).map_isZero (IsZero.of_iso ?_
      ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
        (etaleAbelianDerivedDirectImageSingleIsoOfInjective f ℓ I).symm))
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ (n : ℤ)).app
      ((CochainComplex.singleFunctor _ 0).obj _))
    exact CochainComplex.isZero_of_isLE _ 0 (n : ℤ) (by exact_mod_cast hn)
  -- reduce to the stalks of `R^n f'_* (g')⁻¹G` at geometric points
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
    ((etaleAbelianDerivedDirectImage.{u, 0} f').mapIso
      (((etaleAbelianInverseImage.{u, 0} g').mapDerivedCategorySingleFunctor 0).app G)))
  refine isZero_of_geometricStalkAb_family
    (Ω := fun y : Y' ↦ (GeometricPoint.ofPoint Y' y).residueField)
    (fun y ↦ (GeometricPoint.ofPoint Y' y).hom) ?_ (fun y ↦ ?_)
  · refine Set.eq_univ_iff_forall.2 fun y ↦ Set.mem_iUnion.2 ⟨y, default, ?_⟩
    exact GeometricPoint.ofPoint_liesOver Y' y
  set t := GeometricPoint.ofPoint Y' y
  refine (isZero_stalk_homology_iff_subsingleton_H_strictHenselization
    (BigEtaleSite.containing Y') (BigEtaleSite.contains_containing Y') f' t
    ((etaleAbelianInverseImage.{u, 0} g').obj G) (h03Q9 f' t _) n).2 ?_
  refine (subsingleton_H_iff_of_iso ((etaleAbelianInverseImageCompIso'.{u, 0} _ g' _ rfl).app G)
    n).1 ?_
  refine (subsingleton_H_strictHenselization_iff_geometricFibre g g' f' sq
    (BigEtaleSite.containing Y') (BigEtaleSite.contains_containing Y') t (h0A5H ℓ hℓ) h0A5E hℓ G hG
    n).2 ?_
  -- the same over `S`, at the geometric point `g ∘ t`
  have hk := subsingleton_H_strictHenselization_iff_geometricFibre (𝟙 S) (𝟙 _) f
    (IsPullback.id_horiz f) (BigEtaleSite.containing S) (BigEtaleSite.contains_containing S)
    (GeometricPoint.mk t.residueField (t.hom ≫ g)) (h0A5H ℓ hℓ) h0A5E hℓ G hG n
  simp only [Category.comp_id] at hk
  exact hk.1 (hS _)

/-- **The proper base change theorem, from Tags 03Q9 and 0A5E.** For `f` proper, a cartesian
square and a torsion abelian sheaf `F`, the base change map `g⁻¹Rf_*F ⟶ Rf'_*(g')⁻¹F` is
invertible, granted [Stacks, Tag 03Q9] in all degrees (`h03Q9`) and [Stacks, Tag 0A5E]
(`h0A5E`), in the forms of their developments. This is the source's proof:
[Stacks, Tag 0A4F] reduces to `ℙ¹_S ⟶ S`, where [Stacks, Tag 0A4B] applies, its base change input
being [Stacks, Tag 0A3U] (`isIso_etaleAbelianBaseChange_of_isProper`) and its vanishing input
`higherDirectImagesVanishOnInjectives_projectiveLine`, which consumes [Stacks, Tag 0A5H]
(`subsingleton_H_closedFibre_projectiveLine_of_injective`). -/
theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isProper_of_inputs
    (h03Q9 : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      (s : GeometricPoint Y) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((derivedPushforwardStalkToStrictHenselizationSections (BigEtaleSite.containing Y)
        (BigEtaleSite.contains_containing Y) f s).app ((DerivedCategory.singleFunctor _ 0).obj G)))
    (h0A5E : ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsSepClosed k]
      [IsSepClosed k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
      (_ : topologicalKrullDim X ≤ 1) (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (_ : Stacks.Torsion.torsionSheafProperty.{u + 1} (smallEtaleTopology X) F) (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst k k' f) F q))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange.{u, 0} f :=
  cohomologyCommutesWithBaseChange_of_isProper_of_projectiveLine
    (fun S ↦ cohomologyCommutesWithBaseChange_of_higherDirectImagesVanishOnInjectives _
      (fun _ _ g g' f' sq ↦ isIso_etaleAbelianBaseChange_of_isProper _ g g' f' sq)
      (higherDirectImagesVanishOnInjectives_projectiveLine h03Q9
        (fun ℓ hℓ A _ _ J _ q hq ↦
          subsingleton_H_closedFibre_projectiveLine_of_injective ℓ hℓ A J q hq)
        h0A5E S))
    f inferInstance

end Stacks.EtaleCohomology

end
