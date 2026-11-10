module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.NoncommConstructibleFlatRepresentativeEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekInputs

/-!
# Constructibility and boundedness of `Rπ_*` along a proper morphism

Let `π : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian and `Λ` a finite, possibly
noncommutative, ring. For `K` in `D⁺(X_étale, Λ)` lying in `D_ctf(X_étale, Λ)`, the underlying
sheaves of abelian groups of the cohomology sheaves of `Rπ_* K` are constructible. The proof is
the dévissage of [Stacks, Tag 0GL0] along the spectral sequence of a Cartan--Eilenberg
resolution:

1. restriction of scalars to `ℤ` is exact and commutes with `Rπ_*`
   (`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageRestrictScalars`), so it suffices to
   treat the restriction of scalars of `K`, a complex of sheaves of abelian groups;
2. its cohomology sheaves are the restrictions of scalars of those of `K`; these are torsion
   (`Nat.card Λ` kills them) and constructible over `ℤ`, because `K` is represented by a bounded
   complex of constructible flat sheaves of `Λ`-modules (`X` is quasi-compact and
   quasi-separated), whose cohomology sheaves are constructible over `Λ`, and restriction of
   scalars from a finite ring preserves constructibility;
3. for a constructible torsion sheaf of abelian groups `F`, `R^p π_* F = R^p π_! F` is
   constructible: this is [Stacks, Tag 0GL0], the hypothesis
   `Stacks.EtaleCohomology.LowerShriekConstructibilityInput`, applied with the ring `ℤ` and the
   trivial compactification of the proper `π`;
4. a weak Serre class containing `R^p π_*` of every cohomology sheaf contains the cohomology of
   `Rπ_*` (`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`).

The upper bound on the amplitude of `Rπ_*` on `D⁺_tors` is part (3) of [Stacks, Tag 0G2A] for the
trivial compactification of `π`.

## Main results

* `isConstructibleEtaleModule_restrictScalars_homology_etaleModuleDerivedDirectImage`: the
  constructibility statement above; its form with the homology functor of `D⁺` is
  `isConstructibleEtaleModule_restrictScalars_plusHomology_etaleModuleDerivedDirectImage`.
* `Stacks.EtaleCohomology.exists_isLE_etaleModuleDerivedDirectImage_of_isProper`: for `Λ` finite
  and `Y` quasi-compact, `Rπ_*` raises the upper bound of the cohomology by at most a fixed `N`.
* `Stacks.EtaleCohomology.exists_isLE_etaleModuleDerivedDirectImage_of_isProper_of_isTorsionPlus`:
  the same on `D⁺_tors(X_étale, R)` for an arbitrary ring `R`.

## References

* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 0G2A](https://stacks.math.columbia.edu/tag/0G2A)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`QuasiCompact ?f`, ...) match every goal and send instance search through
-- `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Torsion

variable (Λ : Type) [Ring Λ] [Finite Λ]

/-- `Nat.card Λ` kills every element of a module over a finite ring `Λ`. -/
private theorem nat_card_nsmul_eq_zero {M : Type*} [AddCommGroup M] [Module Λ M] (y : M) :
    Nat.card Λ • y = 0 := by
  have := Fintype.ofFinite Λ
  rw [← Nat.cast_smul_eq_nsmul Λ, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero, zero_smul]

/-- **The underlying abelian sheaf of a sheaf of modules over a finite ring is torsion**:
`Nat.card Λ` vanishes in `Λ`, so it kills every section. -/
theorem isTorsionEtaleModule_restrictScalars_int_of_finite (X : Scheme.{u})
    (F : EtaleModules.{u, 0} Λ X) :
    IsTorsionEtaleModule.{u, 0} ℤ X ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj F) := by
  intro V x
  exact ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ =>
    ⟨Nat.card Λ, Nat.card_pos, nat_card_nsmul_eq_zero Λ (M := F.obj.obj (op W)) _⟩⟩

end Torsion

section Represented

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **The cohomology sheaves of a bounded complex of constructible flat sheaves over a finite ring
are constructible as sheaves of abelian groups** (the direction (2) ⟹ (1) of [Stacks, Tag 03TT],
followed by restriction of scalars to `ℤ`). -/
theorem isConstructibleEtaleModule_restrictScalars_homology_of_isRepresented
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [Ring Λ] [Finite Λ]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsRepresentedByConstructibleFlatEtaleComplex B X Λ K) (i : ℤ) :
    IsBigSiteConstructibleEtaleModule B X ℤ
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X.obj).obj
        ((DerivedCategory.homologyFunctor _ i).obj K)) := by
  have := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  have := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
  have hS := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, 0} B X Λ
  have := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, 0} B X ℤ
  let ρ := etaleModulesToSmallEtale B X Λ
  rw [isRepresentedByConstructibleFlatEtaleComplex_iff] at hK
  have h' :
      IsConstructibleModuleSheaf B X Λ (ρ.obj ((DerivedCategory.homologyFunctor _ i).obj K)) :=
    (isConstructibleModuleSheafProperty.{u, u + 1, 0} B X Λ).prop_of_iso
      ((ρ.mapDerivedCategoryHomologyIso i).app K)
      (isConstructible_of_isRepresentedByConstructibleFlatComplex B X Λ hS _ hK i)
  exact (isConstructibleModuleSheafProperty.{u, u + 1, 0} B X ℤ).prop_of_iso
    ((etaleModulesToSmallEtaleIntRestrictIso B X Λ).app _)
    (isIntConstructible_of_isConstructibleModuleSheaf B X Λ h')

end Represented

section Constructible

/-- **[Stacks, Tag 0GL0] for a proper morphism, through the classical indexing**: for `π`
proper with `Y` Noetherian and `F` a constructible torsion sheaf of abelian groups on `X`, every
`R^p π_* F` is constructible. This is the hypothesis `hC` with the trivial compactification of
`π`, through which `Rπ_!` is `Rπ_*`. -/
theorem isConstructibleEtaleModule_rightDerived_etaleModuleDirectImage_of_isProper
    (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (π : X ⟶ Y) [IsProper π] [IsNoetherian Y]
    (hX : B.Contains X) (hY : B.Contains Y) (hC : LowerShriekConstructibilityInput B)
    (M : EtaleModules.{u, 0} ℤ X) (hMc : IsBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ M)
    (hMt : IsTorsionEtaleModule.{u, 0} ℤ X M) (p : ℕ) :
    IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
      (((etaleModuleDirectImage.{u, 0} ℤ π).rightDerived p).obj M) := by
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
  have hN : IsNoetherian (B.obj Y hY).obj := ‹IsNoetherian Y›
  -- the instances are given explicitly: instance search for them times out here
  have hs : IsSeparated π := IsProper.toIsSeparated
  have hl : LocallyOfFiniteType π := IsProper.toLocallyOfFiniteType
  have hq : QuasiCompact π := inferInstance
  have h : IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        ((derivedLowerShriek.{u, 0} π (CompactificationOf.ofProper π) ℤ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) :=
    @hC (B.obj X hX) (B.obj Y hY) hN π hs hl hq (CompactificationOf.ofProper π) ℤ _ _ M
      hMc hMt p
  let e₁ := (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).mapIso
    ((derivedLowerShriekOfProperIso ℤ π).app ((DerivedCategory.Plus.singleFunctor _ 0).obj M))
  let e₂ := ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} ℤ π) p).app M)
  exact (IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ).prop_of_iso (e₁ ≪≫ e₂.symm) h

/-- The cohomology sheaves of the restriction of scalars to `ℤ` of an object of
`D_ctf(X_étale, Λ)`, `Λ` finite and `X` quasi-compact and quasi-separated, are constructible and
torsion. -/
theorem isConstructibleEtaleModule_and_isTorsion_homology_restrictScalars_of_isCtf
    (B : BigEtaleSite.{u}) {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : B.Contains X) (Λ : Type) [Ring Λ] [Finite Λ]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Plus.ι.obj K)) (q : ℤ) :
    IsBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapDerivedCategoryPlus.obj K)) ∧
      IsTorsionEtaleModule.{u, 0} ℤ X ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapDerivedCategoryPlus.obj K)) := by
  have : CompactSpace (B.obj X hX).obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace (B.obj X hX).obj := ‹QuasiSeparatedSpace X›
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ
  let rX := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let e : (DerivedCategory.Plus.homologyFunctor _ q).obj (rX.mapDerivedCategoryPlus.obj K) ≅
      rX.obj ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Plus.ι.obj K)) :=
    (rX.mapDerivedCategoryHomologyIso q).app (DerivedCategory.Plus.ι.obj K)
  refine ⟨(IsBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ).prop_of_iso e.symm ?_,
    IsTorsionEtaleModule.of_iso ℤ X e.symm
      (isTorsionEtaleModule_restrictScalars_int_of_finite Λ X _)⟩
  exact isConstructibleEtaleModule_restrictScalars_homology_of_isRepresented B (B.obj X hX) Λ _
    ((isCtf_iff_of_qcqs B Λ _).1 hK) q


/-- **Constructibility of the cohomology of `Rπ_*` along a proper morphism** ([Stacks, Tag 0GL0]
for `D_ctf`). Let `π : X ⟶ Y` be proper with `Y` Noetherian, `Λ` a finite ring and `K` an object
of `D⁺(X_étale, Λ)` in `D_ctf(X_étale, Λ)`. Then the underlying sheaf of abelian groups of every
cohomology sheaf of `Rπ_* K` is constructible. Tag 0GL0 itself, for constructible torsion sheaves,
is the hypothesis `hC`, used with the ring `ℤ`. -/
theorem isConstructibleEtaleModule_restrictScalars_homology_etaleModuleDerivedDirectImage
    (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (π : X ⟶ Y) [IsProper π] [IsNoetherian Y]
    (hX : B.Contains X) (hY : B.Contains Y) (Λ : Type) [Ring Λ] [Finite Λ]
    (hC : LowerShriekConstructibilityInput B)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Plus.ι.obj K)) (i : ℤ) :
    IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
        ((DerivedCategory.homologyFunctor _ i).obj
          (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K)))) := by
  -- the instances are given explicitly: instance search for them is very slow here
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace Y := @IsLocallyNoetherian.quasiSeparatedSpace Y
    IsNoetherian.toIsLocallyNoetherian
  have : QuasiSeparated π := IsSeparated.instQuasiSeparated π
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated π
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
  let rY := etaleModuleRestrictScalars (Int.castRingHom Λ) Y
  let P : ObjectProperty (EtaleModules.{u, 0} ℤ X) := fun F =>
    IsBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ F ∧ IsTorsionEtaleModule.{u, 0} ℤ X F
  have : P.IsClosedUnderIsomorphisms := ⟨fun e hF =>
    ⟨(IsBigSiteConstructibleEtaleModule B (B.obj X hX) ℤ).prop_of_iso e hF.1,
      IsTorsionEtaleModule.of_iso ℤ X e hF.2⟩⟩
  have hmain := Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    (etaleModuleDirectImage.{u, 0} ℤ π) P (IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ)
    (fun M hM p => isConstructibleEtaleModule_rightDerived_etaleModuleDirectImage_of_isProper
      B π hX hY hC M hM.1 hM.2 p)
    ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapDerivedCategoryPlus.obj K)
    (isConstructibleEtaleModule_and_isTorsion_homology_restrictScalars_of_isCtf B hX Λ K hK)
  let e : rY.obj ((DerivedCategory.homologyFunctor _ i).obj
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K))) ≅
      (DerivedCategory.homologyFunctor _ i).obj
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} ℤ π).obj
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).mapDerivedCategoryPlus.obj K))) :=
    ((rY.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (DerivedCategory.Plus.ι.mapIso
        ((etaleModuleDerivedDirectImageRestrictScalars (Int.castRingHom Λ) π).app K))
  exact (IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ).prop_of_iso e.symm (hmain.2 i)

/-- **Constructibility of the cohomology of `Rπ_*` along a proper morphism**, with the homology
functor of the bounded below derived category: the same statement as
`isConstructibleEtaleModule_restrictScalars_homology_etaleModuleDerivedDirectImage`. -/
theorem isConstructibleEtaleModule_restrictScalars_plusHomology_etaleModuleDerivedDirectImage
    (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (π : X ⟶ Y) [IsProper π] [IsNoetherian Y]
    (hX : B.Contains X) (hY : B.Contains Y) (Λ : Type) [Ring Λ] [Finite Λ]
    (hC : LowerShriekConstructibilityInput B)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : IsCtf B (B.obj X hX) Λ (DerivedCategory.Plus.ι.obj K)) (i : ℤ) :
    IsBigSiteConstructibleEtaleModule B (B.obj Y hY) ℤ
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
        ((DerivedCategory.Plus.homologyFunctor _ i).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K))) :=
  isConstructibleEtaleModule_restrictScalars_homology_etaleModuleDerivedDirectImage B π hX hY Λ
    hC K hK i

end Constructible

section Bound

/-- **Part (3) of Stacks 0G2A for a proper morphism, on `D⁺_tors`.** If `π : X ⟶ Y` is proper and
`Y` is quasi-compact, there is `N` such that `Rπ_*` carries every object of `D⁺(X_étale, R)` with
torsion cohomology sheaves vanishing above degree `b` to an object vanishing above degree
`b + N`. An object killed by a positive integer has torsion cohomology sheaves
(`Stacks.EtaleCohomology.isTorsionPlus_of_nsmul_id_eq_zero`). -/
theorem exists_isLE_etaleModuleDerivedDirectImage_of_isProper_of_isTorsionPlus
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsProper π] [CompactSpace Y] (R : Type) [Ring R] :
    ∃ N : ℕ, ∀ (K : DerivedCategory.Plus (EtaleModules.{u, 0} R X)),
      isTorsionPlus.{u, 0} R X K → ∀ b : ℤ, (DerivedCategory.Plus.ι.obj K).IsLE b →
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} R π).obj K)).IsLE
          (b + N) := by
  obtain ⟨N, hN⟩ :=
    exists_isLE_derivedLowerShriek_of_isTorsionPlus R π (CompactificationOf.ofProper π)
  refine ⟨N, fun K hK b hb => ?_⟩
  have := hN K hK b ((DerivedCategory.Plus.isLE_ι_obj_iff K b).1 hb)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (DerivedCategory.Plus.ι.mapIso ((derivedLowerShriekOfProperIso R π).app K)) _

/-- **Part (3) of Stacks 0G2A for a proper morphism, over a finite ring.** If `π : X ⟶ Y` is
proper, `Y` is quasi-compact and `Λ` is finite, there is `N` such that `Rπ_*` carries every
object of `D⁺(X_étale, Λ)` vanishing above degree `b` to an object vanishing above degree
`b + N`: every sheaf of `Λ`-modules is torsion. -/
theorem exists_isLE_etaleModuleDerivedDirectImage_of_isProper {X Y : Scheme.{u}} (π : X ⟶ Y)
    [IsProper π] [CompactSpace Y] (Λ : Type) [Ring Λ] [Finite Λ] :
    ∃ N : ℕ, ∀ (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (b : ℤ),
      (DerivedCategory.Plus.ι.obj K).IsLE b →
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedDirectImage.{u, 0} Λ π).obj K)).IsLE
          (b + N) := by
  obtain ⟨N, hN⟩ := exists_isLE_etaleModuleDerivedDirectImage_of_isProper_of_isTorsionPlus π Λ
  refine ⟨N, fun K b hb => hN K (fun q V x => ?_) b hb⟩
  exact ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ =>
    ⟨Nat.card Λ, Nat.card_pos, nat_card_nsmul_eq_zero Λ _⟩⟩

end Bound

end Stacks.EtaleCohomology

end
