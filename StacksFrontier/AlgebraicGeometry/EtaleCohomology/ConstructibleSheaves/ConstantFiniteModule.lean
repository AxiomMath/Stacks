module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafModuleDictionaryEtaleSite
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
import all
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover

/-!
# Constant sheaves of finite modules, torsion coefficients, and inverse images on `D⁺`

Small facts used by the inductions of Stacks 0GKX, 0GKZ and 0GL0.

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_constantSheaf`: on any site with finite limits
  the constant sheaf on a finitely generated module is locally constant of finite type.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_constantSheaf_of_finite`: on a
  quasi-compact quasi-separated scheme, the constant sheaf `M` on a finite module over a Noetherian
  ring is constructible.
* `Stacks.EtaleCohomology.isTorsionEtaleModule_of_natCast_eq_zero`: over a torsion ring every sheaf
  of modules is torsion.
* `Stacks.EtaleCohomology.nonempty_homology_etaleModuleDerivedInverseImagePlus_iso`: inverse image
  is exact, so `H^q(g⁻¹ K) ≅ g⁻¹ H^q(K)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r w c v

namespace Stacks.ConstantSheaf

/-- **A constant sheaf on a finitely generated module is locally constant of finite type**, on
any site with finite limits: the identity covering trivialises it. -/
theorem isFiniteTypeLocallyConstant_constantSheaf {C : Type c} [Category.{v} C] [HasFiniteLimits C]
    (J : GrothendieckTopology C) {R : Type r} [Ring R] [HasWeakSheafify J (ModuleCat.{w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)] (M : ModuleCat.{w} R)
    (hM : ModuleCat.isFG R M) :
    IsFiniteTypeLocallyConstant R J ((constantSheaf J (ModuleCat.{w} R)).obj M) := by
  intro U
  have htop : Sieve.ofArrows (fun _ : PUnit.{max c v + 1} => U) (fun _ => 𝟙 U) = ⊤ :=
    (Sieve.id_mem_iff_eq_top).1 (Sieve.ofArrows_mk _ _ PUnit.unit)
  exact ⟨PUnit, fun _ => U, fun _ => 𝟙 U, htop ▸ J.top_mem U,
    fun _ => ⟨M, hM, ⟨constantSheaf_overPullback_iso J U M⟩⟩⟩

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **The constant sheaf on a finite module over a Noetherian ring is constructible**, on a
quasi-compact quasi-separated scheme of a big étale site: its transport to the small étale site of
Stacks 021B is the constant sheaf there, which is locally constant of finite type. -/
theorem isConstructibleEtaleModule_constantSheaf_of_finite (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    (M : ModuleCat.{max (u + 1) r} Λ) (hM : Module.Finite Λ M) :
    IsBigSiteConstructibleEtaleModule B X Λ
      ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M) :=
  isConstructibleModuleSheaf_congr B Λ X
    ((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
      (SmallEtale.topology B X.obj X.property) X.obj.smallEtaleTopology
      (SmallEtale.toEtaleSite B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)).app M).symm
    (isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X Λ _
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_constantSheaf _ M hM))

/-- **Over a torsion ring every sheaf of modules is torsion**: if `m > 0` vanishes in `Λ`, then
`m` kills every section. -/
theorem isTorsionEtaleModule_of_natCast_eq_zero (Λ : Type r) [Ring Λ] {X : Scheme.{u}} (m : ℕ)
    (hm : 0 < m) (hΛ : (m : Λ) = 0) (G : EtaleModules.{u, r} Λ X) :
    IsTorsionEtaleModule.{u, r} Λ X G :=
  fun V _ => ⟨⊤, X.smallEtaleTopology.top_mem V, fun _ _ _ =>
    ⟨m, hm, by rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]⟩⟩

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- **Cohomology commutes with inverse image on `D⁺`**: inverse image is exact, so the bounded
below derived inverse image acts degreewise and `H^q(g⁻¹ K) ≅ g⁻¹ H^q(K)`. -/
theorem nonempty_homology_etaleModuleDerivedInverseImagePlus_iso (Λ : Type r) [Ring Λ]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y))
    (q : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedInverseImagePlus.{u, r} Λ g).obj K) ≅
      (etaleModuleInverseImage.{u, r} Λ g).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
  ⟨(StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (etaleModuleInverseImage.{u, r} Λ g) q).app (DerivedCategory.Plus.ι.obj K)⟩

end Stacks.EtaleCohomology

end
