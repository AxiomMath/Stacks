module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageTorsionDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AnnihilationLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of constant sheaves after reducing the coefficient ring

Let `f : X ⟶ S` be a morphism of schemes, `Λ` a Noetherian ring and `M` a finite `Λ`-module
annihilated by an integer `ℓ`. The second step of the proof of [Stacks, Tag 0GKW] replaces `Λ`
by `Λ/ℓΛ`: the sheaf `R^q f_* M` computed in sheaves of `Λ`-modules is the sheaf `R^q f_* M`
computed in sheaves of `Λ/ℓΛ`-modules with its scalars restricted to `Λ`
([Stacks, Tag 0D6J]), and restriction of scalars along a surjection of Noetherian rings preserves
constructibility.

## Main results

* `Stacks.EtaleCohomology.etaleModuleRightDerivedDirectImageRestrictScalarsIso`:
  `res_ρ (R^q f_* G) ≅ R^q f_* (res_ρ G)` for sheaves of modules on small étale sites.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerived_constantSheaf_of_quotient`:
  constructibility of `R^q f_* M` over `Λ/ℓΛ` gives it over `Λ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

section RestrictScalars

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-- **`res_ρ (R^q f_* G) ≅ R^q f_* (res_ρ G)`**: the higher direct image of a sheaf of
`Λ'`-modules, read as a sheaf of `Λ`-modules, is the higher direct image of the sheaf read as a
sheaf of `Λ`-modules ([Stacks, Tag 0D6J] for a change of constant coefficient rings). -/
@[sga "4½ Th_finitude 2.2" "Clause b)"]
def etaleModuleRightDerivedDirectImageRestrictScalarsIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : EtaleModules.{u, 0} Λ' X) (q : ℕ) :
    (etaleModuleRestrictScalars ρ Y).obj
        (((etaleModuleDirectImage.{u, 0} Λ' f).rightDerived q).obj G) ≅
      ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((etaleModuleRestrictScalars ρ X).obj G) :=
  (etaleModuleRestrictScalars ρ Y).mapIso
      (CategoryTheory.rightDerivedPlusObjIso (etaleModuleDirectImage.{u, 0} Λ' f) G q).symm ≪≫
    (Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso
      (etaleModuleRestrictScalars ρ Y) q _).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((etaleModuleDerivedDirectImageRestrictScalars ρ f).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≪≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f).mapIso
          (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ X) G)) ≪≫
    CategoryTheory.rightDerivedPlusObjIso (etaleModuleDirectImage.{u, 0} Λ f) _ q

end RestrictScalars

section Quotient

variable {Λ : Type} [CommRing Λ] (I : Ideal Λ)

/-- A `Λ`-module annihilated by an ideal `I`, as a module over `Λ ⧸ I`. -/
def moduleCatQuotientOfTorsionBy (M : ModuleCat.{u + 1} Λ) (hM : Module.IsTorsionBySet Λ M I) :
    ModuleCat.{u + 1} (Λ ⧸ I) :=
  letI := hM.module
  ModuleCat.of (Λ ⧸ I) M

/-- Restricting the scalars of `moduleCatQuotientOfTorsionBy I M` back to `Λ` gives `M`. -/
def restrictScalarsModuleCatQuotientOfTorsionByIso (M : ModuleCat.{u + 1} Λ)
    (hM : Module.IsTorsionBySet Λ M I) :
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I)).obj
        (moduleCatQuotientOfTorsionBy I M hM) ≅ M :=
  letI := hM.module
  letI : Module Λ (moduleCatQuotientOfTorsionBy I M hM) :=
    Module.compHom _ (Ideal.Quotient.mk I)
  LinearEquiv.toModuleIso (X₁ := moduleCatQuotientOfTorsionBy I M hM) (X₂ := M)
    { toFun := fun m => m
      invFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun c m => hM.mk_smul c m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- If `M` is a finite `Λ`-module annihilated by `I`, then `moduleCatQuotientOfTorsionBy I M` is a
finite `Λ ⧸ I`-module. -/
theorem module_finite_moduleCatQuotientOfTorsionBy (M : ModuleCat.{u + 1} Λ)
    (hM : Module.IsTorsionBySet Λ M I) [Module.Finite Λ M] :
    Module.Finite (Λ ⧸ I) (moduleCatQuotientOfTorsionBy I M hM) := by
  let := hM.module
  have := hM.isScalarTower (S := Λ)
  change Module.Finite (Λ ⧸ I) M
  exact Module.Finite.of_restrictScalars_finite (R := Λ) (A := Λ ⧸ I) (M := M)

end Quotient

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- Constructibility of `R^q f_* M'` over `A` gives that of `R^q f_* M` over `Λ`, for `M` the
restriction of scalars of `M'` along a surjection `Λ → A`. -/
private theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_restrictScalars_aux
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj)
    {Λ A : Type} [CommRing Λ] [CommRing A] [IsNoetherianRing Λ] [IsNoetherianRing A]
    (ρ : Λ →+* A) (hρ : Function.Surjective ρ) (M : ModuleCat.{u + 1} Λ)
    (M' : ModuleCat.{u + 1} A) (eM : (ModuleCat.restrictScalars.{u + 1} ρ).obj M' ≅ M) (q : ℕ)
    (h : IsBigSiteConstructibleEtaleModule B S A
      (((etaleModuleDirectImage.{u, 0} A f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M'))) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B S Λ
  let e : ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅
      (etaleModuleRestrictScalars ρ S.obj).obj
        (((etaleModuleDirectImage.{u, 0} A f).rightDerived q).obj
          ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M')) :=
    ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).mapIso
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso eM.symm ≪≫
          ((etaleModuleRestrictScalarsConstantIso ρ X.obj).app M').symm) ≪≫
      (etaleModuleRightDerivedDirectImageRestrictScalarsIso ρ f _ q).symm
  exact (IsBigSiteConstructibleEtaleModule B S Λ).prop_of_iso e.symm
    (isConstructibleEtaleModule_restrictScalars B S ρ hρ _ h)

/-- **The reduction to `Λ/ℓΛ` in the proof of [Stacks, Tag 0GKW].** Let `f : X ⟶ S`, `Λ` a
Noetherian ring and `ℓ` an integer. If `R^q f_* M'` is a constructible sheaf of
`Λ/ℓΛ`-modules for every finite `Λ/ℓΛ`-module `M'` and every `q`, then `R^q f_* M` is a
constructible sheaf of `Λ`-modules for every finite `Λ`-module `M` annihilated by `ℓ` and every
`q`: the constant sheaf `M` is the restriction of scalars of the constant sheaf of `Λ/ℓΛ`-modules
with value `M`, `R^q f_*` commutes with restriction of scalars, and restriction of scalars along
the surjection `Λ → Λ/ℓΛ` preserves constructibility. -/
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_quotient
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj)
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] (ℓ : ℕ)
    (h : ∀ (M' : ModuleCat.{u + 1} (Λ ⧸ Ideal.span {(ℓ : Λ)})),
      Module.Finite (Λ ⧸ Ideal.span {(ℓ : Λ)}) M' → ∀ q : ℕ,
        IsBigSiteConstructibleEtaleModule B S (Λ ⧸ Ideal.span {(ℓ : Λ)})
          (((etaleModuleDirectImage.{u, 0} (Λ ⧸ Ideal.span {(ℓ : Λ)}) f).rightDerived q).obj
            ((constantSheaf X.obj.smallEtaleTopology
              (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {(ℓ : Λ)}))).obj M')))
    (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M) (hℓ : ∀ m : M, ℓ • m = 0) (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let I : Ideal Λ := Ideal.span {(ℓ : Λ)}
  let ρ := Ideal.Quotient.mk I
  have hρ : Function.Surjective ρ := Ideal.Quotient.mk_surjective
  have hMI : Module.IsTorsionBySet Λ M I := by
    rw [Module.isTorsionBySet_iff_torsionBySet_eq_top, Submodule.torsionBySet_span_singleton_eq,
      eq_top_iff]
    intro m _
    change (ℓ : Λ) • m = 0
    rw [Nat.cast_smul_eq_nsmul]
    exact hℓ m
  let M' := moduleCatQuotientOfTorsionBy I M hMI
  have hM' : Module.Finite (Λ ⧸ I) M' := module_finite_moduleCatQuotientOfTorsionBy I M hMI
  exact isConstructibleEtaleModule_rightDerived_constantSheaf_of_restrictScalars_aux B f ρ hρ M M'
    (restrictScalarsModuleCatQuotientOfTorsionByIso I M hMI) q (h M' hM' q)

/-- **Reduction to the modules `Λ/𝔭` in the proof of [Stacks, Tag 0GKW].** Let `Λ` be a
Noetherian ring. If `R^q f_* N` is constructible for every `q` and every `Λ`-module `N`
isomorphic to `Λ/𝔭` for a prime `𝔭`, then `R^q f_* M` is constructible for every finite
`Λ`-module `M` and every `q`: `M` has a finite filtration with successive quotients of the form
`Λ/𝔭`, the constant sheaf functor is exact, and the constructible sheaves form a weak Serre
subcategory, so that the long exact sequence of `R^• f_*` carries constructibility from the two
outer terms of a short exact sequence to the middle one. Only the weak Serre property is used. -/
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_quotientPrime
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj)
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (h : ∀ (N : ModuleCat.{u + 1} Λ) (𝔭 : PrimeSpectrum Λ), (N ≃ₗ[Λ] Λ ⧸ 𝔭.1) → ∀ q : ℕ,
      IsBigSiteConstructibleEtaleModule B S Λ
        (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
          ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)))
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have hQ := isWeakSerreClass_isBigSiteConstructibleEtaleModule B S Λ
  let E := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleModuleDirectImage.{u, 0} Λ f)
  have key : ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ M))) := by
    refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := Λ) (M := M)
      inferInstance (motive := fun N _ _ _ => ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B S Λ
        (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
          ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ N)))) ?_ ?_ ?_
    · intro N _ _ _ _ q
      have : ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).Additive := E.additive q
      have hz : IsZero (ModuleCat.of Λ N) := by
        rw [ModuleCat.isZero_iff_subsingleton]
        infer_instance
      exact (IsBigSiteConstructibleEtaleModule B S Λ).prop_of_isZero
        ((((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).map_isZero
          ((constantSheaf _ _).map_isZero hz)))
    · intro N _ _ _ 𝔭 e q
      exact h (ModuleCat.of Λ N) 𝔭 e q
    · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ g₁ g₂ hinj hsurj hex h₁ h₃ q
      let T : ShortComplex (ModuleCat.{u + 1} Λ) :=
        ModuleCat.shortComplexOfCompEqZero g₁ g₂ (by ext x; exact hex.apply_apply_eq_zero x)
      exact E.prop_obj_X₂ (IsBigSiteConstructibleEtaleModule B S Λ)
        (shortExact_map_constantSheaf_etaleModules B (X := X) Λ T
          (ModuleCat.shortComplex_shortExact T hex hinj hsurj)) h₁ h₃ q
  exact key q

/-- **Constructibility of `R^q f_*` of a constant sheaf descends along a surjection of
coefficient rings.** Let `ρ : Λ →+* A` be a surjection of Noetherian rings and `M` a
`Λ`-module isomorphic to the restriction of scalars of an `A`-module `M'`. If `R^q f_* M'` is a
constructible sheaf of `A`-modules then `R^q f_* M` is a constructible sheaf of `Λ`-modules. -/
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_restrictScalars
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj)
    {Λ A : Type} [CommRing Λ] [CommRing A] [IsNoetherianRing Λ] [IsNoetherianRing A]
    (ρ : Λ →+* A) (hρ : Function.Surjective ρ) (M : ModuleCat.{u + 1} Λ)
    (M' : ModuleCat.{u + 1} A) (eM : (ModuleCat.restrictScalars.{u + 1} ρ).obj M' ≅ M) (q : ℕ)
    (h : IsBigSiteConstructibleEtaleModule B S A
      (((etaleModuleDirectImage.{u, 0} A f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M'))) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  isConstructibleEtaleModule_rightDerived_constantSheaf_of_restrictScalars_aux B f ρ hρ M M' eM q h

/-- A `Λ`-module isomorphic to `Λ ⧸ 𝔭` is the restriction of scalars of the free `Λ ⧸ 𝔭`-module
of rank one. -/
def restrictScalarsULiftQuotientIso {Λ : Type} [CommRing Λ] (𝔭 : Ideal Λ)
    (N : ModuleCat.{u + 1} Λ) (e : N ≃ₗ[Λ] Λ ⧸ 𝔭) :
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk 𝔭)).obj
        (ModuleCat.of (Λ ⧸ 𝔭) (ULift.{u + 1} (Λ ⧸ 𝔭))) ≅ N :=
  letI : Module Λ (ULift.{u + 1} (Λ ⧸ 𝔭)) := Module.compHom _ (Ideal.Quotient.mk 𝔭)
  LinearEquiv.toModuleIso (X₁ := ULift.{u + 1} (Λ ⧸ 𝔭)) (X₂ := N)
    { toFun := fun x => e.symm x.down
      invFun := fun y => ULift.up (e y)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        change e.symm (Ideal.Quotient.mk 𝔭 c • x.down) = c • e.symm x.down
        rw [← map_smul]
        rfl
      left_inv := fun x => by simp
      right_inv := fun y => by simp }

/-- **Stacks 0GKW from its rank one case.** Let `f : X ⟶ S` and `Λ` a Noetherian ring. Assume
that for every prime `ℓ`, every Noetherian ring `A` in which `ℓ = 0` and every `q`, the sheaf
`R^q f_* A` of `A`-modules is constructible. Then `R^q f_* M` is constructible for every finite
`Λ`-module `M` annihilated by a positive integer: by the reduction to prime torsion, to `Λ/ℓΛ`,
and to the quotients `(Λ/ℓΛ)/𝔭`, each of which is the restriction of scalars of the rank one
free module over the Noetherian ring `(Λ/ℓΛ)/𝔭`, in which `ℓ = 0`. -/
@[sga "4 XIV 1.11" "partial"]
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_unit
    (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj)
    (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (hunit : ∀ ℓ : ℕ, ℓ.Prime → ∀ (A : Type) [CommRing A] [IsNoetherianRing A], (ℓ : A) = 0 →
      ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B S A
        (((etaleModuleDirectImage.{u, 0} A f).rightDerived q).obj
          ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (ULift.{u + 1} A)))))
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (hnM : ∀ m : M, n • m = 0) (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  refine isConstructibleEtaleModule_rightDerived_constantSheaf_of_nsmul_eq_zero B f Λ
    (fun ℓ hℓ M hM hℓM q => ?_) n hn M hM hnM q
  refine isConstructibleEtaleModule_rightDerived_constantSheaf_of_quotient B f Λ ℓ
    (fun M' hM' q => ?_) M hM hℓM q
  let Λ' := Λ ⧸ Ideal.span {(ℓ : Λ)}
  have hℓΛ' : (ℓ : Λ') = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(ℓ : Λ)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have := hM'
  refine isConstructibleEtaleModule_rightDerived_constantSheaf_of_quotientPrime B f Λ'
    (fun N 𝔭 e q => ?_) M' q
  have hℓA : (ℓ : Λ' ⧸ 𝔭.1) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔭.1), hℓΛ', map_zero]
  exact isConstructibleEtaleModule_rightDerived_constantSheaf_of_restrictScalars B f
    (Ideal.Quotient.mk 𝔭.1) Ideal.Quotient.mk_surjective N _
    (restrictScalarsULiftQuotientIso 𝔭.1 N e) q (hunit ℓ hℓ (Λ' ⧸ 𝔭.1) hℓA q)

end Stacks.EtaleCohomology

end
