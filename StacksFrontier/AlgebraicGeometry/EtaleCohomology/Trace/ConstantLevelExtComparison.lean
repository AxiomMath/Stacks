module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSmallEtaleAffineVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelChange
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The levels of `Hⁱ(X_k̄, ℤ_ℓ)` of a proper scheme as `Ext` groups

Let `X` be a scheme proper over a finite field `k`, `ℓ` a prime and `N = ℓⁿ⁺¹`. The level `n` of
the constant ℓ-adic sheaf `ℤ_ℓ` (`Stacks.EtaleCohomology.LAdicSheaf.constantSystem`) is, on
Mathlib's small étale site, the constant sheaf `ℤ/N`
(`Stacks.EtaleCohomology.LAdicSheaf.etaleLevelConstantSystemIso`), and the level `n` of
`Hⁱ(X_k̄, ℤ_ℓ)` — the `ℤ_ℓ`-module `Hⁱ_c(X_k̄, (ℤ_ℓ)ₙ)` whose limit is
`Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomology` — is, as an abelian
group,

`Ext^i_{ℤ/N}(ℤ/N_{X_k̄}, ℤ/N_{X_k̄})`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafEquivModuleShriekConstantFinalIso`: the extension by zero of
  the constant sheaf from the final object of the small étale site of Stacks 021B is, on Mathlib's
  small étale site, the constant sheaf.
* `Stacks.EtaleCohomology.LAdicSheaf.etaleLevelConstantSystemIso`: the level `n` of `ℤ_ℓ` is the
  constant sheaf `ℤ/ℓⁿ⁺¹`.
* `Stacks.EtaleCohomology.LAdicSheaf.constantLevelCohomologyAddEquiv`:
  `Hⁱ_c(X_k̄, (ℤ_ℓ)ₙ) ≃+ Ext^i(ℤ/N, ℤ/N)` on `X_k̄`, for `X` proper.

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.InverseSystem

universe u

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace AlgebraicGeometry.SmallEtale

/-- **The extension by zero of the constant sheaf from the final object is the constant sheaf**,
read on Mathlib's small étale site. -/
def sheafEquivModuleShriekConstantFinalIso (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type)
    [CommRing R] :
    (sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)).functor.obj
        (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)) ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} R X.1.smallEtaleTopology := by
  let E := sheafEquiv B X.1 X.property (ModuleCat.{u + 1} R)
  let hT := isTerminal_toEtaleSite_final B X.1 X.property
  let e₁ : coyoneda.obj (op (E.functor.obj
      (moduleShriekConstant.{u, 0, 0} B X R (final B X.1 X.property)))) ≅
      (sheafSections X.1.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
          (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property))) ⋙
        forget (ModuleCat.{u + 1} R) :=
    E.toAdjunction.compCoyonedaIso.app _ ≪≫
      Functor.isoWhiskerLeft E.inverse
        (moduleShriekConstantCoyonedaIso.{u, 0, 0} B X R (final B X.1 X.property))
  let e₂ : coyoneda.obj (op (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} R
      X.1.smallEtaleTopology)) ≅
      (sheafSections X.1.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
          (op ((toEtaleSite B X.1 X.property).obj (final B X.1 X.property))) ⋙
        forget (ModuleCat.{u + 1} R) :=
    (constantSheafAdj X.1.smallEtaleTopology (ModuleCat.{u + 1} R) hT).compCoyonedaIso.app _ ≪≫
      Functor.isoWhiskerLeft _ (ModuleCat.coyonedaULiftSelfIso.{0, u + 1} R)
  exact (Coyoneda.fullyFaithful.preimageIso (e₁ ≪≫ e₂.symm)).unop.symm

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Changing the coefficient ring along a surjection -/

section ChangeOfRings

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (Y : Scheme.{u})

/-- `ρ : Λ → Λ'` as a `Λ`-linear map `Λ ⟶ res_ρ Λ'` of the coefficient modules of the constant
sheaves. -/
def unitReductionLinearMap :
    ModuleCat.of Λ (ULift.{u + 1} Λ) ⟶
      (ModuleCat.restrictScalars.{u + 1} ρ).obj (ModuleCat.of Λ' (ULift.{u + 1} Λ')) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u + 1} ρ).obj
      (ModuleCat.of Λ' (ULift.{u + 1} Λ')))
    ({ toFun := fun x => ULift.up (ρ x.down)
       map_add' := fun x y => ULift.ext _ _ (map_add ρ x.down y.down)
       map_smul' := fun a x => ULift.ext _ _ (map_mul ρ a x.down) } :
      ULift.{u + 1} Λ →ₗ[Λ]
        (ModuleCat.restrictScalars.{u + 1} ρ).obj (ModuleCat.of Λ' (ULift.{u + 1} Λ')))

/-- **The reduction `Λ_Y ⟶ res_ρ Λ'_Y`** of constant sheaves on the small étale site of `Y`. -/
def unitReduction :
    Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology ⟶
      (etaleModuleRestrictScalars ρ Y).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ' Y.smallEtaleTopology) :=
  (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map (unitReductionLinearMap ρ) ≫
    ((etaleModuleRestrictScalarsConstantIso ρ Y).app
      (ModuleCat.of Λ' (ULift.{u + 1} Λ'))).inv

/-- **The restriction of scalars of the constant sheaf, on the unit of sheafification**: the
comparison `res_ρ(Λ'_Y) ≅ (res_ρ Λ')_Y` restricts, on the constant presheaf, to the restriction of
scalars of the unit of sheafification. -/
theorem toSheafify_comp_etaleModuleRestrictScalarsConstantIso_inv (M : ModuleCat.{u + 1} Λ') :
    toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj ((ModuleCat.restrictScalars.{u + 1} ρ).obj M)) ≫
      ((etaleModuleRestrictScalarsConstantIso ρ Y).app M).inv.hom =
    Functor.whiskerRight (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M))
      (ModuleCat.restrictScalars.{u + 1} ρ) := by
  let T := sheafComposeNatTrans Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have key : ((etaleModuleRestrictScalarsConstantIso ρ Y).app M).inv.hom =
      sheafifyMap Y.smallEtaleTopology
        (((Functor.compConstIso Y.Etaleᵒᵖ (ModuleCat.restrictScalars.{u + 1} ρ)).app M).hom) ≫
      (T.app ((Functor.const Y.Etaleᵒᵖ).obj M)).hom := rfl
  have h1 := sheafComposeNatTrans_fac Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (sheafificationAdjunction Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    ((Functor.const Y.Etaleᵒᵖ).obj M)
  let c := ((Functor.compConstIso Y.Etaleᵒᵖ (ModuleCat.restrictScalars.{u + 1} ρ)).app M).hom
  have h2 : toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj ((ModuleCat.restrictScalars.{u + 1} ρ).obj M)) ≫
      sheafifyMap Y.smallEtaleTopology c =
      c ≫ toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj M ⋙ ModuleCat.restrictScalars.{u + 1} ρ) :=
    (toSheafify_naturality Y.smallEtaleTopology c).symm
  rw [key]
  ext U x
  have e2 := congrArg (fun t => (t.app U).hom x) h2
  have e1 := congrArg (fun t => (t.app U).hom x) h1
  exact (congrArg (fun y => ((T.app ((Functor.const Y.Etaleᵒᵖ).obj M)).hom.app U).hom y) e2).trans
    e1

/-- The reduction `Λ_Y ⟶ res_ρ Λ'_Y` on the unit of sheafification: it is `ρ` on the constant
sections. -/
theorem unitReduction_hom_app_toSheafify (U : Y.Etaleᵒᵖ) (x : ULift.{u + 1} Λ) :
    ((unitReduction ρ Y).hom.app U).hom
        (show
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology).obj.obj U
          from ((toSheafify Y.smallEtaleTopology
            ((Functor.const Y.Etaleᵒᵖ).obj (ModuleCat.of Λ (ULift.{u + 1} Λ)))).app U).hom x) =
      ((toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (ModuleCat.of Λ' (ULift.{u + 1} Λ')))).app U).hom
          (ULift.up (ρ x.down)) := by
  have hL := congrArg (fun t => (t.app U).hom (ULift.up (ρ x.down) : ULift.{u + 1} Λ'))
    (toSheafify_comp_etaleModuleRestrictScalarsConstantIso_inv ρ Y
      (ModuleCat.of Λ' (ULift.{u + 1} Λ')))
  have hN := congrArg (fun t => (t.app U).hom x) (toSheafify_naturality Y.smallEtaleTopology
    ((Functor.const Y.Etaleᵒᵖ).map (unitReductionLinearMap ρ)))
  exact (congrArg (fun y => (((etaleModuleRestrictScalarsConstantIso ρ Y).app
    (ModuleCat.of Λ' (ULift.{u + 1} Λ'))).inv.hom.app U).hom y) hN.symm).trans hL

/-- **Two reductions in a row**: `Λ_Y ⟶ res_{ρ₁} R_Y ⟶ res_{ρ₁} res_{ρ₂} S_Y = res_σ S_Y` is the
reduction along `σ = ρ₂ ∘ ρ₁`. -/
theorem unitReduction_comp_map_unitReduction {R S : Type} [CommRing R] [CommRing S]
    (ρ₁ : Λ →+* R) (ρ₂ : R →+* S) (σ : Λ →+* S) (w : σ = ρ₂.comp ρ₁) :
    unitReduction ρ₁ Y ≫ (etaleModuleRestrictScalars ρ₁ Y).map (unitReduction ρ₂ Y) ≫
        (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.app
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf S Y.smallEtaleTopology) =
      unitReduction σ Y := by
  subst w
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (ObjectProperty.FullSubcategory.property _)
  ext U x
  exact ((congrArg (fun y => ((unitReduction ρ₂ Y).hom.app U).hom y)
    (unitReduction_hom_app_toSheafify ρ₁ Y U x)).trans
      (unitReduction_hom_app_toSheafify ρ₂ Y U _)).trans
    (unitReduction_hom_app_toSheafify (ρ₂.comp ρ₁) Y U x).symm

variable {ρ} (d : ℕ) (hρ : Function.Surjective ρ) (hker : ∀ x, ρ x = 0 ↔ ∃ y, x = (d : Λ) * y)

include hker in
/-- `Λ --d--> Λ --ρ--> Λ'` is exact when the kernel of `ρ` is generated by `d`. -/
theorem function_exact_unitReductionLinearMap :
    Function.Exact (d • 𝟙 (ModuleCat.of Λ (ULift.{u + 1} Λ))).hom
      (unitReductionLinearMap.{u} ρ).hom := by
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (hker y.down).1 (congrArg ULift.down hy)
    refine ⟨ULift.up z, ULift.ext _ _ ?_⟩
    show d • z = y.down
    rw [hz, nsmul_eq_mul]
  · rintro ⟨x, rfl⟩
    refine ULift.ext _ _ ?_
    show ρ (d • x.down) = 0
    exact (hker _).2 ⟨x.down, nsmul_eq_mul _ _⟩

include hker in
/-- `d` kills a sheaf of `Λ'`-modules read as a sheaf of `Λ`-modules. -/
theorem nsmul_id_restrictScalars_eq_zero (G : EtaleModules.{u, 0} Λ' Y) :
    d • 𝟙 ((etaleModuleRestrictScalars ρ Y).obj G) = 0 := by
  ext U x
  show d • (show G.obj.obj U from x) = 0
  rw [← Nat.cast_smul_eq_nsmul Λ', ← map_natCast ρ, (hker _).2 ⟨1, (mul_one _).symm⟩, zero_smul]

/-- The constant sheaf functor on the small étale site of `Y` is a left adjoint. -/
instance (Λ : Type) [Ring Λ] :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
  (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (etaleSiteTerminalIsTerminal Y)).isLeftAdjoint

include hρ in
/-- Restriction of scalars along a surjection is full on sheaves of modules. -/
theorem full_etaleModuleRestrictScalars_of_surjective : (etaleModuleRestrictScalars ρ Y).Full := by
  have := restrictScalars_full_of_surjective.{0, 0, u + 1} ρ hρ
  unfold etaleModuleRestrictScalars
  infer_instance

/-- `d • 𝟙 ≫ g = 0` when `d` kills the target of `g`. -/
private theorem nsmul_id_comp_eq_zero_aux {C : Type*} [Category* C] [Preadditive C]
    {A A' : C} (d : ℕ) (g : A ⟶ A') (h : d • 𝟙 A' = 0) : (d • 𝟙 A) ≫ g = 0 := by
  rw [Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id g, ← Preadditive.comp_nsmul, h,
    comp_zero]

include hρ hker in
/-- **In degree zero, `f ↦ u ≫ res_ρ f` is bijective** for the reduction `u : Λ_Y ⟶ res_ρ Λ'_Y`. -/
theorem bijective_unitReduction_comp_map (G : EtaleModules.{u, 0} Λ' Y) :
    Function.Bijective
      (fun f : Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ' Y.smallEtaleTopology ⟶ G =>
        unitReduction ρ Y ≫ (etaleModuleRestrictScalars ρ Y).map f) := by
  have := full_etaleModuleRestrictScalars_of_surjective Y hρ
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Sm : ShortComplex (ModuleCat.{u + 1} Λ) :=
    ShortComplex.mk (d • 𝟙 (ModuleCat.of Λ (ULift.{u + 1} Λ))) (unitReductionLinearMap ρ) (by
      ext x
      exact (function_exact_unitReductionLinearMap d hker _).2 ⟨x, rfl⟩)
  have hSm : Sm.Exact := ModuleCat.shortComplex_exact _
    (function_exact_unitReductionLinearMap d hker)
  have hepi : Epi Sm.g := (ModuleCat.epi_iff_surjective _).2 fun y => by
    obtain ⟨x, hx⟩ := hρ y.down
    exact ⟨ULift.up x, ULift.ext _ _ hx⟩
  have hepiC : Epi (Sm.map C).g := by
    show Epi (C.map Sm.g)
    infer_instance
  let e := ((etaleModuleRestrictScalarsConstantIso ρ Y).app (ModuleCat.of Λ' (ULift.{u + 1} Λ')))
  have hu : Epi (unitReduction ρ Y) := by
    unfold unitReduction
    exact epi_comp' hepiC inferInstance
  refine ⟨fun f f' h => (etaleModuleRestrictScalars ρ Y).map_injective
    ((cancel_epi (unitReduction ρ Y)).1 h), fun g => ?_⟩
  have hg : (Sm.map C).f ≫ g = 0 := by
    show C.map (d • 𝟙 _) ≫ g = 0
    rw [C.map_nsmul, C.map_id]
    exact nsmul_id_comp_eq_zero_aux d g (nsmul_id_restrictScalars_eq_zero Y d hker _)
  obtain ⟨k, hk⟩ := CokernelCofork.IsColimit.desc' (hSm.map C).gIsCokernel g hg
  obtain ⟨f, hf⟩ := (etaleModuleRestrictScalars ρ Y).map_surjective (e.hom ≫ k)
  refine ⟨f, ?_⟩
  show (C.map (unitReductionLinearMap ρ) ≫ e.inv) ≫ (etaleModuleRestrictScalars ρ Y).map f = g
  rw [hf, Category.assoc, e.inv_hom_id_assoc]
  exact hk

/-- `Ext^{n+1}_Λ(Λ_Y, res_ρ I) = 0` for an injective sheaf `I` of `Λ'`-modules. -/
theorem subsingleton_ext_restrictScalars_of_injective (I : EtaleModules.{u, 0} Λ' Y)
    [Injective I] (n : ℕ) :
    Subsingleton (Ext.{u + 1}
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      ((etaleModuleRestrictScalars ρ Y).obj I) (n + 1)) := by
  have : Subsingleton ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf
      Λ' Y.smallEtaleTopology) (n + 1)).obj I) :=
    Ext.subsingleton_of_injective _ I n
  exact (extConstantRestrictScalarsIso ρ Y I
    (n + 1)).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

variable (ρ) in
/-- **The change of coefficients on cohomology**, `Ext^n_{Λ'}(Λ'_Y, G) ⟶ Ext^n_Λ(Λ_Y, res_ρ G)`,
`y ↦ u ∘ res_ρ(y)` for the reduction `u : Λ_Y ⟶ res_ρ Λ'_Y`. -/
def extRestrictScalarsMap (G : EtaleModules.{u, 0} Λ' Y) (n : ℕ) :
    Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ' Y.smallEtaleTopology) G
        n →+
      Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
        ((etaleModuleRestrictScalars ρ Y).obj G) n :=
  Stacks.Cohomology.ExtComparison.extMapAlong.{u + 1, u + 1} (etaleModuleRestrictScalars ρ Y)
    (unitReduction ρ Y) G n

include hρ hker in
/-- **Étale cohomology with `Λ'`-coefficients may be computed with `Λ`-coefficients**, for a
surjection `ρ : Λ → Λ'` with principal kernel: the change of coefficients is bijective. -/
theorem extRestrictScalarsMap_bijective (G : EtaleModules.{u, 0} Λ' Y) (n : ℕ) :
    Function.Bijective (extRestrictScalarsMap ρ Y G n) := by
  have : EnoughInjectives (EtaleModules.{u, 0} Λ' Y) := etaleModules_enoughInjectives Λ' Y
  exact Stacks.Cohomology.ExtComparison.extMapAlong_bijective_of_subsingleton _ _
      (bijective_unitReduction_comp_map Y d hρ hker)
      (fun I _ n => subsingleton_ext_restrictScalars_of_injective Y I n) G n

end ChangeOfRings

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **The level `n` of the constant ℓ-adic sheaf is the constant sheaf `ℤ/ℓⁿ⁺¹`** on Mathlib's
small étale site. -/
def LAdicSheaf.etaleLevelConstantSystemIso (n : ℕ) :
    LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology :=
  SmallEtale.sheafEquivModuleShriekConstantFinalIso B X (ZMod (ℓ ^ (n + 1)))

variable {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [QuasiCompact f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fact ℓ.Prime] in
/-- The kernel of `ℤ_ℓ → ℤ/ℓⁿ⁺¹` is generated by `ℓⁿ⁺¹`. -/
theorem toZModPow_eq_zero_iff [Fact ℓ.Prime] (n : ℕ) (x : ℤ_[ℓ]) :
    PadicInt.toZModPow (n + 1) x = 0 ↔ ∃ y, x = ((ℓ ^ (n + 1) : ℕ) : ℤ_[ℓ]) * y := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton', Nat.cast_pow]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy, mul_comm]⟩⟩

/-- The level `n` of `ℤ_ℓ`, read on `X_k̄` as a sheaf of `ℤ_ℓ`-modules, is the constant sheaf
`ℤ/ℓⁿ⁺¹` read through `ℤ_ℓ → ℤ/ℓⁿ⁺¹`. -/
def LAdicSheaf.constantLevelInverseImageIso (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).obj
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ≅
      (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) _).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) :=
  let I := etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)
  let ρ := PadicInt.toZModPow (p := ℓ) (n + 1)
  I.mapIso ((sheafEquivRestrictScalarsIso B X.1 X.property ρ).app
      ((LAdicSheaf.constantSystem B X ℓ).level n)).symm ≪≫
    I.mapIso ((etaleModuleRestrictScalars ρ X.1).mapIso
      (LAdicSheaf.etaleLevelConstantSystemIso B X ℓ n)) ≪≫
    (etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj (Over.mk f) kbar)).app _ ≪≫
    (etaleModuleRestrictScalars ρ _).mapIso
      ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).app _)

/-- **The level `n` of `Hⁱ(X_k̄, ℤ_ℓ)` is `Ext^i_{ℤ/N}(ℤ/N, ℤ/N)` on `X_k̄`**, `N = ℓⁿ⁺¹`, for `X`
proper over `k` and compactified by itself: the `ℤ_ℓ`-module `Hⁱ_c(X_k̄, (ℤ_ℓ)ₙ)` is, as an
abelian group, the group of `i`-extensions of the constant sheaf `ℤ/N` on `X_k̄` by itself.  It is
`Ext^i_{ℤ_ℓ}(ℤ_ℓ, (ℤ_ℓ)ₙ|_{X_k̄})` (`extConstantAddEquivCompactSupportCohomology`), followed by the
change of coefficients along `ℤ_ℓ ↠ ℤ/N` (`extRestrictScalarsMap_bijective`). -/
def LAdicSheaf.constantLevelCohomologyAddEquiv (i : ℕ) (n : ℕ) :
    (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) ≃+
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) :=
  let Y := fieldBaseChange (Over.mk f) kbar
  let Λ := Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
    Y.smallEtaleTopology
  (extConstantAddEquivCompactSupportCohomology ℤ_[ℓ] f kbar
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) i).trans
    (((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ_[ℓ]
        Y.smallEtaleTopology) i).mapIso
      (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n)).addCommGroupIsoToAddEquiv.trans
      (AddEquiv.ofBijective (extRestrictScalarsMap (PadicInt.toZModPow (n + 1)) Y Λ i)
        (extRestrictScalarsMap_bijective Y (ℓ ^ (n + 1)) (ZMod.ringHom_surjective _)
          (toZModPow_eq_zero_iff (ℓ := ℓ) n) Λ i)).symm)

/-- Equal extension classes stay equal after composing with a degree-zero class. -/
private theorem comp_mk₀_congr {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {X Y Z : C} {i : ℕ} {α β : Ext.{u + 1} X Y i} (a : Y ⟶ Z) (h : α = β) :
    α.comp (Ext.mk₀ a) (add_zero i) = β.comp (Ext.mk₀ a) (add_zero i) := by
  rw [h]

/-- Composition with `a` followed by `e'` is composition with `e` followed by the conjugate
`e.inv ≫ a ≫ e'.hom` of `a`. -/
theorem ext_comp_mk₀_conj {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C] {X Y Y' Z Z' : C}
    {i : ℕ} (α : Ext.{u + 1} X Y i) (a : Y ⟶ Z) (e : Y ≅ Y') (e' : Z ≅ Z') :
    (α.comp (Ext.mk₀ a) (add_zero i)).comp (Ext.mk₀ e'.hom) (add_zero i) =
      (α.comp (Ext.mk₀ e.hom) (add_zero i)).comp (Ext.mk₀ (e.inv ≫ a ≫ e'.hom)) (add_zero i) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀, e.hom_inv_id_assoc]

/-- **Two changes of coefficients in a row**: for exact `R₁`, `R_c`, `R_n` with `R_c ⋙ R₁ ≅ R_n`
and reductions `u₁ : U₀ ⟶ R₁ U₁`, `π : U₁ ⟶ R_c U₂`, `u_n : U₀ ⟶ R_n U₂` with
`u₁ ≫ R₁ π ≫ e = u_n`, the comparison along `u₁` of the comparison along `π` is the comparison
along `u_n`, up to `e`. -/
theorem extMapAlong_extMapAlong {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [HasExt.{u + 1} C₀] [HasExt.{u + 1} C₁]
    [HasExt.{u + 1} C₂] [EnoughInjectives C₂]
    (R₁ : C₁ ⥤ C₀) [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    (Rc : C₂ ⥤ C₁) [Rc.Additive] [PreservesFiniteLimits Rc] [PreservesFiniteColimits Rc]
    (Rn : C₂ ⥤ C₀) [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
    (e : Rc ⋙ R₁ ≅ Rn) {U₀ : C₀} {U₁ : C₁} {U₂ : C₂} (u₁ : U₀ ⟶ R₁.obj U₁)
    (π : U₁ ⟶ Rc.obj U₂) (un : U₀ ⟶ Rn.obj U₂) (hu : u₁ ≫ R₁.map π ≫ e.hom.app U₂ = un)
    {i : ℕ} (z : Ext.{u + 1} U₂ U₂ i) :
    Stacks.Cohomology.ExtComparison.extMapAlong.{u + 1, u + 1} R₁ u₁ (Rc.obj U₂) i
        (Stacks.Cohomology.ExtComparison.extMapAlong.{u + 1, u + 1} Rc π U₂ i z) =
      (Stacks.Cohomology.ExtComparison.extMapAlong.{u + 1, u + 1} Rn un U₂ i z).comp
        (Ext.mk₀ (e.inv.app U₂)) (add_zero i) := by
  simp only [Stacks.Cohomology.ExtComparison.extMapAlong_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  rw [Stacks.ExtFunctorial.mapExactFunctor_comp_functor Rc R₁ U₂ i z]
  have key : z.mapExactFunctor (Rc ⋙ R₁) = ((Ext.mk₀ (e.hom.app U₂)).comp (z.mapExactFunctor Rn)
      (zero_add i)).comp (Ext.mk₀ (e.inv.app U₂)) (add_zero i) := by
    rw [Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.hom U₂ i z,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← NatTrans.comp_app, e.hom_inv_id,
      NatTrans.id_app, Ext.comp_mk₀_id]
  rw [key, ← hu, ← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]

/-- **The transitions of `Hⁱ(X_k̄, ℤ_ℓ)` on `Ext` over `ℤ_ℓ`**: through
`extConstantAddEquivCompactSupportCohomology` and `constantLevelInverseImageIso`, the transition
from level `n + 1` to level `n` is composition with the transition of the levels of `ℤ_ℓ`,
restricted to `X_k̄`. -/
theorem LAdicSheaf.constantLevel_transition_ext (i n : ℕ)
    (x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) (n + 1))) :
    (extConstantAddEquivCompactSupportCohomology ℤ_[ℓ] f kbar
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) i
        ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) i).map
            (homOfLE (n.le_add_right 1)).op x)).comp
        (Ext.mk₀ (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n).hom) (add_zero i) =
      ((extConstantAddEquivCompactSupportCohomology ℤ_[ℓ] f kbar
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
            (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) (n + 1))) i x).comp
        (Ext.mk₀ (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1)).hom)
          (add_zero i)).comp
        (Ext.mk₀ ((LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1)).inv ≫
          (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).map
            ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
              (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ≫
          (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n).hom)) (add_zero i) := by
  have := Fintype.ofFinite k
  rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ]
  have h := extConstantAddEquivCompactSupportCohomology_map ℤ_[ℓ] f kbar
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) i x
  exact (comp_mk₀_congr _ h).trans (ext_comp_mk₀_conj _ _ _ _)

/-- `d • 𝟙 ≫ g = 0` when `d` kills the target of `g`. -/
theorem nsmul_id_comp_eq_zero_of_nsmul_id_eq_zero {C : Type*} [Category* C] [Preadditive C]
    {A A' : C} (d : ℕ) (g : A ⟶ A') (h : d • 𝟙 A' = 0) : (d • 𝟙 A) ≫ g = 0 :=
  nsmul_id_comp_eq_zero_aux d g h

/-- **The transition of `ℤ_ℓ`, read on `X_k̄` as a map `res(ℤ/ℓⁿ⁺²) ⟶ res(ℤ/ℓⁿ⁺¹)` of sheaves of
`ℤ_ℓ`-modules, is a cokernel of `ℓⁿ⁺¹`**. -/
def LAdicSheaf.constantLevelTransitionIsCokernel (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (f := (ℓ ^ (n + 1)) • 𝟙
        ((etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) _).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1 + 1)))
            (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology)))
      ((LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1)).inv ≫
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).map
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
            (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ≫
        (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n).hom)
      (nsmul_id_comp_eq_zero_of_nsmul_id_eq_zero _ _
        (nsmul_id_restrictScalars_eq_zero _ _ (toZModPow_eq_zero_iff (ℓ := ℓ) n) _))) := by
  let I := etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)
  let H := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1 ⋙ I
  have : PreservesFiniteColimits I := etaleModuleInverseImage_preservesFiniteColimits _ _
  let F₀ := LAdicSheaf.constantSystem B X ℓ
  let s₂ := sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
  let s₁ := sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (p := ℓ) (n + 1))
  let c := etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
    (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) X.1
  have h₁ := CokernelCofork.mapIsColimit _ (LAdicSheaf.etaleTransitionIsCokernel B X ℓ F₀ n) H
  let E := (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor
  let s₂' : (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1).obj
      (LAdicSheaf.etaleLevel B X ℓ F₀ (n + 1)) ≅ E.obj (LAdicSheaf.padicLevel B X ℓ F₀ (n + 1)) :=
    s₂.app (F₀.level (n + 1))
  let s₁' : (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).obj
      (LAdicSheaf.etaleLevel B X ℓ F₀ n) ≅ E.obj (LAdicSheaf.padicLevel B X ℓ F₀ n) :=
    s₁.app (F₀.level n)
  have hk : E.map (LAdicSheaf.padicTransition B X ℓ F₀ n) ≫ s₁'.inv = s₂'.inv ≫
      (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1).map
        (LAdicSheaf.etaleTransition B X ℓ F₀ n) ≫ c.hom.app (LAdicSheaf.etaleLevel B X ℓ F₀ n) :=
    LAdicSheaf.sheafEquiv_map_padicTransition B X ℓ F₀ n
  have key : s₂'.inv ≫ (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1).map
        (LAdicSheaf.etaleTransition B X ℓ F₀ n) ≫ c.hom.app (LAdicSheaf.etaleLevel B X ℓ F₀ n) ≫
        s₁'.hom = E.map (LAdicSheaf.padicTransition B X ℓ F₀ n) := by
    rw [← Category.assoc, ← Category.assoc, Category.assoc s₂'.inv, ← hk, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine Cofork.isColimitOfIsos _ h₁ _
    (I.mapIso s₂' ≪≫ LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1))
    (I.mapIso s₂' ≪≫ LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1))
    (I.mapIso (c.app (LAdicSheaf.etaleLevel B X ℓ F₀ n) ≪≫ s₁') ≪≫
      LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n) ?_ ?_ ?_
  · simp [H]
  · simp
  · change _ = (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1)).inv ≫
      I.map (E.map (LAdicSheaf.padicTransition B X ℓ F₀ n)) ≫
      (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n).hom
    rw [← key]
    simp [H, CokernelCofork.map, Functor.map_comp]

/-- **The reduction `res(ℤ/ℓⁿ⁺²) ⟶ res(res(ℤ/ℓⁿ⁺¹)) = res(ℤ/ℓⁿ⁺¹)` on a scheme `Y` is a cokernel of
`ℓⁿ⁺¹`**, as sheaves of `ℤ_ℓ`-modules. -/
def constantLevelReductionIsCokernel (Y : Scheme.{u}) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (f := (ℓ ^ (n + 1)) • 𝟙
        ((etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) Y).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1 + 1)))
            Y.smallEtaleTopology)))
      ((etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) Y).map
          (LevelChange.reduction Y (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 1 + 1))) ≫
        (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
          (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) Y).hom.app
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
            Y.smallEtaleTopology))
      (nsmul_id_comp_eq_zero_of_nsmul_id_eq_zero _ _
        (nsmul_id_restrictScalars_eq_zero _ _ (toZModPow_eq_zero_iff (ℓ := ℓ) n) _))) := by
  have : NeZero (ℓ ^ (n + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hS := LevelChange.reductionShortComplex_exact Y (pow_dvd_pow ℓ (by lia : n + 1 ≤ n + 1 + 1))
  have h₁ := CokernelCofork.mapIsColimit _ hS.gIsCokernel
    (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) Y)
  refine Cofork.isColimitOfIsos _ h₁ _ (Iso.refl _) (Iso.refl _)
    ((etaleModuleRestrictScalarsComp (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
      (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) Y).app _) ?_ ?_ ?_
  · simp
  · simp
  · simp [CokernelCofork.map]

omit [Finite k] [QuasiCompact f] [IsProper f] in
/-- **The transition of `ℤ_ℓ` on `X_k̄` is the reduction up to an automorphism of `ℤ/ℓⁿ⁺¹`**. -/
theorem LAdicSheaf.exists_constantLevelTransition_eq (n : ℕ) :
    ∃ ψ : Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology,
      ((etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) _).map
          (LevelChange.reduction _ (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 1 + 1))) ≫
        (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
          (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) _).hom.app _) ≫
        (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) _).map ψ.hom =
      (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar (n + 1)).inv ≫
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj (Over.mk f) kbar)).map
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
            (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) n)) ≫
        (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar n).hom := by
  have hc := constantLevelReductionIsCokernel (ℓ := ℓ) (fieldBaseChange (Over.mk f) kbar) n
  have hd := LAdicSheaf.constantLevelTransitionIsCokernel B X ℓ f kbar n
  have := full_etaleModuleRestrictScalars_of_surjective (fieldBaseChange (Over.mk f) kbar)
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := ℓ) (n + 1)))
  let hR := Functor.FullyFaithful.ofFullyFaithful
    (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1))
      (fieldBaseChange (Over.mk f) kbar))
  refine ⟨hR.preimageIso (hc.coconePointUniqueUpToIso hd), ?_⟩
  rw [Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
  exact hc.comp_coconePointUniqueUpToIso_hom hd WalkingParallelPair.one

omit [Finite k] [QuasiCompact f] in
/-- Reading `LAdicSheaf.constantLevelCohomologyAddEquiv` back along the reduction
`ℤ_ℓ ⟶ ℤ/ℓᵐ⁺¹` recovers the class composed with `LAdicSheaf.constantLevelInverseImageIso`. -/
theorem LAdicSheaf.extMapAlong_unitReduction_constantLevelCohomologyAddEquiv (i m : ℕ)
    (y : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
      i).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) m)) :
    Stacks.Cohomology.ExtComparison.extMapAlong.{u + 1, u + 1}
        (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (m + 1))
          (fieldBaseChange (Over.mk f) kbar))
        (unitReduction (PadicInt.toZModPow (m + 1)) (fieldBaseChange (Over.mk f) kbar))
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (m + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i
        (LAdicSheaf.constantLevelCohomologyAddEquiv B X ℓ f kbar i m y) =
      (extConstantAddEquivCompactSupportCohomology ℤ_[ℓ] f kbar
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) m)) i y).comp
        (Ext.mk₀ (LAdicSheaf.constantLevelInverseImageIso B X ℓ f kbar m).hom) (add_zero i) :=
  AddEquiv.apply_symm_apply (AddEquiv.ofBijective
    (extRestrictScalarsMap (PadicInt.toZModPow (m + 1)) (fieldBaseChange (Over.mk f) kbar)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (m + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i)
    (extRestrictScalarsMap_bijective (fieldBaseChange (Over.mk f) kbar) (ℓ ^ (m + 1))
      (ZMod.ringHom_surjective _) (toZModPow_eq_zero_iff (ℓ := ℓ) m) _ i)) _

/-- **The transition square of `Hⁱ(X_k̄, ℤ_ℓ)` on `Ext`**: through
`LAdicSheaf.constantLevelCohomologyAddEquiv`, the transition from level `n + 1` to level `n`
followed by the change of level `Ext^i_{ℤ/ℓⁿ⁺¹}(ℤ/ℓⁿ⁺¹, ℤ/ℓⁿ⁺¹) ⟶ Ext^i_{ℤ/ℓⁿ⁺²}(ℤ/ℓⁿ⁺², ℤ/ℓⁿ⁺¹)`
(`LevelChange.extMap`) is composition with the reduction `ℤ/ℓⁿ⁺² ⟶ ℤ/ℓⁿ⁺¹` twisted by an
automorphism `ψ` of `ℤ/ℓⁿ⁺¹`. -/
theorem LAdicSheaf.exists_constantLevelCohomology_transition (i n : ℕ) :
    ∃ ψ : Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology,
    ∀ x : (geometricCompactSupportPadicCohomology B X ℓ f (CompactificationOf.ofProper f) kbar
        i).obj (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) (n + 1)),
      LevelChange.extMap _ (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 1 + 1))
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology) i
          (LAdicSheaf.constantLevelCohomologyAddEquiv B X ℓ f kbar i n
            ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f
              (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) i).map
                (homOfLE (n.le_add_right 1)).op x)) =
        (LAdicSheaf.constantLevelCohomologyAddEquiv B X ℓ f kbar i (n + 1) x).comp
          (Ext.mk₀ (LevelChange.reduction _ (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 1 + 1)) ≫
            (LevelChange.restrict _ (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 1 + 1))).map ψ.hom))
          (add_zero i) := by
  obtain ⟨ψ, hψ⟩ := LAdicSheaf.exists_constantLevelTransition_eq B X ℓ f kbar n
  refine ⟨ψ, fun x => ?_⟩
  let Y := fieldBaseChange (Over.mk f) kbar
  have hdvd : ℓ ^ (n + 1) ∣ ℓ ^ (n + 1 + 1) := pow_dvd_pow ℓ (by lia)
  let e := etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
    (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) Y
  have : EnoughInjectives (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) Y) :=
    etaleModules_enoughInjectives _ Y
  apply (extRestrictScalarsMap_bijective Y (ℓ ^ (n + 1 + 1)) (ZMod.ringHom_surjective _)
    (toZModPow_eq_zero_iff (ℓ := ℓ) (n + 1)) ((LevelChange.restrict Y hdvd).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        Y.smallEtaleTopology)) i).1
  refine (extMapAlong_extMapAlong (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) Y)
    (LevelChange.restrict Y hdvd) (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) Y) e
    (unitReduction (PadicInt.toZModPow (n + 1 + 1)) Y) (LevelChange.reduction Y hdvd)
    (unitReduction (PadicInt.toZModPow (n + 1)) Y)
    (unitReduction_comp_map_unitReduction Y _ (levelCast ℓ n) _ (toZModPow_succ_comp ℓ n)) _).trans
    (Eq.trans ?_ (Stacks.Cohomology.ExtComparison.extMapAlong_comp_mk₀
      (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) Y)
      (unitReduction (PadicInt.toZModPow (n + 1 + 1)) Y)
      (LevelChange.reduction Y hdvd ≫ (LevelChange.restrict Y hdvd).map ψ.hom)
      (LAdicSheaf.constantLevelCohomologyAddEquiv B X ℓ f kbar i (n + 1) x)).symm)
  refine (comp_mk₀_congr _
    (LAdicSheaf.extMapAlong_unitReduction_constantLevelCohomologyAddEquiv B X ℓ f kbar i n
      _)).trans ?_
  refine (comp_mk₀_congr _
    (LAdicSheaf.constantLevel_transition_ext B X ℓ f kbar i n x)).trans ?_
  refine Eq.trans ?_ (comp_mk₀_congr _
    (LAdicSheaf.extMapAlong_unitReduction_constantLevelCohomologyAddEquiv B X ℓ f kbar i (n + 1)
      x)).symm
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2
  rw [← hψ]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id, Functor.comp_map,
    Functor.map_comp]

end Stacks.EtaleCohomology

end
