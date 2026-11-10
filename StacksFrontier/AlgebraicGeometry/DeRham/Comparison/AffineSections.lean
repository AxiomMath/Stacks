module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.AffineOpenWedge
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Conditions
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.PresentationMapsNaturality
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Charts
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Rigidity
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenFormsMapSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# The maps of Section 0FL7 on the sections over affine opens

Let `f : Y ⟶ X` be a morphism of schemes and `(U, V)` a pair of affine opens with `f(V) ⊆ U`,
`A = Γ(X, U)`, `B = Γ(Y, V)`. This file identifies the sections over `V` of the sheaves of
Section 0FL7 with the modules of the ring-level construction of Remark 0FL9:

* `Γ(Ω_{Y/ℤ}, V) ≃ Ω[B⁄ℤ]` and `Γ(Ω^p_{Y/ℤ}, V) ≃ ⋀ᵖ Ω[B⁄ℤ]` (Stacks 01UT and 01I8);
* `Γ(f^*Ω_{X/ℤ}, V) ≃ B ⊗_A Ω[A⁄ℤ]` and `Γ(f^*Ω^q_{X/ℤ}, V) ≃ ⋀^q (B ⊗_A Ω[A⁄ℤ])`;

and the canonical map `f^*Ω^q_{X/ℤ} ⟶ Ω^q_{Y/ℤ}` with `⋀^q` of
`KaehlerDifferential.mapBaseChange ℤ A B`. It then proves, at the level of sheaves, the
consequence of conditions (0H9C) and (0H9D) recorded after their statement in Section 0FL7 and
in Tag 0FLA ("in particular"): `c^p` carries the image of a pulled back form `ω` to `ω ⊗ δ`;
and the rigidity of such maps on an affine chart on which the cokernel of
`B ⊗_A Ω[A⁄ℤ] → Ω[B⁄ℤ]` is killed by powers of a nonzerodivisor `J` of the target.

## Main definitions

* `AlgebraicGeometry.Scheme.absoluteDifferentialsSectionsEquiv`,
  `AlgebraicGeometry.Scheme.absoluteFormsSectionsEquiv`: the absolute differentials and forms on
  an affine open.
* `AlgebraicGeometry.Scheme.pullbackDifferentialsSectionsEquiv`,
  `AlgebraicGeometry.Scheme.pullbackFormsSectionsEquiv`: the pulled back ones.

## Main results

* `AlgebraicGeometry.Scheme.affineOpenExteriorPowerΓIso_absoluteFormsMap`: the canonical map on
  forms on an affine chart.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.app_absoluteFormsMap`: the maps of Section 0FL7 are
  multiplication by `δ` on pulled back forms.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.app_eq_of_isSMulRegular`: rigidity on an affine chart.
-/
@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra formsPullbackAffineOpenΓIso
    relativeDifferentialFormsMap_app_exteriorPower_map)
open Stacks.AlgebraicGeometry.AffineDifferentials (relativeDifferentialsMap_app_eq_mapBaseChange)

universe u

/-- If `ℤ → R` is surjective, the Kähler differentials of an `R`-algebra over `R` and over `ℤ`
agree. -/
def KaehlerDifferential.intEquivOfSurjective (R B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] (h : Function.Surjective (algebraMap ℤ R)) : Ω[B⁄ℤ] ≃ₗ[B] Ω[B⁄R] :=
  LinearEquiv.ofBijective (KaehlerDifferential.map ℤ R B B) ⟨by
    have := KaehlerDifferential.subsingleton_of_surjective ℤ R h
    have : Subsingleton (B ⊗[R] Ω[R⁄ℤ]) := inferInstance
    rw [← LinearMap.ker_eq_bot, ← KaehlerDifferential.range_mapBaseChange, LinearMap.range_eq_bot]
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply],
    KaehlerDifferential.map_surjective ℤ R B⟩

/-- `KaehlerDifferential.intEquivOfSurjective` on a universal differential. -/
theorem KaehlerDifferential.intEquivOfSurjective_D (R B : Type*) [CommRing R] [CommRing B]
    [Algebra R B] (h : Function.Surjective (algebraMap ℤ R)) (b : B) :
    KaehlerDifferential.intEquivOfSurjective R B h (KaehlerDifferential.D ℤ B b) =
      KaehlerDifferential.D R B b :=
  KaehlerDifferential.map_D ℤ R B B b

/-- `KaehlerDifferential.intEquivOfSurjective` commutes with the maps
`B ⊗[A] Ω[A⁄·] → Ω[B⁄·]`. -/
theorem KaehlerDifferential.intEquivOfSurjective_mapBaseChange (R A B : Type*) [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap ℤ R)) (t : B ⊗[A] Ω[A⁄ℤ]) :
    KaehlerDifferential.intEquivOfSurjective R B h (KaehlerDifferential.mapBaseChange ℤ A B t) =
      KaehlerDifferential.mapBaseChange R A B
        ((KaehlerDifferential.intEquivOfSurjective R A h).baseChange A B _ _ t) := by
  have key : ((KaehlerDifferential.intEquivOfSurjective R B h).toLinearMap.restrictScalars A).comp
      (KaehlerDifferential.map ℤ ℤ A B) =
      (KaehlerDifferential.map R R A B).comp
        (KaehlerDifferential.intEquivOfSurjective R A h).toLinearMap := by
    refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
    simp [KaehlerDifferential.intEquivOfSurjective_D]
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul b m =>
    rw [KaehlerDifferential.mapBaseChange_tmul, map_smul, LinearEquiv.baseChange_tmul,
      KaehlerDifferential.mapBaseChange_tmul]
    exact congrArg (b • ·) (LinearMap.congr_fun key m)

namespace AlgebraicGeometry.Scheme

/-- The ring of global sections of `Spec ℤ` receives `ℤ` surjectively. -/
theorem surjective_algebraMap_int_Γ_specZ :
    Function.Surjective (algebraMap ℤ Γ(Spec (.of (ULift.{u} ℤ)), ⊤)) := by
  intro x
  obtain ⟨y, rfl⟩ :=
    (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.symm.surjective x
  refine ⟨y.down, ?_⟩
  have hy : y = ((y.down : ℤ) : ULift.{u} ℤ) := ULift.ext (by simp)
  rw [algebraMap_int_eq, eq_intCast]
  conv_rhs => rw [hy]
  rw [map_intCast]

variable (Y : Scheme.{u}) {V : Y.Opens} (hV : IsAffineOpen V)

/-- **The absolute differentials of a scheme on an affine open**:
`Γ(Ω_{Y/ℤ}, V) ≃ Ω[Γ(Y, V)⁄ℤ]`, Stacks 01UT for the morphism to `Spec ℤ`. -/
def absoluteDifferentialsSectionsEquiv :
    Γ(Hom.relativeDifferentials Y.toSpecZ, V) ≃ₗ[Γ(Y, V)] Ω[Γ(Y, V)⁄ℤ] :=
  letI := (Y.toSpecZ.appLE ⊤ V le_top).hom.toAlgebra
  haveI := Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections Y.toSpecZ hV
    (V := ⊤) le_top (isAffineOpen_top _)
  let e := asIso (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections Y.toSpecZ ⊤ V
    le_top)
  let φ : Γ(Hom.relativeDifferentials Y.toSpecZ, V) →ₗ[Γ(Y, V)]
      Ω[Γ(Y, V)⁄Γ(Spec (.of (ULift.{u} ℤ)), ⊤)] :=
    { toFun := fun m => e.inv.hom m
      map_add' := fun a c => map_add _ a c
      map_smul' := fun c a => map_smul _ c a }
  let ψ : Ω[Γ(Y, V)⁄Γ(Spec (.of (ULift.{u} ℤ)), ⊤)] →ₗ[Γ(Y, V)]
      Γ(Hom.relativeDifferentials Y.toSpecZ, V) :=
    { toFun := fun m => e.hom.hom m
      map_add' := fun a c => map_add _ a c
      map_smul' := fun c a => map_smul _ c a }
  let e₁ : Γ(Hom.relativeDifferentials Y.toSpecZ, V) ≃ₗ[Γ(Y, V)]
      Ω[Γ(Y, V)⁄Γ(Spec (.of (ULift.{u} ℤ)), ⊤)] :=
    LinearEquiv.ofLinearMap φ ψ
      (LinearMap.ext fun x => congrArg (fun g => g.hom x) e.hom_inv_id)
      (LinearMap.ext fun x => congrArg (fun g => g.hom x) e.inv_hom_id)
  let e₂ : Ω[Γ(Y, V)⁄Γ(Spec (.of (ULift.{u} ℤ)), ⊤)] ≃ₗ[Γ(Y, V)] Ω[Γ(Y, V)⁄ℤ] :=
    (KaehlerDifferential.intEquivOfSurjective _ _ surjective_algebraMap_int_Γ_specZ).symm
  e₁ ≪≫ₗ e₂

/-- `absoluteDifferentialsSectionsEquiv` carries `d b` to `D b`. -/
theorem absoluteDifferentialsSectionsEquiv_symm_D (b : Γ(Y, V)) :
    (absoluteDifferentialsSectionsEquiv Y hV).symm (KaehlerDifferential.D ℤ Γ(Y, V) b) =
      (Hom.universalRelativeDerivation Y.toSpecZ).d b := by
  let := (Y.toSpecZ.appLE ⊤ V le_top).hom.toAlgebra
  change (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections Y.toSpecZ ⊤ V
    le_top).hom (KaehlerDifferential.intEquivOfSurjective _ _ surjective_algebraMap_int_Γ_specZ
      (KaehlerDifferential.D ℤ Γ(Y, V) b)) = _
  rw [KaehlerDifferential.intEquivOfSurjective_D]
  exact Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d Y.toSpecZ ⊤ V le_top b

/-- **The absolute differential `p`-forms of a scheme on an affine open**:
`Γ(Ω^p_{Y/ℤ}, V) ≃ ⋀ᵖ Ω[Γ(Y, V)⁄ℤ]`, Stacks 01I8 and 01UT. -/
def absoluteFormsSectionsEquiv (p : ℕ) :
    Γ(absoluteDifferentialForms Y p, V) ≃ₗ[Γ(Y, V)] ⋀[Γ(Y, V)]^p Ω[Γ(Y, V)⁄ℤ] :=
  (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso (Hom.relativeDifferentials Y.toSpecZ)
      hV (isExteriorAlgebra_relativeDifferentialFormsAlgebra
        Y.toSpecZ) p).toLinearEquiv ≪≫ₗ
    Stacks.AffineExteriorPower.exteriorPowerCongr (absoluteDifferentialsSectionsEquiv Y hV) p

/-- `absoluteFormsSectionsEquiv` unfolded. -/
theorem absoluteFormsSectionsEquiv_apply (p : ℕ) (ω : Γ(absoluteDifferentialForms Y p, V)) :
    absoluteFormsSectionsEquiv Y hV p ω =
      exteriorPower.map p (absoluteDifferentialsSectionsEquiv Y hV).toLinearMap
        ((Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
          (Hom.relativeDifferentials Y.toSpecZ) hV
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra
            Y.toSpecZ) p).hom ω) :=
  rfl

variable {Y} {X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (e : V ≤ f ⁻¹ᵁ U)

include hV hU in
/-- The pullback of local sections of `Ω_{X/ℤ}` over `U` to sections of `f^*Ω_{X/ℤ}` over `V`
exhibits the latter as the base change of the former, for affine `U`, `V` with `V ≤ f⁻¹U`. -/
theorem isBaseChange_pullbackSectionHom :
    letI := (f.appLE U V e).hom.toAlgebra
    letI : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj
        (Hom.relativeDifferentials X.toSpecZ), V) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
    haveI : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj
        (Hom.relativeDifferentials X.toSpecZ), V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ ρ : Γ(Hom.relativeDifferentials X.toSpecZ, U) →ₗ[Γ(X, U)]
        Γ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ), V),
      (∀ a, ρ a = pullbackSectionHom f (Hom.relativeDifferentials X.toSpecZ) U V e a) ∧
        IsBaseChange Γ(Y, V) ρ := by
  let := (f.appLE U V e).hom.toAlgebra
  let : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj
      (Hom.relativeDifferentials X.toSpecZ), V) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj
      (Hom.relativeDifferentials X.toSpecZ), V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : (Hom.relativeDifferentials X.toSpecZ).IsQuasicoherent :=
    Hom.isQuasicoherent_relativeDifferentials X.toSpecZ
  let ρ : Γ(Hom.relativeDifferentials X.toSpecZ, U) →ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ), V) :=
    { toFun := pullbackSectionHom f (Hom.relativeDifferentials X.toSpecZ) U V e
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a =>
        pullbackSectionHom_smul f (Hom.relativeDifferentials X.toSpecZ) U V e r a }
  exact ⟨ρ, fun _ => rfl, AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
    (f.appLE U V e).hom rfl
    (affinePullbackSectionsBaseChangeIso f (Hom.relativeDifferentials X.toSpecZ) hU hV e)
    ρ fun m => affinePullbackSectionsBaseChangeIso_one_tmul f
      (Hom.relativeDifferentials X.toSpecZ) hU hV e m⟩

/-- **The pulled back absolute differentials on an affine open**:
`Γ(f^*Ω_{X/ℤ}, V) ≃ Γ(Y, V) ⊗_{Γ(X, U)} Ω[Γ(X, U)⁄ℤ]` for affine `U`, `V` with `V ≤ f⁻¹U`. -/
def pullbackDifferentialsSectionsEquiv :
    letI := (f.appLE U V e).hom.toAlgebra
    Γ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ), V) ≃ₗ[Γ(Y, V)]
      Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ] :=
  letI := (f.appLE U V e).hom.toAlgebra
  letI : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj
      (Hom.relativeDifferentials X.toSpecZ), V) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
  haveI : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj
      (Hom.relativeDifferentials X.toSpecZ), V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Γ(Y, V) Γ(Y, V))
      (absoluteDifferentialsSectionsEquiv X hU).symm).trans
    (isBaseChange_pullbackSectionHom hV f hU e).choose_spec.2.equiv).symm

/-- `pullbackDifferentialsSectionsEquiv` carries `1 ⊗ D a` to the pullback of `d a`. -/
theorem pullbackDifferentialsSectionsEquiv_symm_one_tmul_D (a : Γ(X, U)) :
    letI := (f.appLE U V e).hom.toAlgebra
    (pullbackDifferentialsSectionsEquiv hV f hU e).symm
        ((1 : Γ(Y, V)) ⊗ₜ KaehlerDifferential.D ℤ Γ(X, U) a) =
      Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
        ((Hom.universalRelativeDerivation X.toSpecZ).d a) := by
  let := (f.appLE U V e).hom.toAlgebra
  let : Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj
      (Hom.relativeDifferentials X.toSpecZ), V) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj
      (Hom.relativeDifferentials X.toSpecZ), V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h := (isBaseChange_pullbackSectionHom hV f hU e).choose_spec
  change h.2.equiv ((1 : Γ(Y, V)) ⊗ₜ (absoluteDifferentialsSectionsEquiv X hU).symm
    (KaehlerDifferential.D ℤ Γ(X, U) a)) = _
  rw [h.2.equiv_tmul, one_smul, h.1, absoluteDifferentialsSectionsEquiv_symm_D]
  rfl

/-- **The pulled back absolute differential `q`-forms on an affine open**:
`Γ(f^*Ω^q_{X/ℤ}, V) ≃ ⋀^q (Γ(Y, V) ⊗_{Γ(X, U)} Ω[Γ(X, U)⁄ℤ])`. -/
def pullbackFormsSectionsEquiv (q : ℕ) :
    letI := (f.appLE U V e).hom.toAlgebra
    Γ(f.pullbackForms q, V) ≃ₗ[Γ(Y, V)] ⋀[Γ(Y, V)]^q (Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ]) :=
  letI := (f.appLE U V e).hom.toAlgebra
  (formsPullbackAffineOpenΓIso f X.toSpecZ
      hV q).toLinearEquiv ≪≫ₗ
    Stacks.AffineExteriorPower.exteriorPowerCongr (pullbackDifferentialsSectionsEquiv hV f hU e) q

/-- `pullbackFormsSectionsEquiv` unfolded. -/
theorem pullbackFormsSectionsEquiv_symm_apply (q : ℕ)
    (ω : letI := (f.appLE U V e).hom.toAlgebra;
      ⋀[Γ(Y, V)]^q (Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ])) :
    letI := (f.appLE U V e).hom.toAlgebra
    (pullbackFormsSectionsEquiv hV f hU e q).symm ω =
      (formsPullbackAffineOpenΓIso f
        X.toSpecZ hV q).inv
        (exteriorPower.map q (pullbackDifferentialsSectionsEquiv hV f hU e).symm.toLinearMap ω) :=
  rfl

/-- **The canonical map `f^*Ω_{X/ℤ} ⟶ Ω_{Y/ℤ}` on an affine chart** is
`KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V)`, read through the identifications of the
sections with Kähler differentials. -/
theorem relativeDifferentialsMap_app_pullbackDifferentialsSectionsEquiv_symm
    (t : letI := (f.appLE U V e).hom.toAlgebra; Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ]) :
    letI := (f.appLE U V e).hom.toAlgebra
    (Hom.relativeDifferentialsMap f X.toSpecZ Y.toSpecZ (𝟙 _) (comp_toSpecZ f)).app V
        ((pullbackDifferentialsSectionsEquiv hV f hU e).symm t) =
      (absoluteDifferentialsSectionsEquiv Y hV).symm
        (KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V) t) := by
  let : Algebra Γ(Spec (.of (ULift.{u} ℤ)), ⊤) Γ(X, U) :=
    (X.toSpecZ.appLE ⊤ U le_top).hom.toAlgebra
  let := (f.appLE U V e).hom.toAlgebra
  let : Algebra Γ(Spec (.of (ULift.{u} ℤ)), ⊤) Γ(Y, V) :=
    (Y.toSpecZ.appLE ⊤ V le_top).hom.toAlgebra
  have := Stacks.AlgebraicGeometry.AffineDifferentials.isScalarTower_appLE f X.toSpecZ
    Y.toSpecZ (comp_toSpecZ f) ⊤ U V le_top e le_top
  set iA := KaehlerDifferential.intEquivOfSurjective Γ(Spec (.of (ULift.{u} ℤ)), ⊤) Γ(X, U)
    surjective_algebraMap_int_Γ_specZ
  set iB := KaehlerDifferential.intEquivOfSurjective Γ(Spec (.of (ULift.{u} ℤ)), ⊤) Γ(Y, V)
    surjective_algebraMap_int_Γ_specZ
  have key := relativeDifferentialsMap_app_eq_mapBaseChange
    f X.toSpecZ Y.toSpecZ (comp_toSpecZ f) ⊤ U V le_top e le_top
    ((pullbackDifferentialsSectionsEquiv hV f hU e).symm.toLinearMap.comp
      (iA.baseChange Γ(X, U) Γ(Y, V) _ _).symm.toLinearMap)
    ((absoluteDifferentialsSectionsEquiv Y hV).symm.toLinearMap.comp iB.symm.toLinearMap)
    (fun a => by
      change (pullbackDifferentialsSectionsEquiv hV f hU e).symm
        ((1 : Γ(Y, V)) ⊗ₜ iA.symm (KaehlerDifferential.D _ Γ(X, U) a)) = _
      rw [(LinearEquiv.symm_apply_eq iA).mpr
          (KaehlerDifferential.intEquivOfSurjective_D _ _ _ a).symm,
        pullbackDifferentialsSectionsEquiv_symm_one_tmul_D]
      rfl)
    (fun c => by
      change (absoluteDifferentialsSectionsEquiv Y hV).symm
        (iB.symm (KaehlerDifferential.D _ Γ(Y, V) c)) = _
      rw [(LinearEquiv.symm_apply_eq iB).mpr
          (KaehlerDifferential.intEquivOfSurjective_D _ _ _ c).symm,
        absoluteDifferentialsSectionsEquiv_symm_D])
    (iA.baseChange Γ(X, U) Γ(Y, V) _ _ t)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at key
  rw [key, ← KaehlerDifferential.intEquivOfSurjective_mapBaseChange, LinearEquiv.symm_apply_apply]

/-- **The canonical map `f^*Ω^q_{X/ℤ} ⟶ Ω^q_{Y/ℤ}` on an affine chart**, read through the
identification of sections of `f^*Ω^q_{X/ℤ}` with exterior powers. -/
theorem affineOpenExteriorPowerΓIso_absoluteFormsMap (q : ℕ)
    (ω : letI := (f.appLE U V e).hom.toAlgebra;
      ⋀[Γ(Y, V)]^q (Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ])) :
    letI := (f.appLE U V e).hom.toAlgebra
    (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
        (Hom.relativeDifferentials Y.toSpecZ) hV
        (isExteriorAlgebra_relativeDifferentialFormsAlgebra
          Y.toSpecZ) q).hom
      ((f.absoluteFormsMap q).app V
        ((formsPullbackAffineOpenΓIso f
          X.toSpecZ hV q).inv
          (exteriorPower.map q (pullbackDifferentialsSectionsEquiv hV f hU e).symm.toLinearMap
            ω))) =
      exteriorPower.map q (absoluteDifferentialsSectionsEquiv Y hV).symm.toLinearMap
        (exteriorPower.map q (KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V)) ω) := by
  let := (f.appLE U V e).hom.toAlgebra
  exact relativeDifferentialFormsMap_app_exteriorPower_map
    f X.toSpecZ Y.toSpecZ hV q (comp_toSpecZ f) _ _ _ (LinearMap.ext fun t =>
      relativeDifferentialsMap_app_pullbackDifferentialsSectionsEquiv_symm hV f hU e t) ω

end AlgebraicGeometry.Scheme

/-! ### The maps of Section 0FL7 on pulled back forms -/

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.PullbackTensorCoherence MonoidalCategory

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : Scheme.{u}} {f : Y ⟶ X} {L : Y.Modules}

/-- The unit of a graded algebra restricted to an open is its unit there. -/
theorem _root_.SheafOfModules.GradedAlgebra.one_eval_map {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (E : SheafOfModules.GradedAlgebra.{u, u} R) {U V : Cᵒᵖ} (g : U ⟶ V) :
    (E.piece 0).val.map g (E.one.eval U) = E.one.eval V :=
  PresheafOfModules.sections_property E.one g

/-- **The maps of Section 0FL7 on pulled back forms are multiplication by `δ`** (Stacks Tag 0FLA,
"in particular"; Section 0FL7, the remark after the conditions): if `c` satisfies (0H9C) and
(0H9D), then `c^p` carries the image of a local section `ω` of `f^*Ω^p_{X/ℤ}` in `Ω^p_{Y/ℤ}` to
`ω ⊗ δ`. -/
theorem GarelMaps.app_absoluteFormsMap {δ : Γ(L, ⊤)} {c : f.GarelMaps L} (hn : c.IsNormalized δ)
    (hm : c.IsMultiplicative) (p : ℕ) (V : Y.Opens) (ω : (f.pullbackForms p).val.obj (op V)) :
    (c p).val.app (op V) ((f.absoluteFormsMap p).val.app (op V) ω) =
      f.twistedPullbackFormsTmul L p V ω (L.val.map (homOfLE le_top).op δ) := by
  set one₀ := (absoluteDifferentialFormsAlgebra Y).one.eval (op V)
  set δV := L.val.map (homOfLE (le_top : V ≤ ⊤)).op δ
  have hmul := (GarelMaps.isMultiplicative_iff c).mp hm p 0 V ω one₀
  rw [absoluteFormsAction_tmul] at hmul
  have e₁ : eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add p 0).symm) =
      𝟙 (absoluteDifferentialForms Y (p + 0 : ℕ)) :=
    eqToHom_refl _ _
  have e₂ : eqToHom (congrArg (f.twistedPullbackForms L) (Nat.cast_add p 0).symm) =
      𝟙 (f.twistedPullbackForms L (p + 0 : ℕ)) :=
    eqToHom_refl _ _
  have h1 : (eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add p 0).symm)).val.app
      (op V) (((absoluteDifferentialFormsAlgebra Y).mul p 0).app (op V)
        ((f.absoluteFormsMap p).val.app (op V) ω) one₀) =
      (f.absoluteFormsMap p).val.app (op V) ω := by
    rw [e₁]
    exact eq_of_heq ((absoluteDifferentialFormsAlgebra Y).mul_one p (op V) _)
  have hc0 : (c 0).val.app (op V) one₀ =
      f.twistedPullbackFormsTmul L 0 V ((pullbackFormsAlgebra f).one.eval (op V)) δV := by
    have h := (GarelMaps.isNormalized_iff δ c).mp hn
    have hnat := congrArg ((f.twistedPullbackForms L 0).val.map (homOfLE (le_top : V ≤ ⊤)).op) h
    refine (congrArg ((c 0).val.app (op V))
      (SheafOfModules.GradedAlgebra.one_eval_map _ (homOfLE (le_top : V ≤ ⊤)).op).symm).trans ?_
    refine (PresheafOfModules.naturality_apply (c 0).val (homOfLE (le_top : V ≤ ⊤)).op
      _).trans (hnat.trans ?_)
    · refine (tmul_restrict (homOfLE (le_top : V ≤ ⊤)).op _ _).trans ?_
      exact congrArg (fun z => f.twistedPullbackFormsTmul L 0 V z δV)
        (SheafOfModules.GradedAlgebra.one_eval_map (pullbackFormsAlgebra f)
          (homOfLE (le_top : V ≤ ⊤)).op)
  have h2 : (eqToHom (congrArg (f.twistedPullbackForms L) (Nat.cast_add p 0).symm)).val.app
      (op V) (f.twistedPullbackFormsTmul L (p + 0 : ℕ) V
        (((pullbackFormsAlgebra f).mul p 0).app (op V) ω
          ((pullbackFormsAlgebra f).one.eval (op V))) δV) =
      f.twistedPullbackFormsTmul L p V ω δV := by
    rw [e₂]
    exact congrArg (fun z => f.twistedPullbackFormsTmul L p V z δV)
      (eq_of_heq ((pullbackFormsAlgebra f).mul_one p (op V) ω))
  refine (congrArg ((c p).val.app (op V)) h1.symm).trans (hmul.trans ?_)
  refine (congrArg (fun z => (f.twistedPullbackFormsMul L p 0).val.app (op V)
    (tmul Y.toRingedSpace (f.pullbackForms p) (f.twistedPullbackForms L 0) (op V) ω z))
    hc0).trans ?_
  exact (twistedPullbackFormsMul_tmul f L p 0 V ω _ δV).trans h2

/-- **Pulled back forms generate up to `J`-torsion, on an affine chart.** If every element of
`Ω[Γ(Y, V)⁄ℤ]` is carried into the image of `Γ(Y, V) ⊗ Ω[Γ(X, U)⁄ℤ]` by a power of `J`, then every
local section of `Ω^p_{Y/ℤ}` over `V` is carried by a power of `J` into the image of
`f^*Ω^p_{X/ℤ}`. -/
theorem exists_pow_smul_eq_absoluteFormsMap {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (e : V ≤ f ⁻¹ᵁ U) (J : Γ(Y, V))
    (hJ : letI := (f.appLE U V e).hom.toAlgebra; ∀ x : Ω[Γ(Y, V)⁄ℤ], ∃ k : ℕ,
      J ^ k • x ∈ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V)))
    (p : ℕ) (η : Γ(absoluteDifferentialForms Y p, V)) :
    ∃ (k : ℕ) (ζ : Γ(f.pullbackForms p, V)), (f.absoluteFormsMap p).app V ζ = J ^ k • η := by
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨k, ω, hω⟩ := exteriorPower.exists_pow_smul_mem_range_map
    (KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V)) J hJ p
    (absoluteFormsSectionsEquiv Y hV p η)
  have k1 := affineOpenExteriorPowerΓIso_absoluteFormsMap hV f hU e p ω
  refine ⟨k, (pullbackFormsSectionsEquiv hV f hU e p).symm ω,
    (absoluteFormsSectionsEquiv Y hV p).injective ?_⟩
  rw [pullbackFormsSectionsEquiv_symm_apply, absoluteFormsSectionsEquiv_apply, k1]
  exact ((Stacks.AffineExteriorPower.exteriorPowerCongr _ p).apply_symm_apply _).trans
    (hω.trans (map_smul _ _ _).symm)

/-- **Rigidity of the maps of Section 0FL7 on an affine chart** (proof of Stacks Tag 0FLA). Let
`c`, `c'` satisfy (0H9C) and (0H9D) for the same `δ`. If on an affine chart `(U, V)` the cokernel
of `Γ(Y, V) ⊗ Ω[Γ(X, U)⁄ℤ] → Ω[Γ(Y, V)⁄ℤ]` is killed by powers of `J` and `J` is a
nonzerodivisor on the sections over `V` of every `f^*Ω^p_{X/ℤ} ⊗ L`, then `c` and `c'` agree on
the sections over `V`. -/
theorem GarelMaps.app_eq_of_isSMulRegular {δ : Γ(L, ⊤)} {c c' : f.GarelMaps L}
    (hn : c.IsNormalized δ) (hm : c.IsMultiplicative) (hn' : c'.IsNormalized δ)
    (hm' : c'.IsMultiplicative) {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (e : V ≤ f ⁻¹ᵁ U) (J : Γ(Y, V))
    (hJ : letI := (f.appLE U V e).hom.toAlgebra; ∀ x : Ω[Γ(Y, V)⁄ℤ], ∃ k : ℕ,
      J ^ k • x ∈ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V)))
    (hreg : ∀ p : ℕ, IsSMulRegular Γ(f.twistedPullbackForms L p, V) J) (p : ℕ)
    (η : Γ(absoluteDifferentialForms Y p, V)) :
    (c p).app V η = (c' p).app V η := by
  obtain ⟨k, ζ, hζ⟩ := exists_pow_smul_eq_absoluteFormsMap hV hU e J hJ p η
  refine (hreg p).pow k ?_
  change J ^ k • (c p).app V η = J ^ k • (c' p).app V η
  rw [← Scheme.Modules.Hom.app_smul, ← Scheme.Modules.Hom.app_smul, ← hζ]
  exact (GarelMaps.app_absoluteFormsMap hn hm p V ζ).trans
    (GarelMaps.app_absoluteFormsMap hn' hm' p V ζ).symm

end AlgebraicGeometry.Scheme.Hom

/-! ### Multiplicativity of the identifications -/

namespace AlgebraicGeometry.Scheme

open Stacks.AffineExteriorPower

variable (Y : Scheme.{u}) {V : Y.Opens} (hV : IsAffineOpen V)

/-- `absoluteFormsSectionsEquiv` unfolded, with the comparison applied as a linear map. -/
theorem absoluteFormsSectionsEquiv_apply_hom (p : ℕ) (ω : Γ(absoluteDifferentialForms Y p, V)) :
    absoluteFormsSectionsEquiv Y hV p ω =
      exteriorPower.map p (absoluteDifferentialsSectionsEquiv Y hV).toLinearMap
        ((Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
          (Hom.relativeDifferentials Y.toSpecZ) hV
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra
            Y.toSpecZ) p).hom.hom ω) :=
  rfl

/-- **The identification of absolute forms on an affine open is multiplicative**: it carries the
product of `Ω^•_{Y/ℤ}` to the wedge product. -/
theorem absoluteFormsSectionsEquiv_mul (p q : ℕ) (α : Γ(absoluteDifferentialForms Y p, V))
    (β : Γ(absoluteDifferentialForms Y q, V)) :
    absoluteFormsSectionsEquiv Y hV (p + q)
        ((eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add p q).symm)).val.app
          (op V) (((absoluteDifferentialFormsAlgebra Y).mul p q).app (op V) α β)) =
      exteriorPower.wedgeMul p q (absoluteFormsSectionsEquiv Y hV p α)
        (absoluteFormsSectionsEquiv Y hV q β) := by
  refine (absoluteFormsSectionsEquiv_apply_hom Y hV (p + q) _).trans ?_
  rw [affineOpenExteriorPowerΓIso_hom_mul, exteriorPower.wedgeMul_map]
  exact congrArg₂ (fun x y => exteriorPower.wedgeMul p q x y)
    (absoluteFormsSectionsEquiv_apply_hom Y hV p α).symm
    (absoluteFormsSectionsEquiv_apply_hom Y hV q β).symm

/-- The identification of absolute forms on an affine open carries the unit to the empty
wedge. -/
theorem absoluteFormsSectionsEquiv_one :
    absoluteFormsSectionsEquiv Y hV 0 ((absoluteDifferentialFormsAlgebra Y).one.eval (op V)) =
      exteriorPower.ιMulti Γ(Y, V) 0 Fin.elim0 := by
  have h := congrArg (exteriorPower.map 0 (absoluteDifferentialsSectionsEquiv Y hV).toLinearMap)
    (affineOpenExteriorPowerΓIso_hom_one _ hV
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra Y.toSpecZ))
  refine (absoluteFormsSectionsEquiv_apply Y hV 0 _).trans (h.trans ?_)
  exact (exteriorPower.map_apply_ιMulti _ _).trans
    (congrArg (exteriorPower.ιMulti Γ(Y, V) 0) (funext fun i => i.elim0))

variable {Y} {X : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (e : V ≤ f ⁻¹ᵁ U)

open Stacks.AlgebraicGeometry.AffineDifferentialForms (pullbackFormsIso)
open Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The comparison `formsPullbackAffineOpenΓIso` applied to a section. -/
theorem formsPullbackAffineOpenΓIso_hom_apply (q : ℕ) (ω : Γ(f.pullbackForms q, V)) :
    (formsPullbackAffineOpenΓIso f X.toSpecZ hV q).hom ω =
      (affineOpenExteriorPowerΓIso
          ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ)) hV
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) q).hom.hom
          (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom V ω) :=
  rfl

/-- `pullbackFormsSectionsEquiv` unfolded through `formsPullbackAffineOpenΓIso`. -/
theorem pullbackFormsSectionsEquiv_apply_iso (q : ℕ) (ω : Γ(f.pullbackForms q, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    pullbackFormsSectionsEquiv hV f hU e q ω =
      exteriorPower.map q (pullbackDifferentialsSectionsEquiv hV f hU e).toLinearMap
        ((formsPullbackAffineOpenΓIso f X.toSpecZ hV q).hom ω) :=
  rfl

/-- `pullbackFormsSectionsEquiv` unfolded: the comparison of Tag 01CI on sections, the comparison
of Tag 01I8, and `⋀^q` of the identification in degree one. -/
theorem pullbackFormsSectionsEquiv_apply (q : ℕ) (ω : Γ(f.pullbackForms q, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    pullbackFormsSectionsEquiv hV f hU e q ω =
      exteriorPower.map q (pullbackDifferentialsSectionsEquiv hV f hU e).toLinearMap
        ((affineOpenExteriorPowerΓIso
          ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ)) hV
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) q).hom.hom
          (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom V ω)) :=
  (pullbackFormsSectionsEquiv_apply_iso hV f hU e q ω).trans
    (congrArg _ (formsPullbackAffineOpenΓIso_hom_apply hV f q ω))

/-- **The canonical map `f^*Ω^q_{X/ℤ} ⟶ Ω^q_{Y/ℤ}` on an affine chart** is `⋀^q` of
`KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V)`, read through the identifications of the
sections with exterior powers. -/
theorem absoluteFormsSectionsEquiv_absoluteFormsMap (q : ℕ) (ω : Γ(f.pullbackForms q, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    absoluteFormsSectionsEquiv Y hV q ((f.absoluteFormsMap q).val.app (op V) ω) =
      exteriorPower.map q (KaehlerDifferential.mapBaseChange ℤ Γ(X, U) Γ(Y, V))
        (pullbackFormsSectionsEquiv hV f hU e q ω) := by
  let := (f.appLE U V e).hom.toAlgebra
  have h := affineOpenExteriorPowerΓIso_absoluteFormsMap hV f hU e q
    (pullbackFormsSectionsEquiv hV f hU e q ω)
  have hω : (formsPullbackAffineOpenΓIso f X.toSpecZ hV q).inv
      (exteriorPower.map q (pullbackDifferentialsSectionsEquiv hV f hU e).symm.toLinearMap
        (pullbackFormsSectionsEquiv hV f hU e q ω)) = ω :=
    (pullbackFormsSectionsEquiv_symm_apply hV f hU e q _).symm.trans
      (LinearEquiv.symm_apply_apply _ _)
  rw [hω] at h
  refine (absoluteFormsSectionsEquiv_apply_hom Y hV q _).trans ?_
  refine (congrArg (exteriorPower.map q (absoluteDifferentialsSectionsEquiv Y hV).toLinearMap)
    h).trans ?_
  exact (exteriorPowerCongr (absoluteDifferentialsSectionsEquiv Y hV) q).apply_symm_apply _

/-- **The comparison of Tag 01CI for absolute forms is multiplicative**: on every local section,
it carries the product of `f^*Ω^•_{X/ℤ}` to the product of `⋀(f^*Ω_{X/ℤ})`. -/
theorem pullbackFormsIso_hom_app_mul (p q : ℤ) (W : Y.Opens) (α : Γ(f.pullbackForms p, W))
    (β : Γ(f.pullbackForms q, W)) :
    Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ (p + q)).hom W
        (((Hom.pullbackFormsAlgebra f).mul p q).app (op W) α β) =
      ((Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
          (Hom.relativeDifferentials X.toSpecZ))).mul p q).app (op W)
        (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ p).hom W α)
        (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom W β) := by
  have key : ((Hom.pullbackFormsAlgebra f).mul p q).app (op W) α β =
      ((Stacks.PullbackExteriorAlgebra.comparisonGradedAlgebra f.toLRSHom.toShHom
        (absoluteDifferentialFormsAlgebra X)).mul p q).app (op W) α β :=
    (mulHom_tmul (Z := Y.toRingedSpace) (Hom.pullbackFormsAlgebra f) p q (op W) α β).symm.trans
      (congrArg (fun φ => φ.val.app (op W) (tmul Y.toRingedSpace _ _ (op W) α β))
        (Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra f.toLRSHom.toShHom
          (absoluteDifferentialFormsAlgebra X) p q))
  exact (congrArg (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ (p + q)).hom W)
    key).trans ((Stacks.PullbackExteriorAlgebra.comparisonUnitalHom f.toLRSHom.toShHom
      (Hom.relativeDifferentialFormsAlgebra X.toSpecZ)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Hom.relativeDifferentials X.toSpecZ))
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).1).map_mul p q (op W) α β)

/-- **The comparison of Tag 01CI for absolute forms is unital.** -/
theorem pullbackFormsIso_hom_app_one (W : Y.Opens) :
    Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ 0).hom W
        ((Hom.pullbackFormsAlgebra f).one.eval (op W)) =
      (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
          (Hom.relativeDifferentials X.toSpecZ))).one.eval (op W) := by
  have hW : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine (congrArg (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ 0).hom W)
    (SheafOfModules.GradedAlgebra.one_eval_map (Hom.pullbackFormsAlgebra f)
      (homOfLE hW).op).symm).trans ?_
  refine (PresheafOfModules.naturality_apply (pullbackFormsIso f X.toSpecZ 0).hom.val
    (homOfLE hW).op _).trans ?_
  refine Eq.trans ?_ (SheafOfModules.GradedAlgebra.one_eval_map (Scheme.Modules.exteriorAlgebra
    ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ))) (homOfLE hW).op)
  refine congrArg _ ?_
  refine (congrArg (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ 0).hom (f ⁻¹ᵁ ⊤))
    (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval f.toLRSHom.toShHom
      (absoluteDifferentialFormsAlgebra X) ⊤)).trans ?_
  exact Stacks.PullbackExteriorAlgebra.comparisonHom_one f.toLRSHom.toShHom
      (Hom.relativeDifferentialFormsAlgebra X.toSpecZ)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Hom.relativeDifferentials X.toSpecZ))
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).1 (op ⊤)

/-- **The identification of pulled back forms on an affine open is multiplicative**: it carries
the product of `f^*Ω^•_{X/ℤ}` to the wedge product. -/
theorem pullbackFormsSectionsEquiv_mul (p q : ℕ) (α : Γ(f.pullbackForms p, V))
    (β : Γ(f.pullbackForms q, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    pullbackFormsSectionsEquiv hV f hU e (p + q)
        ((eqToHom (congrArg f.pullbackForms (Nat.cast_add p q).symm)).val.app (op V)
          (((Hom.pullbackFormsAlgebra f).mul p q).app (op V) α β)) =
      exteriorPower.wedgeMul p q (pullbackFormsSectionsEquiv hV f hU e p α)
        (pullbackFormsSectionsEquiv hV f hU e q β) := by
  let := (f.appLE U V e).hom.toAlgebra
  have h1 : Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ ((p + q : ℕ) : ℤ)).hom V
      ((eqToHom (congrArg f.pullbackForms (Nat.cast_add p q).symm)).val.app (op V)
          (((Hom.pullbackFormsAlgebra f).mul p q).app (op V) α β)) =
      (eqToHom (congrArg (pieceModules (Scheme.Modules.exteriorAlgebra
          ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ))))
          (Nat.cast_add p q).symm)).val.app (op V)
        (((Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
          (Hom.relativeDifferentials X.toSpecZ))).mul p q).app (op V)
        (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ p).hom V α)
        (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom V β)) :=
    pullbackFormsIso_hom_app_mul f p q V α β
  refine (pullbackFormsSectionsEquiv_apply hV f hU e (p + q) _).trans ?_
  refine (congrArg (fun x => exteriorPower.map (p + q)
    (pullbackDifferentialsSectionsEquiv hV f hU e).toLinearMap
      ((affineOpenExteriorPowerΓIso
          ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ)) hV
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) (p + q)).hom.hom x)) h1).trans ?_
  refine (congrArg (exteriorPower.map (p + q)
    (pullbackDifferentialsSectionsEquiv hV f hU e).toLinearMap)
    (affineOpenExteriorPowerΓIso_hom_mul _ hV
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) p q _ _)).trans ?_
  refine (exteriorPower.wedgeMul_map p q _ _ _).trans ?_
  exact congrArg₂ (fun x y => exteriorPower.wedgeMul p q x y)
    (pullbackFormsSectionsEquiv_apply hV f hU e p α).symm
    (pullbackFormsSectionsEquiv_apply hV f hU e q β).symm

/-- The identification of pulled back forms on an affine open carries the unit to the empty
wedge. -/
theorem pullbackFormsSectionsEquiv_one :
    letI := (f.appLE U V e).hom.toAlgebra
    pullbackFormsSectionsEquiv hV f hU e 0 ((Hom.pullbackFormsAlgebra f).one.eval (op V)) =
      exteriorPower.ιMulti Γ(Y, V) 0 Fin.elim0 := by
  let := (f.appLE U V e).hom.toAlgebra
  refine (pullbackFormsSectionsEquiv_apply hV f hU e 0 _).trans ?_
  refine (congrArg (fun x => exteriorPower.map 0
    (pullbackDifferentialsSectionsEquiv hV f hU e).toLinearMap
      ((affineOpenExteriorPowerΓIso
          ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ)) hV
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) 0).hom.hom x))
    (show Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ ((0 : ℕ) : ℤ)).hom V
        ((Hom.pullbackFormsAlgebra f).one.eval (op V)) =
      (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
          (Hom.relativeDifferentials X.toSpecZ))).one.eval (op V) from
      pullbackFormsIso_hom_app_one f V)).trans ?_
  refine (congrArg (exteriorPower.map 0 (pullbackDifferentialsSectionsEquiv hV f hU e).toLinearMap)
    (affineOpenExteriorPowerΓIso_hom_one _ hV
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _))).trans ?_
  exact (exteriorPower.map_apply_ιMulti _ _).trans
    (congrArg (exteriorPower.ιMulti Γ(Y, V) 0) (funext fun i => i.elim0))

end AlgebraicGeometry.Scheme

/-! ### Naturality of the identifications -/

namespace Stacks.AffineExteriorPower

open _root_.AlgebraicGeometry
open SheafOfModules.GradedAlgebra (IsExteriorAlgebra)

variable {X X' : Scheme.{u}} {U : X.Opens} {U' : X'.Opens} {F : X.Modules} {F' : X'.Modules}
  [F.IsQuasicoherent] [F'.IsQuasicoherent] (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
  {E : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)}
  {gen : F ⟶ E.piece 1} (hE : IsExteriorAlgebra E gen)
  {E' : SheafOfModules.GradedAlgebra.{u, u}
    (Stacks.RingedSpace.structureRingSheaf X'.toRingedSpace)}
  {gen' : F' ⟶ E'.piece 1} (hE' : IsExteriorAlgebra E' gen')

/-- **A semilinear map of sections of exterior powers, read through Tag 01I8.** Let
`T : Γ(⋀ⁿ F, U) → Γ(⋀ⁿ F', U')` be semilinear over a ring map `φ : Γ(X, U) → Γ(X', U')`, and let
`ψ`, `ψ'` identify the sections of `F` and `F'` with modules `P` and `P'`. If `g` generates the
sections of `F` and `T` carries the ordered product of the generators at a family of the `g j`
to the ordered product of the generators at the corresponding `g' j`, where `ψ' (g' j)` is the
image under a `φ`-semilinear `K : P → P'` of `ψ (g j)`, then `T` is `⋀ⁿ K`. -/
theorem map_affineOpenExteriorPowerΓIso_hom_semilinear {P P' : Type u} [AddCommGroup P]
    [Module Γ(X, U) P] [AddCommGroup P'] [Module Γ(X', U') P']
    (ψ : Γ(F, U) ≃ₗ[Γ(X, U)] P) (ψ' : Γ(F', U') ≃ₗ[Γ(X', U')] P')
    {φ : Γ(X, U) →+* Γ(X', U')} (K : P →ₛₗ[φ] P') {ι : Type*} (g : ι → Γ(F, U))
    (g' : ι → Γ(F', U')) (hspan : Submodule.span Γ(X, U) (Set.range g) = ⊤)
    (hg : ∀ j, ψ' (g' j) = K (ψ (g j))) (n : ℕ)
    (T : Γ(pieceModules E (n : ℤ), U) →ₛₗ[φ] Γ(pieceModules E' (n : ℤ), U'))
    (hT : ∀ c : Fin n → ι,
      T (E.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => gen.val.app (op U) (g (c i))) =
        E'.toPresheafGradedAlgebra.homogeneousProd (op U') n
          fun i => gen'.val.app (op U') (g' (c i)))
    (x : Γ(pieceModules E (n : ℤ), U)) :
    exteriorPower.map n ψ'.toLinearMap ((affineOpenExteriorPowerΓIso F' hU' hE' n).hom.hom (T x)) =
      ExteriorAlgebra.powMapₛₗ n φ K
        (exteriorPower.map n ψ.toLinearMap
          ((affineOpenExteriorPowerΓIso F hU hE n).hom.hom x)) := by
  let G : ⋀[Γ(X, U)]^n P →ₛₗ[φ] ⋀[Γ(X', U')]^n P' :=
    (((exteriorPower.map n ψ'.toLinearMap).comp
      (affineOpenExteriorPowerΓIso F' hU' hE' n).hom.hom).comp T).comp
      ((affineOpenExteriorPowerΓIso F hU hE n).inv.hom.comp
        (exteriorPower.map n ψ.symm.toLinearMap))
  have hG : ∀ y, G y = exteriorPower.map n ψ'.toLinearMap
      ((affineOpenExteriorPowerΓIso F' hU' hE' n).hom.hom (T
        ((affineOpenExteriorPowerΓIso F hU hE n).inv.hom
          (exteriorPower.map n ψ.symm.toLinearMap y)))) := fun y => by
    simp only [G, LinearMap.comp_apply]
  have hspan' : Submodule.span Γ(X, U) (Set.range fun j => ψ (g j)) = ⊤ := by
    have h := congrArg (Submodule.map ψ.toLinearMap) hspan
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    rw [Set.range_comp' ψ g]
    exact h
  have key : ∀ y, G y = ExteriorAlgebra.powMapₛₗ n φ K y := by
    intro y
    have hy : y ∈ Submodule.span Γ(X, U) (exteriorPower.ιMulti Γ(X, U) n ''
        {a | Set.range a ⊆ Set.range fun j => ψ (g j)}) := by
      rw [exteriorPower.ιMulti_span_of_span Γ(X, U) n P hspan']
      trivial
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      choose k hk using fun i => ha (Set.mem_range_self i)
      obtain rfl : a = fun i => ψ (g (k i)) := funext fun i => (hk i).symm
      have h1 : exteriorPower.map n ψ.symm.toLinearMap
          (exteriorPower.ιMulti Γ(X, U) n fun i => ψ (g (k i))) =
          exteriorPower.ιMulti Γ(X, U) n fun i => g (k i) :=
        (exteriorPower.map_apply_ιMulti _ _).trans
          (congrArg (exteriorPower.ιMulti Γ(X, U) n) (funext fun i => ψ.symm_apply_apply _))
      rw [hG, h1, affineOpenExteriorPowerΓIso_inv_ιMulti, hT k,
        affineOpenExteriorPowerΓIso_hom_homogeneousProd, exteriorPower.map_apply_ιMulti,
        ExteriorAlgebra.powMapₛₗ_ιMulti]
      exact congrArg (exteriorPower.ιMulti Γ(X', U') n) (funext fun i => hg (k i))
    | zero => rw [map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]
  have hx : exteriorPower.map n ψ.symm.toLinearMap
      (exteriorPower.map n ψ.toLinearMap ((affineOpenExteriorPowerΓIso F hU hE n).hom.hom x)) =
      (affineOpenExteriorPowerΓIso F hU hE n).hom.hom x :=
    (exteriorPowerCongr ψ n).symm_apply_apply _
  have hx' : (affineOpenExteriorPowerΓIso F hU hE n).inv.hom
      ((affineOpenExteriorPowerΓIso F hU hE n).hom.hom x) = x :=
    congrArg (fun k => ModuleCat.Hom.hom k x) (affineOpenExteriorPowerΓIso F hU hE n).hom_inv_id
  refine Eq.trans ?_ ((hG _).symm.trans (key _))
  exact congrArg (fun z => exteriorPower.map n ψ'.toLinearMap
    ((affineOpenExteriorPowerΓIso F' hU' hE' n).hom.hom (T z)))
    (hx'.symm.trans (congrArg (affineOpenExteriorPowerΓIso F hU hE n).inv.hom hx.symm))

end Stacks.AffineExteriorPower

namespace AlgebraicGeometry.Scheme

open Stacks.AffineExteriorPower
open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms (relativeDifferentialFormsGenerator)
open Stacks.AlgebraicGeometry.AffineDifferentialForms (pullbackFormsIso)

variable (Y : Scheme.{u}) {V V' : Y.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')

/-- A family spans the target of a linear equivalence if it is the image of a spanning family. -/
private theorem span_range_eq_top_of_equiv {R M N ι : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) (g : ι → M) (h : ι → N)
    (hg : Submodule.span R (Set.range g) = ⊤) (hgh : ∀ i, e (g i) = h i) :
    Submodule.span R (Set.range h) = ⊤ := by
  have := congrArg (Submodule.map e.toLinearMap) hg
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
  rwa [← funext hgh]

include hV in
/-- The universal differentials of the sections span the absolute differentials over an affine
open. -/
theorem span_range_universalRelativeDerivation_d :
    Submodule.span Γ(Y, V) (Set.range fun b : Γ(Y, V) =>
      show Γ(Hom.relativeDifferentials Y.toSpecZ, V) from
        (Hom.universalRelativeDerivation Y.toSpecZ).d b) = ⊤ := by
  exact span_range_eq_top_of_equiv (absoluteDifferentialsSectionsEquiv Y hV).symm _ _
    (KaehlerDifferential.span_range_derivation ℤ Γ(Y, V))
    (absoluteDifferentialsSectionsEquiv_symm_D Y hV)

/-- `absoluteDifferentialsSectionsEquiv` carries the universal derivation to `D`. -/
theorem absoluteDifferentialsSectionsEquiv_d (b : Γ(Y, V)) :
    absoluteDifferentialsSectionsEquiv Y hV ((Hom.universalRelativeDerivation Y.toSpecZ).d b) =
      KaehlerDifferential.D ℤ Γ(Y, V) b := by
  rw [← absoluteDifferentialsSectionsEquiv_symm_D Y hV, LinearEquiv.apply_symm_apply]

variable {Y}

/-- **The identification of absolute forms is natural under restriction**: restricting a form from
`V` to an affine `V' ≤ V` is `⋀ᵖ` of a semilinear map `u : Ω[Γ(Y, V)⁄ℤ] → Ω[Γ(Y, V')⁄ℤ]` over the
restriction of functions carrying `D b` to `D b|_{V'}`, for instance
`Stacks.KaehlerDifferentialSquare.map`, which is `KaehlerDifferential.map ℤ ℤ Γ(Y, V) Γ(Y, V')`. -/
theorem absoluteFormsSectionsEquiv_restrict (h : V' ≤ V) (p : ℕ)
    (u : Ω[Γ(Y, V)⁄ℤ] →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] Ω[Γ(Y, V')⁄ℤ])
    (hu : ∀ b, u (KaehlerDifferential.D ℤ Γ(Y, V) b) =
      KaehlerDifferential.D ℤ Γ(Y, V') ((Y.presheaf.map (homOfLE h).op).hom b))
    (η : Γ(absoluteDifferentialForms Y p, V)) :
    absoluteFormsSectionsEquiv Y hV' p
        ((absoluteDifferentialForms Y p).presheaf.map (homOfLE h).op η) =
      ExteriorAlgebra.powMapₛₗ p (Y.presheaf.map (homOfLE h).op).hom u
        (absoluteFormsSectionsEquiv Y hV p η) := by
  let T : Γ(absoluteDifferentialForms Y p, V) →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom]
      Γ(absoluteDifferentialForms Y p, V') :=
    { toFun := (absoluteDifferentialForms Y p).presheaf.map (homOfLE h).op
      map_add' := map_add _
      map_smul' := Scheme.Modules.map_smul _ (homOfLE h) }
  have hg : ∀ b : Γ(Y, V), absoluteDifferentialsSectionsEquiv Y hV'
      ((Hom.universalRelativeDerivation Y.toSpecZ).d ((Y.presheaf.map (homOfLE h).op).hom b)) =
      u (absoluteDifferentialsSectionsEquiv Y hV ((Hom.universalRelativeDerivation Y.toSpecZ).d b))
      := fun b => by
    rw [absoluteDifferentialsSectionsEquiv_d, absoluteDifferentialsSectionsEquiv_d, hu]
  have hT : ∀ c : Fin p → Γ(Y, V), T ((absoluteDifferentialFormsAlgebra
      Y).toPresheafGradedAlgebra.homogeneousProd (op V) p fun i =>
        (relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V)
          ((Hom.universalRelativeDerivation Y.toSpecZ).d (c i))) =
      (absoluteDifferentialFormsAlgebra Y).toPresheafGradedAlgebra.homogeneousProd (op V') p
        fun i => (relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V')
          ((Hom.universalRelativeDerivation Y.toSpecZ).d
            ((Y.presheaf.map (homOfLE h).op).hom (c i))) := fun c => by
    refine ((absoluteDifferentialFormsAlgebra Y).toPresheafGradedAlgebra.homogeneousProd_naturality
      (homOfLE h).op p _).trans ?_
    refine congrArg ((absoluteDifferentialFormsAlgebra Y).toPresheafGradedAlgebra.homogeneousProd
      (op V') p) (funext fun i => ?_)
    refine (PresheafOfModules.naturality_apply
      (relativeDifferentialFormsGenerator Y.toSpecZ).val (homOfLE h).op _).symm.trans ?_
    exact congrArg ((relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V'))
      ((Hom.universalRelativeDerivation Y.toSpecZ).d_map (homOfLE h).op (c i)).symm
  have key := map_affineOpenExteriorPowerΓIso_hom_semilinear hV hV'
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra Y.toSpecZ)
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra Y.toSpecZ)
    (absoluteDifferentialsSectionsEquiv Y hV) (absoluteDifferentialsSectionsEquiv Y hV') u
    (fun b : Γ(Y, V) => show Γ(Hom.relativeDifferentials Y.toSpecZ, V) from
      (Hom.universalRelativeDerivation Y.toSpecZ).d b)
    (fun b : Γ(Y, V) => show Γ(Hom.relativeDifferentials Y.toSpecZ, V') from
      (Hom.universalRelativeDerivation Y.toSpecZ).d ((Y.presheaf.map (homOfLE h).op).hom b))
    (span_range_universalRelativeDerivation_d Y hV) hg p T hT η
  have hTη : (absoluteDifferentialForms Y p).presheaf.map (homOfLE h).op η = T η := rfl
  rw [absoluteFormsSectionsEquiv_apply_hom, hTη, key, absoluteFormsSectionsEquiv_apply_hom]

/-- **The identification of absolute forms is natural under restriction**, with the map on
differentials `Stacks.DeRham.kaehlerMapₛₗ`, which is `KaehlerDifferential.map ℤ ℤ Γ(Y, V) Γ(Y, V')`
read as a semilinear map. -/
theorem absoluteFormsSectionsEquiv_restrict_kaehlerMapₛₗ (h : V' ≤ V) (p : ℕ)
    (η : Γ(absoluteDifferentialForms Y p, V)) :
    letI := Y.restrictAlgebra h
    absoluteFormsSectionsEquiv Y hV' p
        ((absoluteDifferentialForms Y p).presheaf.map (homOfLE h).op η) =
      ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, V) Γ(Y, V'))
        (Stacks.DeRham.kaehlerMapₛₗ Γ(Y, V) Γ(Y, V')) (absoluteFormsSectionsEquiv Y hV p η) :=
  let := Y.restrictAlgebra h
  absoluteFormsSectionsEquiv_restrict hV hV' h p _
    (Stacks.DeRham.kaehlerMapₛₗ_D Γ(Y, V) Γ(Y, V')) η

/-- The elements `1 ⊗ D a` span `B ⊗[A] Ω[A⁄ℤ]` over `B`. -/
theorem _root_.KaehlerDifferential.span_range_one_tmul_D (A B : Type*) [CommRing A]
    [CommRing B] [Algebra A B] :
    Submodule.span B (Set.range fun a : A => (1 : B) ⊗ₜ[A] KaehlerDifferential.D ℤ A a) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem hx hy
  | tmul b ω =>
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℤ A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    rw [← mul_one b, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    refine Submodule.smul_mem _ b ?_
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero =>
      rw [TensorProduct.tmul_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul B a]
      exact Submodule.smul_mem _ _ hx

variable {X : Scheme.{u}} (f : Y ⟶ X) {U U' : X.Opens} (hU : IsAffineOpen U)
  (hU' : IsAffineOpen U') (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')

/-- `pullbackDifferentialsSectionsEquiv` carries the pullback of `d a` to `1 ⊗ D a`. -/
theorem pullbackDifferentialsSectionsEquiv_pullbackSection_d (a : Γ(X, U)) :
    letI := (f.appLE U V e).hom.toAlgebra
    pullbackDifferentialsSectionsEquiv hV f hU e
        (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
          ((Hom.universalRelativeDerivation X.toSpecZ).d a)) =
      (1 : Γ(Y, V)) ⊗ₜ KaehlerDifferential.D ℤ Γ(X, U) a := by
  let := (f.appLE U V e).hom.toAlgebra
  have k := congrArg (pullbackDifferentialsSectionsEquiv hV f hU e)
    (pullbackDifferentialsSectionsEquiv_symm_one_tmul_D hV f hU e a)
  rw [LinearEquiv.apply_symm_apply] at k
  exact k.symm

include hV hU in
/-- The pullbacks of the universal differentials of the sections of `X` over `U` span the sections
over `V` of the pulled back absolute differentials. -/
theorem span_range_pullbackSection_d :
    Submodule.span Γ(Y, V) (Set.range fun a : Γ(X, U) =>
      show Γ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ), V) from
        Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
          ((Hom.universalRelativeDerivation X.toSpecZ).d a)) = ⊤ := by
  let := (f.appLE U V e).hom.toAlgebra
  exact span_range_eq_top_of_equiv (pullbackDifferentialsSectionsEquiv hV f hU e).symm _ _
    (KaehlerDifferential.span_range_one_tmul_D Γ(X, U) Γ(Y, V))
    (pullbackDifferentialsSectionsEquiv_symm_one_tmul_D hV f hU e)

/-- **The identification of pulled back forms is natural under restriction**: for affine
`U' ≤ U` and `V' ≤ V` with `V' ≤ f⁻¹U'`, restricting from `V` to `V'` is `⋀^q` of a semilinear
map `u : Γ(Y, V) ⊗ Ω[Γ(X, U)⁄ℤ] → Γ(Y, V') ⊗ Ω[Γ(X, U')⁄ℤ]` over the restriction of functions
carrying `1 ⊗ D a` to `1 ⊗ D a|_{U'}`; such a `u` is the base change of the restriction and of
`KaehlerDifferential.map`, which these values pin down. -/
theorem pullbackFormsSectionsEquiv_restrict (hUU : U' ≤ U) (hVV : V' ≤ V) (q : ℕ)
    (u : letI := (f.appLE U V e).hom.toAlgebra
      letI := (f.appLE U' V' e').hom.toAlgebra
      (Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ]) →ₛₗ[(Y.presheaf.map (homOfLE hVV).op).hom]
        (Γ(Y, V') ⊗[Γ(X, U')] Ω[Γ(X, U')⁄ℤ]))
    (hu : letI := (f.appLE U V e).hom.toAlgebra
      letI := (f.appLE U' V' e').hom.toAlgebra
      ∀ a, u ((1 : Γ(Y, V)) ⊗ₜ KaehlerDifferential.D ℤ Γ(X, U) a) =
        (1 : Γ(Y, V')) ⊗ₜ
          KaehlerDifferential.D ℤ Γ(X, U') ((X.presheaf.map (homOfLE hUU).op).hom a))
    (ω : Γ(f.pullbackForms q, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    letI := (f.appLE U' V' e').hom.toAlgebra
    pullbackFormsSectionsEquiv hV' f hU' e' q
        ((f.pullbackForms q).presheaf.map (homOfLE hVV).op ω) =
      ExteriorAlgebra.powMapₛₗ q (Y.presheaf.map (homOfLE hVV).op).hom u
        (pullbackFormsSectionsEquiv hV f hU e q ω) := by
  let := (f.appLE U V e).hom.toAlgebra
  let := (f.appLE U' V' e').hom.toAlgebra
  let F := (Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ)
  let E := Scheme.Modules.exteriorAlgebra F
  let T : Γ(pieceModules E (q : ℤ), V) →ₛₗ[(Y.presheaf.map (homOfLE hVV).op).hom]
      Γ(pieceModules E (q : ℤ), V') :=
    { toFun := (pieceModules E (q : ℤ)).presheaf.map (homOfLE hVV).op
      map_add' := map_add _
      map_smul' := Scheme.Modules.map_smul _ (homOfLE hVV) }
  have hres : ∀ a : Γ(X, U), F.presheaf.map (homOfLE hVV).op
      (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
        ((Hom.universalRelativeDerivation X.toSpecZ).d a)) =
      Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U' V' e'
        ((Hom.universalRelativeDerivation X.toSpecZ).d ((X.presheaf.map (homOfLE hUU).op).hom a))
      := fun a => by
    refine (Stacks.Conormal.pullbackSection_restrict_target f _ U V V' e hVV _).trans ?_
    refine (Stacks.Conormal.pullbackSection_restrict_source f _ U U' hUU V' e' _).trans ?_
    exact congrArg (Scheme.Modules.pullbackSection f _ U' V' e')
      ((Hom.universalRelativeDerivation X.toSpecZ).d_map (homOfLE hUU).op a).symm
  have hg : ∀ a : Γ(X, U), pullbackDifferentialsSectionsEquiv hV' f hU' e'
      (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U' V' e'
        ((Hom.universalRelativeDerivation X.toSpecZ).d ((X.presheaf.map (homOfLE hUU).op).hom a))) =
      u (pullbackDifferentialsSectionsEquiv hV f hU e
        (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
          ((Hom.universalRelativeDerivation X.toSpecZ).d a))) := fun a => by
    rw [pullbackDifferentialsSectionsEquiv_pullbackSection_d,
      pullbackDifferentialsSectionsEquiv_pullbackSection_d, hu]
  have hT : ∀ c : Fin q → Γ(X, U), T (E.toPresheafGradedAlgebra.homogeneousProd (op V) q fun i =>
        (Scheme.Modules.exteriorGenerator F).val.app (op V)
          (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
            ((Hom.universalRelativeDerivation X.toSpecZ).d (c i)))) =
      E.toPresheafGradedAlgebra.homogeneousProd (op V') q fun i =>
        (Scheme.Modules.exteriorGenerator F).val.app (op V')
          (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U' V' e'
            ((Hom.universalRelativeDerivation X.toSpecZ).d
              ((X.presheaf.map (homOfLE hUU).op).hom (c i)))) := fun c => by
    refine (E.toPresheafGradedAlgebra.homogeneousProd_naturality (homOfLE hVV).op q _).trans ?_
    refine congrArg (E.toPresheafGradedAlgebra.homogeneousProd (op V') q) (funext fun i => ?_)
    refine (PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator F).val (homOfLE hVV).op _).symm.trans ?_
    exact congrArg ((Scheme.Modules.exteriorGenerator F).val.app (op V')) (hres (c i))
  have key := map_affineOpenExteriorPowerΓIso_hom_semilinear hV hV'
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F)
    (pullbackDifferentialsSectionsEquiv hV f hU e) (pullbackDifferentialsSectionsEquiv hV' f hU' e')
    u (fun a : Γ(X, U) => show Γ(F, V) from
      Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
        ((Hom.universalRelativeDerivation X.toSpecZ).d a))
    (fun a : Γ(X, U) => show Γ(F, V') from
      Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U' V' e'
        ((Hom.universalRelativeDerivation X.toSpecZ).d ((X.presheaf.map (homOfLE hUU).op).hom a)))
    (span_range_pullbackSection_d hV f hU e) hg q T hT
    (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom V ω)
  have hnat : Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom V'
      ((f.pullbackForms q).presheaf.map (homOfLE hVV).op ω) =
      T (Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ q).hom V ω) :=
    PresheafOfModules.naturality_apply (pullbackFormsIso f X.toSpecZ q).hom.val (homOfLE hVV).op ω
  refine (pullbackFormsSectionsEquiv_apply hV' f hU' e' q _).trans (Eq.trans ?_ (key.trans ?_))
  · exact congrArg (fun z => exteriorPower.map q
      (pullbackDifferentialsSectionsEquiv hV' f hU' e').toLinearMap
      ((affineOpenExteriorPowerΓIso F hV' (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F)
        q).hom.hom z)) hnat
  exact congrArg _ (pullbackFormsSectionsEquiv_apply hV f hU e q ω).symm

/-- **The identification of pulled back forms is natural under restriction**, with the map on
pulled back differentials `Stacks.DeRham.formsBaseChangeMapₛₗ`: the base change of the restriction
of functions and of `KaehlerDifferential.map ℤ ℤ Γ(X, U) Γ(X, U')`. -/
theorem pullbackFormsSectionsEquiv_restrict_formsBaseChangeMapₛₗ (hUU : U' ≤ U) (hVV : V' ≤ V)
    (q : ℕ) (ω : Γ(f.pullbackForms q, V)) :
    letI := f.chartAlgebra e
    letI := f.chartAlgebra e'
    letI := X.restrictAlgebra hUU
    letI := Y.restrictAlgebra hVV
    letI := f.chartAlgebra (hVV.trans e)
    haveI := f.isScalarTower_chartAlgebra_restrict e e' hUU hVV
    haveI := f.isScalarTower_restrict_chartAlgebra e hVV
    pullbackFormsSectionsEquiv hV' f hU' e' q
        ((f.pullbackForms q).presheaf.map (homOfLE hVV).op ω) =
      ExteriorAlgebra.powMapₛₗ q (algebraMap Γ(Y, V) Γ(Y, V'))
        (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, U) Γ(Y, V) Γ(X, U') Γ(Y, V'))
        (pullbackFormsSectionsEquiv hV f hU e q ω) :=
  let := f.chartAlgebra e
  let := f.chartAlgebra e'
  let := X.restrictAlgebra hUU
  let := Y.restrictAlgebra hVV
  let := f.chartAlgebra (hVV.trans e)
  have := f.isScalarTower_chartAlgebra_restrict e e' hUU hVV
  have := f.isScalarTower_restrict_chartAlgebra e hVV
  pullbackFormsSectionsEquiv_restrict hV hV' f hU hU' e e' hUU hVV q _ (fun a => by
    rw [Stacks.DeRham.formsBaseChangeMapₛₗ_tmul, map_one, KaehlerDifferential.map_D]
    rfl) ω

/-! ### Naturality under pullback -/

/-- **A multiplicative and unital family of maps of local sections of two sheaves of graded
algebras carries an ordered product of degree-one sections to the ordered product of their
images.** -/
theorem homogeneousProd_map_of_map_mul {X₁ X₂ : Scheme.{u}}
    {E₁ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X₁.toRingedSpace)}
    {E₂ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X₂.toRingedSpace)}
    {W₁ : X₁.Opens} {W₂ : X₂.Opens}
    (Φ : ∀ n : ℤ, (E₁.piece n).val.obj (op W₁) → (E₂.piece n).val.obj (op W₂))
    (hmul : ∀ (i j : ℤ) (x : (E₁.piece i).val.obj (op W₁)) (y : (E₁.piece j).val.obj (op W₁)),
      Φ (i + j) ((E₁.mul i j).app (op W₁) x y) = (E₂.mul i j).app (op W₂) (Φ i x) (Φ j y))
    (hone : Φ 0 (E₁.one.eval (op W₁)) = E₂.one.eval (op W₂))
    (n : ℕ) (z : Fin n → (E₁.piece 1).val.obj (op W₁)) :
    Φ n (E₁.toPresheafGradedAlgebra.homogeneousProd (op W₁) n z) =
      E₂.toPresheafGradedAlgebra.homogeneousProd (op W₂) n fun i => Φ 1 (z i) := by
  induction n with
  | zero => exact hone
  | succ n ih =>
    change Φ ((n : ℤ) + 1) ((E₁.mul (n : ℤ) 1).app (op W₁)
      (E₁.toPresheafGradedAlgebra.homogeneousProd (op W₁) n fun i => z i.castSucc)
        (z (Fin.last n))) = _
    rw [hmul (n : ℤ) 1, ih fun i => z i.castSucc]
    rfl

variable {Y' : Scheme.{u}} (b : Y' ⟶ Y) {W : Y'.Opens} (hW : IsAffineOpen W)

/-- The canonical map on absolute forms, applied to the pullback of a local form, is the
restriction of the pulled back local form. -/
theorem absoluteFormsMap_app_pullbackSection (hb : W ≤ b ⁻¹ᵁ V) (p : ℤ)
    (η : Γ(absoluteDifferentialForms Y p, V)) :
    (b.absoluteFormsMap p).app W
        (Scheme.Modules.pullbackSection b (absoluteDifferentialForms Y p) V W hb η) =
      (absoluteDifferentialForms Y' p).presheaf.map (homOfLE hb).op
        (b.absoluteFormsPullback p V η) :=
  PresheafOfModules.naturality_apply (b.absoluteFormsMap p).val (homOfLE hb).op _

/-- **Pulling back an ordered product of exact differentials**: the pullback along `b` of
`d c₁ ∧ ⋯ ∧ d cₙ`, restricted to `W ≤ b⁻¹V`, is `d b^♯c₁ ∧ ⋯ ∧ d b^♯cₙ`. -/
theorem absoluteFormsPullback_homogeneousProd (hb : W ≤ b ⁻¹ᵁ V) (n : ℕ)
    (c : Fin n → Γ(Y, V)) :
    (absoluteDifferentialForms Y' n).presheaf.map (homOfLE hb).op
        (b.absoluteFormsPullback n V
          ((absoluteDifferentialFormsAlgebra Y).toPresheafGradedAlgebra.homogeneousProd (op V) n
            fun i => (relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V)
              ((Hom.universalRelativeDerivation Y.toSpecZ).d (c i)))) =
      (absoluteDifferentialFormsAlgebra Y').toPresheafGradedAlgebra.homogeneousProd (op W) n
        fun i => (relativeDifferentialFormsGenerator Y'.toSpecZ).val.app (op W)
          ((Hom.universalRelativeDerivation Y'.toSpecZ).d ((b.appLE V W hb).hom (c i))) := by
  refine (homogeneousProd_map_of_map_mul
    (fun i x => (absoluteDifferentialForms Y' i).presheaf.map (homOfLE hb).op
      (b.absoluteFormsPullback i V x)) (fun i j x y => ?_) ?_ n _).trans ?_
  · refine (congrArg ((absoluteDifferentialForms Y' (i + j)).presheaf.map (homOfLE hb).op)
      (Hom.relativeDifferentialFormsPullback_mul b Y.toSpecZ Y'.toSpecZ (𝟙 _) (comp_toSpecZ b)
        i j V x y)).trans ?_
    exact ((absoluteDifferentialFormsAlgebra Y').mul i j).naturality (homOfLE hb).op _ _
  · refine (congrArg ((absoluteDifferentialForms Y' 0).presheaf.map (homOfLE hb).op)
      (Hom.relativeDifferentialFormsPullback_one b Y.toSpecZ Y'.toSpecZ (𝟙 _) (comp_toSpecZ b)
        V)).trans ?_
    exact SheafOfModules.GradedAlgebra.one_eval_map (absoluteDifferentialFormsAlgebra Y')
      (homOfLE hb).op
  refine congrArg ((absoluteDifferentialFormsAlgebra Y').toPresheafGradedAlgebra.homogeneousProd
    (op W) n) (funext fun i => ?_)
  refine (congrArg ((absoluteDifferentialForms Y' 1).presheaf.map (homOfLE hb).op)
    (Hom.relativeDifferentialFormsPullback_exteriorGenerator_d b Y.toSpecZ Y'.toSpecZ (𝟙 _)
      (comp_toSpecZ b) V (c i))).trans ?_
  refine (PresheafOfModules.naturality_apply
    (relativeDifferentialFormsGenerator Y'.toSpecZ).val (homOfLE hb).op _).symm.trans ?_
  exact congrArg ((relativeDifferentialFormsGenerator Y'.toSpecZ).val.app (op W))
    ((Hom.universalRelativeDerivation Y'.toSpecZ).d_map (homOfLE hb).op _).symm

/-- **The identification of absolute forms is natural under pullback**: for `b : Y' ⟶ Y` and
affine `W ≤ b⁻¹V`, the canonical map `b^*Ω^p_{Y/ℤ} ⟶ Ω^p_{Y'/ℤ}` on the pullback of a local form
over `V` is `⋀ᵖ` of a semilinear map `u : Ω[Γ(Y, V)⁄ℤ] → Ω[Γ(Y', W)⁄ℤ]` over `b^♯` carrying `D c`
to `D b^♯c`, for instance `Stacks.DeRham.kaehlerMapₛₗ`. -/
theorem absoluteFormsSectionsEquiv_absoluteFormsMap_pullbackSection (hb : W ≤ b ⁻¹ᵁ V) (p : ℕ)
    (u : Ω[Γ(Y, V)⁄ℤ] →ₛₗ[(b.appLE V W hb).hom] Ω[Γ(Y', W)⁄ℤ])
    (hu : ∀ c, u (KaehlerDifferential.D ℤ Γ(Y, V) c) =
      KaehlerDifferential.D ℤ Γ(Y', W) ((b.appLE V W hb).hom c))
    (η : Γ(absoluteDifferentialForms Y p, V)) :
    absoluteFormsSectionsEquiv Y' hW p ((b.absoluteFormsMap p).app W
        (Scheme.Modules.pullbackSection b (absoluteDifferentialForms Y p) V W hb η)) =
      ExteriorAlgebra.powMapₛₗ p (b.appLE V W hb).hom u (absoluteFormsSectionsEquiv Y hV p η) := by
  let T : Γ(absoluteDifferentialForms Y p, V) →ₛₗ[(b.appLE V W hb).hom]
      Γ(absoluteDifferentialForms Y' p, W) :=
    { toFun := fun x => (b.absoluteFormsMap p).app W
        (Scheme.Modules.pullbackSection b (absoluteDifferentialForms Y p) V W hb x)
      map_add' := fun x y =>
        (congrArg ((b.absoluteFormsMap p).app W)
          (map_add (ConcreteCategory.hom
            (pullbackSectionHom b (absoluteDifferentialForms Y p) V W hb)) x y)).trans
          (map_add _ _ _)
      map_smul' := fun r x =>
        (congrArg ((b.absoluteFormsMap p).app W)
          (pullbackSectionHom_smul b (absoluteDifferentialForms Y p) V W hb r x)).trans
          (Scheme.Modules.Hom.app_smul _ _ _) }
  have hg : ∀ c : Γ(Y, V), absoluteDifferentialsSectionsEquiv Y' hW
      ((Hom.universalRelativeDerivation Y'.toSpecZ).d ((b.appLE V W hb).hom c)) =
      u (absoluteDifferentialsSectionsEquiv Y hV ((Hom.universalRelativeDerivation Y.toSpecZ).d c))
      := fun c => by
    rw [absoluteDifferentialsSectionsEquiv_d, absoluteDifferentialsSectionsEquiv_d, hu]
  have hT : ∀ c : Fin p → Γ(Y, V), T ((absoluteDifferentialFormsAlgebra
      Y).toPresheafGradedAlgebra.homogeneousProd (op V) p fun i =>
        (relativeDifferentialFormsGenerator Y.toSpecZ).val.app (op V)
          ((Hom.universalRelativeDerivation Y.toSpecZ).d (c i))) =
      (absoluteDifferentialFormsAlgebra Y').toPresheafGradedAlgebra.homogeneousProd (op W) p
        fun i => (relativeDifferentialFormsGenerator Y'.toSpecZ).val.app (op W)
          ((Hom.universalRelativeDerivation Y'.toSpecZ).d ((b.appLE V W hb).hom (c i))) :=
    fun c => (absoluteFormsMap_app_pullbackSection b hb p _).trans
      (absoluteFormsPullback_homogeneousProd b hb p c)
  have key := map_affineOpenExteriorPowerΓIso_hom_semilinear hV hW
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra Y.toSpecZ)
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra Y'.toSpecZ)
    (absoluteDifferentialsSectionsEquiv Y hV) (absoluteDifferentialsSectionsEquiv Y' hW) u
    (fun c : Γ(Y, V) => show Γ(Hom.relativeDifferentials Y.toSpecZ, V) from
      (Hom.universalRelativeDerivation Y.toSpecZ).d c)
    (fun c : Γ(Y, V) => show Γ(Hom.relativeDifferentials Y'.toSpecZ, W) from
      (Hom.universalRelativeDerivation Y'.toSpecZ).d ((b.appLE V W hb).hom c))
    (span_range_universalRelativeDerivation_d Y hV) hg p T hT η
  have hTη : (b.absoluteFormsMap p).app W
      (Scheme.Modules.pullbackSection b (absoluteDifferentialForms Y p) V W hb η) = T η := rfl
  rw [absoluteFormsSectionsEquiv_apply_hom, hTη, key, absoluteFormsSectionsEquiv_apply_hom]

/-- **The identification of absolute forms is natural under pullback**, with the map on
differentials `Stacks.DeRham.kaehlerMapₛₗ` of `b^♯ : Γ(Y, V) → Γ(Y', W)`. -/
theorem absoluteFormsSectionsEquiv_absoluteFormsMap_pullbackSection_kaehlerMapₛₗ
    (hb : W ≤ b ⁻¹ᵁ V) (p : ℕ) (η : Γ(absoluteDifferentialForms Y p, V)) :
    letI := b.chartAlgebra hb
    absoluteFormsSectionsEquiv Y' hW p ((b.absoluteFormsMap p).app W
        (Scheme.Modules.pullbackSection b (absoluteDifferentialForms Y p) V W hb η)) =
      ExteriorAlgebra.powMapₛₗ p (algebraMap Γ(Y, V) Γ(Y', W))
        (Stacks.DeRham.kaehlerMapₛₗ Γ(Y, V) Γ(Y', W)) (absoluteFormsSectionsEquiv Y hV p η) :=
  let := b.chartAlgebra hb
  absoluteFormsSectionsEquiv_absoluteFormsMap_pullbackSection hV b hW hb p _
    (Stacks.DeRham.kaehlerMapₛₗ_D Γ(Y, V) Γ(Y', W)) η

/-- **Tag 01CI for absolute forms on a pulled back ordered product of generators**: the
comparison carries the pullback of `d c₁ ∧ ⋯ ∧ d cₙ` to the ordered product of the generators of
`⋀(f^*Ω_{X/ℤ})` at the pulled back differentials. -/
theorem pullbackFormsIso_hom_app_pullbackSection_homogeneousProd (n : ℕ)
    (s : Fin n → Γ(Hom.relativeDifferentials X.toSpecZ, U)) :
    Scheme.Modules.Hom.app (pullbackFormsIso f X.toSpecZ n).hom V
        (Scheme.Modules.pullbackSection f (absoluteDifferentialForms X n) U V e
          ((absoluteDifferentialFormsAlgebra X).toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => (relativeDifferentialFormsGenerator X.toSpecZ).val.app (op U) (s i))) =
      (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
          (Hom.relativeDifferentials X.toSpecZ))).toPresheafGradedAlgebra.homogeneousProd (op V) n
        fun i => (Scheme.Modules.exteriorGenerator ((Scheme.Modules.pullback f).obj
          (Hom.relativeDifferentials X.toSpecZ))).val.app (op V)
          (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e (s i)) := by
  refine (PresheafOfModules.naturality_apply (pullbackFormsIso f X.toSpecZ n).hom.val
    (homOfLE e).op _).trans ?_
  refine (congrArg _ (Stacks.PullbackExteriorAlgebra.comparisonHom_homogeneousProd
    f.toLRSHom.toShHom (Hom.relativeDifferentialFormsAlgebra X.toSpecZ)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Hom.relativeDifferentials X.toSpecZ))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _).1 (op U) n s)).trans ?_
  refine ((Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
    (Hom.relativeDifferentials X.toSpecZ))).toPresheafGradedAlgebra.homogeneousProd_naturality
      (homOfLE e).op n _).trans ?_
  refine congrArg ((Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback f).obj
    (Hom.relativeDifferentials X.toSpecZ))).toPresheafGradedAlgebra.homogeneousProd (op V) n)
    (funext fun i => ?_)
  exact (PresheafOfModules.naturality_apply (Scheme.Modules.exteriorGenerator
    ((Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ))).val
      (homOfLE e).op _).symm

variable {X' : Scheme.{u}} {f' : Y' ⟶ X'} {a : X' ⟶ X} (w : b ≫ f = f' ≫ a) {U₂ : X'.Opens}
  (hU₂ : IsAffineOpen U₂)

/-- **The identification of pulled back forms is natural under base change**: along a
commutative square `b ≫ f = f' ≫ a` and charts `(U, V)` of `f` and `(U₂, W)` of `f'` with
`U₂ ≤ a⁻¹U`, `W ≤ b⁻¹V`, the map `b^*f^*Ω^q_{X/ℤ} ⟶ f'^*Ω^q_{X'/ℤ}` on the pullback of a local
section over `V` is `⋀^q` of a semilinear map
`u : Γ(Y, V) ⊗ Ω[Γ(X, U)⁄ℤ] → Γ(Y', W) ⊗ Ω[Γ(X', U₂)⁄ℤ]` over `b^♯` carrying `1 ⊗ D x` to
`1 ⊗ D a^♯x`, for instance `Stacks.DeRham.formsBaseChangeMapₛₗ`. -/
theorem pullbackFormsSectionsEquiv_pullbackFormsBaseChange (e' : W ≤ f' ⁻¹ᵁ U₂)
    (ha : U₂ ≤ a ⁻¹ᵁ U) (hb : W ≤ b ⁻¹ᵁ V) (q : ℕ)
    (u : letI := (f.appLE U V e).hom.toAlgebra
      letI := (f'.appLE U₂ W e').hom.toAlgebra
      (Γ(Y, V) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄ℤ]) →ₛₗ[(b.appLE V W hb).hom]
        (Γ(Y', W) ⊗[Γ(X', U₂)] Ω[Γ(X', U₂)⁄ℤ]))
    (hu : letI := (f.appLE U V e).hom.toAlgebra
      letI := (f'.appLE U₂ W e').hom.toAlgebra
      ∀ x, u ((1 : Γ(Y, V)) ⊗ₜ KaehlerDifferential.D ℤ Γ(X, U) x) =
        (1 : Γ(Y', W)) ⊗ₜ KaehlerDifferential.D ℤ Γ(X', U₂) ((a.appLE U U₂ ha).hom x))
    (ω : Γ(f.pullbackForms q, V)) :
    letI := (f.appLE U V e).hom.toAlgebra
    letI := (f'.appLE U₂ W e').hom.toAlgebra
    pullbackFormsSectionsEquiv hW f' hU₂ e' q ((Hom.pullbackFormsBaseChange w q).app W
        (Scheme.Modules.pullbackSection b (f.pullbackForms q) V W hb ω)) =
      ExteriorAlgebra.powMapₛₗ q (b.appLE V W hb).hom u
        (pullbackFormsSectionsEquiv hV f hU e q ω) := by
  let := (f.appLE U V e).hom.toAlgebra
  let := (f'.appLE U₂ W e').hom.toAlgebra
  let F := (Scheme.Modules.pullback f).obj (Hom.relativeDifferentials X.toSpecZ)
  let F' := (Scheme.Modules.pullback f').obj (Hom.relativeDifferentials X'.toSpecZ)
  let E := Scheme.Modules.exteriorAlgebra F
  let E' := Scheme.Modules.exteriorAlgebra F'
  let c := pullbackFormsIso f X.toSpecZ q
  let c' := pullbackFormsIso f' X'.toSpecZ q
  let T₀ : Γ(f.pullbackForms q, V) →ₛₗ[(b.appLE V W hb).hom] Γ(f'.pullbackForms q, W) :=
    { toFun := fun x => (Hom.pullbackFormsBaseChange w q).app W
        (Scheme.Modules.pullbackSection b (f.pullbackForms q) V W hb x)
      map_add' := fun x y =>
        (congrArg ((Hom.pullbackFormsBaseChange w q).app W)
          (map_add (ConcreteCategory.hom
            (pullbackSectionHom b (f.pullbackForms q) V W hb)) x y)).trans
          (map_add _ _ _)
      map_smul' := fun r x =>
        (congrArg ((Hom.pullbackFormsBaseChange w q).app W)
          (pullbackSectionHom_smul b (f.pullbackForms q) V W hb r x)).trans
          (Scheme.Modules.Hom.app_smul _ _ _) }
  let T : Γ(pieceModules E (q : ℤ), V) →ₛₗ[(b.appLE V W hb).hom] Γ(pieceModules E' (q : ℤ), W) :=
    ((sectionsLinearEquivOfIso c' W).toLinearMap.comp T₀).comp
      (sectionsLinearEquivOfIso c V).symm.toLinearMap
  have hg : ∀ x : Γ(X, U), pullbackDifferentialsSectionsEquiv hW f' hU₂ e'
      (Scheme.Modules.pullbackSection f' (Hom.relativeDifferentials X'.toSpecZ) U₂ W e'
        ((Hom.universalRelativeDerivation X'.toSpecZ).d ((a.appLE U U₂ ha).hom x))) =
      u (pullbackDifferentialsSectionsEquiv hV f hU e
        (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
          ((Hom.universalRelativeDerivation X.toSpecZ).d x))) := fun x => by
    rw [pullbackDifferentialsSectionsEquiv_pullbackSection_d,
      pullbackDifferentialsSectionsEquiv_pullbackSection_d, hu]
  have hT : ∀ k : Fin q → Γ(X, U), T (E.toPresheafGradedAlgebra.homogeneousProd (op V) q fun i =>
        (Scheme.Modules.exteriorGenerator F).val.app (op V)
          (Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
            ((Hom.universalRelativeDerivation X.toSpecZ).d (k i)))) =
      E'.toPresheafGradedAlgebra.homogeneousProd (op W) q fun i =>
        (Scheme.Modules.exteriorGenerator F').val.app (op W)
          (Scheme.Modules.pullbackSection f' (Hom.relativeDifferentials X'.toSpecZ) U₂ W e'
            ((Hom.universalRelativeDerivation X'.toSpecZ).d ((a.appLE U U₂ ha).hom (k i)))) :=
      fun k => by
    have h1 := pullbackFormsIso_hom_app_pullbackSection_homogeneousProd f e q
      fun i => (Hom.universalRelativeDerivation X.toSpecZ).d (k i)
    have h2 := Hom.pullbackFormsBaseChange_pullbackSection w q U V W e hb
      ((absoluteDifferentialFormsAlgebra X).toPresheafGradedAlgebra.homogeneousProd (op U) q
        fun i => (relativeDifferentialFormsGenerator X.toSpecZ).val.app (op U)
          ((Hom.universalRelativeDerivation X.toSpecZ).d (k i)))
    have h3 := Stacks.Conormal.pullbackSection_restrict_source f' (absoluteDifferentialForms X' q)
      (a ⁻¹ᵁ U) U₂ ha W e' (a.absoluteFormsPullback q U
        ((absoluteDifferentialFormsAlgebra X).toPresheafGradedAlgebra.homogeneousProd (op U) q
          fun i => (relativeDifferentialFormsGenerator X.toSpecZ).val.app (op U)
            ((Hom.universalRelativeDerivation X.toSpecZ).d (k i))))
    have h4 := absoluteFormsPullback_homogeneousProd a ha q k
    have h5 := pullbackFormsIso_hom_app_pullbackSection_homogeneousProd f' e' q
      fun i => (Hom.universalRelativeDerivation X'.toSpecZ).d ((a.appLE U U₂ ha).hom (k i))
    change Scheme.Modules.Hom.app c'.hom W (T₀ (Scheme.Modules.Hom.app c.inv V _)) = _
    have h1' := (congrArg (Scheme.Modules.Hom.app c.inv V) h1.symm).trans
      (Stacks.SheafOfModules.inv_val_app_hom_val_app c (op V) _)
    refine (congrArg (fun z => Scheme.Modules.Hom.app c'.hom W (T₀ z)) h1').trans ?_
    refine Eq.trans ?_ h5
    refine congrArg (Scheme.Modules.Hom.app c'.hom W) (h2.trans (h3.trans ?_))
    exact congrArg (Scheme.Modules.pullbackSection f' (absoluteDifferentialForms X' q) U₂ W e') h4
  have key := map_affineOpenExteriorPowerΓIso_hom_semilinear hV hW
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F')
    (pullbackDifferentialsSectionsEquiv hV f hU e) (pullbackDifferentialsSectionsEquiv hW f' hU₂ e')
    u (fun x : Γ(X, U) => show Γ(F, V) from
      Scheme.Modules.pullbackSection f (Hom.relativeDifferentials X.toSpecZ) U V e
        ((Hom.universalRelativeDerivation X.toSpecZ).d x))
    (fun x : Γ(X, U) => show Γ(F', W) from
      Scheme.Modules.pullbackSection f' (Hom.relativeDifferentials X'.toSpecZ) U₂ W e'
        ((Hom.universalRelativeDerivation X'.toSpecZ).d ((a.appLE U U₂ ha).hom x)))
    (span_range_pullbackSection_d hV f hU e) hg q T hT (Scheme.Modules.Hom.app c.hom V ω)
  have hTω : Scheme.Modules.Hom.app c'.hom W ((Hom.pullbackFormsBaseChange w q).app W
      (Scheme.Modules.pullbackSection b (f.pullbackForms q) V W hb ω)) =
      T (Scheme.Modules.Hom.app c.hom V ω) :=
    congrArg (fun z => Scheme.Modules.Hom.app c'.hom W (T₀ z))
      (Stacks.SheafOfModules.inv_val_app_hom_val_app c (op V) ω).symm
  refine (pullbackFormsSectionsEquiv_apply hW f' hU₂ e' q _).trans (Eq.trans ?_ (key.trans ?_))
  · exact congrArg (fun z => exteriorPower.map q
      (pullbackDifferentialsSectionsEquiv hW f' hU₂ e').toLinearMap
      ((affineOpenExteriorPowerΓIso F' hW (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F')
        q).hom.hom z)) hTω
  exact congrArg _ (pullbackFormsSectionsEquiv_apply hV f hU e q ω).symm

/-- **The identification of pulled back forms along a square of charts**, with the base change
map `Stacks.DeRham.formsBaseChangeMapₛₗ` of the square of rings. -/
theorem pullbackFormsSectionsEquiv_pullbackFormsBaseChange_formsBaseChangeMapₛₗ
    (e' : W ≤ f' ⁻¹ᵁ U₂) (ha : U₂ ≤ a ⁻¹ᵁ U) (hb : W ≤ b ⁻¹ᵁ V) (q : ℕ)
    (ω : Γ(f.pullbackForms q, V)) :
    letI := f.chartAlgebra e
    letI := f'.chartAlgebra e'
    letI := a.chartAlgebra ha
    letI := b.chartAlgebra hb
    letI := Hom.squareAlgebra f' a ha e'
    haveI := Hom.isScalarTower_squareAlgebra_left ha e'
    haveI := f.isScalarTower_squareAlgebra_right w e ha hb e'
    pullbackFormsSectionsEquiv hW f' hU₂ e' q ((Hom.pullbackFormsBaseChange w q).app W
        (Scheme.Modules.pullbackSection b (f.pullbackForms q) V W hb ω)) =
      ExteriorAlgebra.powMapₛₗ q (algebraMap Γ(Y, V) Γ(Y', W))
        (Stacks.DeRham.formsBaseChangeMapₛₗ Γ(X, U) Γ(Y, V) Γ(X', U₂) Γ(Y', W))
        (pullbackFormsSectionsEquiv hV f hU e q ω) :=
  let := f.chartAlgebra e
  let := f'.chartAlgebra e'
  let := a.chartAlgebra ha
  let := b.chartAlgebra hb
  let := Hom.squareAlgebra f' a ha e'
  have := Hom.isScalarTower_squareAlgebra_left ha e'
  have := f.isScalarTower_squareAlgebra_right w e ha hb e'
  pullbackFormsSectionsEquiv_pullbackFormsBaseChange hV f hU e b hW w hU₂ e' ha hb q _
    (fun x => by
      rw [Stacks.DeRham.formsBaseChangeMapₛₗ_tmul, map_one, KaehlerDifferential.map_D]
      rfl) ω

end AlgebraicGeometry.Scheme

end
