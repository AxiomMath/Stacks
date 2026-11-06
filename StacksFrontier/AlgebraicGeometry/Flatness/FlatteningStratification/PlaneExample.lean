module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# A module with no universal flattening

Let `k` be a field, `R = k[x, y]` and let `𝓕` be the quasi-coherent module on `Spec R`
associated to `k[x, x⁻¹, y]/(y) = (R/(y))[1/x]`, viewed as a module over `Spec R` through the
identity morphism. This file computes the base change of `𝓕` to any affine `R`-scheme and
deduces that the flatness functor of `𝓕` takes a singleton value on every quotient
`R/(x, y)^n`: the pulled-back module vanishes there, hence is trivially flat.

Together with the failure of flatness on `Spec R` itself, this is the Stacks Project's example
of a quasi-coherent module admitting no universal flattening.

## Main definitions

* `AlgebraicGeometry.PlaneFlatteningExample` records the ground field of the example.
* `AlgebraicGeometry.PlaneFlatteningExample.R`, `.M` and `.F` are the ring, the module and the
  associated quasi-coherent sheaf.
* `AlgebraicGeometry.PlaneFlatteningExample.flatnessSituation` and
  `AlgebraicGeometry.PlaneFlatteningExample.flatValue` are the flatness situation of the
  example and the value of its flatness functor on an affine `R`-scheme.
* `IsLocalizedModule.baseChangeLocalizedEquiv` identifies the localization of a scalar
  extension with the scalar extension of a localized module.

## Main results

* `AlgebraicGeometry.PlaneFlatteningExample.affineBaseChangeModuleIso` identifies the module
  pulled back to `Spec A` with the sheaf associated to `(A/yA)[1/x]`.
* `AlgebraicGeometry.PlaneFlatteningExample.flatValue_infinitesimalQuotient_unique` exhibits
  the unique value of the flatness functor on each infinitesimal quotient of the origin.

## Implementation notes

The module `k[x, x⁻¹, y]/(y)` is represented as the localization of the `R`-module `R/(y)` at
the powers of `x`, which is canonically the indicated quotient of the localized polynomial
ring. The scheme, the morphism and the sheaf are determined by the field rather than stored as
independent data.

The flatness functor is subterminal by construction, so a `Unique` instance expresses exactly
that its value is a singleton. The exponent `n` is allowed to be zero, where the quotient is
the zero ring.

## References

* [Stacks Project, Tag 0FJ1](https://stacks.math.columbia.edu/tag/0FJ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

/-- A tensor product whose right factor is trivial is trivial. -/
public lemma TensorProduct.subsingleton_of_subsingleton_right {R S M : Type*}
    [CommSemiring R] [AddCommMonoid S] [Module R S] [AddCommMonoid M] [Module R M]
    (hM : Subsingleton M) : Subsingleton (S ⊗[R] M) :=
  inferInstance

namespace IsLocalizedModule

/-- Localization of a scalar extension is the scalar extension of a localized module. -/
@[ega "0 1.5.4" "partial"]
public noncomputable def baseChangeLocalizedEquiv
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (f : R) {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers f) φ] :
    LocalizedModule (Submonoid.powers f) (B ⊗[R] M) ≃ₗ[R] B ⊗[R] M' :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers f) (B ⊗[R] M)).restrictScalars R).trans
    ((TensorProduct.leftComm R (Localization (Submonoid.powers f)) B M).trans
      ((TensorProduct.congr (LinearEquiv.refl R B)
          ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).restrictScalars
            R).symm).trans
        (TensorProduct.congr (LinearEquiv.refl R B)
          (IsLocalizedModule.iso (Submonoid.powers f) φ))))

/-- On elements with denominator one, the scalar extension comparison is the base change
map. -/
public theorem baseChangeLocalizedEquiv_mk
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (f : R) {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers f) φ] (b : B) (m : M) :
    baseChangeLocalizedEquiv R B f φ (LocalizedModule.mk (b ⊗ₜ[R] m) 1) =
      b ⊗ₜ[R] φ m := by
  unfold baseChangeLocalizedEquiv
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [LocalizedModule.equivTensorProduct_apply_mk, TensorProduct.leftComm_tmul]
  simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [Localization.mk_one, LinearEquiv.restrictScalars_symm_apply,
    LocalizedModule.equivTensorProduct_symm_apply_tmul_one]
  simp only [IsLocalizedModule.iso_mk_one]

/-- The comparison after the localization map is the base change of the original map. -/
public theorem baseChangeLocalizedEquiv_comp
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (f : R) {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (φ : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers f) φ] :
    (baseChangeLocalizedEquiv R B f φ).toLinearMap.comp
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (B ⊗[R] M)) =
      (LinearMap.baseChange B φ).restrictScalars R := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LocalizedModule.mkLinearMap_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  induction x with
  | tmul b m =>
      rw [LinearMap.baseChange_tmul]
      exact baseChangeLocalizedEquiv_mk R B f φ b m
  | add x y hx hy =>
      rw [show LocalizedModule.mk (x + y) (1 : Submonoid.powers f) =
            LocalizedModule.mk x 1 + LocalizedModule.mk y 1 by
          rw [LocalizedModule.mk_add_mk]
          simp]
      rw [map_add, map_add, hx, hy]

end IsLocalizedModule

namespace AlgebraicGeometry

/-- The ground field of the flattening example on the affine plane. -/
public structure PlaneFlatteningExample where
  /-- The field `k`. -/
  k : Type u
  /-- Its field structure. -/
  [field : Field k]

attribute [instance] PlaneFlatteningExample.field

namespace PlaneFlatteningExample

/-- The polynomial ring `k[x, y]`. -/
public abbrev R (E : PlaneFlatteningExample.{u}) := MvPolynomial (Fin 2) E.k

/-- The coordinate `x`. -/
public abbrev x (E : PlaneFlatteningExample.{u}) : E.R := MvPolynomial.X 0

/-- The coordinate `y`. -/
public abbrev y (E : PlaneFlatteningExample.{u}) : E.R := MvPolynomial.X 1

/-- The ideal `(y)` in `k[x, y]`. -/
public abbrev yIdeal (E : PlaneFlatteningExample.{u}) : Ideal E.R := Ideal.span {E.y}

/-- The `R`-module `(R/(y))[1/x]`, canonically `k[x, x⁻¹, y]/(y)`. -/
public abbrev M (E : PlaneFlatteningExample.{u}) :=
  LocalizedModule (Submonoid.powers E.x) (E.R ⧸ E.yIdeal)

/-- The affine plane `Spec (k[x, y])`. -/
public abbrev X (E : PlaneFlatteningExample.{u}) : Scheme.{u} :=
  Spec (.of E.R)

/-- The associated quasi-coherent sheaf of the localized quotient module. -/
public abbrev F (E : PlaneFlatteningExample.{u}) :
    SheafOfModules.{u} (structureSheafRing E.X.toRingedSpace) :=
  tilde (ModuleCat.of (CommRingCat.of E.R) E.M)

/-- The flatness situation for the identity of `Spec (k[x, y])`. -/
public def flatnessSituation (E : PlaneFlatteningExample.{u}) :
    FlatnessSituation.{u} where
  S := E.X
  X := E.X
  f := 𝟙 E.X
  F := E.F
  isQuasicoherent := by
    change (tilde (ModuleCat.of (CommRingCat.of E.R) E.M)).IsQuasicoherent
    infer_instance

/-- The value of the flatness functor on an affine `R`-scheme `Spec A`. -/
public abbrev flatValue (E : PlaneFlatteningExample.{u}) (A : Type u)
    [CommRing A] [Algebra E.R A] : Type :=
  E.flatnessSituation.flatFunctor.obj
    (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E.R A)))))

/-- On `Spec A`, the example module is the associated sheaf of `(A/yA)[1/x]`. -/
public noncomputable def affineBaseChangeModuleIso
    (E : PlaneFlatteningExample.{u}) (A : Type u)
    [CommRing A] [Algebra E.R A] :
    (modulePullback
      (Spec.map (CommRingCat.ofHom (algebraMap E.R A))).toLRSHom.toShHom).obj E.F ≅
      tilde (ModuleCat.of (CommRingCat.of A)
        (LocalizedModule (Submonoid.powers (algebraMap E.R A E.x))
          (A ⧸ Ideal.span {algebraMap E.R A E.y}))) := by
  let f : CommRingCat.of E.R ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap E.R A)
  let S := Submonoid.powers (algebraMap E.R A E.x)
  let M₀ := E.R ⧸ E.yIdeal
  let q : M₀ →ₗ[E.R] E.M := LocalizedModule.mkLinearMap (Submonoid.powers E.x) M₀
  let eExt : LocalizedModule (Submonoid.powers E.x) (A ⊗[E.R] M₀) ≃ₗ[E.R]
      A ⊗[E.R] E.M := IsLocalizedModule.baseChangeLocalizedEquiv E.R A E.x q
  let qA : A ⊗[E.R] M₀ →ₗ[A] A ⊗[E.R] E.M := LinearMap.baseChange A q
  have hqA : IsLocalizedModule (Submonoid.powers E.x) (qA.restrictScalars E.R) := by
    rw [← IsLocalizedModule.baseChangeLocalizedEquiv_comp E.R A E.x q]
    exact IsLocalizedModule.of_linearEquiv (Submonoid.powers E.x)
      (LocalizedModule.mkLinearMap (Submonoid.powers E.x) (A ⊗[E.R] M₀))
      eExt
  haveI : IsLocalizedModule S qA := by
    have hq' : IsLocalizedModule
        (Algebra.algebraMapSubmonoid A (Submonoid.powers E.x)) qA :=
      IsLocalizedModule.of_restrictScalars (Submonoid.powers E.x) qA
    simpa [S, Algebra.algebraMapSubmonoid_powers] using hq'
  have hI : Ideal.map (algebraMap E.R A) E.yIdeal =
      Ideal.span {algebraMap E.R A E.y} := by
    rw [PlaneFlatteningExample.yIdeal, Ideal.map_span]
    simp
  have eQ : A ⊗[E.R] M₀ ≃ₗ[A]
      A ⧸ Ideal.span {algebraMap E.R A E.y} := by
    rw [← hI]
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A E.yIdeal).symm.toLinearEquiv
  let qT : A ⊗[E.R] M₀ →ₗ[A]
      LocalizedModule S (A ⧸ Ideal.span {algebraMap E.R A E.y}) :=
    (LocalizedModule.mkLinearMap S _).comp eQ.toLinearMap
  haveI : IsLocalizedModule S qT := by
    dsimp [qT]
    infer_instance
  let eLoc : LocalizedModule S (A ⧸ Ideal.span {algebraMap E.R A E.y}) ≃ₗ[A]
      A ⊗[E.R] E.M := IsLocalizedModule.linearEquiv S qT qA
  let extObj := (ModuleCat.extendScalars f.hom).obj
    (ModuleCat.of (CommRingCat.of E.R) E.M)
  let eChange : (↑extObj) ≃ₗ[A] A ⊗[E.R] E.M := by
    letI : Module A (↑((ModuleCat.restrictScalars f.hom).obj
        (ModuleCat.of (CommRingCat.of A) A))) := inferInstanceAs (Module A A)
    letI : Module A (↑((ModuleCat.restrictScalars f.hom).obj
        (ModuleCat.of (CommRingCat.of A) A)) ⊗[E.R] E.M) := by
      change Module A (↑extObj)
      exact extObj.isModule
    letI : IsScalarTower E.R A
        (↑((ModuleCat.restrictScalars f.hom).obj
          (ModuleCat.of (CommRingCat.of A) A))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    change (↑((ModuleCat.restrictScalars f.hom).obj
      (ModuleCat.of (CommRingCat.of A) A)) ⊗[E.R] E.M) ≃ₗ[A] _
    exact TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (LinearEquiv.refl E.R E.M)
  let eBase : (↑extObj) ≃ₗ[A]
      LocalizedModule S (A ⧸ Ideal.span {algebraMap E.R A E.y}) :=
    eChange.trans eLoc.symm
  exact (pullbackTildeIso (CommRingCat.of E.R) (CommRingCat.of A) f).app
      (ModuleCat.of (CommRingCat.of E.R) E.M) ≪≫
    (tilde.functor (CommRingCat.of A)).mapIso eBase.toModuleIso

end PlaneFlatteningExample

/-- Localizing the quotient of a ring by a principal ideal at the powers of a nilpotent
element gives the zero module. -/
public lemma localizedModule_subsingleton_of_pow_eq_zero
    {A : Type u} [CommRing A] {a b : A} {n : ℕ} (ha : a ^ n = 0) :
    Subsingleton (LocalizedModule (Submonoid.powers a) (A ⧸ Ideal.span {b})) :=
  subsingleton_of_forall_eq 0 fun z =>
    LocalizedModule.eq_zero_of_smul_eq_zero (a ^ n)
      ((Submonoid.mem_powers_iff (a ^ n) a).2 ⟨n, rfl⟩) z (by rw [ha, zero_smul])

/-- The stalks of the sheaf associated to the zero module on an affine scheme are trivial. -/
public lemma tilde_stalk_subsingleton
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (hM : Subsingleton M) (q : PrimeSpectrum.Top R) :
    Subsingleton ((tilde M).presheaf.stalk q) := by
  let f := (tilde.toStalk M q).hom
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj q.asIdeal.primeCompl f z
  have hs0 : s • z = 0 := by rw [hs, Subsingleton.elim m 0, map_zero]
  exact IsLocalizedModule.smul_injective f s (by simpa using hs0)

namespace PlaneFlatteningExample

/-- The flatness functor has one value on every infinitesimal quotient of the origin in the
flattening example on the affine plane (the first claim of **Stacks 0FJ1**, stated in full by
`AlgebraicGeometry.PlaneFlatteningExample.flatFunctor_unique_isEmpty_not_representable`). -/
public noncomputable instance flatValue_infinitesimalQuotient_unique
    (E : PlaneFlatteningExample.{u}) (n : ℕ) :
    Unique (E.flatValue (E.R ⧸ (Ideal.span ({E.x, E.y} : Set E.R)) ^ n)) := by
  let I : Ideal E.R := Ideal.span ({E.x, E.y} : Set E.R)
  let A := E.R ⧸ I ^ n
  let a := algebraMap E.R A E.x
  let b := algebraMap E.R A E.y
  have ha : a ^ n = 0 := by
    change (algebraMap E.R A E.x) ^ n = 0
    rw [← map_pow]
    change Ideal.Quotient.mk (I ^ n) (E.x ^ n) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) n
  let M := LocalizedModule (Submonoid.powers a) (A ⧸ Ideal.span {b})
  have hM : Subsingleton M := localizedModule_subsingleton_of_pow_eq_zero ha
  let F_A := tilde (ModuleCat.of (CommRingCat.of A) M)
  let t : Spec (CommRingCat.of A) ⟶ E.X :=
    Spec.map (CommRingCat.ofHom (algebraMap E.R A))
  let p1 := pullback.fst (𝟙 E.X) t
  let p2 := pullback.snd (𝟙 E.X) t
  let G := (modulePullback p2.toLRSHom.toShHom).obj F_A
  have hG : IsFlatOver p2.toLRSHom.toShHom G := by
    apply isFlatOver_of_subsingleton_stalks
    intro z
    have hsource := tilde_stalk_subsingleton
      (ModuleCat.of (CommRingCat.of A) M) hM (p2.toLRSHom.toShHom.hom.base z)
    let : Algebra ((Spec (CommRingCat.of A)).presheaf.stalk
        (p2.toLRSHom.toShHom.hom.base z))
        ((Limits.pullback (𝟙 E.X) t).presheaf.stalk z) :=
      (p2.toLRSHom.toShHom.hom.stalkMap z).hom.toAlgebra
    let : Module ((Spec (CommRingCat.of A)).presheaf.stalk
        (p2.toLRSHom.toShHom.hom.base z))
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F_A.val.presheaf
          (p2.toLRSHom.toShHom.hom.base z)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        F_A.val (p2.toLRSHom.toShHom.hom.base z)
    have htarget : Subsingleton (TensorProduct
        ((Spec (CommRingCat.of A)).presheaf.stalk (p2.toLRSHom.toShHom.hom.base z))
        ((Limits.pullback (𝟙 E.X) t).presheaf.stalk z)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F_A.val.presheaf
          (p2.toLRSHom.toShHom.hom.base z))) :=
      TensorProduct.subsingleton_of_subsingleton_right hsource
    obtain ⟨e, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      p2.toLRSHom.toShHom F_A z
    exact ⟨fun m m' => e.injective (htarget.allEq (e m) (e m'))⟩
  let eaff := affineBaseChangeModuleIso E A
  let e2 := (modulePullback p2.toLRSHom.toShHom).mapIso eaff
  have hG' : IsFlatOver p2.toLRSHom.toShHom
      ((modulePullback p2.toLRSHom.toShHom).obj
        ((modulePullback t.toLRSHom.toShHom).obj E.F)) :=
    isFlatOver_of_moduleIso p2.toLRSHom.toShHom e2.symm hG
  have hcomp : p2 ≫ t = p1 := by
    dsimp [p1, p2]
    simpa using (pullback.condition :
      pullback.fst (𝟙 E.X) t ≫ 𝟙 E.X = pullback.snd (𝟙 E.X) t ≫ t).symm
  let ecomp := schemeModulePullbackCompIso p2 t
  have ecomp' :
      ((modulePullback p2.toLRSHom.toShHom).obj
        ((modulePullback t.toLRSHom.toShHom).obj E.F)) ≅
        ((modulePullback p1.toLRSHom.toShHom).obj E.F) := by
    simpa only [hcomp, Functor.comp_obj] using ecomp.app E.F
  have hflat : E.flatnessSituation.IsFlatAfterBaseChange
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E.R A)))) := by
    change IsFlatOver p2.toLRSHom.toShHom
      ((modulePullback p1.toLRSHom.toShHom).obj E.F)
    exact isFlatOver_of_moduleIso p2.toLRSHom.toShHom ecomp' hG'
  change Unique (E.flatValue A)
  let value : E.flatValue A := ⟨hflat⟩
  exact ⟨⟨value⟩, fun x => Subsingleton.elim _ _⟩

end PlaneFlatteningExample

end AlgebraicGeometry
