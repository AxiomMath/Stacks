module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleBaseChange
public import StacksFrontier.RingTheory.Dualizing.NoetherianPairings.DualizingModuleIndependence
public import StacksFrontier.RingTheory.Dualizing.NoetherianPairings.DualizingModuleFlatBaseChange
public import StacksFrontier.RingTheory.Dualizing.NoetherianPairings.Ports.CommonFiniteFactorization
public import StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.SimultaneousLocalization
import all StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization

/-!
# Transitivity of the localization comparisons for relative dualizing modules

The three identifications of Tag 0BT2 — replacing the base of a quasi-finite map of Noetherian
rings by a localization through which it factors, localizing the target, and doing both at once
— are
`Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away`,
`Stacks.Discriminant.localizedModule_dualizingModule_equiv` and
`Stacks.Discriminant.localizedModule_dualizingModule_equiv_of_baseLocalization`, together with
their characterizations on tensors and their naturality in the chosen finite-open
factorizations.  They are proved in
`StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization`,
`StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization` and
`StacksFrontier.AlgebraicGeometry.Discriminant.SimultaneousLocalization`, which this module
imports and re-exports.

What is proved here is how those identifications compose when the *ring* is localized twice,
rather than when the factorization is changed.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away_trans`: two successive
  replacements of the base by a localization compose to the single replacement computed over
  the original base.
* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_trans`: two successive
  localizations of the target compose to the single localization at the product of the two
  elements.
* `Stacks.Discriminant.localizedModule_dualizingModule_equiv_comm_base`: localizing the target
  and replacing the base commute.

## Implementation notes

Each of the three proofs compares two routes through the finite-open models, so each needs the
identifications computed on a pure tensor through the explicit factorization they were built
from.  Those computations are
`Stacks.Discriminant.dualizingModule_equiv_of_isLocalization_away_formula` and
`Stacks.Discriminant.localizedModule_dualizingModule_equiv_apply`, which live with the
constructions they compute, in `StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization`
and `StacksFrontier.AlgebraicGeometry.Discriminant.TargetLocalization`; this module imports both.
A caller wanting the identification itself should use the public `..._tmul` characterizations
instead.

The comparison `dualizingModuleEquiv` of two factorizations is used only through its
characterizing lemmas: unfolding its construction, which passes through the join of two
subalgebras of the target, makes unification unfold `SetLike.coe` without bound.  It is
irreducible where it is defined and the proofs below rely on that.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

universe u v w x y z t q s

namespace Stacks.Discriminant

open scoped TensorProduct

/-- If `S` is the localization of `R` away from `r` and `R → T` factors through `S`, then
`S → T → S ⊗[R] T` is a scalar tower for the right algebra structure on `S ⊗[R] T`. -/
private theorem isScalarTower_tensorProduct_rightAlgebra
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (r : R) [IsLocalization.Away r S] :
    letI : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    IsScalarTower S T (S ⊗[R] T) := by
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  show (algebraMap R S x) ⊗ₜ[R] (1 : T) = (1 : S) ⊗ₜ[R] algebraMap S T (algebraMap R S x)
  rw [← IsScalarTower.algebraMap_apply R S T x]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul x

/-- Two ring maps out of `Aff ⊗[A] C` and `Aff ⊗[Af] (Af ⊗[A] C)` that agree on pure tensors
agree after `Algebra.TensorProduct.cancelBaseChange`. -/
private theorem ringHom_cancelBaseChange_symm_eq
    {A Af Aff C B : Type*} [CommRing A] [CommRing Af] [CommRing Aff] [CommRing C] [CommRing B]
    [Algebra A Af] [Algebra A Aff] [Algebra Af Aff] [IsScalarTower A Af Aff] [Algebra A C]
    (ρ₁ : (Aff ⊗[Af] (Af ⊗[A] C)) →+* B) (ρ₂ : (Aff ⊗[A] C) →+* B)
    (hρ : ∀ (a : Aff) (c : C), ρ₁ (a ⊗ₜ[Af] ((1 : Af) ⊗ₜ[A] c)) = ρ₂ (a ⊗ₜ[A] c))
    (c : Aff ⊗[A] C) :
    ρ₁ ((Algebra.TensorProduct.cancelBaseChange A Af Aff Aff C).symm c) = ρ₂ c := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    exact hρ a c

/-- Extending a linear form twice, along `A → Af → Aff`, is extending it once along `A → Aff`,
up to `Algebra.TensorProduct.cancelBaseChange`. -/
private theorem dual_baseChange_baseChange_comp_cancelBaseChange_symm
    {A Af Aff C : Type*} [CommRing A] [CommRing Af] [CommRing Aff] [CommRing C]
    [Algebra A Af] [Algebra A Aff] [Algebra Af Aff] [IsScalarTower A Af Aff] [Algebra A C]
    (φ : Module.Dual A C) :
    Module.Dual.baseChange Aff (Module.Dual.baseChange Af φ) ∘ₗ
        (Algebra.TensorProduct.cancelBaseChange A Af Aff Aff C).symm.toLinearMap =
      Module.Dual.baseChange Aff φ := by
  refine LinearMap.ext fun c => ?_
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul, Module.Dual.baseChange_apply_tmul]
    rw [smul_assoc, one_smul]

/-- An `S`-linear map out of a localization `N` of an `R`-module agrees with an `S`-linear
equivalence as soon as the two agree on the image of the localization map. -/
private theorem apply_eq_of_isLocalizedModule_of_linearEquiv
    {R S D N P : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup D] [Module R D] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [AddCommGroup P] [Module S P]
    (s : Submonoid R) (lm : D →ₗ[R] N) (hlm : IsLocalizedModule s lm)
    (u : N →ₗ[S] P) (e : N ≃ₗ[S] P) (h : ∀ ω, u (lm ω) = e (lm ω)) (n : N) :
    u n = e n := by
  let : Module R P := Module.compHom P (algebraMap R S)
  have : IsScalarTower R S P := IsScalarTower.of_compHom (R := R) (A := S) (M := P)
  have := hlm
  let eR : N ≃ₗ[R] P := e.restrictScalars R
  have : IsLocalizedModule s (eR.toLinearMap ∘ₗ lm) := IsLocalizedModule.of_linearEquiv s lm eR
  exact LinearMap.congr_fun (IsLocalizedModule.linearMap_ext s lm (eR.toLinearMap ∘ₗ lm)
    (g := u.restrictScalars R) (g' := eR.toLinearMap) (LinearMap.ext h)) n

/-- The base-change comparison `Af ⊗[A] B ≃ B` attached to a localization `Af` of the base through
which `A → B` factors sends a pure tensor to the product of the images of its two factors. -/
private theorem baseChangeTargetEquiv_tmul
    {A : Type u} {B : Type v} {Af : Type w}
    [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    (f : A) [IsLocalization.Away f Af] (a : Af) (b : B) :
    letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    baseChangeTargetEquiv f (a ⊗ₜ[A] b) = algebraMap Af B a * b := by
  let : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Af B (Af ⊗[A] B) :=
    isScalarTower_tensorProduct_rightAlgebra (S := Af) (T := B) f
  have hsplit : (a ⊗ₜ[A] b : Af ⊗[A] B) =
      (a ⊗ₜ[A] (1 : B)) * ((1 : Af) ⊗ₜ[A] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hone : baseChangeTargetEquiv f ((1 : Af) ⊗ₜ[A] b) = b :=
    (baseChangeTargetEquiv f).commutes b
  have hleft : baseChangeTargetEquiv f (a ⊗ₜ[A] (1 : B)) = algebraMap Af B a :=
    (AlgEquiv.restrictScalars Af (baseChangeTargetEquiv f)).commutes a
  rw [hsplit, map_mul, hone, hleft]

/-- If the comparison of `F` with `G` sends `x` to `y`, then comparing `F` with a third
factorization `H` sends `x` to the comparison of `G` with `H` applied to `y`. -/
private theorem dualizingModuleEquiv_apply_eq_of_apply_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B) (G : FiniteOpenFactorization.{u, v, x} A B)
    (H : FiniteOpenFactorization.{u, v, y} A B) {x : dualizingModule F} {y : dualizingModule G}
    (hxy : dualizingModuleEquiv F G x = y) :
    dualizingModuleEquiv F H x = dualizingModuleEquiv G H y := by
  rw [← hxy, ← LinearEquiv.trans_apply, dualizingModuleEquiv_trans]

/-- Replacing the base by a localization commutes with comparing the source factorizations. -/
private theorem dualizingModule_equiv_of_isLocalization_away_comp_dualizingModuleEquiv
    {A : Type u} {B : Type v} {Af : Type w} [CommRing A] [CommRing B] [CommRing Af]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing Af] [Algebra.QuasiFinite A B]
    (f : A) [IsLocalization.Away f Af]
    (F : FiniteOpenFactorization.{u, v, x} A B) (F' : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{w, v, z} Af B) (m : dualizingModule F) :
    dualizingModule_equiv_of_isLocalization_away f F' G (dualizingModuleEquiv F F' m) =
      dualizingModule_equiv_of_isLocalization_away f F G m :=
  (dualizingModule_equiv_of_isLocalization_away_natural f F F' G G m).symm.trans
    (DFunLike.congr_fun (dualizingModuleEquiv_refl G) _)

/-- Localizing the target commutes with comparing the source factorizations, for a localization
map that is transported along the comparison. -/
private theorem localizedModule_dualizingModule_equiv_comp_dualizingModuleEquiv
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x} [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B) (F' : FiniteOpenFactorization.{u, v, z} A B)
    (K : FiniteOpenFactorization.{u, w, t} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (lm : dualizingModule F' →ₗ[B] M) (hM : IsLocalizedModule (Submonoid.powers g) lm)
    (lmF : dualizingModule F →ₗ[B] M) (hF : IsLocalizedModule (Submonoid.powers g) lmF)
    (hlmF : ∀ x, lmF x = lm (dualizingModuleEquiv F F' x)) (m : M) :
    localizedModule_dualizingModule_equiv g F K lmF hF m =
      localizedModule_dualizingModule_equiv g F' K lm hM m :=
  (DFunLike.congr_fun (dualizingModuleEquiv_refl K) _).symm.trans
    (localizedModule_dualizingModule_equiv_natural_in_source g F F' K K lmF hF lm hM
      LinearMap.id hlmF m)

/-- The identification of the localization of the dualizing module with the dualizing module
of a factorization `G`, computed on a pure tensor through `locFact`. -/
private theorem localizedModule_dualizingModule_equiv_tmul_locFact
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x} [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B) (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (lm : dualizingModule F →ₗ[B] M) (hM : IsLocalizedModule (Submonoid.powers g) lm)
    (φ : Module.Dual A F.middle) (b : B) :
    localizedModule_dualizingModule_equiv g F G lm hM (lm (dualizingModule.tmul F φ b)) =
      dualizingModuleEquiv (locFact (Bg := Bg) g F) G
        (dualizingModule.tmul (locFact (Bg := Bg) g F) φ (algebraMap B Bg b)) :=
  (localizedModule_dualizingModule_equiv_apply g F G lm hM _).trans
    (DFunLike.congr_arg (dualizingModuleEquiv _ G)
      (dualizingTensorLocalizationEquiv_tmul g F φ b))

/-- **Replacing the base by a localization twice is replacing it once.** Suppose `A → B` factors
through the localization `Af` of `A` away from `f`, that `Af → B` factors through the localization
`Aff` of `Af` away from `f'`, and that `Aff` is also the localization of `A` away from a single
element `e`.  Then the two successive base-replacement identifications of part (1) compose to the
single one computed over `A` directly.

This is transitivity of part (1) *in the base ring*, as opposed to
`dualizingModule_equiv_of_isLocalization_away_natural`, which varies only the chosen finite-open
factorizations. -/
public theorem dualizingModule_equiv_of_isLocalization_away_trans
    {A : Type u} {B : Type v} {Af : Type w} {Aff : Type x}
    [CommRing A] [CommRing B] [CommRing Af] [CommRing Aff]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [Algebra A Aff] [Algebra Af Aff] [Algebra Aff B]
    [IsScalarTower A Af Aff] [IsScalarTower A Aff B] [IsScalarTower Af Aff B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing Af] [IsNoetherianRing Aff]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite Af B]
    (f : A) [IsLocalization.Away f Af]
    (f' : Af) [IsLocalization.Away f' Aff]
    (e : A) [IsLocalization.Away e Aff]
    (F : FiniteOpenFactorization.{u, v, z} A B)
    (G : FiniteOpenFactorization.{w, v, q} Af B)
    (H : FiniteOpenFactorization.{x, v, s} Aff B)
    (ω : dualizingModule F) :
    dualizingModule_equiv_of_isLocalization_away f' G H
        (dualizingModule_equiv_of_isLocalization_away f F G ω) =
      dualizingModule_equiv_of_isLocalization_away e F H ω := by
  classical
  let : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Af B (Af ⊗[A] B) :=
    isScalarTower_tensorProduct_rightAlgebra (S := Af) (T := B) f
  let : Algebra B (Aff ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Aff B (Aff ⊗[A] B) :=
    isScalarTower_tensorProduct_rightAlgebra (S := Aff) (T := B) e
  let : Algebra B (Aff ⊗[Af] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Aff B (Aff ⊗[Af] B) :=
    isScalarTower_tensorProduct_rightAlgebra (S := Aff) (T := B) f'
  induction ω using dualizingModule.induction_on with
  | zero => simp only [map_zero]
  | add xx yy hx hy => simp only [map_add, hx, hy]
  | tmul φ b =>
    let Pf := retargetFactorization (FiniteOpenFactorization.baseChange F Af)
      (AlgEquiv.restrictScalars Af (baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f))
    let Pe := retargetFactorization (FiniteOpenFactorization.baseChange F Aff)
      (AlgEquiv.restrictScalars Aff (baseChangeTargetEquiv (A := A) (B := B) (Af := Aff) e))
    let Pff := retargetFactorization (FiniteOpenFactorization.baseChange Pf Aff)
      (AlgEquiv.restrictScalars Aff (baseChangeTargetEquiv (A := Af) (B := B) (Af := Aff) f'))
    have hstep1 :
        dualizingModule_equiv_of_isLocalization_away f F G (dualizingModule.tmul F φ b) =
          dualizingModuleEquiv Pf G (dualizingModule.tmul Pf (Module.Dual.baseChange Af φ) b) :=
      dualizingModule_equiv_of_isLocalization_away_formula f F G φ b
    have hstep2 := dualizingModule_equiv_of_isLocalization_away_comp_dualizingModuleEquiv f' Pf G H
      (dualizingModule.tmul Pf (Module.Dual.baseChange Af φ) b)
    have hstep3 := dualizingModule_equiv_of_isLocalization_away_formula (A := Af) (B := B)
      (Af := Aff) f' Pf H (Module.Dual.baseChange Af φ) b
    have hdirect := dualizingModule_equiv_of_isLocalization_away_formula (A := A) (B := B)
      (Af := Aff) e F H φ b
    have he := ringHom_cancelBaseChange_symm_eq (algebraMap Pff.middle B)
      (algebraMap Pe.middle B) fun xa c => by
        have hinner : algebraMap Pf.middle B ((1 : Af) ⊗ₜ[A] c) = algebraMap F.middle B c := by
          show baseChangeTargetEquiv f ((1 : Af) ⊗ₜ[A] algebraMap F.middle B c) = _
          exact (baseChangeTargetEquiv f).commutes _
        have hL : algebraMap Pff.middle B (xa ⊗ₜ[Af] ((1 : Af) ⊗ₜ[A] c)) =
            algebraMap Aff B xa * algebraMap F.middle B c := by
          show baseChangeTargetEquiv f'
            (xa ⊗ₜ[Af] algebraMap Pf.middle B ((1 : Af) ⊗ₜ[A] c)) = _
          rw [hinner, baseChangeTargetEquiv_tmul]
        have hR : algebraMap Pe.middle B (xa ⊗ₜ[A] c) =
            algebraMap Aff B xa * algebraMap F.middle B c := by
          show baseChangeTargetEquiv e (xa ⊗ₜ[A] algebraMap F.middle B c) = _
          rw [baseChangeTargetEquiv_tmul]
        exact hL.trans hR.symm
    have hcmp : dualizingModuleEquiv Pff Pe (dualizingModule.tmul _
          (Module.Dual.baseChange Aff (Module.Dual.baseChange Af φ)) b) =
        dualizingModule.tmul Pe (Module.Dual.baseChange Aff φ) b :=
      (comparison_restrict_of_equiv Pe Pff
        (Algebra.TensorProduct.cancelBaseChange A Af Aff Aff F.middle).symm he
        (Module.Dual.baseChange Aff (Module.Dual.baseChange Af φ)) b).trans
        (congrArg (fun ψ => dualizingModule.tmul Pe ψ b)
          (dual_baseChange_baseChange_comp_cancelBaseChange_symm (Af := Af) (Aff := Aff) φ))
    have hC := dualizingModuleEquiv_apply_eq_of_apply_eq Pff Pe H hcmp
    exact (DFunLike.congr_arg (dualizingModule_equiv_of_isLocalization_away f' G H) hstep1).trans
      (hstep2.trans (hstep3.trans (hC.trans hdirect.symm)))

/-- **Localizing the target twice is localizing it once.** Let `Bg` be the localization of `B`
away from `g`, let `Bh` be the localization of `Bg` away from `h`, and suppose `Bh` is also the
localization of `B` away from a single element `g'`.  Given a model `N` of the twofold
localization of the relative dualizing module of `F`, presented both as a localization away from
`h` of the dualizing module of a factorization `G` of `A → Bg` and as a localization away from
`g'` of the dualizing module of `F` itself — compatibly, which is what `hcompat` says — the two
resulting identifications of `N` with the dualizing module of a factorization `H` of `A → Bh`
agree.

This is transitivity of part (2) *in the target ring*, as opposed to
`localizedModule_dualizingModule_equiv_natural`, which varies only the chosen finite-open
factorizations. -/
public theorem localizedModule_dualizingModule_equiv_trans
    {A : Type u} {B : Type v} {Bg : Type w} {Bh : Type x} {M : Type y} {N : Type z}
    [CommRing A] [CommRing B] [CommRing Bg] [CommRing Bh]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [Algebra Bg Bh] [Algebra B Bh] [Algebra A Bh]
    [IsScalarTower A B Bh] [IsScalarTower B Bg Bh] [IsScalarTower A Bg Bh]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    [IsNoetherianRing Bg] [Algebra.QuasiFinite A Bg]
    (g : B) [IsLocalization.Away g Bg]
    (h : Bg) [IsLocalization.Away h Bh]
    (g' : B) [IsLocalization.Away g' Bh]
    (F : FiniteOpenFactorization.{u, v, t} A B)
    (G : FiniteOpenFactorization.{u, w, q} A Bg)
    (H : FiniteOpenFactorization.{u, x, s} A Bh)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    [AddCommGroup N] [Module B N] [Module Bg N] [Module Bh N]
    [IsScalarTower B Bg N] [IsScalarTower Bg Bh N] [IsScalarTower B Bh N]
    (lm₁ : dualizingModule F →ₗ[B] M) (hM : IsLocalizedModule (Submonoid.powers g) lm₁)
    (lmG : dualizingModule G →ₗ[Bg] N) (hlmG : IsLocalizedModule (Submonoid.powers h) lmG)
    (lmc : dualizingModule F →ₗ[B] N) (hlmc : IsLocalizedModule (Submonoid.powers g') lmc)
    (hcompat : ∀ ω : dualizingModule F,
      lmc ω = lmG (localizedModule_dualizingModule_equiv g F G lm₁ hM (lm₁ ω)))
    (n : N) :
    localizedModule_dualizingModule_equiv h G H lmG hlmG n =
      localizedModule_dualizingModule_equiv g' F H lmc hlmc n := by
  classical
  let L := locFact (Bg := Bg) g F
  let lmFg : dualizingModule L →ₗ[Bg] N := lmG ∘ₗ (dualizingModuleEquiv L G).toLinearMap
  let : IsLocalizedModule (Submonoid.powers h) lmG := hlmG
  let : IsLocalizedModule (Submonoid.powers h) lmFg :=
    IsLocalizedModule.of_linearEquiv_right _ lmG (dualizingModuleEquiv L G)
  refine apply_eq_of_isLocalizedModule_of_linearEquiv _ lmc hlmc
    (localizedModule_dualizingModule_equiv h G H lmG hlmG).toLinearMap
    (localizedModule_dualizingModule_equiv g' F H lmc hlmc) (fun ω => ?_) n
  induction ω using dualizingModule.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ b =>
    let L₂ := locFact (Bg := Bh) h L
    let L' := locFact (Bg := Bh) g' F
    have hlhs0 : lmc (dualizingModule.tmul F φ b) =
        lmFg (dualizingModule.tmul L φ (algebraMap B Bg b)) :=
      (hcompat _).trans (DFunLike.congr_arg lmG
        (localizedModule_dualizingModule_equiv_tmul_locFact g F G lm₁ hM φ b))
    have hnat := localizedModule_dualizingModule_equiv_comp_dualizingModuleEquiv h L G H lmG hlmG
      lmFg inferInstance (fun _ => rfl)
      (lmFg (dualizingModule.tmul L φ (algebraMap B Bg b)))
    have hA := localizedModule_dualizingModule_equiv_tmul_locFact h L H lmFg inferInstance φ
      (algebraMap B Bg b)
    have hB := localizedModule_dualizingModule_equiv_tmul_locFact g' F H lmc hlmc φ b
    have hbh : algebraMap Bg Bh (algebraMap B Bg b) = algebraMap B Bh b :=
      (IsScalarTower.algebraMap_apply B Bg Bh b).symm
    have he : ∀ c : L'.middle,
        algebraMap L₂.middle Bh (AlgEquiv.refl (R := A) c) = algebraMap L'.middle Bh c :=
      fun c => (IsScalarTower.algebraMap_apply B Bg Bh (algebraMap F.middle B c)).symm
    have hcmp : dualizingModuleEquiv L₂ L' (dualizingModule.tmul L₂ φ (algebraMap B Bh b)) =
        dualizingModule.tmul L' φ (algebraMap B Bh b) :=
      comparison_restrict_of_equiv L' L₂ (AlgEquiv.refl (R := A)) he φ (algebraMap B Bh b)
    have hC := dualizingModuleEquiv_apply_eq_of_apply_eq L₂ L' H hcmp
    exact (DFunLike.congr_arg (localizedModule_dualizingModule_equiv h G H lmG hlmG) hlhs0).trans
      (hnat.symm.trans (hA.trans ((DFunLike.congr_arg (dualizingModuleEquiv L₂ H)
        (congrArg (fun y => dualizingModule.tmul L₂ φ y) hbh)).trans (hC.trans hB.symm))))

/-- **Localizing the target and replacing the base by a localization commute.** Let `Af` be the
localization of `A` away from `f`, through which `A → B` factors, and let `Bg` be the localization
of `B` away from `g`.  A model `M` of the localization of the relative dualizing module of `F`
away from `g` can be identified with the dualizing module of a factorization `K` of `Af → Bg` in
two ways: localize the target first and replace the base afterwards, or replace the base first —
passing to a factorization `G'` of `Af → B`, which turns `M` into a localization of *its*
dualizing module, as `hcompat` records — and localize the target afterwards.  The two agree.

With `g` the image of `f` this is the content of
`localizedModule_dualizingModule_equiv_of_baseLocalization_eq_comp`; here `f` and `g` are
unrelated. -/
public theorem localizedModule_dualizingModule_equiv_comm_base
    {A : Type u} {B : Type v} {Af : Type w} {Bg : Type x} {M : Type y}
    [CommRing A] [CommRing B] [CommRing Af] [CommRing Bg]
    [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]
    [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [Algebra Af Bg] [IsScalarTower Af B Bg] [IsScalarTower A Af Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing Af] [IsNoetherianRing Bg]
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A Bg] [Algebra.QuasiFinite Af B]
    (f : A) [IsLocalization.Away f Af]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, z} A B)
    (G : FiniteOpenFactorization.{u, x, t} A Bg)
    (G' : FiniteOpenFactorization.{w, v, q} Af B)
    (K : FiniteOpenFactorization.{w, x, s} Af Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (lm : dualizingModule F →ₗ[B] M) (hM : IsLocalizedModule (Submonoid.powers g) lm)
    (lm' : dualizingModule G' →ₗ[B] M) (hM' : IsLocalizedModule (Submonoid.powers g) lm')
    (hcompat : ∀ ω : dualizingModule F,
      lm' (dualizingModule_equiv_of_isLocalization_away f F G' ω) = lm ω)
    (m : M) :
    dualizingModule_equiv_of_isLocalization_away f G K
        (localizedModule_dualizingModule_equiv g F G lm hM m) =
      localizedModule_dualizingModule_equiv g G' K lm' hM' m := by
  classical
  let : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Af B (Af ⊗[A] B) :=
    isScalarTower_tensorProduct_rightAlgebra (S := Af) (T := B) f
  let : Algebra Bg (Af ⊗[A] Bg) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Af Bg (Af ⊗[A] Bg) :=
    isScalarTower_tensorProduct_rightAlgebra (S := Af) (T := Bg) f
  let P := retargetFactorization (FiniteOpenFactorization.baseChange F Af)
    (AlgEquiv.restrictScalars Af (baseChangeTargetEquiv (A := A) (B := B) (Af := Af) f))
  let lmP : dualizingModule P →ₗ[B] M := lm' ∘ₗ (dualizingModuleEquiv P G').toLinearMap
  let : IsLocalizedModule (Submonoid.powers g) lm' := hM'
  let : IsLocalizedModule (Submonoid.powers g) lmP :=
    IsLocalizedModule.of_linearEquiv_right _ lm' (dualizingModuleEquiv P G')
  refine apply_eq_of_isLocalizedModule_of_linearEquiv _ lm hM
    ((dualizingModule_equiv_of_isLocalization_away f G K).toLinearMap.comp
      (localizedModule_dualizingModule_equiv g F G lm hM).toLinearMap)
    (localizedModule_dualizingModule_equiv g G' K lm' hM') (fun ω => ?_) m
  induction ω using dualizingModule.induction_on with
  | zero => simp only [map_zero]
  | add xx yy hx hy => simp only [map_add, hx, hy]
  | tmul φ b =>
    let L := locFact (Bg := Bg) g F
    let Q := retargetFactorization (FiniteOpenFactorization.baseChange L Af)
      (AlgEquiv.restrictScalars Af (baseChangeTargetEquiv (A := A) (B := Bg) (Af := Af) f))
    let LP := locFact (Bg := Bg) g P
    -- route A: part (2) at `g`, then part (1) at `f`
    have hL1 := localizedModule_dualizingModule_equiv_tmul_locFact g F G lm hM φ b
    have hL2 := dualizingModule_equiv_of_isLocalization_away_comp_dualizingModuleEquiv (B := Bg) f L
      G K (dualizingModule.tmul L φ (algebraMap B Bg b))
    have hL3 : dualizingModule_equiv_of_isLocalization_away f L K
          (dualizingModule.tmul L φ (algebraMap B Bg b)) =
        dualizingModuleEquiv Q K
          (dualizingModule.tmul Q (Module.Dual.baseChange Af φ) (algebraMap B Bg b)) :=
      dualizingModule_equiv_of_isLocalization_away_formula f L K φ (algebraMap B Bg b)
    -- route B: part (1) at `f`, then part (2) at `g` over the localized base
    have hR1 : lm (dualizingModule.tmul F φ b) =
        lmP (dualizingModule.tmul P (Module.Dual.baseChange Af φ) b) :=
      (hcompat _).symm.trans (DFunLike.congr_arg lm'
        (dualizingModule_equiv_of_isLocalization_away_formula f F G' φ b))
    have hR2 := localizedModule_dualizingModule_equiv_comp_dualizingModuleEquiv (A := Af) g P G' K
      lm' hM' lmP inferInstance (fun _ => rfl)
      (lmP (dualizingModule.tmul P (Module.Dual.baseChange Af φ) b))
    have hR3 := localizedModule_dualizingModule_equiv_tmul_locFact (A := Af) (Bg := Bg) g P K lmP
      inferInstance (Module.Dual.baseChange Af φ) b
    -- the two canonical factorizations over the localized base agree
    have he : ∀ c : Af ⊗[A] F.middle,
        algebraMap Q.middle Bg (AlgEquiv.refl (R := Af) c) = algebraMap LP.middle Bg c := by
      intro c
      induction c using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | add xx yy hx hy =>
        exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
      | tmul a c =>
        have h1 : algebraMap Q.middle Bg (a ⊗ₜ[A] c) =
            algebraMap Af Bg a * algebraMap L.middle Bg c := by
          show baseChangeTargetEquiv f (a ⊗ₜ[A] algebraMap L.middle Bg c) = _
          rw [baseChangeTargetEquiv_tmul]
        have h2 : algebraMap LP.middle Bg (a ⊗ₜ[A] c) =
            algebraMap B Bg (algebraMap Af B a * algebraMap F.middle B c) := by
          show algebraMap B Bg (baseChangeTargetEquiv f (a ⊗ₜ[A] algebraMap F.middle B c)) = _
          rw [baseChangeTargetEquiv_tmul]
        have h3 : algebraMap Af Bg a * algebraMap L.middle Bg c =
            algebraMap B Bg (algebraMap Af B a * algebraMap F.middle B c) := by
          rw [map_mul, ← IsScalarTower.algebraMap_apply Af B Bg a]
          rfl
        exact h1.trans (h3.trans h2.symm)
    have hC := dualizingModuleEquiv_apply_eq_of_apply_eq Q LP K
      (comparison_restrict_of_equiv LP Q (AlgEquiv.refl (R := Af)) he
        (Module.Dual.baseChange Af φ) (algebraMap B Bg b))
    exact (DFunLike.congr_arg (dualizingModule_equiv_of_isLocalization_away f G K) hL1).trans
      (hL2.trans (hL3.trans (hC.trans (hR3.symm.trans (hR2.trans
        (DFunLike.congr_arg (localizedModule_dualizingModule_equiv g G' K lm' hM') hR1.symm))))))

end Stacks.Discriminant

end
