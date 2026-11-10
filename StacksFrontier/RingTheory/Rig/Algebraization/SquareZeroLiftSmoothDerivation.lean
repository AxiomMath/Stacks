module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Derivations into localizations and base changes

Let `R → S` be a ring map with `Ω[S⁄R]` finitely presented over `S`. This file records three
facts about the `S`-modules `Derivation R S P` used in the smooth square-zero lifting step.

* Postcomposing derivations with a localization map `P → P'` of `S`-modules is a localization
  map `Derivation R S P → Derivation R S P'`.
* For a flat `S`-algebra `S'`, `Derivation R S P ⊗[S] S'` is `Derivation R S (P ⊗[S] S')`.
* For a localization `S → T` and a `T`-module `Y`, restricting derivations along `S → T` is a
  bijection `Derivation R T Y → Derivation R S Y`.

All three go through `KaehlerDifferential.linearMapEquivDerivation`, which turns derivations into
`S`-linear maps out of `Ω[S⁄R]`, and the corresponding facts about `Hom` out of a finitely
presented module (`Module.FinitePresentation.isLocalizedModule_map`,
`Module.FinitePresentation.isBaseChange_map`) and about `Ω` of a localization
(`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`).

## Main results

* `Rig.SquareZeroLift.isLocalizedModule_llcomp`
* `Rig.SquareZeroLift.derivationBaseChangeEquiv`
* `Rig.SquareZeroLift.bijective_compAlgebraMap_of_isLocalization`
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct KaehlerDifferential

universe u v w

section Localize

variable (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  [Module.FinitePresentation S Ω[S⁄R]] (p : Submonoid S)
  {P : Type w} {P' : Type w} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
  [AddCommGroup P'] [Module S P'] [Module R P'] [IsScalarTower R S P']
  (g : P →ₗ[S] P') [IsLocalizedModule p g]

omit [Module.FinitePresentation S Ω[S⁄R]] [Module R P'] [IsScalarTower R S P'] in
/-- Precomposition with a localization map `Ω → Ω'`, into a module on which `p` acts invertibly,
is bijective. -/
private theorem bijective_lcomp_mkLinearMap
    (hP' : ∀ x : p, IsUnit (algebraMap S (Module.End S P') x)) :
    Function.Bijective (LinearMap.lcomp S P' (LocalizedModule.mkLinearMap p Ω[S⁄R])) :=
  ⟨fun _ _ h ↦ IsLocalizedModule.ext p (LocalizedModule.mkLinearMap p Ω[S⁄R]) hP' h,
    fun φ ↦ ⟨IsLocalizedModule.lift p (LocalizedModule.mkLinearMap p Ω[S⁄R]) φ hP',
      IsLocalizedModule.lift_comp p _ φ hP'⟩⟩

/-- **Postcomposing derivations with a localization is a localization.** If `g : P → P'` is a
localization map of `S`-modules at `p` and `Ω[S⁄R]` is finitely presented, then
`Derivation R S P → Derivation R S P'`, `D ↦ g ∘ D`, is a localization map at `p`. -/
theorem isLocalizedModule_llcomp :
    IsLocalizedModule p (Derivation.llcomp (R := R) (A := S) g) := by
  let Ω' := LocalizedModule p Ω[S⁄R]
  let fΩ := LocalizedModule.mkLinearMap p Ω[S⁄R]
  let E : (Ω' →ₗ[S] P') ≃ₗ[S] (Ω[S⁄R] →ₗ[S] P') :=
    LinearEquiv.ofBijective _ (bijective_lcomp_mkLinearMap R p (IsLocalizedModule.map_units g))
  let L : (Ω[S⁄R] →ₗ[S] P) ≃ₗ[S] Derivation R S P := linearMapEquivDerivation R S
  let L' : (Ω[S⁄R] →ₗ[S] P') ≃ₗ[S] Derivation R S P' := linearMapEquivDerivation R S
  have key : Derivation.llcomp (R := R) (A := S) g =
      ((L'.toLinearMap ∘ₗ E.toLinearMap) ∘ₗ IsLocalizedModule.map p fΩ g) ∘ₗ
        L.symm.toLinearMap := by
    refine LinearMap.ext fun D ↦ Derivation.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    change g (D x) = L' (E (IsLocalizedModule.map p fΩ g (L.symm D))) x
    simp only [L', E, L, LinearEquiv.ofBijective_apply, LinearMap.lcomp_apply,
      linearMapEquivDerivation_apply_apply]
    rw [← LinearMap.comp_apply, IsLocalizedModule.map_comp]
    exact congrArg g (Derivation.liftKaehlerDifferential_comp_D D x).symm
  rw [key]
  have : IsLocalizedModule p ((L'.toLinearMap ∘ₗ E.toLinearMap) ∘ₗ
      IsLocalizedModule.map p fΩ g) := by
    rw [LinearMap.comp_assoc]
    exact IsLocalizedModule.of_linearEquiv p _ (E.trans L')
  exact IsLocalizedModule.of_linearEquiv_right p _ L.symm

end Localize

section BaseChange

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  (S' : Type v) [CommRing S'] [Algebra S S']
  (P : Type w) [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]

/-- The base change map `Derivation R S P ⊗[S] S' → Derivation R S (P ⊗[S] S')`,
`D ⊗ x ↦ (v ↦ D v ⊗ x)`. -/
noncomputable def derivationBaseChange :
    Derivation R S P ⊗[S] S' →ₗ[S] Derivation R S (P ⊗[S] S') :=
  TensorProduct.lift
    ((Derivation.llcomp (R := R) (A := S)).comp (TensorProduct.mk S P S').flip).flip

/-- `derivationBaseChange` sends `D ⊗ x` to the derivation `v ↦ D v ⊗ x`. -/
@[simp]
theorem derivationBaseChange_tmul_apply (D : Derivation R S P) (x : S') (v : S) :
    derivationBaseChange R S S' P (D ⊗ₜ x) v = D v ⊗ₜ x := rfl

/-- **Flat base change of derivations.** If `S'` is a flat `S`-algebra and `Ω[S⁄R]` is finitely
presented, `derivationBaseChange` is bijective. -/
theorem bijective_derivationBaseChange [Module.Flat S S'] [Module.FinitePresentation S Ω[S⁄R]] :
    Function.Bijective (derivationBaseChange R S S' P) := by
  let L : (Ω[S⁄R] →ₗ[S] P) ≃ₗ[S] Derivation R S P := linearMapEquivDerivation R S
  let L' : (Ω[S⁄R] →ₗ[S] P ⊗[S] S') ≃ₗ[S] Derivation R S (P ⊗[S] S') :=
    linearMapEquivDerivation R S
  let e1 : Derivation R S P ⊗[S] S' ≃ₗ[S] S' ⊗[S] (Ω[S⁄R] →ₗ[S] P) :=
    (LinearEquiv.rTensor S' L.symm).trans (TensorProduct.comm S _ S')
  let e3 : S' ⊗[S] (Ω[S⁄R] →ₗ[S] P) ≃ₗ[S] (S' ⊗[S] Ω[S⁄R] →ₗ[S'] S' ⊗[S] P) :=
    (Module.FinitePresentation.isBaseChange_map S Ω[S⁄R] P S').equiv.restrictScalars S
  let e4 : (S' ⊗[S] Ω[S⁄R] →ₗ[S'] S' ⊗[S] P) ≃ₗ[S] (Ω[S⁄R] →ₗ[S] S' ⊗[S] P) :=
    (LinearMap.liftBaseChangeEquiv S').symm.restrictScalars S
  let e5 : (Ω[S⁄R] →ₗ[S] S' ⊗[S] P) ≃ₗ[S] (Ω[S⁄R] →ₗ[S] P ⊗[S] S') :=
    LinearEquiv.congrRight (TensorProduct.comm S S' P)
  let e : Derivation R S P ⊗[S] S' ≃ₗ[S] Derivation R S (P ⊗[S] S') :=
    e1.trans (e3.trans (e4.trans (e5.trans L')))
  have he : (e : Derivation R S P ⊗[S] S' →ₗ[S] _) = derivationBaseChange R S S' P := by
    refine TensorProduct.ext' fun D x ↦ Derivation.ext fun v ↦ ?_
    simp only [e, e1, e3, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.rTensor_tmul, TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply,
      IsBaseChange.equiv_tmul]
    change (TensorProduct.comm S S' P) ((x • (LinearMap.liftBaseChangeEquiv S').symm
      (LinearMap.baseChange S' (L.symm D))) (KaehlerDifferential.D R S v)) = D v ⊗ₜ x
    rw [LinearMap.smul_apply, LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.baseChange_tmul,
      show (L.symm D) (KaehlerDifferential.D R S v) = D v from
        Derivation.liftKaehlerDifferential_comp_D D v, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one, TensorProduct.comm_tmul]
  rw [← he]
  exact e.bijective

end BaseChange

section Restrict

variable (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S] (p : Submonoid S)
  (T : Type v) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [IsLocalization p T]
  (Y : Type w) [AddCommGroup Y] [Module T Y] [Module S Y] [Module R Y] [IsScalarTower S T Y]
  [IsScalarTower R T Y] [IsScalarTower R S Y]

include p in
omit [IsScalarTower R T Y] [IsScalarTower R S Y] in
/-- A derivation out of a localization `S → T` is determined by its restriction to `S`. -/
private theorem injective_compAlgebraMap_of_isLocalization :
    Function.Injective (fun d : Derivation R T Y ↦ d.compAlgebraMap S) := by
  intro d d' h
  refine Derivation.ext fun x ↦ ?_
  obtain ⟨⟨a, c⟩, hx⟩ := IsLocalization.surj p x
  have hd (s : S) : d (algebraMap S T s) = d' (algebraMap S T s) :=
    congrArg (fun D : Derivation R S Y ↦ D s) h
  have key : ∀ D : Derivation R T Y, algebraMap S T c • D x =
      D (algebraMap S T a) - x • D (algebraMap S T c) := by
    intro D
    rw [← hx, D.leibniz]
    abel
  have h1 : algebraMap S T c • d x = algebraMap S T c • d' x := by
    rw [key d, key d', hd a, hd c]
  exact ((Module.End.isUnit_iff _).mp ((IsLocalization.map_units T c).map
    (algebraMap T (Module.End T Y)))).1 (by simpa [Module.algebraMap_end_apply] using h1)

include p in
/-- Every derivation out of `S` extends to a derivation out of a localization `S → T`. -/
private theorem surjective_compAlgebraMap_of_isLocalization :
    Function.Surjective (fun d : Derivation R T Y ↦ d.compAlgebraMap S) := by
  intro δ
  have : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization p
  let φ : Ω[S⁄R] →ₗ[S] Y := (linearMapEquivDerivation R S).symm δ
  let ψ : Ω[T⁄R] →ₗ[T] Y := (LinearMap.liftBaseChange T φ) ∘ₗ
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap
  refine ⟨linearMapEquivDerivation R T ψ, Derivation.ext fun a ↦ ?_⟩
  change ψ (KaehlerDifferential.D R T (algebraMap S T a)) = δ a
  simp only [ψ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.liftBaseChange_tmul, one_smul]
  exact Derivation.liftKaehlerDifferential_comp_D δ a

include p in
/-- **Derivations of a localization are determined by, and extend uniquely from, their
restriction.** For a localization `S → T` and a `T`-module `Y`, restricting derivations along
`S → T` is a bijection `Derivation R T Y → Derivation R S Y`. -/
theorem bijective_compAlgebraMap_of_isLocalization :
    Function.Bijective (fun d : Derivation R T Y ↦ d.compAlgebraMap S) :=
  ⟨injective_compAlgebraMap_of_isLocalization R p T Y,
    surjective_compAlgebraMap_of_isLocalization R p T Y⟩

end Restrict

end Rig.SquareZeroLift

end
