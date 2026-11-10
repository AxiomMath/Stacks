module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.UniversalInjectivity
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealResidueFibre

/-!
# Universal injectivity from injectivity on residue-field fibres

In the finitely presented localized-module situation of Stacks 0AT6, a map `u` from the
distinguished module to a flat module, both flat over the base ring, is universally
injective as soon as `u ⊗ κ(𝔭)` is injective for every prime `𝔭` of the base ring — provided
the situation acquires a pure spreadout after passing to a finitely generated quotient of
each local ring of the base. That proviso is the conclusion of Stacks 0AT8, which is not yet
available in this library, so it is carried here as an explicit hypothesis.

## Main definitions

* `AlgebraicGeometry.LocalQuotientBaseChange` records the base change of the standing
  situation to a quotient of the local ring at a prime.
* `AlgebraicGeometry.localQuotient_map` and `AlgebraicGeometry.localQuotient_map_ulift` are
  the map induced by `u` on such a base change, the second with its target lifted to the
  universe in which Stacks 0AT7 tests universal injectivity.
* `AlgebraicGeometry.fiberBaseChangeEquiv` compares the fibre of a base-changed module with
  a fibre of the original one.

## Main results

* `AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective_of_pureSpreadout`
  is the residue-field criterion for universal injectivity, conditional on the pure-spreadout
  hypothesis.

The generic injectivity lemmas at the head of the file —
`AlgebraicGeometry.injective_lTensor_baseChange_iff`,
`AlgebraicGeometry.injective_rTensor_of_universallyInjective_baseChange` and
`AlgebraicGeometry.injective_lTensor_field_of_fibre` — together with the definitions above
are the shared infrastructure of this cluster, and are public so that the files downstream
of it use them rather than restate them.

## Implementation notes

The base-changed algebra and localization are characterized by pushout properties, and the
base-changed module by its tensor-product universal property, so that arbitrary
representatives of these canonical base changes are admissible rather than fixed
tensor-product models. The isomorphism of base rings identifies the new base with the
specified local quotient.

The map denoted `u ⊗ id_{κ(𝔭)}` in the source is `u.rTensor p.ResidueField`. The annihilator
argument is applied directly to the kernel after tensoring with an arbitrary module;
flatness identifies tensors annihilated by a finitely generated ideal with tensors coming
from the corresponding annihilator submodule.

## References

* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- A representative of the base change of the standing situation of Stacks 0AT6 to a
quotient of the local ring at a prime. -/
structure LocalQuotientBaseChange
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p)) where
  /-- The algebra structure of the new base ring over the old one. -/
  [algebraBase : Algebra X.A Y.A]
  /-- The identification of the new base ring with the prescribed local quotient. -/
  baseEquiv : Y.A ≃+* (Localization.AtPrime p ⧸ I)
  /-- The identification is compatible with the maps from the old base ring. -/
  baseEquiv_algebraMap : ∀ a : X.A,
    baseEquiv (algebraMap X.A Y.A a) =
      Ideal.Quotient.mk I (algebraMap X.A (Localization.AtPrime p) a)
  /-- The algebra structure of the new algebra over the old one. -/
  [algebraB : Algebra X.B Y.B]
  /-- The algebra structure of the new algebra over the old base ring. -/
  [algebraAB' : Algebra X.A Y.B]
  /-- The maps into the new algebra through the old algebra form a tower. -/
  [towerAB : IsScalarTower X.A X.B Y.B]
  /-- The maps into the new algebra through the new base ring form a tower. -/
  [towerBaseB : IsScalarTower X.A Y.A Y.B]
  /-- The new algebra is the base change of the old one. -/
  algebraPushout : Algebra.IsPushout X.A Y.A X.B Y.B
  /-- The algebra structure of the new localization over the old one. -/
  [algebraLocalized : Algebra X.Bₛ Y.Bₛ]
  /-- The algebra structure of the new localization over the old base ring. -/
  [algebraALocalized : Algebra X.A Y.Bₛ]
  /-- The maps into the new localization through the old localization form a tower. -/
  [towerALocalized : IsScalarTower X.A X.Bₛ Y.Bₛ]
  /-- The maps into the new localization through the new base ring form a tower. -/
  [towerBaseLocalized : IsScalarTower X.A Y.A Y.Bₛ]
  /-- The new localization is the base change of the old one. -/
  localizedPushout : Algebra.IsPushout X.A Y.A X.Bₛ Y.Bₛ
  /-- The algebra structure of the new localization over the old algebra. -/
  [algebraBLocalized : Algebra X.B Y.Bₛ]
  /-- The maps into the new localization through the old localization form a tower over the
  old algebra. -/
  [towerBLocalized : IsScalarTower X.B X.Bₛ Y.Bₛ]
  /-- The maps into the new localization through the new algebra form a tower. -/
  [towerBBaseLocalized : IsScalarTower X.B Y.B Y.Bₛ]
  /-- Localizing and base changing the old algebra agree. -/
  localization_commutes : ∀ b : X.B,
    algebraMap Y.B Y.Bₛ (algebraMap X.B Y.B b) =
      algebraMap X.Bₛ Y.Bₛ (algebraMap X.B X.Bₛ b)
  /-- The new multiplicative subset is the image of the old one. -/
  submonoid_eq_map : Y.S = X.S.map (algebraMap X.B Y.B)
  /-- The old localization acts on the new module. -/
  [moduleLocalized : Module X.Bₛ Y.N]
  /-- The actions of the two localizations on the new module form a tower. -/
  [towerLocalizedModule : IsScalarTower X.Bₛ Y.Bₛ Y.N]
  /-- The map from the old module to the new one. -/
  moduleMap : X.N →ₗ[X.Bₛ] Y.N
  /-- The map of modules is compatible with the map of algebras. -/
  moduleMap_algebra : ∀ (b : X.B) (n : X.N),
    moduleMap (b • n) = (algebraMap X.B Y.B b) • moduleMap n
  /-- The new module is the base change of the old one. -/
  moduleBaseChange : IsBaseChange Y.Bₛ moduleMap


open TensorProduct

/-- Injectivity after tensoring with a base change `S ⊗[R] N → S ⊗[R] M` of `f`, tested against
an `S`-module `Q`, is injectivity of `f ⊗ id_Q`. -/
theorem injective_lTensor_baseChange_iff
    {R S N M Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    (f : N →ₗ[R] M) :
    Function.Injective ((f.baseChange S).lTensor Q) ↔ Function.Injective (f.lTensor Q) := by
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S Q N
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S Q M
  have hcomm : ((f.baseChange S).lTensor Q).restrictScalars R ∘ₗ
      eN.symm.toLinearMap.restrictScalars R =
      eM.symm.toLinearMap.restrictScalars R ∘ₗ f.lTensor Q := by
    ext q n
    simp [eN, eM]
  constructor
  · intro h x y hxy
    apply eN.symm.injective
    apply h
    exact (LinearMap.congr_fun hcomm x).trans
      ((congrArg eM.symm hxy).trans (LinearMap.congr_fun hcomm y).symm)
  · intro h x y hxy
    obtain ⟨x, rfl⟩ := eN.symm.surjective x
    obtain ⟨y, rfl⟩ := eN.symm.surjective y
    congr 1
    apply h
    apply eM.symm.injective
    exact (LinearMap.congr_fun hcomm x).symm.trans
      (hxy.trans (LinearMap.congr_fun hcomm y))

/-- A base change of a map which is injective on every residue-field fibre stays injective on
every fibre of the new base. -/
theorem injective_rTensor_of_universallyInjective_baseChange
    {R : Type u₁} [CommRing R] {N : Type u₂} {M : Type u₃}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (f : N →ₗ[R] M) (S : Type*) [CommRing S] [Algebra R S]
    (hf : UniversallyInjectivePoly.{_, u₄} (f.baseChange S))
    (Q : Type u₄) [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q] :
    Function.Injective (f.rTensor Q) :=
  (LinearMap.lTensor_inj_iff_rTensor_inj Q f).mp
    ((injective_lTensor_baseChange_iff f).mp
      ((LinearMap.lTensor_inj_iff_rTensor_inj Q _).mpr (hf Q)))

/-- Injectivity on the residue-field fibre at the contraction of a field extension of the base
gives injectivity after tensoring with that field. -/
theorem injective_lTensor_field_of_fibre
    {R N M : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (f : N →ₗ[R] M) (K : Type*) [Field K] [Algebra R K]
    (p : Ideal R) [p.IsPrime] (hp : p = RingHom.ker (algebraMap R K))
    (hf : Function.Injective (f.rTensor p.ResidueField)) :
    Function.Injective (f.lTensor K) := by
  have hunits : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) :=
    fun r hr => isUnit_iff_ne_zero.mpr fun h => hr (hp ▸ RingHom.mem_ker.mpr h)
  let g := Ideal.ResidueField.lift p (algebraMap R K) hp.le hunits
  let : Algebra p.ResidueField K := g.toAlgebra
  let : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p (algebraMap R K) hp.le hunits r).symm)
  exact (injective_lTensor_baseChange_iff (S := p.ResidueField) (Q := K) f).mp
    (Module.Flat.lTensor_preserves_injective_linearMap (f.baseChange p.ResidueField)
      ((LinearMap.lTensor_inj_iff_rTensor_inj p.ResidueField f).mpr hf))

/-- Comparison of the fibre of a base-changed module with a fibre of the original one. -/
noncomputable def fiberBaseChangeLinearEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P : Type*} [AddCommGroup P] [Module R P]
    {K L : Type*} [CommRing K] [CommRing L] [Algebra S K] [Algebra S L]
    [Module R K] [Module R L]
    [IsScalarTower R S K] [IsScalarTower R S L]
    (e : K ≃ₐ[S] L) : ((S ⊗[R] P) ⊗[S] K) ≃ₗ[R] P ⊗[R] L :=
  (TensorProduct.comm S (S ⊗[R] P) K).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R S S K P).restrictScalars R ≪≫ₗ
    TensorProduct.comm R K P ≪≫ₗ
    LinearEquiv.lTensor P (e.toLinearEquiv.restrictScalars R)

private theorem injective_rTensor_congr
    {R : Type*} [CommSemiring R]
    {M N Q Q' : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid Q] [Module R Q]
    [AddCommMonoid Q'] [Module R Q']
    (f : M →ₗ[R] N) (e : Q ≃ₗ[R] Q') :
    Function.Injective (f.rTensor Q) ↔ Function.Injective (f.rTensor Q') := by
  have hcomm : f.rTensor Q' ∘ₗ LinearMap.lTensor M e.toLinearMap =
      LinearMap.lTensor N e.toLinearMap ∘ₗ f.rTensor Q := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [← (LinearEquiv.lTensor N e).injective.of_comp_iff (f.rTensor Q),
    ← LinearEquiv.coe_coe, LinearEquiv.coe_lTensor, ← LinearMap.coe_comp,
    ← hcomm, LinearMap.coe_comp, ← LinearEquiv.coe_lTensor, LinearEquiv.coe_coe,
    Function.Injective.of_comp_iff' _ (LinearEquiv.lTensor M e).bijective]

/-- The comparison of fibres is natural in the module. -/
theorem fiberBaseChangeLinearEquiv_natural
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {K L : Type*} [CommRing K] [CommRing L] [Algebra S K] [Algebra S L]
    [Module R K] [Module R L]
    [IsScalarTower R S K] [IsScalarTower R S L]
    (e : K ≃ₐ[S] L) (f : P →ₗ[R] Q) :
    (fiberBaseChangeLinearEquiv (P := Q) e).toLinearMap ∘ₗ (f.baseChange S).rTensor K =
      f.rTensor L ∘ₗ (fiberBaseChangeLinearEquiv (P := P) e).toLinearMap := by
  ext z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
    simpa only [LinearMap.map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul w k =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ hw₁ hw₂ =>
      simpa only [TensorProduct.add_tmul, LinearMap.map_add] using
        congrArg₂ (· + ·) hw₁ hw₂
    | tmul s p =>
      simp [fiberBaseChangeLinearEquiv, LinearMap.baseChange_tmul,
        AlgebraTensorModule.cancelBaseChange_tmul]

private noncomputable def cancelBaseChange_rTensorEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Module S Q]
    [IsScalarTower R S Q] :
    ((S ⊗[R] P) ⊗[S] Q) ≃ₗ[R] P ⊗[R] Q :=
  (TensorProduct.comm S (S ⊗[R] P) Q).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R S S Q P).restrictScalars R ≪≫ₗ
    TensorProduct.comm R Q P

private theorem cancelBaseChange_rTensorEquiv_natural
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P P' Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P'] [AddCommGroup Q] [Module R Q]
    [Module S Q] [IsScalarTower R S Q]
    (f : P →ₗ[R] P') :
    (cancelBaseChange_rTensorEquiv (R := R) (S := S) (P := P') (Q := Q)).toLinearMap ∘ₗ
        (f.baseChange S).rTensor Q =
      f.rTensor Q ∘ₗ
        (cancelBaseChange_rTensorEquiv (R := R) (S := S) (P := P) (Q := Q)).toLinearMap := by
  ext z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
    simpa only [LinearMap.map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul w q =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ hw₁ hw₂ =>
      simpa only [TensorProduct.add_tmul, LinearMap.map_add] using
        congrArg₂ (· + ·) hw₁ hw₂
    | tmul s p =>
      simp [cancelBaseChange_rTensorEquiv, LinearMap.baseChange_tmul,
        AlgebraTensorModule.cancelBaseChange_tmul]

private theorem rTensor_injective_of_shortExact
    {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Flat R M']
    (f : M →ₗ[R] M') {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {g₁ : A →ₗ[R] B} {g₂ : B →ₗ[R] C}
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (hg₂ : Function.Surjective g₂)
    (hA : Function.Injective (f.rTensor A))
    (hC : Function.Injective (f.rTensor C)) :
    Function.Injective (f.rTensor B) := by
  have hsq₁ : (f.rTensor B) ∘ₗ LinearMap.lTensor M g₁ =
      LinearMap.lTensor M' g₁ ∘ₗ (f.rTensor A) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hsq₂ : (f.rTensor C) ∘ₗ LinearMap.lTensor M g₂ =
      LinearMap.lTensor M' g₂ ∘ₗ (f.rTensor B) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  exact Stacks.UniversalInjectivity.FGIdealTest.injective_middle_of_exact hsq₁ hsq₂
    (_root_.lTensor_exact M hg hg₂)
    (Module.Flat.lTensor_preserves_injective_linearMap g₁ hg₁) hA hC

private theorem rTensor_injective_of_ideal_power_annihilated
    {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Flat R M']
    (f : M →ₗ[R] M') (I : Ideal R)
    (hkill : ∀ (P : Type u₅) [AddCommGroup P] [Module R P],
      (∀ (a : R), a ∈ I → ∀ x : P, a • x = 0) → Function.Injective (f.rTensor P))
    {Q : Type u₅} [AddCommGroup Q] [Module R Q] (n : ℕ)
    (hn : ∀ (a : R), a ∈ I ^ n → ∀ x : Q, a • x = 0) :
    Function.Injective (f.rTensor Q) := by
  induction n generalizing Q with
  | zero =>
    have hzero : ∀ x : Q, x = 0 := fun x => by simpa using hn 1 (by simp) x
    have : Subsingleton Q := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    exact fun x y _ => Subsingleton.elim x y
  | succ n ih =>
    let K : Submodule R Q := I • ⊤
    have hkillK : ∀ (a : R), a ∈ I ^ n → ∀ x : K, a • x = 0 := by
      intro a ha x
      apply Subtype.ext
      change a • (x : Q) = 0
      refine Submodule.smul_induction_on x.2 ?_ ?_
      · intro b hb y hy
        change a • (b • y) = 0
        rw [← mul_smul]
        apply hn (a * b) ?_ y
        rw [pow_succ]
        exact Ideal.mul_mem_mul ha hb
      · intro x y hx hy
        rw [smul_add, hx, hy, add_zero]
    let Qquot := Q ⧸ K
    have hkillQuot : ∀ (a : R), a ∈ I → ∀ x : Qquot, a • x = 0 := by
      intro a ha x
      obtain ⟨y, rfl⟩ := K.mkQ_surjective x
      change K.mkQ (a • y) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul ha (Submodule.mem_top)
    exact rTensor_injective_of_shortExact f
      (g₁ := K.subtype)
      (g₂ := K.mkQ)
      (LinearMap.exact_subtype_mkQ K)
      K.injective_subtype (Submodule.mkQ_surjective _)
      (ih hkillK) (hkill Qquot hkillQuot)

/-- The module in a local quotient base change is also the base change of the original
module along the induced map on the base rings: the localized pushout identifies
base change over the localized algebra with base change over the base ring. -/
theorem isBaseChange_localQuotient_moduleMap
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    letI : Algebra X.Bₛ Y.Bₛ := hbc.algebraLocalized
    letI : Algebra X.A Y.Bₛ := hbc.algebraALocalized
    letI : IsScalarTower X.A Y.A Y.Bₛ := hbc.towerBaseLocalized
    letI : IsScalarTower X.A X.Bₛ Y.Bₛ := hbc.towerALocalized
    letI : Module X.Bₛ Y.N := hbc.moduleLocalized
    letI : IsScalarTower X.Bₛ Y.Bₛ Y.N := hbc.towerLocalizedModule
    letI : Module Y.Bₛ Y.N := Y.moduleBₛN
    letI : Module Y.A Y.N := Y.moduleBase
    letI : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
    letI : IsScalarTower X.A Y.A Y.N :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower X.A Y.Bₛ Y.N :=
      IsScalarTower.of_algebraMap_smul fun a n => by
        change (algebraMap X.A Y.Bₛ a) • n = (algebraMap X.A Y.A a) • n
        rw [IsScalarTower.algebraMap_apply X.A Y.A Y.Bₛ]
        exact IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A Y.A a) n
    letI : IsScalarTower X.A X.Bₛ Y.N :=
      IsScalarTower.of_algebraMap_smul fun a n => by
        rw [← IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A X.Bₛ a) n,
          ← IsScalarTower.algebraMap_smul Y.Bₛ a n,
          ← IsScalarTower.algebraMap_apply X.A X.Bₛ Y.Bₛ]
    IsBaseChange Y.A (hbc.moduleMap.restrictScalars X.A) := by
  let : CommRing Y.A := Y.commRingA
  let : Algebra X.A Y.A := hbc.algebraBase
  let : CommRing Y.Bₛ := Y.commRingBₛ
  let : Algebra X.Bₛ Y.Bₛ := hbc.algebraLocalized
  let : Algebra X.A Y.Bₛ := hbc.algebraALocalized
  let : IsScalarTower X.A Y.A Y.Bₛ := hbc.towerBaseLocalized
  let : IsScalarTower X.A X.Bₛ Y.Bₛ := hbc.towerALocalized
  let : Module X.Bₛ Y.N := hbc.moduleLocalized
  let : Module Y.Bₛ Y.N := Y.moduleBₛN
  let : IsScalarTower X.Bₛ Y.Bₛ Y.N := hbc.towerLocalizedModule
  let : IsScalarTower X.A X.Bₛ X.N := X.isScalarTower_moduleBase
  let : Module Y.A Y.N := Y.moduleBase
  let : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  let : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower X.A Y.Bₛ Y.N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      change (algebraMap X.A Y.Bₛ a) • n = (algebraMap X.A Y.A a) • n
      rw [IsScalarTower.algebraMap_apply X.A Y.A Y.Bₛ]
      exact IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A Y.A a) n
  let : IsScalarTower X.A X.Bₛ Y.N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      rw [← IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A X.Bₛ a) n,
        ← IsScalarTower.algebraMap_smul Y.Bₛ a n,
        ← IsScalarTower.algebraMap_apply X.A X.Bₛ Y.Bₛ]
  let : Algebra.IsPushout X.A Y.A X.Bₛ Y.Bₛ := hbc.localizedPushout
  let e₁ : Y.Bₛ ⊗[X.Bₛ] X.N ≃ₗ[Y.A] Y.A ⊗[X.A] X.N :=
    Algebra.IsPushout.cancelBaseChange X.A Y.A X.Bₛ Y.Bₛ X.N
  let e₂ : Y.Bₛ ⊗[X.Bₛ] X.N ≃ₗ[Y.Bₛ] Y.N := hbc.moduleBaseChange.equiv
  let e : Y.A ⊗[X.A] X.N ≃ₗ[Y.A] Y.N :=
    e₁.symm.trans (e₂.restrictScalars Y.A)
  apply IsBaseChange.of_equiv e
  intro n
  change e₂ (e₁.symm (1 ⊗ₜ[X.A] n)) = hbc.moduleMap n
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  calc
    e₂ ((algebraMap Y.A Y.Bₛ 1) ⊗ₜ[X.Bₛ] n) =
        (algebraMap Y.A Y.Bₛ 1) • hbc.moduleMap n :=
      hbc.moduleBaseChange.equiv_tmul (algebraMap Y.A Y.Bₛ 1) n
    _ = hbc.moduleMap n := by rw [map_one, one_smul]

/-- The module in a local quotient base change is also the base change of the original
module along the induced map on the base rings: the localized pushout identifies
base change over the localized algebra with base change over the base ring. -/
private theorem localQuotient_moduleMap_isBaseChange
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    letI : Algebra X.Bₛ Y.Bₛ := hbc.algebraLocalized
    letI : Algebra X.A Y.Bₛ := hbc.algebraALocalized
    letI : IsScalarTower X.A Y.A Y.Bₛ := hbc.towerBaseLocalized
    letI : IsScalarTower X.A X.Bₛ Y.Bₛ := hbc.towerALocalized
    letI : Module X.Bₛ Y.N := hbc.moduleLocalized
    letI : IsScalarTower X.Bₛ Y.Bₛ Y.N := hbc.towerLocalizedModule
    letI : Module Y.Bₛ Y.N := Y.moduleBₛN
    letI : Module Y.A Y.N := Y.moduleBase
    letI : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
    letI : IsScalarTower X.A Y.A Y.N :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower X.A Y.Bₛ Y.N :=
      IsScalarTower.of_algebraMap_smul fun a n => by
        change (algebraMap X.A Y.Bₛ a) • n = (algebraMap X.A Y.A a) • n
        rw [IsScalarTower.algebraMap_apply X.A Y.A Y.Bₛ]
        exact IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A Y.A a) n
    letI : IsScalarTower X.A X.Bₛ Y.N :=
      IsScalarTower.of_algebraMap_smul fun a n => by
        rw [← IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A X.Bₛ a) n,
          ← IsScalarTower.algebraMap_smul Y.Bₛ a n,
          ← IsScalarTower.algebraMap_apply X.A X.Bₛ Y.Bₛ]
    IsBaseChange Y.A (hbc.moduleMap.restrictScalars X.A) := by
  let : CommRing Y.A := Y.commRingA
  let : Algebra X.A Y.A := hbc.algebraBase
  let : CommRing Y.Bₛ := Y.commRingBₛ
  let : Algebra X.Bₛ Y.Bₛ := hbc.algebraLocalized
  let : Algebra X.A Y.Bₛ := hbc.algebraALocalized
  let : IsScalarTower X.A Y.A Y.Bₛ := hbc.towerBaseLocalized
  let : IsScalarTower X.A X.Bₛ Y.Bₛ := hbc.towerALocalized
  let : Module X.Bₛ Y.N := hbc.moduleLocalized
  let : Module Y.Bₛ Y.N := Y.moduleBₛN
  let : IsScalarTower X.Bₛ Y.Bₛ Y.N := hbc.towerLocalizedModule
  let : IsScalarTower X.A X.Bₛ X.N := X.isScalarTower_moduleBase
  let : Module Y.A Y.N := Y.moduleBase
  let : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  let : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower X.A Y.Bₛ Y.N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      change (algebraMap X.A Y.Bₛ a) • n = (algebraMap X.A Y.A a) • n
      rw [IsScalarTower.algebraMap_apply X.A Y.A Y.Bₛ]
      exact IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A Y.A a) n
  let : IsScalarTower X.A X.Bₛ Y.N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      rw [← IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.A X.Bₛ a) n,
        ← IsScalarTower.algebraMap_smul Y.Bₛ a n,
        ← IsScalarTower.algebraMap_apply X.A X.Bₛ Y.Bₛ]
  let : Algebra.IsPushout X.A Y.A X.Bₛ Y.Bₛ := hbc.localizedPushout
  let e₁ : Y.Bₛ ⊗[X.Bₛ] X.N ≃ₗ[Y.A] Y.A ⊗[X.A] X.N :=
    Algebra.IsPushout.cancelBaseChange X.A Y.A X.Bₛ Y.Bₛ X.N
  let e₂ : Y.Bₛ ⊗[X.Bₛ] X.N ≃ₗ[Y.Bₛ] Y.N := hbc.moduleBaseChange.equiv
  let e : Y.A ⊗[X.A] X.N ≃ₗ[Y.A] Y.N :=
    e₁.symm.trans (e₂.restrictScalars Y.A)
  apply IsBaseChange.of_equiv e
  intro n
  change e₂ (e₁.symm (1 ⊗ₜ[X.A] n)) = hbc.moduleMap n
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  calc
    e₂ ((algebraMap Y.A Y.Bₛ 1) ⊗ₜ[X.Bₛ] n) =
        (algebraMap Y.A Y.Bₛ 1) • hbc.moduleMap n :=
      hbc.moduleBaseChange.equiv_tmul (algebraMap Y.A Y.Bₛ 1) n
    _ = hbc.moduleMap n := by rw [map_one, one_smul]

/-- The map induced by `u` on the local quotient model. -/
noncomputable def localQuotientMap
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    Y.N →ₗ[Y.A] (Y.A ⊗[X.A] M) := by
  letI : CommRing Y.A := Y.commRingA
  letI : Algebra X.A Y.A := hbc.algebraBase
  letI : Module X.A Y.A := hbc.algebraBase.toModule
  letI : Module Y.A Y.N := Y.moduleBase
  letI : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  letI : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let hN := isBaseChange_localQuotient_moduleMap X p I Y hbc
  exact (u.baseChange Y.A).comp hN.equiv.symm.toLinearMap

/-- The map induced by `u` on the local quotient model. -/
private noncomputable def localQuotient_map
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    Y.N →ₗ[Y.A] (Y.A ⊗[X.A] M) := by
  letI : CommRing Y.A := Y.commRingA
  letI : Algebra X.A Y.A := hbc.algebraBase
  letI : Module X.A Y.A := hbc.algebraBase.toModule
  letI : Module Y.A Y.N := Y.moduleBase
  letI : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  letI : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let hN := localQuotient_moduleMap_isBaseChange X p I Y hbc
  exact (u.baseChange Y.A).comp hN.equiv.symm.toLinearMap

/-- The induced map on a local quotient base change, with target lifted to the universe in
which Stacks 0AT7 tests universal injectivity. -/
noncomputable def localQuotientMapULift
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    letI : Module X.A Y.A := hbc.algebraBase.toModule
    Y.N →ₗ[Y.A] ULift.{max (max u₁ u₃) u₄, max u₁ u₄}
      (Y.A ⊗[X.A] M) := by
  letI : Algebra X.A Y.A := hbc.algebraBase
  letI : Module X.A Y.A := hbc.algebraBase.toModule
  let e : ULift.{max (max u₁ u₃) u₄, max u₁ u₄}
      (Y.A ⊗[X.A] M) ≃ₗ[Y.A] (Y.A ⊗[X.A] M) := ULift.moduleEquiv
  exact e.symm.toLinearMap.comp (localQuotientMap X p I Y hbc u)

private theorem localQuotientMapULift_residueField_injective
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : ∀ (q : Ideal X.A) [q.IsPrime], Function.Injective (u.rTensor q.ResidueField)) :
    Function.Injective ((localQuotientMapULift X p I Y hbc u).rTensor
      (Y.A ⧸ IsLocalRing.maximalIdeal Y.A)) := by
  let : CommRing Y.A := Y.commRingA
  let : Algebra X.A Y.A := hbc.algebraBase
  let : Module X.A Y.A := hbc.algebraBase.toModule
  let : Module Y.A Y.N := Y.moduleBase
  let : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  let : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let K := Y.A ⧸ IsLocalRing.maximalIdeal Y.A
  have hmax : p.map (algebraMap X.A (Localization.AtPrime p)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)
  have hIker : I ≤ RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rwa [show RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) from IsLocalRing.ker_residue, ← hmax]
  have hIker' : ∀ a : Localization.AtPrime p, a ∈ I →
      algebraMap (Localization.AtPrime p) p.ResidueField a = 0 := fun a ha =>
    RingHom.mem_ker.mp (hIker ha)
  let g₀ : Localization.AtPrime p ⧸ I →+* p.ResidueField :=
    Ideal.Quotient.lift I (algebraMap (Localization.AtPrime p) p.ResidueField) hIker'
  have hg₀ : Function.Surjective g₀ :=
    Ideal.Quotient.lift_surjective_of_surjective (I := I) hIker'
      (f := algebraMap (Localization.AtPrime p) p.ResidueField)
      (IsLocalRing.residue_surjective (R := Localization.AtPrime p))
  let g : Y.A →+* p.ResidueField := g₀.comp hbc.baseEquiv.toRingHom
  have hg : Function.Surjective g := hg₀.comp hbc.baseEquiv.surjective
  let : Algebra Y.A p.ResidueField := g.toAlgebra
  have hker : RingHom.ker (Algebra.ofId Y.A p.ResidueField) = IsLocalRing.maximalIdeal Y.A :=
    IsLocalRing.ker_eq_maximalIdeal _ hg
  have hAlg : (algebraMap Y.A p.ResidueField).comp (algebraMap X.A Y.A) =
      algebraMap X.A p.ResidueField := by
    ext a
    change g₀ (hbc.baseEquiv (algebraMap X.A Y.A a)) = _
    rw [hbc.baseEquiv_algebraMap]
    exact Ideal.Quotient.lift_mk _ _ _
  let : IsScalarTower X.A Y.A p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' hAlg.symm
  let eAlg : K ≃ₐ[Y.A] p.ResidueField :=
    (Ideal.quotientEquivAlgOfEq Y.A hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId Y.A p.ResidueField) hg)
  let eN := isBaseChange_localQuotient_moduleMap X p I Y hbc
  have hmap : (localQuotientMap X p I Y hbc u).comp eN.equiv.toLinearMap =
      u.baseChange Y.A := by
    change ((u.baseChange Y.A).comp eN.equiv.symm.toLinearMap).comp
      eN.equiv.toLinearMap = u.baseChange Y.A
    rw [LinearMap.comp_assoc]
    simp
  have hbase : Function.Injective ((u.baseChange Y.A).rTensor K) := by
    intro x y hxy
    have htransport := congrArg (fiberBaseChangeLinearEquiv (P := M) eAlg) hxy
    have htransport' : u.rTensor p.ResidueField
        ((fiberBaseChangeLinearEquiv (P := X.N) eAlg) x) =
        u.rTensor p.ResidueField ((fiberBaseChangeLinearEquiv (P := X.N) eAlg) y) := by
      have hx := LinearMap.congr_fun (fiberBaseChangeLinearEquiv_natural eAlg u) x
      have hy := LinearMap.congr_fun (fiberBaseChangeLinearEquiv_natural eAlg u) y
      rw [LinearMap.comp_apply] at hx hy
      exact hx.symm.trans (htransport.trans hy)
    exact (fiberBaseChangeLinearEquiv (P := X.N) eAlg).injective (hu p htransport')
  have hcompTensor : (u.baseChange Y.A).rTensor K =
      (localQuotientMap X p I Y hbc u).rTensor K ∘ₗ (eN.equiv.toLinearMap.rTensor K) := by
    rw [← LinearMap.rTensor_comp, hmap]
  have hlocal : Function.Injective ((localQuotientMap X p I Y hbc u).rTensor K) := by
    refine (Function.Injective.of_comp_iff' _ (eN.equiv.rTensor K).bijective).mp ?_
    rw [hcompTensor] at hbase
    exact hbase
  let eULift : ULift.{max (max u₁ u₃) u₄} (Y.A ⊗[X.A] M) ≃ₗ[Y.A]
      Y.A ⊗[X.A] M := ULift.moduleEquiv
  have hULiftComp : (localQuotientMapULift X p I Y hbc u).rTensor K =
      eULift.symm.toLinearMap.rTensor K ∘ₗ
        (localQuotientMap X p I Y hbc u).rTensor K := by
    rw [← LinearMap.rTensor_comp]
    rfl
  rw [hULiftComp]
  exact (eULift.symm.rTensor K).injective.comp hlocal


private theorem localQuotient_map_universallyInjective_of_maximal_fiber
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y)) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    letI : Module X.A Y.A := hbc.algebraBase.toModule
    Function.Injective ((IsLocalRing.maximalIdeal Y.A •
      (⊤ : Submodule Y.A Y.N)).mapQ
        (IsLocalRing.maximalIdeal Y.A •
          (⊤ : Submodule Y.A
            (ULift.{max (max u₁ u₃) u₄, max u₁ u₄} (Y.A ⊗[X.A] M))))
        (localQuotientMapULift X p I Y hbc u)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal Y.A)
          (localQuotientMapULift X p I Y hbc u))) →
    UniversallyInjective (localQuotientMapULift X p I Y hbc u) := by
  let : Algebra X.A Y.A := hbc.algebraBase
  let : Module X.A Y.A := hbc.algebraBase.toModule
  let e : ULift.{max (max u₁ u₃) u₄, max u₁ u₄}
      (Y.A ⊗[X.A] M) ≃ₗ[Y.A] (Y.A ⊗[X.A] M) := ULift.moduleEquiv
  let : Module.Flat Y.A
      (ULift.{max (max u₁ u₃) u₄, max u₁ u₄} (Y.A ⊗[X.A] M)) :=
    Module.Flat.of_linearEquiv e
  exact fun hfiber => universallyInjective_of_injective_mod_maximalIdeal
    Y hspread (localQuotientMapULift X p I Y hbc u) fun m hm => by
      rwa [IsLocalRing.eq_maximalIdeal hm]

private theorem localQuotient_rTensor_injective
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : ∀ (q : Ideal X.A) [q.IsPrime],
      Function.Injective (u.rTensor q.ResidueField))
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y))
    {Q : Type (max (max u₁ u₃) u₄)} [AddCommGroup Q]
    [Module Y.A Q] :
    letI : CommRing Y.A := Y.commRingA
    letI : Algebra X.A Y.A := hbc.algebraBase
    letI : Module X.A Y.A := hbc.algebraBase.toModule
    letI : Module X.A Q := Module.compHom Q (algebraMap X.A Y.A)
    letI : IsScalarTower X.A Y.A Q :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Injective (u.rTensor Q) := by
  let : CommRing Y.A := Y.commRingA
  let : Algebra X.A Y.A := hbc.algebraBase
  let : Module X.A Y.A := hbc.algebraBase.toModule
  let : Module X.A Q := Module.compHom Q (algebraMap X.A Y.A)
  let : IsScalarTower X.A Y.A Q :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfiberQ : Function.Injective ((IsLocalRing.maximalIdeal Y.A •
      (⊤ : Submodule Y.A Y.N)).mapQ
        (IsLocalRing.maximalIdeal Y.A •
          (⊤ : Submodule Y.A
            (ULift.{max (max u₁ u₃) u₄} (Y.A ⊗[X.A] M))))
        (localQuotientMapULift X p I Y hbc u)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal Y.A)
          (localQuotientMapULift X p I Y hbc u))) :=
    (mapQ_injective_iff_rTensor_quotient
      (localQuotientMapULift X p I Y hbc u)
      (IsLocalRing.maximalIdeal Y.A)).mpr
      (localQuotientMapULift_residueField_injective X p I Y hbc hI u hu)
  have hlocalLiftQ : Function.Injective ((localQuotientMapULift X p I Y hbc u).rTensor Q) :=
    localQuotient_map_universallyInjective_of_maximal_fiber X p I Y hbc u hspread hfiberQ Q
  let eULift : ULift.{max (max u₁ u₃) u₄} (Y.A ⊗[X.A] M) ≃ₗ[Y.A]
      (Y.A ⊗[X.A] M) := ULift.moduleEquiv
  have hULiftComp : (localQuotientMapULift X p I Y hbc u).rTensor Q =
      eULift.symm.toLinearMap.rTensor Q ∘ₗ (localQuotientMap X p I Y hbc u).rTensor Q := by
    rw [← LinearMap.rTensor_comp]
    rfl
  have hlocal : Function.Injective ((localQuotientMap X p I Y hbc u).rTensor Q) :=
    fun x y hxy => hlocalLiftQ (by
      rw [hULiftComp]
      exact congrArg (eULift.symm.toLinearMap.rTensor Q) hxy)
  let eN := isBaseChange_localQuotient_moduleMap X p I Y hbc
  let : Module Y.A Y.N := Y.moduleBase
  let : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  let : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcomp : (localQuotientMap X p I Y hbc u).rTensor Q ∘ₗ
      (eN.equiv.toLinearMap.rTensor Q) = (u.baseChange Y.A).rTensor Q := by
    rw [← LinearMap.rTensor_comp]
    change (((u.baseChange Y.A).comp eN.equiv.symm.toLinearMap).comp
      eN.equiv.toLinearMap).rTensor Q = _
    simp [LinearMap.comp_assoc]
  have hbase : Function.Injective ((u.baseChange Y.A).rTensor Q) := by
    rw [← hcomp]
    exact hlocal.comp (eN.equiv.rTensor Q).injective
  exact (LinearMap.lTensor_inj_iff_rTensor_inj Q u).mp
    ((injective_lTensor_baseChange_iff u).mp
      ((LinearMap.lTensor_inj_iff_rTensor_inj Q _).mpr hbase))

private lemma injective_iff_injective_of_comm
    {α β γ δ : Type*} {a : α → γ} {b : β → δ} {f : α → β} {g : γ → δ}
    (ha : Function.Bijective a) (hb : Function.Injective b)
    (h : ∀ x, b (f x) = g (a x)) : Function.Injective f ↔ Function.Injective g := by
  constructor
  · intro hf x y hxy
    obtain ⟨x, rfl⟩ := ha.surjective x
    obtain ⟨y, rfl⟩ := ha.surjective y
    exact congrArg a (hf (hb (by simpa only [h] using hxy)))
  · intro hg x y hxy
    apply ha.injective
    exact hg (by simpa only [← h] using congrArg b hxy)

private lemma rTensor_injective_extendScalarsOfIsLocalization
    {A : Type*} [CommRing A]
    (S : Submonoid A) (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ]
    [IsLocalization S Aₛ] {N N' Qₛ : Type*}
    [AddCommGroup N] [Module A N] [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module Aₛ N'] [IsScalarTower A Aₛ N']
    [AddCommGroup Qₛ] [Module A Qₛ]
    [Module Aₛ Qₛ] [IsScalarTower A Aₛ Qₛ]
    (fₛ : N →ₗ[A] N') (hf : Function.Injective (fₛ.rTensor Qₛ)) :
      Function.Injective ((LinearMap.extendScalarsOfIsLocalization S Aₛ fₛ).rTensor Qₛ) := by
  have sq₂ : (IsLocalization.moduleTensorEquiv S Aₛ N' Qₛ).toLinearMap ∘ₗ
      (LinearMap.extendScalarsOfIsLocalization S Aₛ fₛ).rTensor Qₛ =
      LinearMap.extendScalarsOfIsLocalization S Aₛ (fₛ.rTensor Qₛ) ∘ₗ
        (IsLocalization.moduleTensorEquiv S Aₛ N Qₛ).toLinearMap :=
    TensorProduct.ext' fun _ _ => rfl
  exact (injective_iff_injective_of_comm
    (IsLocalization.moduleTensorEquiv S Aₛ N Qₛ).bijective
    (IsLocalization.moduleTensorEquiv S Aₛ N' Qₛ).injective (LinearMap.congr_fun sq₂)).mpr hf

private theorem localQuotient_localizedMapRp_rTensor_injective_of_annihilated
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : ∀ (q : Ideal X.A) [q.IsPrime],
      Function.Injective (u.rTensor q.ResidueField))
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y))
    {Q : Type (max (max u₁ u₃) u₄)} [AddCommGroup Q]
    [Module (Localization.AtPrime p) Q]
    (hkill : ∀ (a : Localization.AtPrime p), a ∈ I → ∀ x : Q, a • x = 0) :
    Function.Injective
      ((LinearMap.extendScalarsOfIsLocalization p.primeCompl
        (Localization.AtPrime p) (Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapR (R
          := X.A) u p)).rTensor Q) := by
  let Rp := Localization.AtPrime p
  let : IsLocalization p.primeCompl Rp := inferInstance
  let : CommRing Y.A := Y.commRingA
  let : Algebra X.A Y.A := hbc.algebraBase
  let qAct : Rp ⧸ I →+* Module.End Rp Q :=
    Ideal.Quotient.lift I (algebraMap Rp (Module.End Rp Q)) (by
      intro a ha
      apply RingHom.mem_ker.mpr
      ext x
      change a • x = 0
      exact hkill a ha x)
  let : Module (Rp ⧸ I) Q := Module.compHom Q qAct
  let : Module Y.A Q := Module.compHom Q (qAct.comp hbc.baseEquiv.toRingHom)
  let : Module X.A Q := Module.compHom Q (algebraMap X.A Y.A)
  have hcompat (a : X.A) (x : Q) :
      (algebraMap X.A Y.A a) • x = (algebraMap X.A Rp a) • x := by
    change (qAct (hbc.baseEquiv (algebraMap X.A Y.A a))) x = _
    rw [hbc.baseEquiv_algebraMap]
    change (qAct (Ideal.Quotient.mk I (algebraMap X.A Rp a))) x = _
    rfl
  let : IsScalarTower X.A Rp Q := IsScalarTower.of_algebraMap_smul fun a x =>
    (hcompat a x).symm
  exact rTensor_injective_extendScalarsOfIsLocalization p.primeCompl Rp _
    (Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapR_rTensor_injective u p Q
      (localQuotient_rTensor_injective X p I Y hbc hI u hu hspread (Q := Q)))

private theorem rTensor_eq_zero_of_annihilated
    {R N M : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.Flat R N] [Module.Flat R M]
    (f : N →ₗ[R] M) (J : Ideal R) (hJ : J.FG)
    (h : ∀ (P : Type u₅) [AddCommGroup P] [Module R P],
      (∀ a ∈ J, ∀ x : P, a • x = 0) → Function.Injective (f.rTensor P))
    {Q : Type u₅} [AddCommGroup Q] [Module R Q]
    (x : N ⊗[R] Q) (hx : ∀ a ∈ J, a • x = 0)
    (hfx : f.rTensor Q x = 0) : x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hJ
  let g : Q →ₗ[R] (s → Q) := LinearMap.pi fun a => (a.val • LinearMap.id)
  have hgx : g.lTensor N x = 0 := by
    apply (TensorProduct.piRight R R N (fun _ : s => Q)).injective
    ext a
    have hn : (LinearMap.proj a) ∘ₗ
        (TensorProduct.piRight R R N (fun _ : s => Q)).toLinearMap ∘ₗ
          g.lTensor N = a.val • LinearMap.id := by
      ext n q
      simp [g, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    simpa only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
      map_zero, Pi.zero_apply] using
      (LinearMap.congr_fun hn x).trans (hx a.val (hs ▸ Submodule.subset_span a.property))
  obtain ⟨y, rfl⟩ := (Module.Flat.lTensor_exact N
    (LinearMap.exact_subtype_ker_map g) x).mp hgx
  have hk : ∀ a ∈ J, ∀ q : LinearMap.ker g, a • q = 0 := by
    intro a ha q
    apply Subtype.ext
    change a • (q : Q) = 0
    rw [← hs] at ha
    refine Submodule.span_induction (fun b hb => ?_) (by simp)
      (fun b c _ _ hb hc => by simp [add_smul, hb, hc])
      (fun b c _ hc => by simp [mul_smul, hc]) ha
    exact congrFun q.property ⟨b, hb⟩
  have hy : f.rTensor (LinearMap.ker g) y = 0 := by
    apply (injective_iff_map_eq_zero (g.ker.subtype.lTensor M)).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ g.ker.injective_subtype)
    have hn : g.ker.subtype.lTensor M ∘ₗ f.rTensor g.ker =
        f.rTensor Q ∘ₗ g.ker.subtype.lTensor N := by
      rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun hn y).trans hfx
  rw [(injective_iff_map_eq_zero _).mp (h g.ker hk) y hy, map_zero]

private noncomputable def localizedTensorEquiv
    {R : Type*} [CommRing R] (S : Submonoid R)
    (N Q : Type*) [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] :
    LocalizedModule S (N ⊗[R] Q) ≃ₗ[Localization S]
      LocalizedModule S N ⊗[Localization S] (Localization S ⊗[R] Q) :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.iso S (AlgebraTensorModule.rTensor R Q
      (LocalizedModule.mkLinearMap S N))) ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R (Localization S) (Localization S)
      (LocalizedModule S N) Q).symm

private theorem localizedTensorEquiv_mk_tmul
    {R : Type*} [CommRing R] (S : Submonoid R)
    {N Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    (n : N) (q : Q) :
    localizedTensorEquiv S N Q (LocalizedModule.mk (n ⊗ₜ[R] q) 1) =
      LocalizedModule.mk n 1 ⊗ₜ[Localization S] ((1 : Localization S) ⊗ₜ[R] q) := by
  change (AlgebraTensorModule.cancelBaseChange R (Localization S) (Localization S)
    (LocalizedModule S N) Q).symm
    (IsLocalizedModule.iso S
      (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap S N))
      (LocalizedModule.mk (n ⊗ₜ[R] q) 1)) = _
  simp [AlgebraTensorModule.cancelBaseChange_symm_tmul]

private theorem localizedTensorEquiv_natural
    {R : Type*} [CommRing R] (S : Submonoid R)
    {N M Q : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (f : N →ₗ[R] M) :
    (localizedTensorEquiv S M Q).toLinearMap ∘ₗ LocalizedModule.map S (f.rTensor Q) =
      (LocalizedModule.map S f).rTensor (Localization S ⊗[R] Q) ∘ₗ
        (localizedTensorEquiv S N Q).toLinearMap := by
  have : IsLocalizedModule S (LinearMap.id :
      (LocalizedModule S M ⊗[Localization S] (Localization S ⊗[R] Q)) →ₗ[R] _) :=
    isLocalizedModule_id S _ (Localization S)
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S (N ⊗[R] Q))
    (IsLocalizedModule.map_units (LinearMap.id :
      (LocalizedModule S M ⊗[Localization S] (Localization S ⊗[R] Q)) →ₗ[R] _))
  ext n q
  simp [localizedTensorEquiv_mk_tmul, LocalizedModule.map_mk]

/-- **Stacks Project, Tag 0AT9.** In the finitely presented localized-module situation,
a linear map between flat modules which is injective on every residue-field fibre is
universally injective. -/
theorem universallyInjective_of_rTensor_residueField_injective_of_pureSpreadout
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (hAT8 : ∀ (p : Ideal X.A) [p.IsPrime],
      ∃ I : Ideal (Localization.AtPrime p),
        I.FG ∧ I ≤ p.map (algebraMap X.A (Localization.AtPrime p)) ∧
          ∃ Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
              max u₁ u₃, max u₁ (max u₃ u₄)},
            Nonempty (LocalQuotientBaseChange X Y p I) ∧
              Nonempty (PureSpreadout.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄),
                max (max u₁ u₃) u₄} Y))
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    [Module.Flat X.A X.N] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : ∀ (p : Ideal X.A) [p.IsPrime],
      Function.Injective (u.rTensor p.ResidueField)) :
    UniversallyInjective u := by
  intro Q _ _
  let Q' := ULift.{max u₁ u₃} Q
  apply (injective_rTensor_congr u (ULift.moduleEquiv : Q' ≃ₗ[X.A] Q)).mp
  let K := LinearMap.ker (u.rTensor Q')
  have hK : ∀ z : K, z = 0 := by
    apply (weakAss_empty_iff_zero (R := X.A)).mpr
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    have : p.IsPrime := IsWeaklyAssociatedPrime.isPrime X.A K hp
    obtain ⟨t, ht⟩ := (weaklyAssociated_iff_exists_radical_eq p).mp hp
    obtain ⟨I, hFG, hI, Y, ⟨hbc⟩, hspread⟩ := hAT8 p
    have hImax : I ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rwa [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    have hIproper : I ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime p)).ne_top
        (top_le_iff.mp (htop ▸ hImax))
    let : Nontrivial (Localization.AtPrime p ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hIproper
    let : IsLocalRing (Localization.AtPrime p ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let : IsLocalRing Y.A := hbc.baseEquiv.symm.isLocalRing
    let f := LocalizedModule.map p.primeCompl u
    have hkill : ∀ (P : Type (max (max u₁ u₃) u₄)) [AddCommGroup P]
        [Module (Localization.AtPrime p) P],
        (∀ a ∈ I, ∀ x : P, a • x = 0) → Function.Injective (f.rTensor P) :=
      fun _ _ _ hP => localQuotient_localizedMapRp_rTensor_injective_of_annihilated
        X p I Y hbc hI u hu hspread hP
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (J := annihilatorOfElem_semiring (R := Localization.AtPrime p) t)
      (ht.symm ▸ hImax) hFG
    let e := localizedTensorEquiv p.primeCompl X.N Q'
    let j := LocalizedModule.map p.primeCompl K.subtype
    have hj : Function.Injective j :=
      LocalizedModule.map_injective p.primeCompl K.subtype K.injective_subtype
    have hekill : ∀ a ∈ I ^ n, a • e (j t) = 0 := by
      intro a ha
      rw [← map_smul, ← map_smul,
        (mem_annihilatorOfElem_semiring_iff t a).mp (hn ha), map_zero, map_zero]
    have heker : f.rTensor (Localization.AtPrime p ⊗[X.A] Q') (e (j t)) = 0 := by
      have hnat := LinearMap.congr_fun (localizedTensorEquiv_natural p.primeCompl
        (Q := Q') u) (j t)
      have htker : LocalizedModule.map p.primeCompl (u.rTensor Q') (j t) = 0 := by
        induction t using LocalizedModule.induction_on with
        | _ k s =>
          change LocalizedModule.map p.primeCompl (u.rTensor Q')
            (LocalizedModule.map p.primeCompl K.subtype (LocalizedModule.mk k s)) = 0
          rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
          change LocalizedModule.mk ((u.rTensor Q') k.val) s = 0
          rw [show (u.rTensor Q') k.val = 0 from k.property, LocalizedModule.zero_mk]
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, htker, map_zero, e, f]
        using hnat.symm
    have hezero : e (j t) = 0 := rTensor_eq_zero_of_annihilated f (I ^ n) hFG.pow
      (fun P _ _ hP => rTensor_injective_of_ideal_power_annihilated f I hkill n hP)
      (e (j t)) hekill heker
    have htzero : t = 0 := hj (by
      apply e.injective
      simpa only [map_zero] using hezero)
    have htop : IsLocalRing.maximalIdeal (Localization.AtPrime p) = ⊤ := by
      rw [← ht, htzero, annihilatorOfElem_semiring]
      simp [Submodule.annihilator_bot]
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime p)).ne_top htop
  exact (injective_iff_map_eq_zero _).mpr fun z hz => congrArg Subtype.val (hK ⟨z, hz⟩)


end AlgebraicGeometry

end
