module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LocalizedModuleSpreadout
public import StacksFrontier.RingTheory.Flat.MittagLeffler
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Module.Localization.UniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealResidueFibre

/-!
# Universal injectivity from maximal-ideal fibres

In the finitely presented localized-module situation, suppose a pure spreadout exists. A map
from the distinguished module to a flat module is universally injective as soon as it is
injective modulo every maximal ideal of the base ring.

## Main results

* `AlgebraicGeometry.universallyInjective_of_injective_mod_maximalIdeal` gives the
  maximal-ideal criterion for universal injectivity.
* `AlgebraicGeometry.injective_rTensor_congr_of_linearEquiv` records that an injectivity test
  after tensoring depends on the test module only through its isomorphism class.

## Implementation notes

The reduction of a module modulo a maximal ideal `m` is represented by the quotient by
`m • ⊤`; the induced map is `Submodule.mapQ`. Existence of a pure spreadout is expressed by
`Nonempty`, with its test-module universe chosen to match the test-module universe of the
conclusion.

The proof first establishes the criterion for a projective source and a flat target, by
localizing at each maximal ideal and invoking the local statement
`Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal` (Tag 05FQ),
whose conclusion is the universal injectivity predicate written out. It then transfers the
criterion to the localized module by writing each element of `N ⊗ Q` as the image of an
element of `N' ⊗ Q` under the spreadout map divided by a denominator; the denominator acts
invertibly, which is what `smulUnitEquiv` records.

## References

* [Stacks Project, Tag 0AT7](https://stacks.math.columbia.edu/tag/0AT7)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace AlgebraicGeometry

open TensorProduct

/-- Base change on the left and on the right commute. -/
private theorem rTensor_comp_lTensor_comm {R : Type*} [CommSemiring R]
    {M N Q Q' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    (f : M →ₗ[R] N) (g : Q →ₗ[R] Q') :
    f.rTensor Q' ∘ₗ LinearMap.lTensor M g = LinearMap.lTensor N g ∘ₗ f.rTensor Q := by
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- The two spellings of base change along a linear map agree. -/
private theorem algebraTensor_rTensor_eq {R : Type*} [CommRing R]
    {M N Q : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) :
    LinearMap.rTensor Q f = TensorProduct.AlgebraTensorModule.rTensor R Q f := by
  ext x q
  rfl

/-- Tensoring with isomorphic test modules gives equivalent injectivity tests: injectivity of
a base change is invariant under a linear equivalence of test modules. -/
theorem injective_rTensor_congr_of_linearEquiv {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommGroup M] [Module R M] {N Q Q' : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q] [AddCommGroup Q']
    [Module R Q'] (f : M →ₗ[R] N) (e : Q ≃ₗ[R] Q') :
    Function.Injective (f.rTensor Q) ↔ Function.Injective (f.rTensor Q') := by
  rw [← (LinearEquiv.lTensor N e).injective.of_comp_iff (f.rTensor Q),
    ← LinearEquiv.coe_coe, LinearEquiv.coe_lTensor, ← LinearMap.coe_comp,
    ← rTensor_comp_lTensor_comm f e.toLinearMap, LinearMap.coe_comp,
    ← LinearEquiv.coe_lTensor, LinearEquiv.coe_coe,
    Function.Injective.of_comp_iff' _ (LinearEquiv.lTensor M e).bijective]

/-- The canonical isomorphism of a localized module restricts to the localization map. -/
private theorem iso_comp_mkLinearMap {R : Type*} [CommSemiring R] (S : Submonoid R)
    {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    (IsLocalizedModule.iso S f).toLinearMap ∘ₗ LocalizedModule.mkLinearMap S M = f := by
  ext x
  simp

/-- Injectivity of a base change is invariant under a linear equivalence of test modules. -/
private alias injective_rTensor_congr := injective_rTensor_congr_of_linearEquiv

/-- A map from a projective module to a flat module which is injective modulo every maximal
ideal is universally injective. -/
private theorem universallyInjective_of_injective_mapQ_maximal
    {R : Type u₁} {P M : Type u₄} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : P →ₗ[R] M)
    (hf : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((m • (⊤ : Submodule R P)).mapQ
        (m • (⊤ : Submodule R M)) f (Submodule.smul_top_le_comap_smul_top m f))) :
    UniversallyInjective f := by
  classical
  intro Q _ _
  apply injective_of_localized_maximal (f.rTensor Q)
  intro m hm
  let k := m.ResidueField
  let Rm := Localization.AtPrime m
  let Pm := LocalizedModule m.primeCompl P
  let Mm := LocalizedModule m.primeCompl M
  let fmA : Pm →ₗ[R] Mm := LocalizedModule.map m.primeCompl f
  let fm : Pm →ₗ[Rm] Mm :=
    LinearMap.extendScalarsOfIsLocalization m.primeCompl Rm fmA
  let : Module.Projective Rm Pm :=
    Module.projective_of_isLocalizedModule m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl P)
  let : Module.Flat Rm Mm :=
    Module.Flat.of_isLocalizedModule Rm m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl M)
  have hk : Function.Injective (f.rTensor k) := by
    have hquot := (mapQ_injective_iff_rTensor_quotient f m).mp (hf m)
    let e : (R ⧸ m) ≃ₗ[R] k := LinearEquiv.ofBijective
      ((Algebra.linearMap (R ⧸ m) k).restrictScalars R)
      m.bijective_algebraMap_quotient_residueField
    exact (injective_rTensor_congr_of_linearEquiv f e).mp hquot
  have hfmA : Function.Injective (fmA.rTensor k) := by
    apply IsLocalizedModule.rTensor_injective_of_rTensor_injective m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl P)
      (LocalizedModule.mkLinearMap m.primeCompl M) f fmA ?_ k hk
    exact IsLocalizedModule.map_comp m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl P)
      (LocalizedModule.mkLinearMap m.primeCompl M) f
  let : IsLocalizedModule m.primeCompl (LinearMap.id : k →ₗ[R] k) :=
    isLocalizedModule_id m.primeCompl k Rm
  have hfm : Function.Injective (fm.rTensor k) :=
    (LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization
      m.primeCompl Rm (LinearMap.id : k →ₗ[R] k) fmA).mp hfmA
  have hfiber : Function.Injective
      ((IsLocalRing.maximalIdeal Rm • (⊤ : Submodule Rm Pm)).mapQ
        (IsLocalRing.maximalIdeal Rm • (⊤ : Submodule Rm Mm)) fm
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal Rm) fm)) :=
    (mapQ_injective_iff_rTensor_quotient fm (IsLocalRing.maximalIdeal Rm)).2 hfm
  have hlocal :=
    Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal fm hfiber
  let Qm := LocalizedModule m.primeCompl Q
  let qm : Q →ₗ[R] Qm := LocalizedModule.mkLinearMap m.primeCompl Q
  let : Module Rm Qm := inferInstance
  let : IsScalarTower R Rm Qm := inferInstance
  have hlocalQ : Function.Injective (fmA.rTensor Q) := by
    have hright : Function.Injective
        ((LinearMap.extendScalarsOfIsLocalization m.primeCompl Rm fmA).rTensor Qm) :=
      hlocal Qm
    exact (LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization
      m.primeCompl Rm qm fmA).mpr hright
  let lP := TensorProduct.AlgebraTensorModule.rTensor R Q
    (LocalizedModule.mkLinearMap m.primeCompl P)
  let lM := TensorProduct.AlgebraTensorModule.rTensor R Q
    (LocalizedModule.mkLinearMap m.primeCompl M)
  have hlP : IsLocalizedModule m.primeCompl lP :=
    IsLocalizedModule.rTensor R m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl P)
  have hlM : IsLocalizedModule m.primeCompl lM :=
    IsLocalizedModule.rTensor R m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl M)
  let eP := IsLocalizedModule.iso m.primeCompl lP
  let eM := IsLocalizedModule.iso m.primeCompl lM
  let loc := IsLocalizedModule.map m.primeCompl
    (LocalizedModule.mkLinearMap m.primeCompl (P ⊗[R] Q))
    (LocalizedModule.mkLinearMap m.primeCompl (M ⊗[R] Q)) (f.rTensor Q)
  have hsq : (TensorProduct.AlgebraTensorModule.rTensor R Q fmA) ∘ₗ
      eP.toLinearMap = eM.toLinearMap ∘ₗ loc := by
    apply IsLocalizedModule.linearMap_ext m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (P ⊗[R] Q))
      lM
    rw [LinearMap.comp_assoc]
    rw [iso_comp_mkLinearMap m.primeCompl lP, LinearMap.comp_assoc]
    have hmap : loc ∘ₗ LocalizedModule.mkLinearMap m.primeCompl (P ⊗[R] Q) =
        LocalizedModule.mkLinearMap m.primeCompl (M ⊗[R] Q) ∘ₗ f.rTensor Q :=
      IsLocalizedModule.map_comp m.primeCompl
        (LocalizedModule.mkLinearMap m.primeCompl (P ⊗[R] Q))
        (LocalizedModule.mkLinearMap m.primeCompl (M ⊗[R] Q)) (f.rTensor Q)
    rw [hmap, ← LinearMap.comp_assoc,
      iso_comp_mkLinearMap m.primeCompl lM]
    rw [algebraTensor_rTensor_eq f]
    change TensorProduct.AlgebraTensorModule.rTensor R Q fmA ∘ₗ
        TensorProduct.AlgebraTensorModule.rTensor R Q
          (LocalizedModule.mkLinearMap m.primeCompl P) =
      TensorProduct.AlgebraTensorModule.rTensor R Q
          (LocalizedModule.mkLinearMap m.primeCompl M) ∘ₗ
        TensorProduct.AlgebraTensorModule.rTensor R Q f
    rw [← TensorProduct.AlgebraTensorModule.rTensor_comp]
    have hbase : fmA ∘ₗ LocalizedModule.mkLinearMap m.primeCompl P =
        LocalizedModule.mkLinearMap m.primeCompl M ∘ₗ f := by
      dsimp [fmA]
      exact IsLocalizedModule.map_comp m.primeCompl
        (LocalizedModule.mkLinearMap m.primeCompl P)
        (LocalizedModule.mkLinearMap m.primeCompl M) f
    rw [hbase, ← TensorProduct.AlgebraTensorModule.rTensor_comp]
  have hloc : Function.Injective loc := by
    have hcomp : Function.Injective (eM.toLinearMap ∘ₗ loc) := by
      rw [← hsq]
      have hlocalQ' : Function.Injective
          (TensorProduct.AlgebraTensorModule.rTensor R Q fmA) := by
        rw [← algebraTensor_rTensor_eq fmA]
        exact hlocalQ
      exact hlocalQ'.comp eP.injective
    exact (eM.injective.of_comp_iff loc).mp hcomp
  change Function.Injective loc
  exact hloc

/-- A universally injective map is injective modulo every maximal ideal. -/
private theorem universallyInjective_injective_mapQ
    {R : Type u₁} {P M : Type u₄} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    (f : P →ₗ[R] M) (hf : UniversallyInjective f)
    (m : Ideal R) [m.IsMaximal] :
    Function.Injective ((m • (⊤ : Submodule R P)).mapQ
      (m • (⊤ : Submodule R M)) f (Submodule.smul_top_le_comap_smul_top m f)) := by
  let k := R ⧸ m
  let : Field k := IsField.toField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp inferInstance)
  let Q := P ⧸ (m • (⊤ : Submodule R P))
  let : Module k Q := inferInstance
  let fbar := (m • (⊤ : Submodule R P)).mapQ
      (m • (⊤ : Submodule R M)) f (Submodule.smul_top_le_comap_smul_top m f)
  intro x y hxy
  by_contra hne
  let z := x - y
  have hzmap : fbar z = 0 := by
    change fbar (x - y) = 0
    rw [map_sub, hxy]
    exact sub_self _
  have hz : z ≠ 0 := by
    intro h
    apply hne
    exact sub_eq_zero.mp h
  obtain ⟨p, hp_eq⟩ := (Submodule.Quotient.mk_surjective (m • (⊤ : Submodule R P))) z
  have hp : p ∉ m • (⊤ : Submodule R P) := by
    intro hp
    apply hz
    rw [← hp_eq]
    exact (Submodule.Quotient.mk_eq_zero (m • (⊤ : Submodule R P))).2 hp
  have hzmap' : fbar (Submodule.Quotient.mk p) = 0 := by rw [hp_eq]; exact hzmap
  have hfp : f p ∈ m • (⊤ : Submodule R M) := by
    have hzero : (Submodule.Quotient.mk (f p) :
        M ⧸ (m • (⊤ : Submodule R M))) = 0 := by
      simpa [fbar, Submodule.mapQ_apply] using hzmap'
    exact (Submodule.Quotient.mk_eq_zero (m • (⊤ : Submodule R M))).1 hzero
  have hq : (Submodule.Quotient.mk p : Q) ≠ 0 := by
    intro hzero
    exact hp ((Submodule.Quotient.mk_eq_zero (m • (⊤ : Submodule R P))).1 hzero)
  have hlin : LinearIndepOn k (fun _ : Unit => (Submodule.Quotient.mk p : Q)) {()} :=
    (linearIndepOn_singleton_iff k
      (v := fun _ : Unit => (Submodule.Quotient.mk p : Q)) (i := ())).2 hq
  obtain ⟨ℓ, hℓ⟩ := Module.exists_dual_forall_apply_eq_one
    (ι := Unit) (K := k) (V := Q) hlin
  let g : M →ₗ[R] M ⊗[R] Q :=
    { toFun := fun z => z ⊗ₜ[R] (Submodule.Quotient.mk p : Q)
      map_add' := fun z w => add_tmul _ _ _
      map_smul' := fun r z => by simp [TensorProduct.smul_tmul] }
  have hgker : m • (⊤ : Submodule R M) ≤ LinearMap.ker g := by
    rw [Submodule.smul_le]
    intro r hr z hz
    simp only [Submodule.mem_top] at hz
    have hrx : r • (Submodule.Quotient.mk p : Q) = 0 := by
      rw [← Submodule.Quotient.mk_smul (m • (⊤ : Submodule R P))]
      exact (Submodule.Quotient.mk_eq_zero (m • (⊤ : Submodule R P))).2
        (Submodule.smul_mem_smul hr (Submodule.mem_top))
    change g (r • z) = 0
    change (r • z) ⊗ₜ[R] (Submodule.Quotient.mk p : Q) = 0
    rw [TensorProduct.smul_tmul, hrx, tmul_zero]
  have hkill : f.rTensor Q (p ⊗ₜ[R] (Submodule.Quotient.mk p : Q)) = 0 := by
    change f p ⊗ₜ[R] (Submodule.Quotient.mk p : Q) = 0
    exact LinearMap.mem_ker.mp (hgker hfp)
  have hnonzero : p ⊗ₜ[R] (Submodule.Quotient.mk p : Q) ≠ 0 := by
    intro hz
    let L : Q →ₗ[R] k := ℓ.restrictScalars R
    have hmap := congrArg (LinearMap.lTensor P L) hz
    simp only [LinearMap.lTensor_tmul] at hmap
    simp only [map_zero] at hmap
    change p ⊗ₜ[R] ℓ (Submodule.Quotient.mk p) = 0 at hmap
    rw [hℓ () (by simp)] at hmap
    have hmap' : p ⊗ₜ[R] Ideal.Quotient.mk m 1 = 0 := by simpa using hmap
    have hquot := congrArg (tensorQuotEquivQuotSMul P m) hmap'
    have hbad : (Submodule.Quotient.mk p :
        P ⧸ (m • (⊤ : Submodule R P))) = 0 := by
      simpa only [tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero] using hquot
    exact hp ((Submodule.Quotient.mk_eq_zero (m • (⊤ : Submodule R P))).1 hbad)
  have hinj : Function.Injective (f.rTensor Q) := hf Q
  have hzero := hinj (a₁ := p ⊗ₜ[R] (Submodule.Quotient.mk p : Q)) (a₂ := 0) hkill
  exact hnonzero hzero

/-- Multiplication by a unit of an algebra acting on a module is a linear automorphism over
the base ring. -/
private noncomputable def smulUnitEquiv
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (u : Sˣ) : M ≃ₗ[R] M where
  toFun x := (u : S) • x
  invFun x := (↑(u⁻¹) : S) • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  map_add' x y := smul_add _ _ _
  map_smul' r x := by
    exact smul_comm (u : S) r x

/-- **Stacks Project, Tag 0AT7 (universal injectivity).** A map into a flat
module which is injective modulo each maximal ideal is universally injective,
provided the distinguished localized module admits a pure spreadout. -/
@[stacks 0AT7 "universal_injectivity"]
theorem universallyInjective_of_injective_mod_maximalIdeal
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (hspread : Nonempty (PureSpreadout.{u₁, u₂, u₃, u₄, u₄} X))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : ∀ (m : Ideal X.A) [m.IsMaximal],
      Function.Injective
        (Submodule.mapQ (m • (⊤ : Submodule X.A X.N))
          (m • (⊤ : Submodule X.A M)) u
          (Submodule.smul_top_le_comap_smul_top m u))) :
    UniversallyInjective u := by
  classical
  let P := Classical.choice hspread
  let : CommRing P.C := P.commRingC
  let : Algebra X.B P.C := P.algebraBC
  let : Algebra X.A P.C := P.algebraAC
  let : IsScalarTower X.A X.B P.C := P.isScalarTowerABC
  let : Algebra P.C X.Bₛ := P.algebraCBₛ
  let : IsScalarTower X.B P.C X.Bₛ := P.isScalarTowerBCBₛ
  let : AddCommGroup P.N' := P.addCommGroupN'
  let : Module P.C P.N' := P.moduleCN'
  let : Module X.B P.N' := P.moduleBN'
  let : Module X.A P.N' := P.moduleAN'
  let : IsScalarTower X.B P.C P.N' := P.isScalarTowerBCN'
  let : IsScalarTower X.A P.C P.N' := P.isScalarTowerACN'
  let : Module P.C X.N := P.moduleCN
  let : IsScalarTower P.C X.Bₛ X.N := P.isScalarTowerCBₛN
  let : IsScalarTower X.B P.C X.N := P.isScalarTowerBCN
  let : IsScalarTower X.A P.C X.N := P.isScalarTowerACN
  let fB : P.N' →ₗ[X.B] X.N := P.localizationMap.restrictScalars X.B
  let fA : P.N' →ₗ[X.A] X.N := P.localizationMap.restrictScalars X.A
  have : IsLocalizedModule X.S fB := P.isLocalizedModule
  let : IsScalarTower X.A X.B P.N' := IsScalarTower.of_algebraMap_smul fun a x => by
    rw [← IsScalarTower.algebraMap_smul P.C (algebraMap X.A X.B a) x,
      ← IsScalarTower.algebraMap_smul P.C a x]
    exact congrArg (fun c : P.C => c • x)
      (congrArg (fun f : X.A →+* P.C => f a)
        (IsScalarTower.algebraMap_eq X.A X.B P.C).symm)
  let : Module.Projective X.A P.N' := P.projective
  let unit (s : X.S) : X.Bₛˣ := (IsLocalization.map_units X.Bₛ s).unit
  let stage (s : X.S) : P.N' →ₗ[X.A] X.N :=
    (smulUnitEquiv (R := X.A) (S := X.Bₛ) (M := X.N) ((unit s)⁻¹)).toLinearMap.comp fA
  have hstage_mk (s : X.S) (x : P.N') :
      stage s x = IsLocalizedModule.mk' fB x s := by
    symm
    apply IsLocalizedModule.mk'_eq_iff.mpr
    change fB x = algebraMap X.B X.Bₛ (s : X.B) •
      ((↑((unit s)⁻¹) : X.Bₛ) • fA x)
    have hunit : (unit s : X.Bₛ) = algebraMap X.B X.Bₛ (s : X.B) :=
      (IsLocalization.map_units X.Bₛ s).unit_spec
    rw [← hunit, smul_smul]
    have huinv : (unit s : X.Bₛ) * (↑((unit s)⁻¹) : X.Bₛ) = 1 := Units.val_inv _
    rw [huinv, one_smul]
    rfl
  have hstage_univ (s : X.S) : UniversallyInjective (stage s) := by
    intro Q _ _
    let e : X.N ≃ₗ[X.A] X.N :=
      smulUnitEquiv (R := X.A) (S := X.Bₛ) (M := X.N) ((unit s)⁻¹)
    have he : Function.Injective
        ((LinearEquiv.rTensor Q e).toLinearMap) := (LinearEquiv.rTensor Q e).injective
    have hcomp : (stage s).rTensor Q =
        (LinearEquiv.rTensor Q e).toLinearMap.comp
          (fA.rTensor Q) := by
      change (e.toLinearMap.comp fA).rTensor Q = _
      ext x q
      rfl
    rw [hcomp]
    exact he.comp (P.universallyInjective Q)
  let numerator (t : X.S) : P.N' →ₗ[X.A] P.N' :=
    { toFun := fun x => (t : X.B) • x
      map_add' := fun x y => smul_add _ _ _
      map_smul' := fun a x => smul_comm (t : X.B) a x }
  have hstage_adjust (s t : X.S) :
      stage (s * t) ∘ₗ numerator t = stage s := by
    ext x
    rw [LinearMap.comp_apply, hstage_mk, hstage_mk]
    exact IsLocalizedModule.mk'_cancel_right fB x s t
  intro Q _ _
  apply (show Function.Injective (u.rTensor Q) from ?_)
  intro a b hab
  let z := a - b
  have hz : u.rTensor Q z = 0 := by
    dsimp [z]
    rw [map_sub, hab]
    exact sub_self _
  have hbar_comp (s : X.S) (m : Ideal X.A) [m.IsMaximal] :
      Function.Injective ((m • (⊤ : Submodule X.A P.N')).mapQ
        (m • (⊤ : Submodule X.A M)) (u.comp (stage s))
        (Submodule.smul_top_le_comap_smul_top m (u.comp (stage s)))) := by
    have hs := universallyInjective_injective_mapQ (stage s) (hstage_univ s) m
    have hu_m : Function.Injective
        ((m • (⊤ : Submodule X.A X.N)).mapQ
          (m • (⊤ : Submodule X.A M)) u
          (Submodule.smul_top_le_comap_smul_top m u)) := hu m
    have hsTensor : Function.Injective ((stage s).rTensor (X.A ⧸ m)) :=
      (mapQ_injective_iff_rTensor_quotient (stage s) m).mp hs
    have huTensor : Function.Injective (u.rTensor (X.A ⧸ m)) :=
      (mapQ_injective_iff_rTensor_quotient u m).mp hu_m
    apply (mapQ_injective_iff_rTensor_quotient (u.comp (stage s)) m).mpr
    rw [LinearMap.rTensor_comp]
    exact huTensor.comp hsTensor
  have hcomp_univ (s : X.S) : UniversallyInjective (u.comp (stage s)) :=
    universallyInjective_of_injective_mapQ_maximal (u.comp (stage s)) (hbar_comp s)
  have hcover : ∀ w : X.N ⊗[X.A] Q, ∃ s : X.S, ∃ y : P.N' ⊗[X.A] Q,
      (stage s).rTensor Q y = w := by
    intro w
    refine TensorProduct.inductionOn w ?_ ?_
    · intro n q
      obtain ⟨⟨x, s⟩, hn⟩ := IsLocalizedModule.mk'_surjective X.S fB n
      change IsLocalizedModule.mk' fB x s = n at hn
      refine ⟨s, x ⊗ₜ[X.A] q, ?_⟩
      rw [LinearMap.rTensor_tmul, hstage_mk, hn]
    · intro w₁ w₂ hw₁ hw₂
      obtain ⟨s, y₁, rfl⟩ := hw₁
      obtain ⟨t, y₂, rfl⟩ := hw₂
      refine ⟨s * t, (numerator t).rTensor Q y₁ + (numerator s).rTensor Q y₂, ?_⟩
      have h (s t : X.S) (y : P.N' ⊗[X.A] Q) :
          (stage (s * t)).rTensor Q ((numerator t).rTensor Q y) =
            (stage s).rTensor Q y := by
        change ((stage (s * t)).rTensor Q ∘ₗ (numerator t).rTensor Q) y = _
        rw [← LinearMap.rTensor_comp, hstage_adjust]
      rw [map_add, h s t y₁]
      congr 1
      simpa only [mul_comm s t] using h t s y₂
  obtain ⟨s, y, hy⟩ := hcover z
  have hkill : (u.comp (stage s)).rTensor Q y = 0 := by
    rw [LinearMap.rTensor_comp_apply, hy]
    exact hz
  have hy0 := (hcomp_univ s Q) (a₁ := y) (a₂ := 0) hkill
  have hz0 : z = 0 := by
    calc
      z = (stage s).rTensor Q y := hy.symm
      _ = 0 := by simp [hy0]
  exact sub_eq_zero.mp hz0

end AlgebraicGeometry
