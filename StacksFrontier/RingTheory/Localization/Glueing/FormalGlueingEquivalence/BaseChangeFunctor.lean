module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.Modules
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.UnitIdeal
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.UnitIdeal

/-!
# Formal glueing of module categories: the base-change functor

Flat base change carries module glueing data for `R → S` to module glueing data for the
base-changed map `R' → S ⊗[R] R'`. This file transports the Čech comparisons along base change,
proves the cocycle and compatibility conditions of the base-changed overlap isomorphisms,
assembles the base-changed module glueing datum, identifies the base change of the modules
presenting compatible sections and of the components of canonical glueing data, and constructs
the base-change functor between the categories of module glueing data.
-/

section

namespace FormalGlueing

universe u v x w

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open scoped ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

public theorem extendScalarsEquiv_tmul
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat A)
    (b : B) (m : M) :
    extendScalarsEquiv B M (b ⊗ₜ[A, algebraMap A B] m) = b ⊗ₜ[A] m := rfl

private noncomputable abbrev cechTransportEquiv
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) {M L : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup L] [Module B L]
    (e : L ≃ₗ[B] B ⊗[A] M) (s : Finset (Fin r)) :
    Cech.cechMod (fun i ↦ algebraMap A B (f i)) L s ≃ₗ[B]
      B ⊗[A] Cech.cechMod f M s :=
  localizedEquiv _ e ≪≫ₗ cechBaseChangeEquiv B f M s

private theorem cechBaseChangeEquiv_mk_apply
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) (M : Type*) [AddCommGroup M] [Module A M]
    (s : Finset (Fin r)) (z : B ⊗[A] M) :
    cechBaseChangeEquiv B f M s (LocalizedModule.mkLinearMap
      (Cech.cechSub (fun i ↦ algebraMap A B (f i)) s) _ z) =
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) M).baseChange B z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul b m => exact cechBaseChangeEquiv_mk B f M s b m

private theorem cechTransportEquiv_mk
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) {M L : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup L] [Module B L]
    (e : L ≃ₗ[B] B ⊗[A] M) (s : Finset (Fin r)) (z : L) :
    cechTransportEquiv B f e s (LocalizedModule.mkLinearMap
      (Cech.cechSub (fun i ↦ algebraMap A B (f i)) s) _ z) =
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) M).baseChange B (e z) :=
  (congrArg (cechBaseChangeEquiv B f M s) (localizedEquiv_mk _ e z)).trans
    (cechBaseChangeEquiv_mk_apply B f M s (e z))

private theorem cechBaseChange_isLocalized
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) (M : Type*) [AddCommGroup M] [Module A M]
    (s : Finset (Fin r)) :
    IsLocalizedModule (Cech.cechSub (fun i ↦ algebraMap A B (f i)) s)
      ((LocalizedModule.mkLinearMap (Cech.cechSub f s) M).baseChange B) := by
  simpa only [Cech.cechSub, Algebra.algebraMapSubmonoid_powers, map_prod] using
    isLocalized_baseChange (B := B) (Cech.cechSub f s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)

private theorem cechTransportEquiv_naturality
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) {M N L K : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup L] [Module B L] [AddCommGroup K] [Module B K]
    (e : L ≃ₗ[B] B ⊗[A] M) (d : K ≃ₗ[B] B ⊗[A] N)
    (g : M →ₗ[A] N) (g' : L →ₗ[B] K)
    (h : ∀ z, d (g' z) = g.baseChange B (e z))
    (s : Finset (Fin r)) :
    (cechTransportEquiv B f d s).toLinearMap.comp
      (FormalGlueing.localizedMap (fun i ↦ algebraMap A B (f i)) s g') =
      ((FormalGlueing.localizedMap f s g).baseChange B).comp
        (cechTransportEquiv B f e s).toLinearMap := by
  let := cechBaseChange_isLocalized B f N s
  apply IsLocalizedModule.linearMap_ext
    (Cech.cechSub (fun i ↦ algebraMap A B (f i)) s)
    (LocalizedModule.mkLinearMap _ L)
    ((LocalizedModule.mkLinearMap (Cech.cechSub f s) N).baseChange B)
  ext z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    FormalGlueing.localizedMap_mk, cechTransportEquiv_mk]
  rw [h]
  generalize e z = y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simpa only [map_add] using congrArg₂ (· + ·) hy hy'
  | tmul b m => simp only [LinearMap.baseChange_tmul, FormalGlueing.localizedMap_mk]


private theorem cech_ext
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {s t : Finset (Fin r)} (h : s ⊆ t)
    {g k : Cech.cechMod f M s →ₗ[A] Cech.cechMod f N t}
    (he : g.comp (LocalizedModule.mkLinearMap (Cech.cechSub f s) M) =
      k.comp (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)) : g = k := by
  apply IsLocalizedModule.ext (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M) _ he
  intro a
  exact IsLocalizedModule.map_units
    (S := Submonoid.closure (f '' (↑t : Set (Fin r))))
    (LocalizedModule.mkLinearMap (Cech.cechSub f t) N)
    ⟨a, Cech.cechSub_le_closure f h a.2⟩

private theorem cechTransportEquiv_iterated
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) {M L : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup L] [Module B L]
    (e : L ≃ₗ[B] B ⊗[A] M)
    (c : FormalGlueing.LocalizationComparisons f)
    (d : FormalGlueing.LocalizationComparisons (fun i ↦ algebraMap A B (f i)))
    (s t : Finset (Fin r)) :
    (cechTransportEquiv B f e (s ∪ t)).toLinearMap.comp (d.iterated L s t).toLinearMap =
      ((c.iterated M s t).toLinearMap.baseChange B).comp
        (cechTransportEquiv B f (cechTransportEquiv B f e s) t).toLinearMap := by
  apply (LinearMap.cancel_left (cechTransportEquiv B f e (s ∪ t)).symm.injective).mp
  apply cech_ext _ Finset.subset_union_right
  apply cech_ext _ Finset.subset_union_left
  ext z
  apply (cechTransportEquiv B f e (s ∪ t)).injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    FormalGlueing.iterated_mk, cechTransportEquiv_mk]
  generalize e z = y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simpa only [map_add] using congrArg₂ (· + ·) hy hy'
  | tmul b m => simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      FormalGlueing.iterated_mk]

private theorem cechTransportEquiv_congr
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) {M L : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup L] [Module B L]
    (e : L ≃ₗ[B] B ⊗[A] M) {s t : Finset (Fin r)} (h : s = t) :
    (cechTransportEquiv B f e t).toLinearMap.comp
      (FormalGlueing.cechModCongr (fun i ↦ algebraMap A B (f i)) h).toLinearMap =
      ((FormalGlueing.cechModCongr f h).toLinearMap.baseChange B).comp
        (cechTransportEquiv B f e s).toLinearMap := by
  subst t
  show _ = (LinearMap.id.baseChange B).comp _
  simp only [LinearMap.baseChange_id, LinearMap.id_comp]
  rfl


private theorem cechTransportEquiv_iterated_symm
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {r : ℕ} (f : Fin r → A) {M L : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup L] [Module B L]
    (e : L ≃ₗ[B] B ⊗[A] M)
    (c : FormalGlueing.LocalizationComparisons f)
    (d : FormalGlueing.LocalizationComparisons (fun i ↦ algebraMap A B (f i)))
    (s t : Finset (Fin r)) (z) :
    cechTransportEquiv B f (cechTransportEquiv B f e s) t ((d.iterated L s t).symm z) =
      ((c.iterated M s t).symm.toLinearMap.baseChange B)
        (cechTransportEquiv B f e (s ∪ t) z) := by
  have h := LinearMap.congr_fun (cechTransportEquiv_iterated B f e c d s t)
    ((d.iterated L s t).symm z)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
  rw [h]
  show _ = (AlgebraTensorModule.congr (LinearEquiv.refl B B) (c.iterated M s t)).symm
    ((AlgebraTensorModule.congr (LinearEquiv.refl B B) (c.iterated M s t)) _)
  simp only [LinearEquiv.symm_apply_apply]

set_option maxHeartbeats 1600000 in
-- The cocycle identity composes six transported Čech comparisons, which needs a larger budget.
private theorem baseChangeAlphaIJ_cocycle
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons f} (X : FormalGlueing.ModuleGlueingDatum S f c)
    (d : FormalGlueing.LocalizationComparisons (fun i ↦ algebraMap R B (f i)))
    (i j k : Fin r) :
    let f' := fun i ↦ algebraMap R B (f i)
    let a := baseChangeAlphaIJ S B f X
    (d.iterated _ {j} {i}).toLinearMap.comp
        ((FormalGlueing.localizedMap f' {i} (a j k).toLinearMap).comp
          ((d.iterated _ {k} {i}).symm.toLinearMap.comp
            ((FormalGlueing.cechModCongr f'
              (show {i} ∪ {k} = {k} ∪ {i} by simp [Finset.union_comm])).toLinearMap.comp
              ((d.iterated _ {i} {k}).toLinearMap.comp
                ((FormalGlueing.localizedMap f' {k} (a i j).toLinearMap).comp
                  (d.iterated _ {j} {k}).symm.toLinearMap))))) =
      (FormalGlueing.cechModCongr f' (show {i} ∪ {j} = {j} ∪ {i} by simp
        [Finset.union_comm])).toLinearMap.comp
        ((d.iterated _ {i} {j}).toLinearMap.comp
          ((FormalGlueing.localizedMap f' {j} (a i k).toLinearMap).comp
            ((d.iterated _ {k} {j}).symm.toLinearMap.comp
              (FormalGlueing.cechModCongr f'
                (show {j} ∪ {k} = {k} ∪ {j} by simp [Finset.union_comm])).toLinearMap))) := by
  let f' := fun i ↦ algebraMap R B (f i)
  let e l := awayTensorEquiv B (f l) (X.localPiece l)
  let E l s := cechTransportEquiv B f (e l) s
  let D l s t := cechTransportEquiv B f (E l s) t
  have hi l s t z : E l (s ∪ t) (d.iterated _ s t z) =
      ((c.iterated _ s t).toLinearMap.baseChange B) (D l s t z) :=
    LinearMap.congr_fun (cechTransportEquiv_iterated B f (e l) c d s t) z
  have hs l s t z : D l s t ((d.iterated _ s t).symm z) =
      ((c.iterated _ s t).symm.toLinearMap.baseChange B) (E l (s ∪ t) z) :=
    cechTransportEquiv_iterated_symm B f (e l) c d s t z
  have hc l {s t : Finset (Fin r)} (h : s = t) z :
      E l t (FormalGlueing.cechModCongr f' h z) =
        ((FormalGlueing.cechModCongr f h).toLinearMap.baseChange B) (E l s z) :=
    LinearMap.congr_fun (cechTransportEquiv_congr B f (e l) h) z
  have hn l n t z :
      D n {l} t (FormalGlueing.localizedMap f' t (baseChangeAlphaIJ S B f X l n).toLinearMap z) =
      ((FormalGlueing.localizedMap f t (X.alphaIJ l n).toLinearMap).baseChange B)
        (D l {n} t z) := by
    apply LinearMap.congr_fun (cechTransportEquiv_naturality B f (E l {n}) (E n {l})
      (X.alphaIJ l n).toLinearMap (baseChangeAlphaIJ S B f X l n).toLinearMap
    (baseChangeAlphaIJ_commutes S B f X l n) t) z
  dsimp only [f'] at hc hn
  apply (LinearMap.cancel_left (E k ({j} ∪ {i})).injective).mp
  ext z
  dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  show E k ({j} ∪ {i}) _ = E k ({j} ∪ {i}) _
  simp only [hi, hs, hc, hn]
  have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange B) (X.cocycle i j k))
    (E i ({j} ∪ {k}) z)
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using h


private noncomputable abbrev tensorTransportEquiv
    (R S B P : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing P]
    [Algebra R S] [Algebra R B] [Algebra R P] [Algebra S P] [Algebra B P]
    [IsScalarTower R S P] [IsScalarTower R B P]
    {M L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup L] [Module B L]
    (e : L ≃ₗ[B] B ⊗[R] M) :
    P ⊗[B] L ≃ₗ[P] P ⊗[S] (S ⊗[R] M) :=
  AlgebraTensorModule.congr (LinearEquiv.refl P P) e ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R B P P M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R S P P M).symm

private theorem tensorTransportEquiv_naturality
    (R S B P : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing P]
    [Algebra R S] [Algebra R B] [Algebra R P] [Algebra S P] [Algebra B P]
    [IsScalarTower R S P] [IsScalarTower R B P]
    {M N L K : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module B L] [AddCommGroup K] [Module B K]
    (e : L ≃ₗ[B] B ⊗[R] M) (d : K ≃ₗ[B] B ⊗[R] N)
    (g : M →ₗ[R] N) (g' : L →ₗ[B] K)
    (h : ∀ z, d (g' z) = g.baseChange B (e z)) (z : P ⊗[B] L) :
    tensorTransportEquiv R S B P d (TensorProduct.map LinearMap.id g' z) =
      TensorProduct.map LinearMap.id (g.baseChange S)
        (tensorTransportEquiv R S B P e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul p l =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, tensorTransportEquiv,
      LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h]
    generalize e l = y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simpa only [map_add, tmul_add] using congrArg₂ (· + ·) hy hy'
    | tmul b m =>
      simp only [LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply]

private theorem baseChangeAlpha_compatibility
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons f} (X : FormalGlueing.ModuleGlueingDatum S f c)
    (i j : Fin r)
    (m : (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj X.generic) :
    TensorProduct.map LinearMap.id (baseChangeAlphaIJ S B f X i j).toLinearMap
        (TensorProduct.map LinearMap.id
          (LocalizedModule.mkLinearMap (Cech.cechSub (fun i ↦ algebraMap R B (f i)) {j}) _)
          (baseChangeAlpha S B f X i (LocalizedModule.mkLinearMap
            (Submonoid.powers (algebraMap B (S ⊗[R] B) (algebraMap R B (f i)))) _ m))) =
      TensorProduct.map LinearMap.id
        (LocalizedModule.mkLinearMap (Cech.cechSub (fun i ↦ algebraMap R B (f i)) {i}) _)
        (baseChangeAlpha S B f X j (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap B (S ⊗[R] B) (algebraMap R B (f j)))) _ m)) := by
  let e l := awayTensorEquiv B (f l) (X.localPiece l)
  let E l s := cechTransportEquiv B f (e l) s
  apply (tensorTransportEquiv R S B (S ⊗[R] B) (E j {i})).injective
  rw [tensorTransportEquiv_naturality R S B (S ⊗[R] B) (E i {j}) (E j {i})
    (X.alphaIJ i j).toLinearMap (baseChangeAlphaIJ S B f X i j).toLinearMap
    (baseChangeAlphaIJ_commutes S B f X i j)]
  have hmk l n := tensorTransportEquiv_naturality R S B (S ⊗[R] B) (e l) (E l {n})
    (LocalizedModule.mkLinearMap (Cech.cechSub f {n}) _)
    (LocalizedModule.mkLinearMap (Cech.cechSub (fun i ↦ algebraMap R B (f i)) {n}) _)
    (cechTransportEquiv_mk B f (e l) {n})
  rw [hmk i j, hmk j i]
  show TensorProduct.map _ _ (TensorProduct.map _ _
    (genericLocalTensorEquiv S B (f i) (X.localPiece i) _)) =
      TensorProduct.map _ _ (genericLocalTensorEquiv S B (f j) (X.localPiece j) _)
  rw [baseChangeAlpha_commutes, baseChangeAlpha_commutes]
  obtain ⟨z, rfl⟩ := (extendScalarsEquiv (S ⊗[R] B) X.generic).symm.surjective m
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add m n hm hn => simpa only [map_add] using congrArg₂ (· + ·) hm hn
  | tmul t m =>
    show TensorProduct.map _ _ (TensorProduct.map _ _ (TensorProduct.map _ _
      (genericLocalizationEquiv S B (f i) X.generic (LocalizedModule.mkLinearMap _ _
        (t ⊗ₜ[S, Algebra.TensorProduct.includeLeftRingHom] m))))) =
      TensorProduct.map _ _ (TensorProduct.map _ _
        (genericLocalizationEquiv S B (f j) X.generic (LocalizedModule.mkLinearMap _ _
          (t ⊗ₜ[S, Algebra.TensorProduct.includeLeftRingHom] m))))
    simp only [genericLocalizationEquiv_mk, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe]
    exact congrArg (fun z ↦ t ⊗ₜ[S] z) (X.alpha_compatibility i j m)


private theorem awayTensorEquiv_symm_tmul {R : Type*} (B : Type*)
    [CommRing R] [CommRing B] [Algebra R B] (a : R)
    (M : ModuleCat (Localization.Away a)) (b : B)
    (m : (ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).obj M) :
    (awayTensorEquiv B a M).symm (b ⊗ₜ[R] m) =
      (algebraMap B (Localization.Away (algebraMap R B a)) b)
        ⊗ₜ[Localization.Away a, awayMap B a] m := by
  apply (awayTensorEquiv B a M).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (awayTensorEquiv_tmul B a M b m).symm

private theorem awayTensorEquiv_naturality {R : Type*} (B : Type*)
    [CommRing R] [CommRing B] [Algebra R B] (a : R)
    {M N : ModuleCat (Localization.Away a)} (g : M ⟶ N) (z) :
    awayTensorEquiv B a N ((ModuleCat.extendScalars (awayMap B a)).map g z) =
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away a))).map g).hom.baseChange B)
        (awayTensorEquiv B a M z) := by
  show awayTensorEquiv B a N
    ((((ModuleCat.restrictScalars (algebraMap B (Localization.Away (algebraMap R B a)))).map
      ((ModuleCat.extendScalars (awayMap B a)).map g)).hom) z) = _
  obtain ⟨y, rfl⟩ := (awayTensorEquiv B a M).symm.surjective z
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y y' hy hy' => simpa only [map_add] using congrArg₂ (· + ·) hy hy'
  | tmul b m =>
    rw [awayTensorEquiv_symm_tmul]
    show awayTensorEquiv B a N
      (algebraMap B (Localization.Away (algebraMap R B a)) b ⊗ₜ[Localization.Away a, awayMap B a] g
        m) = _
    rw [awayTensorEquiv_tmul, awayTensorEquiv_tmul, LinearMap.baseChange_tmul]
    rfl


private theorem localOverlapEquiv_naturality {R : Type*} (B : Type*)
    [CommRing R] [CommRing B] [Algebra R B] {r : ℕ} (f : Fin r → R) (i : Fin r)
    {M N : ModuleCat (Localization.Away (f i))} (g : M ⟶ N)
    (s : Finset (Fin r)) (z) :
    localOverlapEquiv B f i N s
      (FormalGlueing.localizedMap (fun i ↦ algebraMap R B (f i)) s
        (((ModuleCat.restrictScalars (algebraMap B (Localization.Away (algebraMap R B (f i))))).map
          ((ModuleCat.extendScalars (awayMap B (f i))).map g)).hom) z) =
      ((FormalGlueing.localizedMap f s
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map g).hom).baseChange
          B)
          (localOverlapEquiv B f i M s z) := by
  apply LinearMap.congr_fun (cechTransportEquiv_naturality B f
    (awayTensorEquiv B (f i) M) (awayTensorEquiv B (f i) N)
    ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map g).hom
    (((ModuleCat.restrictScalars (algebraMap B (Localization.Away (algebraMap R B (f i))))).map
      ((ModuleCat.extendScalars (awayMap B (f i))).map g)).hom)
    (awayTensorEquiv_naturality B (f i) g) s) z

section BaseChange

variable {R : Type u} (S : Type v) (B : Type x)
  [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
  {r : ℕ} (f : Fin r → R)
  {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}

private noncomputable abbrev baseChangeDatum
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c) :
    FormalGlueing.ModuleGlueingDatum.{x, max v x, max u v x w} (S ⊗[R] B)
      (fun i ↦ algebraMap R B (f i)) (FormalGlueing.localizationComparisons _) where
  generic := (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj X.generic
  localPiece i := (ModuleCat.extendScalars (awayMap B (f i))).obj (X.localPiece i)
  alpha := baseChangeAlpha S B f X
  alphaIJ := baseChangeAlphaIJ S B f X
  alpha_compatibility := baseChangeAlpha_compatibility S B f X
  cocycle := baseChangeAlphaIJ_cocycle S B f X _

end BaseChange

private noncomputable def genericBaseEquiv
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (M : ModuleCat S) :
    FormalGlueing.restrictFromTarget (R := B) (S ⊗[R] B)
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj M) ≃ₗ[B]
      B ⊗[R] FormalGlueing.restrictFromTarget (R := R) S M := by
  letI : Module R M := Module.compHom M (algebraMap R S)
  letI : IsScalarTower R S M := restrictScalars_tower M
  let N := (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj M
  letI : Module B N := Module.compHom N (algebraMap B (S ⊗[R] B))
  letI : IsScalarTower B (S ⊗[R] B) N := restrictScalars_tower N
  exact (extendScalarsEquiv (S ⊗[R] B) M).restrictScalars B ≪≫ₗ
    pushoutTensorEquiv R S B (S ⊗[R] B) M

private theorem genericBaseEquiv_symm_tmul
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (M : ModuleCat S) (b : B)
    (m : FormalGlueing.restrictFromTarget (R := R) S M) :
    (genericBaseEquiv S B M).symm (b ⊗ₜ[R] m) =
      (algebraMap B (S ⊗[R] B) b) ⊗ₜ[S, Algebra.TensorProduct.includeLeftRingHom] m := by
  let : Module R M := Module.compHom M (algebraMap R S)
  let : IsScalarTower R S M := restrictScalars_tower M
  show (extendScalarsEquiv (S ⊗[R] B) M).symm
    ((pushoutTensorEquiv R S B (S ⊗[R] B) M).symm (b ⊗ₜ[R] m)) = _
  exact congrArg (extendScalarsEquiv (S ⊗[R] B) M).symm
    (pushoutTensorEquiv_symm_tmul R S B (S ⊗[R] B) M b m)

private theorem genericBaseEquiv_tmul
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (M : ModuleCat S) (b : B) (m : M) :
    genericBaseEquiv S B M
      ((algebraMap B (S ⊗[R] B) b) ⊗ₜ[S, Algebra.TensorProduct.includeLeftRingHom] m) =
      b ⊗ₜ[R] (show FormalGlueing.restrictFromTarget (R := R) S M from m) := by
  have h := genericBaseEquiv_symm_tmul (R := R) S B M b
    (show FormalGlueing.restrictFromTarget (R := R) S M from m)
  simpa only [LinearEquiv.apply_symm_apply] using (congrArg (genericBaseEquiv S B M) h).symm


private abbrev sectionAmbient
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) {c : FormalGlueing.LocalizationComparisons f}
    (X : FormalGlueing.ModuleGlueingDatum S f c) :=
  FormalGlueing.restrictFromTarget (R := R) S X.generic ×
    ∀ i, FormalGlueing.restrictFromAway f i (X.localPiece i)

private abbrev sectionRelations
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) {c : FormalGlueing.LocalizationComparisons f}
    (X : FormalGlueing.ModuleGlueingDatum S f c) :=
  (∀ i, S ⊗[R] FormalGlueing.restrictFromAway f i (X.localPiece i)) ×
    ∀ i j, Cech.cechMod f (FormalGlueing.restrictFromAway f j (X.localPiece j)) {i}

private noncomputable def sectionDefect
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) {c : FormalGlueing.LocalizationComparisons f}
    (X : FormalGlueing.ModuleGlueingDatum S f c) :
    sectionAmbient S f X →ₗ[R] sectionRelations S f X where
  toFun z := (fun i ↦ X.alpha i
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ z.1) -
        1 ⊗ₜ[R] z.2 i,
    fun i j ↦ X.alphaIJ i j (LocalizedModule.mkLinearMap (Cech.cechSub f {j}) _ (z.2 i)) -
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) _ (z.2 j))
  map_add' z y := by
    apply Prod.ext
    · funext i
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, tmul_add]
      rw [map_add, map_add]
      abel
    · funext i j
      simp only [Prod.snd_add, Pi.add_apply, map_add]
      abel
  map_smul' a z := by
    apply Prod.ext
    · funext i
      change X.alpha i (LocalizedModule.mkLinearMap _ _
        ((algebraMap R S a) • (show X.generic from z.1))) -
        (TensorProduct.mk R S _) 1 (a • z.2 i) = _
      rw [map_smul, map_smul, map_smul]
      simp only [RingHom.id_apply, Prod.smul_fst, Pi.smul_apply,
        IsScalarTower.algebraMap_smul, smul_sub]
      rfl
    · funext i j
      change X.alphaIJ i j (LocalizedModule.mkLinearMap _ _ (a • z.2 i)) -
        LocalizedModule.mkLinearMap _ _ (a • z.2 j) = a • (_ - _)
      rw [map_smul, map_smul, map_smul, smul_sub]

private theorem compatibleSections_eq_ker
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) {c : FormalGlueing.LocalizationComparisons f}
    (X : FormalGlueing.ModuleGlueingDatum S f c) :
    FormalGlueing.compatibleSections S f c X = (sectionDefect S f X).ker := by
  ext z
  simp only [FormalGlueing.compatibleSections, Submodule.mem_mk,
    LinearMap.mem_ker, sectionDefect, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.mk_eq_zero, funext_iff, Pi.zero_apply, sub_eq_zero]
  rfl

private noncomputable def ambientBaseEquiv
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c) :
    sectionAmbient (S ⊗[R] B) (fun i ↦ algebraMap R B (f i))
      (baseChangeDatum.{u, v, x, w} S B f X) ≃ₗ[B] B ⊗[R] sectionAmbient S f X :=
  LinearEquiv.prodCongr (genericBaseEquiv S B X.generic)
      ((LinearEquiv.piCongrRight fun i ↦ awayTensorEquiv B (f i) (X.localPiece i)) ≪≫ₗ
        (TensorProduct.piRight R B B _).symm) ≪≫ₗ
    (TensorProduct.prodRight R B B _ _).symm

private noncomputable def relationsBaseEquiv
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c) :
    sectionRelations (S ⊗[R] B) (fun i ↦ algebraMap R B (f i))
      (baseChangeDatum.{u, v, x, w} S B f X) ≃ₗ[B] B ⊗[R] sectionRelations S f X := by
  let e i : (S ⊗[R] B) ⊗[B] FormalGlueing.restrictFromAway
      (fun i ↦ algebraMap R B (f i)) i ((baseChangeDatum.{u, v, x, w} S B f X).localPiece i) ≃ₗ[B]
        B ⊗[R] (S ⊗[R] FormalGlueing.restrictFromAway f i (X.localPiece i)) :=
    (genericLocalTensorEquiv S B (f i) (X.localPiece i)).restrictScalars B ≪≫ₗ
      pushoutTensorEquiv R S B (S ⊗[R] B) _
  exact LinearEquiv.prodCongr
    ((LinearEquiv.piCongrRight e) ≪≫ₗ (TensorProduct.piRight R B B _).symm)
    ((LinearEquiv.piCongrRight fun i ↦
      (LinearEquiv.piCongrRight fun j ↦ localOverlapEquiv B f j (X.localPiece j) {i}) ≪≫ₗ
        (TensorProduct.piRight R B B _).symm) ≪≫ₗ
      (TensorProduct.piRight R B B _).symm) ≪≫ₗ
    (TensorProduct.prodRight R B B _ _).symm


private noncomputable def flatKernelEquiv
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    {M N L K : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module B L] [AddCommGroup K] [Module B K]
    (g : M →ₗ[R] N) (g' : L →ₗ[B] K)
    (e : L ≃ₗ[B] B ⊗[R] M) (d : K ≃ₗ[B] B ⊗[R] N)
    (h : ∀ z, d (g' z) = g.baseChange B (e z)) :
    B ⊗[R] g.ker ≃ₗ[B] g'.ker := by
  let k : (g.baseChange B).ker ≃ₗ[B] g'.ker :=
    { toFun z := ⟨e.symm z, by
        apply d.injective
        rw [map_zero, h, LinearEquiv.apply_symm_apply]
        exact z.2⟩
      invFun z := ⟨e z, by
        change g.baseChange B (e z) = 0
        rw [← h, z.2, map_zero]⟩
      left_inv z := by ext; exact e.apply_symm_apply z
      right_inv z := by ext; exact e.symm_apply_apply z
      map_add' z y := by ext; exact map_add e.symm _ _
      map_smul' a z := by ext; exact map_smul e.symm _ _ }
  exact g.tensorKerEquiv B B ≪≫ₗ k

private theorem flatKernelEquiv_tmul
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    {M N L K : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module B L] [AddCommGroup K] [Module B K]
    (g : M →ₗ[R] N) (g' : L →ₗ[B] K)
    (e : L ≃ₗ[B] B ⊗[R] M) (d : K ≃ₗ[B] B ⊗[R] N)
    (h : ∀ z, d (g' z) = g.baseChange B (e z)) (b : B) (z : g.ker) :
    (flatKernelEquiv B g g' e d h (b ⊗ₜ[R] z)).1 = e.symm (b ⊗ₜ[R] z.1) := by
  show e.symm ((g.tensorKerEquiv B B (b ⊗ₜ[R] z)).1) = _
  rw [LinearMap.tensorKerEquiv_apply, LinearMap.tensorKer_tmul]

private theorem ambientBaseEquiv_symm_tmul
    {R : Type u} (S : Type v) (B : Type x)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {r : ℕ} (f : Fin r → R)
    {c : FormalGlueing.LocalizationComparisons.{u, max u v x w} f}
    (X : FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} S f c)
    (b : B) (z : sectionAmbient S f X) :
    (ambientBaseEquiv.{u, v, x, w} S B f X).symm (b ⊗ₜ[R] z) =
      ((genericBaseEquiv S B X.generic).symm (b ⊗ₜ[R] z.1),
        fun i ↦ (awayTensorEquiv B (f i) (X.localPiece i)).symm (b ⊗ₜ[R] z.2 i)) := by
  simp only [ambientBaseEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    TensorProduct.prodRight_tmul, LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
    LinearEquiv.piCongrRight_symm]
  rfl

private noncomputable def canonicalGenericBaseEquiv
    {R : Type*} (S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (M : ModuleCat R) :
    (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)).obj
        (ModuleCat.of S (S ⊗[R] M)) ≃ₗ[S ⊗[R] B]
      (S ⊗[R] B) ⊗[B] (ModuleCat.extendScalars (algebraMap R B)).obj M :=
  extendScalarsEquiv (S ⊗[R] B) (ModuleCat.of S (S ⊗[R] M)) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R S (S ⊗[R] B) (S ⊗[R] B) M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R B (S ⊗[R] B) (S ⊗[R] B) M).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B))
      (extendScalarsEquiv B M).symm

private noncomputable def canonicalLocalBaseEquiv
    {R : Type*} (B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (a : R) (M : ModuleCat R) :
    (ModuleCat.extendScalars (awayMap B a)).obj
        (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) ≃ₗ[Localization.Away
          (algebraMap R B a)]
      LocalizedModule.Away (algebraMap R B a) ((ModuleCat.extendScalars (algebraMap R B)).obj M) :=
        by
  let N := (ModuleCat.extendScalars (awayMap B a)).obj
    (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M))
  letI : Module B N := Module.compHom N (algebraMap B (Localization.Away (algebraMap R B a)))
  letI : IsScalarTower B (Localization.Away (algebraMap R B a)) N := restrictScalars_tower N
  let e : N ≃ₗ[B]
      LocalizedModule.Away (algebraMap R B a) ((ModuleCat.extendScalars (algebraMap R B)).obj M) :=
    awayTensorEquiv B a (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M)) ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (FormalGlueing.restrictModuleOfEquiv (Localization.Away a) (LocalizedModule.Away a M)) ≪≫ₗ
      (awayLocalizationBaseChange B a M).symm ≪≫ₗ
      localizedEquiv (Submonoid.powers (algebraMap R B a)) (extendScalarsEquiv B M).symm
  exact e.extendScalarsOfIsLocalization (Submonoid.powers (algebraMap R B a))
    (Localization.Away (algebraMap R B a))


private theorem genericLocalTensorEquiv_map
    {baseRing : Type*} (targetRing extensionRing : Type*)
    [CommRing baseRing] [CommRing targetRing] [CommRing extensionRing]
    [Algebra baseRing targetRing] [Algebra baseRing extensionRing]
    (parameter : baseRing) {source target : ModuleCat (Localization.Away parameter)}
    (morphism : source ⟶ target) (element) :
    genericLocalTensorEquiv targetRing extensionRing parameter target
        (TensorProduct.map LinearMap.id
          (((ModuleCat.restrictScalars
            (algebraMap extensionRing (Localization.Away (algebraMap baseRing extensionRing
              parameter)))).map
            ((ModuleCat.extendScalars (awayMap extensionRing parameter)).map morphism)).hom)
              element) =
      TensorProduct.map LinearMap.id
        ((((ModuleCat.restrictScalars (algebraMap baseRing (Localization.Away parameter))).map
          morphism).hom).baseChange targetRing)
        (genericLocalTensorEquiv targetRing extensionRing parameter source element) := by
  exact tensorTransportEquiv_naturality baseRing targetRing extensionRing
    (targetRing ⊗[baseRing] extensionRing)
    (awayTensorEquiv extensionRing parameter source) (awayTensorEquiv extensionRing parameter
      target)
    (((ModuleCat.restrictScalars (algebraMap baseRing (Localization.Away parameter))).map
      morphism).hom)
    (((ModuleCat.restrictScalars
      (algebraMap extensionRing (Localization.Away (algebraMap baseRing extensionRing
        parameter)))).map
      ((ModuleCat.extendScalars (awayMap extensionRing parameter)).map morphism)).hom)
    (awayTensorEquiv_naturality extensionRing parameter morphism) element

private theorem localOverlapEquiv_mk_tensor
    {baseRing : Type*} (extensionRing : Type*) [CommRing baseRing] [CommRing extensionRing]
    [Algebra baseRing extensionRing] {rank : ℕ} (family : Fin rank → baseRing)
    (index : Fin rank) (source : ModuleCat (Localization.Away (family index)))
    (indices : Finset (Fin rank)) (coefficient : extensionRing)
    (element : (ModuleCat.restrictScalars (algebraMap baseRing (Localization.Away (family
      index)))).obj source) :
    localOverlapEquiv extensionRing family index source indices
      (LocalizedModule.mkLinearMap (Cech.cechSub (fun index => algebraMap baseRing extensionRing
        (family index)) indices) _
        ((awayTensorEquiv extensionRing (family index) source).symm (coefficient ⊗ₜ[baseRing]
          element))) =
      coefficient ⊗ₜ[baseRing] LocalizedModule.mkLinearMap (Cech.cechSub family indices) _ element
        := by
  dsimp only [localOverlapEquiv, LinearEquiv.trans_apply]
  rw [localizedEquiv_mk, LinearEquiv.apply_symm_apply, cechBaseChangeEquiv_mk]

private theorem awayTensorEquiv_symm_map
    {baseRing : Type*} (extensionRing : Type*) [CommRing baseRing] [CommRing extensionRing]
    [Algebra baseRing extensionRing] (parameter : baseRing)
    {source target : ModuleCat (Localization.Away parameter)} (morphism : source ⟶ target)
    (coefficient : extensionRing)
    (element : (ModuleCat.restrictScalars (algebraMap baseRing (Localization.Away parameter))).obj
      source) :
    (ModuleCat.extendScalars (awayMap extensionRing parameter)).map morphism
      ((awayTensorEquiv extensionRing parameter source).symm (coefficient ⊗ₜ[baseRing] element)) =
      (awayTensorEquiv extensionRing parameter target).symm (coefficient ⊗ₜ[baseRing] morphism
        element) := by
  apply (awayTensorEquiv extensionRing parameter target).injective
  rw [awayTensorEquiv_naturality, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

private noncomputable def baseChangeMap
    {baseRing : Type u} (targetRing : Type v) (extensionRing : Type x)
    [CommRing baseRing] [CommRing targetRing] [CommRing extensionRing]
    [Algebra baseRing targetRing] [Algebra baseRing extensionRing]
    {rank : ℕ} (family : Fin rank → baseRing)
    {comparisons : FormalGlueing.LocalizationComparisons.{u, max u v x w} family}
    {source target :
      FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} targetRing family comparisons}
    (morphism : FormalGlueing.ModuleGlueingMap targetRing family comparisons source target) :
    FormalGlueing.ModuleGlueingMap (targetRing ⊗[baseRing] extensionRing)
      (fun index => algebraMap baseRing extensionRing (family index))
      (FormalGlueing.localizationComparisons _)
      (baseChangeDatum.{u, v, x, w} targetRing extensionRing family source)
      (baseChangeDatum.{u, v, x, w} targetRing extensionRing family target) where
  generic := (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeftRingHom : targetRing →+* targetRing ⊗[baseRing]
      extensionRing)).map
    morphism.generic
  localPiece index := (ModuleCat.extendScalars (awayMap extensionRing (family index))).map
    (morphism.localPiece index)
  alpha_compatibility index element := by
    change baseChangeAlpha targetRing extensionRing family target index
        (LocalizedModule.mkLinearMap _ _
          ((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom : targetRing →+* targetRing ⊗[baseRing]
              extensionRing)).map
            morphism.generic element)) =
      TensorProduct.map LinearMap.id
        (((ModuleCat.restrictScalars
          (algebraMap extensionRing (Localization.Away (algebraMap baseRing extensionRing (family
            index))))).map
          ((ModuleCat.extendScalars (awayMap extensionRing (family index))).map
            (morphism.localPiece index))).hom)
        (baseChangeAlpha targetRing extensionRing family source index (LocalizedModule.mkLinearMap _
          _ element))
    induction element using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add left right left_eq right_eq =>
      simpa only [map_add] using congrArg₂ (· + ·) left_eq right_eq
    | tmul coefficient original =>
      apply (genericLocalTensorEquiv targetRing extensionRing (family index) (target.localPiece
        index)).injective
      rw [baseChangeAlpha_commutes, genericLocalTensorEquiv_map, baseChangeAlpha_commutes]
      change TensorProduct.map LinearMap.id (target.alpha index).toLinearMap
          (genericLocalizationEquiv targetRing extensionRing (family index) target.generic
            (LocalizedModule.mkLinearMap _ _
              (coefficient ⊗ₜ[targetRing, Algebra.TensorProduct.includeLeftRingHom] morphism.generic
                original))) = _
      rw [genericLocalizationEquiv_mk, genericLocalizationEquiv_mk]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe]
      convert congrArg (fun value =>
        (show targetRing ⊗[baseRing] extensionRing from coefficient) ⊗ₜ[targetRing] value)
        (morphism.alpha_compatibility index original) using 1
      simp only [LinearMap.baseChange_eq_ltensor]
      rfl
  alphaIJ_compatibility index otherIndex element := by
    change baseChangeAlphaIJ targetRing extensionRing family target index otherIndex
        (LocalizedModule.mkLinearMap _ _
          ((ModuleCat.extendScalars (awayMap extensionRing (family index))).map
            (morphism.localPiece index) element)) =
      FormalGlueing.localizedMap
        (fun index => algebraMap baseRing extensionRing (family index)) {index}
        (((ModuleCat.restrictScalars
          (algebraMap extensionRing (Localization.Away (algebraMap baseRing extensionRing (family
            otherIndex))))).map
          ((ModuleCat.extendScalars (awayMap extensionRing (family otherIndex))).map
            (morphism.localPiece otherIndex))).hom)
        (baseChangeAlphaIJ targetRing extensionRing family source index otherIndex
          (LocalizedModule.mkLinearMap _ _ element))
    obtain ⟨value, rfl⟩ :=
      (awayTensorEquiv extensionRing (family index) (source.localPiece index)).symm.surjective
        element
    induction value using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add left right left_eq right_eq =>
      simpa only [map_add] using congrArg₂ (· + ·) left_eq right_eq
    | tmul coefficient original =>
      apply (localOverlapEquiv extensionRing family otherIndex (target.localPiece otherIndex)
        {index}).injective
      rw [baseChangeAlphaIJ_commutes, localOverlapEquiv_naturality, baseChangeAlphaIJ_commutes,
        awayTensorEquiv_symm_map, localOverlapEquiv_mk_tensor, localOverlapEquiv_mk_tensor]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
        LinearMap.baseChange_tmul]
      exact congrArg (fun value => coefficient ⊗ₜ[baseRing] value)
        (morphism.alphaIJ_compatibility index otherIndex original)

private noncomputable def baseChangeFunctor
    {baseRing : Type u} (targetRing : Type v) (extensionRing : Type x)
    [CommRing baseRing] [CommRing targetRing] [CommRing extensionRing]
    [Algebra baseRing targetRing] [Algebra baseRing extensionRing]
    {rank : ℕ} (family : Fin rank → baseRing)
    (comparisons : FormalGlueing.LocalizationComparisons.{u, max u v x w} family) :
    letI := FormalGlueing.moduleGlueingCategory.{u, v, max u v x w} targetRing family comparisons
    letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
      (targetRing ⊗[baseRing] extensionRing)
      (fun index => algebraMap baseRing extensionRing (family index))
      (FormalGlueing.localizationComparisons _)
    FormalGlueing.ModuleGlueingDatum.{u, v, max u v x w} targetRing family comparisons ⥤
      FormalGlueing.ModuleGlueingDatum.{x, max v x, max u v x w}
        (targetRing ⊗[baseRing] extensionRing)
        (fun index => algebraMap baseRing extensionRing (family index))
        (FormalGlueing.localizationComparisons _) := by
  letI := FormalGlueing.moduleGlueingCategory.{u, v, max u v x w} targetRing family comparisons
  letI := FormalGlueing.moduleGlueingCategory.{x, max v x, max u v x w}
    (targetRing ⊗[baseRing] extensionRing)
    (fun index => algebraMap baseRing extensionRing (family index))
    (FormalGlueing.localizationComparisons _)
  exact
    { obj := baseChangeDatum.{u, v, x, w} targetRing extensionRing family
      map := baseChangeMap.{u, v, x, w} targetRing extensionRing family
      map_id source := by
        apply FormalGlueing.ModuleGlueingMap.ext
        · exact (ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom :
              targetRing →+* targetRing ⊗[baseRing] extensionRing)).map_id source.generic
        · funext index
          exact (ModuleCat.extendScalars (awayMap extensionRing (family index))).map_id
            (source.localPiece index)
      map_comp first second := by
        apply FormalGlueing.ModuleGlueingMap.ext
        · exact (ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom :
              targetRing →+* targetRing ⊗[baseRing] extensionRing)).map_comp
            first.generic second.generic
        · funext index
          exact (ModuleCat.extendScalars (awayMap extensionRing (family index))).map_comp
            (first.localPiece index) (second.localPiece index) }

end FormalGlueing

end
