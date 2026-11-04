module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksFrontier.RingTheory.Ideal.Quotient.Small
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Logic.Small.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.LocalProperties.Injective
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Essential
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.RingTheory.Dualizing.Complex.More
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull

/-!
# Injective modules under flat base change

Let `A → B` be a flat map of Noetherian rings. If, at every prime `q` of `B`, the extension to
`Localization.AtPrime q` of the contraction of `q` to `A` agrees with the extension of `q`
itself, then base change from `A` to `B` preserves injective modules.

## Main results

* `Module.tensorProduct_injective_of_flat_of_map_comap_eq`: under the stated condition on prime
  ideals, the base change of an injective module is injective.

## Implementation notes

The equality of extended ideals is stated inside the canonical localization
`Localization.AtPrime q`. We write the base change as `B ⊗[A] I`, canonically isomorphic to the
source's `I ⊗[A] B`, so that its `B`-module structure is directly available.

The proof reduces to the case of an indecomposable injective, where the module is the injective
hull of a residue field; localizing at the corresponding prime and using Baer's criterion
transfers injectivity across the flat map. The final step moves all three of the ring, the
target ring and the module into a single universe by universe lifting, which is why the
statement is universe-polymorphic in all three.

## References

* [Stacks Project, Tag 0E4F](https://stacks.math.columbia.edu/tag/0E4F)
-/

@[expose] public section

universe u v w

namespace Module

open CategoryTheory
open scoped DirectSum TensorProduct

/-- **A Noetherian local ring is no larger than its residue field.** The ring injects into the
product of its quotients by the powers of the maximal ideal, each of which is small over the
residue field because the maximal ideal is finitely generated. -/
public theorem small_of_small_residueField {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} (IsLocalRing.ResidueField R)] : Small.{v} R := by
  let m := IsLocalRing.maximalIdeal R
  let : Small.{v} (R ⧸ m) := ‹Small.{v} (IsLocalRing.ResidueField R)›
  let (n : ℕ) : Small.{v} (R ⧸ m ^ n) :=
    Ideal.small_quotient_pow m (IsNoetherian.noetherian m) n
  apply small_of_injective.{v} (f := fun r : R => fun n : ℕ => Ideal.Quotient.mk (m ^ n) r)
  intro x y h
  apply sub_eq_zero.mp
  have hxy : x - y ∈ ⨅ n : ℕ, m ^ n :=
    Ideal.mem_iInf.mpr fun n => Ideal.Quotient.eq.mp (congrFun h n)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing m (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hxy

private theorem tensorProduct_injective_of_indecomposable
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    (H : ∀ (E : ModuleCat.{w} A) [CategoryTheory.Injective E],
      CategoryTheory.Indecomposable E → Module.Injective B (TensorProduct A B E))
    (I : Type w) [AddCommGroup I] [Module A I] [Module.Injective A I] :
    Module.Injective B (TensorProduct A B I) := by
  classical
  let IC := ModuleCat.of A I
  let : CategoryTheory.Injective IC :=
    (Module.injective_iff_injective_object A I).mp inferInstance
  obtain ⟨ι, E, e, hE, hInd⟩ := exists_iso_directSum_of_injective A IC
  let (i : ι) : CategoryTheory.Injective (E i) := hE i
  let (i : ι) : Module.Injective B (TensorProduct A B (E i)) := H (E i) (hInd i)
  let : Module.Injective B (⨁ i, TensorProduct A B (E i)) :=
    directSum_injective B (fun i => TensorProduct A B (E i))
  exact Module.injective_of_linearEquiv (M := ⨁ i, TensorProduct A B (E i))
    ((LinearEquiv.baseChange A B I (⨁ i, E i) e.toLinearEquiv).trans
      (TensorProduct.directSumRight A B B (fun i => E i))).symm ‹_›

private theorem isUnit_smul_of_residueField_injectiveHull
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {K E : ModuleCat.{v} R} (e : K ≃ₗ[R] p.ResidueField)
    (i : K ⟶ E) [Mono i] (hi : IsInjectiveHull i)
    (s : p.primeCompl) : IsUnit (algebraMap R (Module.End R E) s) := by
  let a : p.ResidueFieldˣ := Units.mk0 (algebraMap R p.ResidueField s)
    (fun h => s.property (Ideal.algebraMap_residueField_eq_zero.mp h))
  let eK : K ≃ₗ[R] K :=
    (e.trans ((LinearEquiv.smulOfUnit a).restrictScalars R)).trans e.symm
  have heK (x : K) : eK x = (s : R) • x := by
    apply e.injective
    simp [eK, a, LinearEquiv.smulOfUnit, Algebra.smul_def]
  let f : Module.End R E := algebraMap R (Module.End R E) s
  have hf : IsIso (ModuleCat.ofHom f) :=
    isIso_of_isInjectiveHull_of_extends_iso
      i i hi hi eK.toModuleIso (ModuleCat.ofHom f) (by
        ext x
        show (s : R) • i.hom x = i.hom (eK x)
        rw [heK, map_smul])
  let := hf
  exact (Module.End.isUnit_iff f).mpr (asIso (ModuleCat.ofHom f)).toLinearEquiv.bijective

private theorem exists_localization_module_of_residueField_injectiveHull
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {K E : ModuleCat.{v} R} (e : K ≃ₗ[R] p.ResidueField)
    (i : K ⟶ E) [Mono i] (hi : IsInjectiveHull i) :
    ∃ _ : Module (Localization.AtPrime p) E,
      IsScalarTower R (Localization.AtPrime p) E := by
  let : IsLocalizedModule p.primeCompl (LinearMap.id : E →ₗ[R] E) :=
    { map_units := isUnit_smul_of_residueField_injectiveHull p e i hi
      surj x := ⟨⟨x, 1⟩, by simp⟩
      exists_of_eq h := ⟨1, by simpa using h⟩ }
  let : Module (Localization.AtPrime p) E :=
    IsLocalizedModule.module p.primeCompl (LinearMap.id : E →ₗ[R] E)
  exact ⟨inferInstance,
    IsLocalizedModule.isScalarTower_module p.primeCompl (LinearMap.id : E →ₗ[R] E)⟩

private theorem essential_range_multiple
    {R : Type u} {E K : Type v} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup K] [Module R K]
    (i : ModuleCat.of R K ⟶ ModuleCat.of R E) [Mono i]
    (hi : IsEssentialMono i) :
    ∀ x : E, x ≠ 0 → ∃ r : R, r • x ∈ LinearMap.range i.hom ∧ r • x ≠ 0 := by
  intro x hx
  let e := ModuleCat.subobjectModule (ModuleCat.of R E)
  have hImage : e (Subobject.mk i) = LinearMap.range i.hom := by
    show LinearMap.range (Subobject.mk i).arrow.hom = LinearMap.range i.hom
    rw [← ModuleCat.hom_ext_iff.mp (Subobject.underlyingIso_hom_comp_eq_mk i),
      ModuleCat.hom_comp]
    exact LinearEquiv.range_comp (Subobject.underlyingIso i).toLinearEquiv i.hom
  let P : Submodule R E := R ∙ x
  have hP : P ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  have hPcat : e.symm P ≠ ⊥ := by
    intro hz
    apply hP
    have hz' := congrArg e hz
    rwa [e.apply_symm_apply, e.map_bot] at hz'
  have hmeet := hi (e.symm P) hPcat
  have hmeet' : P ⊓ LinearMap.range i.hom ≠ ⊥ := by
    intro hz
    apply hmeet
    apply e.injective
    rwa [OrderIso.map_inf, e.apply_symm_apply, hImage, e.map_bot]
  obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hmeet')
  have hyP : y.1 ∈ P := (Submodule.mem_inf.mp y.2).1
  have hyI : y.1 ∈ LinearMap.range i.hom := (Submodule.mem_inf.mp y.2).2
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyP
  have hy0 : y.1 ≠ 0 := fun hz => hy (Subtype.ext hz)
  exact ⟨r, by simpa [hr] using hyI, by simpa [hr] using hy0⟩

private theorem injective_over_localization
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S]
    (E : Type v) [AddCommGroup E] [Module R E] [Module S E]
    [IsScalarTower R S E] [Module.Injective R E] : Module.Injective S E := by
  constructor
  intro X Y _ _ _ _ f hf g
  let : Module R X := Module.compHom X (algebraMap R S)
  let : Module R Y := Module.compHom Y (algebraMap R S)
  let : IsScalarTower R S X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R S Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨h, hh⟩ := Module.Injective.out (f.restrictScalars R) hf (g.restrictScalars R)
  exact ⟨h.extendScalarsOfIsLocalization T S, hh⟩

private theorem baer_restrictScalars_of_flat
    {R : Type u} {S : Type v} {E : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
    (hE : Module.Baer S E) : Module.Baer R E := by
  intro J g
  let f : TensorProduct R S J →ₗ[S] S :=
    (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp (J.subtype.baseChange S)
  have hf : Function.Injective f :=
    (TensorProduct.AlgebraTensorModule.rid R S S).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap J.subtype Subtype.val_injective)
  obtain ⟨h, hh⟩ := hE.extension_property f hf (g.liftBaseChange S)
  refine ⟨(h.restrictScalars R).comp (Algebra.linearMap R S), fun x hx => ?_⟩
  have hhx := LinearMap.congr_fun hh (1 ⊗ₜ[R] (⟨x, hx⟩ : J))
  show h (algebraMap R S x) = _
  rw [← mul_one (algebraMap R S x), ← smul_eq_mul, h.map_smul,
    IsScalarTower.algebraMap_smul]
  simpa [f] using hhx

private theorem baer_of_residueField_injectiveHull
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] {K E : ModuleCat.{v} R}
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hi : IsInjectiveHull i) : Module.Baer R E := by
  obtain ⟨mE, tE⟩ := exists_localization_module_of_residueField_injectiveHull p e i hi
  let := mE
  let := tE
  let : Module.Injective R E := (Module.injective_iff_injective_object R E).mpr hi.1
  let : Module.Injective (Localization.AtPrime p) E := injective_over_localization p.primeCompl E
  let : Small.{v} p.ResidueField := small_of_surjective e.surjective
  let : Small.{v} (Localization.AtPrime p) := small_of_small_residueField
  exact baer_restrictScalars_of_flat (S := Localization.AtPrime p)
    (Module.Baer.of_injective inferInstance)

private theorem baer_of_injective_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Type v) [AddCommGroup I] [Module R I] [Module.Injective R I] :
    Module.Baer R I := by
  classical
  let IC := ModuleCat.of R I
  let : CategoryTheory.Injective IC :=
    (Module.injective_iff_injective_object R I).mp inferInstance
  obtain ⟨ι, E, e, hE, hInd⟩ := exists_iso_directSum_of_injective R IC
  have hB (j : ι) : Module.Baer R (E j) := by
    let : CategoryTheory.Injective (E j) := hE j
    obtain ⟨p, hp, K, eK, i, hi, hHull⟩ :=
      exists_residueField_injectiveHull R (E j) (hInd j)
    let := hp
    let := hi
    exact baer_of_residueField_injectiveHull p eK i hHull
  let (j : ι) : Module.Injective R (ULift.{u} (E j)) :=
    ((hB j).of_equiv ULift.moduleEquiv.symm).injective
  let : Module.Injective R (⨁ j, ULift.{u} (E j)) :=
    directSum_injective R (fun j => ULift.{u} (E j))
  exact (Module.Baer.of_injective (inferInstance : Module.Injective R
    (⨁ j, ULift.{u} (E j)))).of_equiv
    ((DirectSum.congrLinearEquiv fun j => (ULift.moduleEquiv : ULift.{u} (E j) ≃ₗ[R] E j)).trans
      e.toLinearEquiv.symm)

private theorem localized_residueField_injectiveHull
    {R E : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R p.ResidueField ⟶ ModuleCat.of R E) [Mono i]
    (hi : IsInjectiveHull i) :
    ∃ (j : ModuleCat.of (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) ⟶
      ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl E)),
      ∃ (hj : Mono j), letI : Mono j := hj; IsInjectiveHull j := by
  classical
  let Rp := Localization.AtPrime p
  let K := p.ResidueField
  let EL := LocalizedModule p.primeCompl E
  let : Module Rp K := inferInstance
  let : IsScalarTower R Rp K := inferInstance
  let fK : K →ₗ[R] K := LinearMap.id
  let : IsLocalizedModule p.primeCompl fK := isLocalizedModule_id p.primeCompl K Rp
  let eK : K ≃ₗ[Rp] LocalizedModule p.primeCompl K :=
    IsLocalizedModule.mapEquiv p.primeCompl fK
      (LocalizedModule.mkLinearMap p.primeCompl K) Rp (LinearEquiv.refl R K)
  have heK (z : K) : eK z = LocalizedModule.mkLinearMap p.primeCompl K z := by
    rw [IsLocalizedModule.mapEquiv_apply]
    show ((IsLocalizedModule.map p.primeCompl fK
      (LocalizedModule.mkLinearMap p.primeCompl K) LinearMap.id) (fK z)) = _
    rw [IsLocalizedModule.map_apply]
    simp
  let : Module.Injective R E := (Module.injective_iff_injective_object R E).mpr hi.1
  have hELinj : Module.Injective Rp EL :=
    Module.injective_of_isLocalizedModule p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl E)
  have hinj : Function.Injective i.hom := (ModuleCat.mono_iff_injective i).mp inferInstance
  let iL : LocalizedModule p.primeCompl K →ₗ[Rp] EL := LocalizedModule.map p.primeCompl i.hom
  let jL : K →ₗ[Rp] EL := iL.comp eK.toLinearMap
  have hjL : Function.Injective jL :=
    (LocalizedModule.map_injective p.primeCompl i.hom hinj).comp eK.injective
  let j : ModuleCat.of Rp (IsLocalRing.ResidueField Rp) ⟶ ModuleCat.of Rp EL :=
    ModuleCat.ofHom jL
  have hj : Mono j := (ModuleCat.mono_iff_injective j).mpr hjL
  let : Mono j := hj
  have hEss : IsEssentialMono j := by
    let r : ModuleCat.of Rp (LinearMap.range jL) ⟶ ModuleCat.of Rp EL :=
      ModuleCat.ofHom (LinearMap.range jL).subtype
    let : Mono r := (ModuleCat.mono_iff_injective r).mpr Subtype.val_injective
    let eRange : K ≃ₗ[Rp] LinearMap.range jL := LinearEquiv.ofInjective jL hjL
    have heq : ModuleCat.ofHom jL = ModuleCat.ofHom eRange.toLinearMap ≫ r := by
      ext x
      simp [r, eRange]
    have hmk : Subobject.mk j = Subobject.mk r :=
      Subobject.mk_eq_mk_of_comm _ _ eRange.toModuleIso heq.symm
    show ∀ q : Subobject (ModuleCat.of Rp EL), q ≠ ⊥ → q ⊓ Subobject.mk j ≠ ⊥
    rw [hmk]
    refine (isEssentialMono_subtype_iff (R := Rp)
      (N := ModuleCat.of Rp EL) (LinearMap.range jL)).2 fun x hx => ?_
    have hK : Function.Injective (LocalizedModule.mkLinearMap p.primeCompl K) :=
      fun z w h => eK.injective ((heK z).trans (h.trans (heK w).symm))
    obtain ⟨c, ⟨w, hw⟩, hc⟩ : ∃ r : Rp, r • x ∈ LinearMap.range iL ∧ r • x ≠ 0 := by
      obtain ⟨⟨y, s⟩, hs⟩ := IsLocalizedModule.surj p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl E) x
      have hy : y ≠ 0 := by
        rintro rfl
        simp only [map_zero] at hs
        exact hx ((IsLocalizedModule.smul_inj
          (LocalizedModule.mkLinearMap p.primeCompl E) s x 0).mp (by simpa using hs))
      obtain ⟨a, ⟨z, hz⟩, han⟩ := essential_range_multiple i hi.2 y hy
      have hz' : (algebraMap R Rp a) • (algebraMap R Rp s) • x =
          iL (LocalizedModule.mkLinearMap p.primeCompl K z) := by
        calc
          (algebraMap R Rp a) • (algebraMap R Rp s) • x =
              (algebraMap R Rp a) • LocalizedModule.mkLinearMap p.primeCompl E y := by
                rw [show (algebraMap R Rp s) • x =
                  LocalizedModule.mkLinearMap p.primeCompl E y by
                    simpa [Submonoid.smul_def] using hs]
          _ = LocalizedModule.mkLinearMap p.primeCompl E (a • y) := by
                rw [IsScalarTower.algebraMap_smul, ← map_smul]
          _ = LocalizedModule.mkLinearMap p.primeCompl E (i.hom z) := by rw [hz]
          _ = iL (LocalizedModule.mkLinearMap p.primeCompl K z) := by
                show LocalizedModule.mk (i.hom z) 1 =
                  LocalizedModule.map p.primeCompl i.hom (LocalizedModule.mk z 1)
                rw [LocalizedModule.map_mk]
      have hx' : (algebraMap R Rp a) • x ∈ LinearMap.range iL := by
        apply (Submodule.smul_mem_iff_of_isUnit (LinearMap.range iL)
          (IsLocalization.map_units Rp s)).1
        refine ⟨LocalizedModule.mkLinearMap p.primeCompl K z, ?_⟩
        calc
          iL (LocalizedModule.mkLinearMap p.primeCompl K z) =
              (algebraMap R Rp a) • (algebraMap R Rp s) • x := hz'.symm
          _ = (algebraMap R Rp s) • (algebraMap R Rp a) • x := by
                rw [← mul_smul, mul_comm, mul_smul]
      refine ⟨algebraMap R Rp a, hx', fun hx0 => han ?_⟩
      have hloc : iL (LocalizedModule.mkLinearMap p.primeCompl K z) = 0 := by
        rw [← hz', ← mul_smul, mul_comm, mul_smul, hx0, smul_zero]
      have hzL : LocalizedModule.mkLinearMap p.primeCompl K z = 0 :=
        LocalizedModule.map_injective p.primeCompl i.hom hinj (hloc.trans (map_zero _).symm)
      have hz0 : z = 0 := hK (by rw [hzL, map_zero])
      simpa [hz0] using hz.symm
    exact ⟨c, ⟨eK.symm w, (congrArg iL (eK.apply_symm_apply w)).trans hw⟩, hc⟩
  exact ⟨j, hj, (Module.injective_iff_injective_object Rp EL).mp hELinj, hEss⟩

private theorem tensorProduct_subsingleton_of_unit_of_torsion
    {A : Type u} {B : Type v} {E : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] (a : A) (ha : IsUnit (algebraMap A B a))
    (hE : ∀ x : E, ∃ n : ℕ, a ^ n • x = 0) : Subsingleton (B ⊗[A] E) := by
  apply subsingleton_of_forall_eq 0
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | add x y hx hy => simp [hx, hy]
  | tmul b x =>
    obtain ⟨n, hn⟩ := hE x
    apply (ha.pow n).smul_left_cancel.mp
    rw [smul_zero, ← map_pow, IsScalarTower.algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul, hn, TensorProduct.tmul_zero]

private theorem pow_smul_eq_zero_of_residueFieldHull
    {A E : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : IsInjectiveHull i) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (x : E) : ∃ n : ℕ, a ^ n • x = 0 := by
  have hmono : Monotone (Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E)) :=
    fun m n h => Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.add_le_add_right h 1) _
  have hx : x ∈ ⨆ n, Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n := by
    rw [Dualizing.iSup_maximalIdealPowTorsion_eq_top A _ _ (LinearEquiv.refl _ _) i hi]
    trivial
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hx
  exact ⟨n + 1, ((Submodule.mem_torsionBySet_iff _ _).mp hn) ⟨a ^ (n + 1), Ideal.pow_mem_pow ha _⟩⟩

private theorem map_comap_eq_of_localization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
        (Ideal.comap (algebraMap A B) q) = IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (q : Ideal B) [q.IsPrime] (C : Type w) [CommRing C] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsLocalization.AtPrime C q] [IsLocalRing C] :
    Ideal.map (algebraMap A C) (Ideal.comap (algebraMap A B) q) =
      IsLocalRing.maximalIdeal C := by
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) C
  have he : e.toRingHom.comp (algebraMap A (Localization.AtPrime q)) = algebraMap A C := by
    ext x
    simp [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q),
      ← IsScalarTower.algebraMap_apply A B C]
  have h := congrArg (Ideal.map e.toRingHom) (hprime q)
  rw [Ideal.map_map, he] at h
  exact h.trans (IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv)

private theorem map_comap_eq_of_localizations
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
        (Ideal.comap (algebraMap A B) q) = IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (M : Submonoid A) (N : Submonoid B)
    (A₁ B₁ : Type w) [CommRing A₁] [CommRing B₁]
    [Algebra A A₁] [Algebra B B₁] [Algebra A B₁] [Algebra A₁ B₁]
    [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [IsLocalization M A₁] [IsLocalization N B₁]
    (q : Ideal B₁) [q.IsPrime] :
    Ideal.map (algebraMap A₁ (Localization.AtPrime q))
      (Ideal.comap (algebraMap A₁ B₁) q) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  let C := Localization.AtPrime q
  let q₀ := Ideal.comap (algebraMap B B₁) q
  let : IsLocalization.AtPrime C q₀ :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N C q
  have h := map_comap_eq_of_localization hprime q₀ C
  have hc : Ideal.comap (algebraMap A B) q₀ =
      Ideal.comap (algebraMap A A₁) (Ideal.comap (algebraMap A₁ B₁) q) := by
    simp only [q₀, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A B B₁,
      ← IsScalarTower.algebraMap_eq A A₁ B₁]
  rw [hc, IsScalarTower.algebraMap_eq A A₁ C, ← Ideal.map_map] at h
  rwa [IsLocalization.map_under M] at h

private theorem tensorProduct_injective_of_local_residueFieldHull
    {A B E : Type u} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    [AddCommGroup E] [Module A E]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
        (Ideal.comap (algebraMap A B) q) = IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : IsInjectiveHull i) : Module.Injective B (B ⊗[A] E) := by
  apply Module.injective_of_localization_maximal
  intro q hq
  let f := TensorProduct.AlgebraTensorModule.rTensor A E
    (Algebra.linearMap B (Localization.AtPrime q))
  let e := IsLocalizedModule.mapEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl (B ⊗[A] E)) f
    (Localization.AtPrime q) (LinearEquiv.refl B (B ⊗[A] E))
  have hlocal : Module.Injective (Localization.AtPrime q)
      (Localization.AtPrime q ⊗[A] E) := by
    by_cases h : Ideal.comap (algebraMap A B) q = IsLocalRing.maximalIdeal A
    · have hmax := hprime q
      rw [h] at hmax
      let : IsLocalHom (algebraMap A (Localization.AtPrime q)) :=
        ((IsLocalRing.local_hom_TFAE _).out 1 3).mpr hmax.le
      obtain ⟨j, _hj, hHull⟩ :=
        Dualizing.exists_isInjectiveHull_tensorProduct A (Localization.AtPrime q) E hmax i hi
      exact (Module.injective_iff_injective_object
        (Localization.AtPrime q) (Localization.AtPrime q ⊗[A] E)).2 hHull.1
    · have hm : ¬ IsLocalRing.maximalIdeal A ≤ Ideal.comap (algebraMap A B) q := fun hm =>
        h (le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hm)
      obtain ⟨a, ha, hqa⟩ := SetLike.not_le_iff_exists.mp hm
      let : Subsingleton (Localization.AtPrime q ⊗[A] E) :=
        tensorProduct_subsingleton_of_unit_of_torsion a
          (by rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q)]
              exact (IsLocalization.AtPrime.isUnit_to_map_iff _ q _).mpr hqa)
          (pow_smul_eq_zero_of_residueFieldHull i hi a ha)
      exact Module.Baer.injective fun J g => ⟨0, fun x hx => Subsingleton.elim _ _⟩
  exact Module.injective_of_linearEquiv e.symm hlocal

private theorem isLocalizedModule_tensorProduct_id
    {A B E : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] (p : Ideal A) [p.IsPrime]
    (hE : ∀ s : p.primeCompl, IsUnit (algebraMap A (Module.End A E) s)) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl)
      (LinearMap.id : B ⊗[A] E →ₗ[B] B ⊗[A] E) := by
  refine ⟨?_, fun x => ⟨⟨x, 1⟩, by simp⟩, fun h => ⟨1, by simpa using h⟩⟩
  intro s
  obtain ⟨a, ha, hsa⟩ := s.property
  have h := (hE ⟨a, ha⟩).map (Module.End.baseChangeHom A B E)
  convert h using 1
  ext b
  simp [← hsa, TensorProduct.smul_tmul', Algebra.smul_def]

private theorem tensorProduct_injective_of_residueFieldHull
    {A B E : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    [AddCommGroup E] [Module A E]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
        (Ideal.comap (algebraMap A B) q) = IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (p : Ideal A) [p.IsPrime]
    (i : ModuleCat.of A p.ResidueField ⟶ ModuleCat.of A E) [Mono i]
    (hi : IsInjectiveHull i) : Module.Injective B (B ⊗[A] E) := by
  let Ap := Localization.AtPrime p
  let S := Algebra.algebraMapSubmonoid B p.primeCompl
  let Bp := Localization S
  let EL := LocalizedModule p.primeCompl E
  let : Module.Flat Ap Bp := (Module.flat_iff_of_isLocalization Ap p.primeCompl Bp).mpr
    inferInstance
  obtain ⟨j, hj, hHull⟩ := localized_residueField_injectiveHull p i hi
  let := hj
  let : Module.Injective Bp (Bp ⊗[Ap] EL) :=
    tensorProduct_injective_of_local_residueFieldHull
      (map_comap_eq_of_localizations hprime p.primeCompl S Ap Bp) j hHull
  let eE : EL ≃ₗ[Ap] Ap ⊗[A] E := IsLocalizedModule.mapEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl E) (TensorProduct.mk A Ap E 1) Ap
    (LinearEquiv.refl A E)
  let e : Bp ⊗[Ap] EL ≃ₗ[Bp] Bp ⊗[A] E :=
    (LinearEquiv.baseChange Ap Bp _ _ eE).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap Bp Bp E)
  let : Module.Injective Bp (Bp ⊗[A] E) := Module.injective_of_linearEquiv e ‹_›
  let : Module.Injective B (Bp ⊗[A] E) :=
    (baer_restrictScalars_of_flat (S := Bp) (Module.Baer.of_injective inferInstance)).injective
  let : IsLocalizedModule S (LinearMap.id : B ⊗[A] E →ₗ[B] B ⊗[A] E) :=
    isLocalizedModule_tensorProduct_id p (isUnit_smul_of_residueField_injectiveHull p
      (LinearEquiv.refl A p.ResidueField) i hi)
  let f := TensorProduct.AlgebraTensorModule.rTensor A E (Algebra.linearMap B Bp)
  exact Module.injective_of_linearEquiv
    (IsLocalizedModule.linearEquiv S f (LinearMap.id : B ⊗[A] E →ₗ[B] B ⊗[A] E)) ‹_›

private theorem tensorProduct_injective_of_map_comap_eq_sameUniverse
    {A B E : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
        (Ideal.comap (algebraMap A B) q) = IsLocalRing.maximalIdeal (Localization.AtPrime q)) :
    Module.Injective B (B ⊗[A] E) := by
  apply tensorProduct_injective_of_indecomposable (I := E)
  intro J hJ hInd
  obtain ⟨p, hp, K, eK, i, hi, hHull⟩ :=
    exists_residueField_injectiveHull A J hInd
  let := hp
  let := hi
  let j : ModuleCat.of A p.ResidueField ⟶ J := eK.symm.toModuleIso.hom ≫ i
  have hj : Subobject.mk j = Subobject.mk i :=
    Subobject.mk_eq_mk_of_comm _ _ eK.symm.toModuleIso rfl
  apply tensorProduct_injective_of_residueFieldHull hprime p j
  refine ⟨hHull.1, ?_⟩
  show ∀ q : Subobject J, q ≠ ⊥ → q ⊓ Subobject.mk j ≠ ⊥
  rw [hj]
  exact hHull.2

attribute [local instance] ULift.algebra' RingHomInvPair.of_ringEquiv
  RingHomInvPair.of_ringEquiv_symm

private theorem tensorProduct_injective_of_map_comap_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
        (Ideal.comap (algebraMap A B) q) = IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (I : Type w) [AddCommGroup I] [Module A I] [Module.Injective A I] :
    Module.Injective B (B ⊗[A] I) := by
  let A₁ := ULift.{max v w} A
  let B₁ := ULift.{max u w} B
  let I₁ := ULift.{max u v} I
  let : IsNoetherianRing A₁ := isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let : IsNoetherianRing B₁ := isNoetherianRing_of_ringEquiv B ULift.ringEquiv.symm
  let : IsLocalization (IsUnit.submonoid A) A₁ :=
    IsLocalization.of_le_isUnit_of_bijective
      Algebra.algebraMapSubmonoid_isUnit_le_isUnit ULift.ringEquiv.symm.bijective
  let : IsLocalization (IsUnit.submonoid B) B₁ :=
    IsLocalization.of_le_isUnit_of_bijective
      Algebra.algebraMapSubmonoid_isUnit_le_isUnit ULift.ringEquiv.symm.bijective
  let : Module.Flat A B₁ := Module.Flat.of_linearEquiv ULift.moduleEquiv
  let : Module.Flat A₁ B₁ :=
    (Module.flat_iff_of_isLocalization A₁ (IsUnit.submonoid A) B₁).mpr inferInstance
  let : Module.Injective A I₁ :=
    ((baer_of_injective_of_isNoetherianRing I).of_equiv ULift.moduleEquiv.symm).injective
  let eI : I₁ ≃ₛₗ[RingHomClass.toRingHom (ULift.ringEquiv : A₁ ≃+* A).symm] I₁ :=
    { __ := AddEquiv.refl I₁
      map_smul' := fun _ _ => rfl }
  let : Module.Injective A₁ I₁ := Module.Injective.of_ringEquiv ULift.ringEquiv.symm eI
  let : Module.Injective B₁ (B₁ ⊗[A₁] I₁) :=
    tensorProduct_injective_of_map_comap_eq_sameUniverse
      (map_comap_eq_of_localizations hprime (IsUnit.submonoid A) (IsUnit.submonoid B) A₁ B₁)
  let e : B₁ ⊗[A₁] I₁ ≃ₗ[B] B ⊗[A] I :=
    (TensorProduct.AlgebraTensorModule.uliftEquiv.{u, v, v, w, 0, max u w, max v w,
      max u v} A B B I).symm.trans ULift.moduleEquiv
  exact Module.Injective.of_ringEquiv (ULift.ringEquiv : B₁ ≃+* B)
    { __ := e.toAddEquiv
      map_smul' := fun b x => e.map_smul b.down x }

/-- **Stacks Project, Tag 0E4F.** A flat map of Noetherian rings for which, locally at every
prime of the target, that prime is generated by its contraction preserves injective modules
under base change. -/
@[stacks 0E4F]
public theorem tensorProduct_injective_of_flat_of_map_comap_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hprime : ∀ (q : Ideal B) [q.IsPrime],
      Ideal.map (algebraMap A (Localization.AtPrime q))
          (Ideal.comap (algebraMap A B) q) =
        Ideal.map (algebraMap B (Localization.AtPrime q)) q)
    (I : Type w) [AddCommGroup I] [Module A I] [Module.Injective A I] :
    Module.Injective B (TensorProduct A B I) := by
  apply tensorProduct_injective_of_map_comap_eq (I := I)
  intro q hq
  exact (hprime q).trans (IsLocalization.AtPrime.map_eq_maximalIdeal q _)

end Module
