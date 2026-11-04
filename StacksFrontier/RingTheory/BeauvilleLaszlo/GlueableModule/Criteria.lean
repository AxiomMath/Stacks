module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.Flatness
public import StacksFrontier.RingTheory.Tor.Vanishing
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule.ModuleSequence

/-!
# Glueable modules: criteria for glueability

Let `R` be a commutative ring and `f : R`. An `R`-module `M` is glueable when the sequence
`0 → M → (M ⊗[R] R^∧) ⊕ M_f → M ⊗[R] (R^∧)_f → 0` is exact, `R^∧` being the `(f)`-adic
completion. This file gives sufficient conditions for glueability.

## Main results

* `glueable_criteria` (Stacks 0BNX): sufficient conditions for glueability —
  `M[f] ∩ ⋂ₙ fⁿM = 0`; vanishing of `Tor₁ᴿ(M, R'_f)`, equivalently `f`-power torsionness of
  `Tor₁ᴿ(M, R')`, which holds for every flat `M`; and flatness of `R → R'`, under which
  every `R`-module is glueable.

## Implementation notes

The Tor criteria are phrased with the categorical `CategoryTheory.Tor'` on `ModuleCat`, so the
ring, algebra and module are lifted into one universe before the Tor functor is applied; the
lifts and the transport lemmas for them are private to this file.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BNX](https://stacks.math.columbia.edu/tag/0BNX)
-/

@[expose] public section

namespace BeauvilleLaszlo

section






open CategoryTheory CategoryTheory.Limits


universe u v w

end

section



open CategoryTheory CategoryTheory.Limits MonoidalCategory


universe u v w
universe a b
universe c

private theorem completion_of_eq_zero_iff {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (x : M) :
    AdicCompletion.of I M x = 0 ↔ ∀ n : ℕ, x ∈ I ^ n • (⊤ : Submodule R M) := by
  constructor
  · intro hx n
    have h := congrArg (fun y : AdicCompletion I M => y.val n) hx
    simpa [AdicCompletion.of_apply, SModEq.zero] using h
  · intro hx
    apply AdicCompletion.ext
    intro n
    simpa [AdicCompletion.of_apply, SModEq.zero] using hx n

/-- Injectivity of `g` restricted to a submodule `p`, in terms of elements of `p`. -/
private theorem injective_restrict_iff {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {N : Type*} [AddCommGroup N] [Module R N] {p : Submodule R M} (g : M →ₗ[R] N) :
    Function.Injective (fun x : p => g x.1) ↔ ∀ x ∈ p, g x = 0 → x = 0 := by
  constructor
  · intro h x hx hgx
    exact congrArg Subtype.val (h (a₁ := ⟨x, hx⟩) (a₂ := 0) (by simpa using hgx))
  · intro h x y hxy
    exact Subtype.ext (sub_eq_zero.1
      (h _ (p.sub_mem x.2 y.2) (by rw [map_sub, sub_eq_zero]; exact hxy)))

private theorem torsionBy_completion_injective_iff {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (f : R) :
    Function.Injective (fun x : Submodule.torsionBy R M f => AdicCompletion.of I M x.1) ↔
      Submodule.torsionBy R M f ⊓ (⨅ n : ℕ, I ^ (n + 1) • ⊤) = ⊥ := by
  have key (x : M) : AdicCompletion.of I M x = 0 ↔
      x ∈ ⨅ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R M) := by
    rw [completion_of_eq_zero_iff, Submodule.mem_iInf]
    exact ⟨fun h n => h _, fun h n => n.casesOn (by simp) h⟩
  rw [injective_restrict_iff, Submodule.eq_bot_iff]
  simp only [Submodule.mem_inf, key, and_imp]

private theorem eq_zero_of_pow_smul_eq_zero_of_torsionBy_injective
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] (f : R) (g : M →ₗ[R] N)
    (hg : ∀ x ∈ Submodule.torsionBy R M f, g x = 0 → x = 0)
    (n : ℕ) (x : M) (hx : f ^ n • x = 0) (hgx : g x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    have hfx : f • (f ^ n • x) = 0 := by
      simpa only [smul_smul, pow_succ', mul_comm] using hx
    exact ih x (hg _ ((Submodule.mem_torsionBy_iff f _).2 hfx)
      (by rw [map_smul, hgx, smul_zero])) hgx

private theorem powerTorsion_completion_injective_of_torsionBy_injective
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (f : R)
    (h : Function.Injective
      (fun x : Submodule.torsionBy R M f => AdicCompletion.of I M x.1)) :
    Function.Injective
      (fun x : modulePowerTorsion M f => AdicCompletion.of I M x.1) := by
  rw [injective_restrict_iff] at h ⊢
  intro x hx hz
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion'_iff (Submonoid.powers f) _).mp hx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a.1 f).mp a.2
  change (a : R) • x = 0 at ha
  exact eq_zero_of_pow_smul_eq_zero_of_torsionBy_injective f (AdicCompletion.of I M) h n x
    (by simpa [hn] using ha) hz

private theorem tensorProductPowerTorsionMap_injective_of_torsionBy_completion_injective
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (f : R)
    (h : Function.Injective (fun x : Submodule.torsionBy R M f =>
      AdicCompletion.of (Ideal.span {f}) M x.1)) :
    Function.Injective
      (tensorProductPowerTorsionMap
        (S := AdicCompletion (Ideal.span {f}) R) M f) := by
  intro x y hxy
  apply powerTorsion_completion_injective_of_torsionBy_injective (Ideal.span {f}) f h
  have hbase :
      (x.1 ⊗ₜ[R] (1 : AdicCompletion (Ideal.span {f}) R)) =
        y.1 ⊗ₜ[R] (1 : AdicCompletion (Ideal.span {f}) R) := by
    simpa only [← tensorProductPowerTorsionMap_apply] using congrArg Subtype.val hxy
  have hcomp := congrArg
    (fun z : TensorProduct R M (AdicCompletion (Ideal.span {f}) R) =>
      AdicCompletion.ofTensorProduct (Ideal.span {f}) M
        ((TensorProduct.comm R M (AdicCompletion (Ideal.span {f}) R)) z)) hbase
  simpa only [TensorProduct.comm_tmul, AdicCompletion.ofTensorProduct_tmul, one_smul]
    using hcomp

private theorem completion_criteria :
    ∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
      (f : R),
      (beauvilleLaszloSequence f
        (algebraMap R (AdicCompletion (Ideal.span {f}) R))).ShortExact →
        ((IsGlueable M f ↔
            Function.Injective
              (tensorProductPowerTorsionMap
                (S := AdicCompletion (Ideal.span {f}) R) M f)) ∧
          (Function.Injective
              (fun x : Submodule.torsionBy R M f ↦
                AdicCompletion.of (Ideal.span {f}) M x.1) ↔
            Submodule.torsionBy R M f ⊓
                (⨅ n : ℕ, (Ideal.span {f}) ^ (n + 1) • ⊤) = ⊥) ∧
          (Function.Injective
              (fun x : Submodule.torsionBy R M f ↦
                AdicCompletion.of (Ideal.span {f}) M x.1) →
            IsGlueable M f)) := by
  intro R _ M _ _ f hR
  have key : IsGlueable M f ↔ Function.Injective
      (tensorProductPowerTorsionMap (S := AdicCompletion (Ideal.span {f}) R) M f) :=
    (isGlueable_iff_adicCompletion_beauvilleLaszloModuleSequence_shortExact M f).trans
      (beauvilleLaszloModuleSequence_exactness_iff_powerTorsionMap.{u, u, w}.2 R M f hR)
  exact ⟨key, torsionBy_completion_injective_iff (Ideal.span {f}) f,
    fun h => key.2 (tensorProductPowerTorsionMap_injective_of_torsionBy_completion_injective f h)⟩

private theorem tensor_shortExact_of_tor_one_isZero {R : Type u} [CommRing R]
    (C : ShortComplex (ModuleCat.{u} R)) (hC : C.ShortExact)
    (M : ModuleCat.{u} R)
    (hTor : IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj C.X₃)) :
    (C.map (MonoidalCategory.tensorLeft M)).ShortExact := by
  obtain ⟨δ, hex⟩ := (hC.exists_Tor'_one_composableArrows_exact_and_epi M).1
  have hδ : δ = 0 := IsZero.eq_of_src hTor _ _
  have hmono : Mono (M ◁ C.f) := (hex.exact' 2 3 4).mono_g hδ
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact hex.exact' 3 4 5
  · exact hmono
  · exact (hC.exists_Tor'_one_composableArrows_exact_and_epi M).2

private theorem tor_one_isZero_of_flat_left {A : Type u} [CommRing A]
    (X Y : ModuleCat.{u} A) [Module.Flat A X] :
    IsZero (((Tor' (ModuleCat.{u} A) 1).obj X).obj Y) := by
  have h : Module.Flat A X := inferInstance
  have hh : IsZero ((Tor' (ModuleCat.{u} A) 1).obj X) :=
    ((Module.Flat.tfae_isZero_Tor' X).out 1 3).mp h
  exact hh.obj Y

private theorem tor_one_isZero_of_flat_right {A : Type u} [CommRing A]
    (X Y : ModuleCat.{u} A) [Module.Flat A Y] :
    IsZero (((Tor' (ModuleCat.{u} A) 1).obj X).obj Y) :=
  IsZero.of_iso (Tor_iso_Tor'.tor_flat_isZero A Y X 0)
    (((torFlip_iso_Tor' A 1).app X).app Y).symm

private theorem flat_ulift {R : Type u} [CommRing R] {M : Type w}
    [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.Flat (ULift.{a} R) (ULift.{b} M) := by
  let A := ULift.{a} R
  let hAlg : Algebra A R := ULift.ringEquiv.toRingHom.toAlgebra
  let hModule : Module A M := ULift.module
  have hFlat : Module.Flat A R := (RingHom.flat_algebraMap_iff).mp
    (RingHom.Flat.of_bijective ULift.ringEquiv.bijective)
  let hTower : IsScalarTower A R M := ⟨fun x r m => by
    show (x.down * r) • m = x.down • r • m
    rw [mul_smul]⟩
  have h : Module.Flat A M :=
    @Module.Flat.trans A R M inferInstance inferInstance hAlg inferInstance
      hModule inferInstance hTower hFlat inferInstance
  let e : ULift.{b} M ≃ₗ[A] M := {
    toEquiv := Equiv.ulift
    map_add' := by intro x y; rfl
    map_smul' := by intro x y; rfl
  }
  exact Module.Flat.of_linearEquiv e

private theorem flat_away_of_flat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] (f : R) :
    Module.Flat R (Localization.Away (algebraMap R S f)) := by
  have : Module.Flat S (Localization.Away (algebraMap R S f)) :=
    IsLocalization.flat _ (Submonoid.powers (algebraMap R S f))
  exact Module.Flat.trans R S (Localization.Away (algebraMap R S f))

private theorem beauvilleLaszloSequence_function_shortExact
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (f : R)
    (h : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact) :
    Function.Injective (toBaseChangeAndAway f (algebraMap R S)) ∧
    Function.Exact (toBaseChangeAndAway f (algebraMap R S))
      (awayDifference f (algebraMap R S)) ∧
    Function.Surjective (awayDifference f (algebraMap R S)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply ULift.up_injective
    apply (AddCommGrpCat.mono_iff_injective _).mp h.mono_f
    exact congrArg ULift.up hxy
  · intro x
    constructor
    · intro hx
      have hx' : ((beauvilleLaszloSequence f (algebraMap R S)).g)
          (ULift.up x) = 0 := ULift.down_injective hx
      obtain ⟨y, hy⟩ :=
        (ShortComplex.ab_exact_iff _).mp h.exact (ULift.up x) hx'
      exact ⟨y.down, congrArg ULift.down hy⟩
    · rintro ⟨y, rfl⟩
      simp [toBaseChangeAndAway_apply,
        awayDifference_apply, Localization.awayMap,
        IsLocalization.Away.map, IsLocalization.map_eq]
  · intro x
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).mp h.epi_g (ULift.up x)
    exact ⟨y.down, congrArg ULift.down hy⟩

private def toBaseChangeAndAwayLinear {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (f : R) :
    R →ₗ[R] S × Localization.Away f where
  toFun := toBaseChangeAndAway f (algebraMap R S)
  map_add' := map_add _
  map_smul' r x := by
    apply Prod.ext
    · change algebraMap R S (r * x) = r • algebraMap R S x
      rw [map_mul, Algebra.smul_def]
    · change algebraMap R (Localization.Away f) (r * x) =
        r • algebraMap R (Localization.Away f) x
      rw [map_mul, Algebra.smul_def]

private noncomputable def awayDifferenceLinear {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (f : R) :
    S × Localization.Away f →ₗ[R] Localization.Away (algebraMap R S f) where
  toFun := awayDifference f (algebraMap R S)
  map_add' := map_add _
  map_smul' r x := by
    change algebraMap S (Localization.Away (algebraMap R S f))
        (r • x.1) - Localization.awayMap (algebraMap R S) f (r • x.2) =
      r • (algebraMap S (Localization.Away (algebraMap R S f)) x.1 -
        Localization.awayMap (algebraMap R S) f x.2)
    simp only [Algebra.smul_def, map_mul, mul_sub, Localization.awayMap,
      IsLocalization.Away.map, IsLocalization.map_eq]
    rw [IsScalarTower.algebraMap_apply R S
      (Localization.Away (algebraMap R S f)) r]

private def liftLinearMap {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    ULift.{a} M →ₗ[ULift.{b} R] ULift.{c} N where
  toFun x := ULift.up (g x.down)
  map_add' := by intro x y; apply ULift.down_injective; exact map_add g _ _
  map_smul' := by intro c x; apply ULift.down_injective; exact map_smul g c.down x.down

private def uliftSemilinear {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] :
    let e : ULift.{b} R ≃+* R := ULift.ringEquiv
    letI : RingHomInvPair (e : ULift.{b} R →+* R) (e.symm : R →+* ULift.{b} R) :=
      RingHomInvPair.of_ringEquiv e
    letI : RingHomInvPair (e.symm : R →+* ULift.{b} R) (e : ULift.{b} R →+* R) :=
      RingHomInvPair.of_ringEquiv_symm e
    ULift.{a} M ≃ₛₗ[(e : ULift.{b} R →+* R)] M := by
  let e : ULift.{b} R ≃+* R := ULift.ringEquiv
  letI : RingHomInvPair (e : ULift.{b} R →+* R) (e.symm : R →+* ULift.{b} R) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R →+* ULift.{b} R) (e : ULift.{b} R →+* R) :=
    RingHomInvPair.of_ringEquiv_symm e
  exact { toEquiv := Equiv.ulift
          map_add' := by intro x y; rfl
          map_smul' := by intro r x; rfl }

private def uliftTensorSemilinear {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    let e : ULift.{b} R ≃+* R := ULift.ringEquiv
    letI : RingHomInvPair (e : ULift.{b} R →+* R) (e.symm : R →+* ULift.{b} R) :=
      RingHomInvPair.of_ringEquiv e
    letI : RingHomInvPair (e.symm : R →+* ULift.{b} R) (e : ULift.{b} R →+* R) :=
      RingHomInvPair.of_ringEquiv_symm e
    TensorProduct (ULift.{b} R) (ULift.{a} M) (ULift.{c} N) ≃ₛₗ[
      (e : ULift.{b} R →+* R)] TensorProduct R M N := by
  let e : ULift.{b} R ≃+* R := ULift.ringEquiv
  letI : RingHomInvPair (e : ULift.{b} R →+* R) (e.symm : R →+* ULift.{b} R) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R →+* ULift.{b} R) (e : ULift.{b} R →+* R) :=
    RingHomInvPair.of_ringEquiv_symm e
  exact TensorProduct.congr uliftSemilinear uliftSemilinear

private noncomputable def torTensorRightIso {A : Type u} [CommRing A]
    (K N F : ModuleCat.{u} A) [Module.Flat A F] (n : ℕ) :
    (tensorRight F).obj (((Tor' (ModuleCat.{u} A) n).obj K).obj N) ≅
      ((Tor' (ModuleCat.{u} A) n).obj K).obj
        (MonoidalCategoryStruct.tensorObj N F) := by
  haveI : (tensorRight F).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let P : ProjectiveResolution K := ProjectiveResolution.of K
  refine (tensorRight F).mapIso (P.isoLeftDerivedObj (tensorRight N) n) ≪≫ ?_
  refine Stacks.Flatness.AwayTorCriterion.mapHomologyIso (tensorRight F) _ n ≪≫ ?_
  refine HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (tensorRightTensor N F).symm
      (ComplexShape.down ℕ)).app P.complex) n ≪≫ ?_
  exact (P.isoLeftDerivedObj
    (tensorRight (MonoidalCategoryStruct.tensorObj N F)) n).symm

private theorem torsion_eq_top_iff_isZero_tensor {A : Type u} [CommRing A]
    (T : Type u) [AddCommGroup T] [Module A T] (a : A) :
    modulePowerTorsion T a = ⊤ ↔
      IsZero (ModuleCat.of A (TensorProduct A T (Localization.Away a))) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  rw [(TensorProduct.comm A T (Localization.Away a)).toEquiv.subsingleton_congr]
  rw [IsLocalizedModule.subsingleton_iff (Submonoid.powers a)
    ((TensorProduct.mk A (Localization.Away a) T) 1)]
  constructor
  · intro h x
    have hx : x ∈ modulePowerTorsion T a := by rw [h]; simp
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion'_iff _ _).mp hx
    exact ⟨r.1, r.2, hr⟩
  · intro h
    ext x
    simp only [Submodule.mem_top, iff_true]
    obtain ⟨r, hr, hx⟩ := h x
    exact (Submodule.mem_torsion'_iff _ _).mpr ⟨⟨r, hr⟩, hx⟩

private theorem tor_one_isZero_iff_torsion_of_tensor_equiv
    {A : Type u} [CommRing A]
    (K N N' : Type u) [AddCommGroup K] [Module A K]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (a : A)
    (e : TensorProduct A N (Localization.Away a) ≃ₗ[A] N') :
    IsZero (((Tor' (ModuleCat.{u} A) 1).obj (ModuleCat.of A K)).obj
      (ModuleCat.of A N')) ↔
    modulePowerTorsion
      (((Tor' (ModuleCat.{u} A) 1).obj (ModuleCat.of A K)).obj
        (ModuleCat.of A N)) a = ⊤ := by
  let F := ModuleCat.of A (Localization.Away a)
  have : Module.Flat A F :=
    IsLocalization.flat (Localization.Away a) (Submonoid.powers a)
  let h := (torTensorRightIso (ModuleCat.of A K) (ModuleCat.of A N) F 1) ≪≫
    (((Tor' (ModuleCat.{u} A) 1).obj (ModuleCat.of A K)).mapIso e.toModuleIso)
  have hh := h.isZero_iff.symm
  exact hh.trans (torsion_eq_top_iff_isZero_tensor _ a).symm

private theorem uliftAway {R : Type u} [CommRing R] (f : R) :
    letI : Algebra (ULift.{a} R) (ULift.{b} (Localization.Away f)) :=
      ULift.algebra' R (ULift.{b} (Localization.Away f))
    IsLocalization.Away (ULift.up f) (ULift.{b} (Localization.Away f)) := by
  let : Algebra (ULift.{a} R) (ULift.{b} (Localization.Away f)) :=
    ULift.algebra' R (ULift.{b} (Localization.Away f))
  have : IsLocalization.Away f (ULift.{b} (Localization.Away f)) :=
    (IsLocalization.isLocalization_iff_of_algEquiv (Submonoid.powers f)
      (ULift.algEquiv (R := R) (A := Localization.Away f))).2 inferInstance
  apply IsLocalization.of_ringEquiv_left (ULift.ringEquiv : ULift.{a} R ≃+* R)
    (M₁ := Submonoid.powers f) (M₂ := Submonoid.powers (ULift.up f))
  · rw [Submonoid.map_powers]
    rfl
  · intro x
    rfl

private noncomputable def uliftAwayBaseChange {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (f : R) :
    letI : Algebra (ULift.{max v w} R) (ULift.{max u w} S) :=
      ULift.algebra' R (ULift.{max u w} S)
    letI : Algebra (ULift.{max v w} R)
        (ULift.{max u w} (Localization.Away (algebraMap R S f))) :=
      ULift.algebra' R (ULift.{max u w} (Localization.Away (algebraMap R S f)))
    letI : Module (ULift.{max v w} R) (Localization.Away (ULift.up f)) :=
      Algebra.toModule
    TensorProduct (ULift.{max v w} R) (ULift.{max u w} S)
      (Localization.Away (ULift.up f)) ≃ₗ[ULift.{max v w} R]
      ULift.{max u w} (Localization.Away (algebraMap R S f)) := by
  let A := ULift.{max v w} R
  let T := ULift.{max u w} S
  let L := ULift.{max u w} (Localization.Away (algebraMap R S f))
  letI : Algebra A T := ULift.algebra' R T
  letI : Algebra A L := ULift.algebra' R L
  letI : Algebra T L := ULift.algebra' S L
  letI : Module A (Localization.Away (ULift.up f)) := Algebra.toModule
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq (by
    intro x
    rfl)
  haveI : IsLocalization.Away (algebraMap A T (ULift.up f)) L := by
    convert uliftAway (algebraMap R S f) using 1
    rfl
  let e₁ := IsLocalization.Away.tensorEquiv (R := A) (S := T)
    (r := ULift.up f) (A := Localization.Away (ULift.up f))
  let e₂ := IsLocalization.algEquiv
    (Submonoid.powers (algebraMap A T (ULift.up f)))
    (Localization.Away (algebraMap A T (ULift.up f))) L
  let eT : @LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ T T _ _
      ULift.module Algebra.toModule := {
    toEquiv := Equiv.refl T
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl
  }
  let eL : @LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ L L _ _
      Algebra.toModule ULift.module := {
    toEquiv := Equiv.refl L
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl
  }
  let e := (e₁.trans e₂).restrictScalars A |>.toLinearEquiv
  exact (TensorProduct.congr eT (LinearEquiv.refl A _)).trans (e.trans eL)

private lemma general_criteria :
    ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (M : Type w) [AddCommGroup M] [Module R M] (f : R),
      (beauvilleLaszloSequence f (algebraMap R S)).ShortExact →
        ((IsZero
            (((Tor' (ModuleCat.{max u v w} (ULift.{max v w} R)) 1).obj
              (ModuleCat.of (ULift.{max v w} R) (ULift.{max u v} M))).obj
                (ModuleCat.of (ULift.{max v w} R)
                  (ULift.{max u w} (Localization.Away (algebraMap R S f))))) →
            IsGlueableFor (S := S) M f) ∧
          (IsZero
              (((Tor' (ModuleCat.{max u v w} (ULift.{max v w} R)) 1).obj
                (ModuleCat.of (ULift.{max v w} R) (ULift.{max u v} M))).obj
                  (ModuleCat.of (ULift.{max v w} R)
                    (ULift.{max u w} (Localization.Away (algebraMap R S f))))) ↔
            modulePowerTorsion
                (((Tor' (ModuleCat.{max u v w} (ULift.{max v w} R)) 1).obj
                  (ModuleCat.of (ULift.{max v w} R) (ULift.{max u v} M))).obj
                    (ModuleCat.of (ULift.{max v w} R) (ULift.{max u w} S)))
                (ULift.up f) = ⊤) ∧
          (Module.Flat R M → IsGlueableFor (S := S) M f) ∧
          (Module.Flat R S → IsGlueableFor (S := S) M f)) :=
  by
    intro R S _ _ _ M _ _ f hshort
    let A := ULift.{max v w} R
    let K := ModuleCat.of A (ULift.{max u v} M)
    let L := ModuleCat.of A
      (ULift.{max u w} (Localization.Away (algebraMap R S f)))
    have hmain : IsZero (((Tor' (ModuleCat.{max u v w} A) 1).obj K).obj L) →
        IsGlueableFor (S := S) M f := by
      intro hTor
      obtain ⟨hinj, hexact, hsurj⟩ :=
        beauvilleLaszloSequence_function_shortExact f hshort
      let d : ULift.{max v w} R →ₗ[A]
          ULift.{max u w} (S × Localization.Away f) :=
        liftLinearMap (toBaseChangeAndAwayLinear f)
      let e : ULift.{max u w} (S × Localization.Away f) →ₗ[A]
          ULift.{max u w} (Localization.Away (algebraMap R S f)) :=
        liftLinearMap (awayDifferenceLinear f)
      have hzero : e.comp d = 0 := by
        apply LinearMap.ext
        intro x
        apply ULift.down_injective
        exact hexact.apply_apply_eq_zero x.down
      let C := ShortComplex.moduleCatMk d e hzero
      have hC : C.ShortExact := by
        refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
        · rw [ShortComplex.moduleCat_exact_iff]
          intro x hx
          obtain ⟨y, hy⟩ := (hexact x.down).mp (congrArg ULift.down hx)
          exact ⟨ULift.up y, congrArg ULift.up hy⟩
        · rw [ModuleCat.mono_iff_injective]
          intro x y hxy
          apply ULift.down_injective
          exact hinj (congrArg ULift.down hxy)
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          obtain ⟨y, hy⟩ := hsurj x.down
          exact ⟨ULift.up y, congrArg ULift.up hy⟩
      have hTensor : (C.map (MonoidalCategory.tensorLeft K)).ShortExact :=
        tensor_shortExact_of_tor_one_isZero C hC K hTor
      let ρ : A ≃+* R := ULift.ringEquiv
      let : RingHomInvPair (ρ : A →+* R) (ρ.symm : R →+* A) :=
        RingHomInvPair.of_ringEquiv ρ
      let : RingHomInvPair (ρ.symm : R →+* A) (ρ : A →+* R) :=
        RingHomInvPair.of_ringEquiv_symm ρ
      let e₁ : TensorProduct A (ULift.{max u v} M) (ULift.{max v w} R) ≃+ M :=
        uliftTensorSemilinear.toAddEquiv.trans (TensorProduct.rid R M).toAddEquiv
      let e₂ : TensorProduct A (ULift.{max u v} M)
          (ULift.{max u w} (S × Localization.Away f)) ≃+
          (TensorProduct R M S × TensorProduct R M (Localization.Away f)) :=
        uliftTensorSemilinear.toAddEquiv.trans
          (TensorProduct.prodRight R R M S (Localization.Away f)).toAddEquiv
      let e₃ : TensorProduct A (ULift.{max u v} M)
          (ULift.{max u w} (Localization.Away (algebraMap R S f))) ≃+
          TensorProduct R M (Localization.Away (algebraMap R S f)) :=
        uliftTensorSemilinear.toAddEquiv
      have hd (x) : e₂ (d.lTensor (ULift.{max u v} M) x) =
          toTensorBaseChanges M f (e₁ x) := by
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul m r =>
          show (m.down ⊗ₜ[R] algebraMap R S r.down,
              m.down ⊗ₜ[R] algebraMap R (Localization.Away f) r.down) =
            ((r.down • m.down) ⊗ₜ[R] (1 : S),
              (r.down • m.down) ⊗ₜ[R] (1 : Localization.Away f))
          simp only [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have he (x) : e₃ (e.lTensor (ULift.{max u v} M) x) =
          tensorAwayDifference M f (e₂ x) := by
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul m s =>
          show m.down ⊗ₜ[R]
              (algebraMap S (Localization.Away (algebraMap R S f)) s.down.1 -
                Localization.awayMap (algebraMap R S) f s.down.2) =
            m.down ⊗ₜ[R] algebraMap S (Localization.Away (algebraMap R S f)) s.down.1 -
              m.down ⊗ₜ[R] Localization.awayMap (algebraMap R S) f s.down.2
          exact TensorProduct.tmul_sub _ _ _
      have hti : Function.Injective (d.lTensor (ULift.{max u v} M)) :=
        (ModuleCat.mono_iff_injective _).mp hTensor.mono_f
      have hte : ∀ x, e.lTensor (ULift.{max u v} M) x = 0 →
          ∃ y, d.lTensor (ULift.{max u v} M) y = x :=
        (ShortComplex.moduleCat_exact_iff _).mp hTensor.exact
      have hts : Function.Surjective (e.lTensor (ULift.{max u v} M)) :=
        (ModuleCat.epi_iff_surjective _).mp hTensor.epi_g
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy
        apply e₁.symm.injective
        apply hti
        apply e₂.injective
        simpa only [hd, e₁.apply_symm_apply] using hxy
      · intro x
        constructor
        · intro hx
          have hx' : e.lTensor (ULift.{max u v} M) (e₂.symm x) = 0 := by
            apply e₃.injective
            simpa only [he, e₂.apply_symm_apply, map_zero] using hx
          obtain ⟨y, hy⟩ := hte _ hx'
          refine ⟨e₁ y, ?_⟩
          rw [← hd, hy, e₂.apply_symm_apply]
        · rintro ⟨y, rfl⟩
          rw [toTensorBaseChanges_apply,
            tensorAwayDifference_apply,
            baseChangeToAway_tmul, localizedBaseChangeToAway_tmul,
            map_one, map_one, sub_self]
      · intro x
        obtain ⟨y, hy⟩ := hts (e₃.symm x)
        refine ⟨e₂ y, ?_⟩
        rw [← he, hy, e₃.apply_symm_apply]
    refine ⟨hmain, ?_, ?_, ?_⟩
    · let A := ULift.{max v w} R
      let T := ULift.{max u w} S
      let L := ULift.{max u w} (Localization.Away (algebraMap R S f))
      let : Algebra A T := ULift.algebra' R T
      let : Algebra A L := ULift.algebra' R L
      let : Module A T := ULift.module
      let : Module A L := ULift.module
      let : Module A (Localization.Away (ULift.up f)) := Algebra.toModule
      exact tor_one_isZero_iff_torsion_of_tensor_equiv
        (ULift.{max u v} M) T L (ULift.up f) (uliftAwayBaseChange f)
    · intro hflat
      let : Module.Flat R M := hflat
      let : Module.Flat A (ULift.{max u v} M) := flat_ulift
      exact hmain (tor_one_isZero_of_flat_left K L)
    · intro hflat
      let : Module.Flat R S := hflat
      let : Module.Flat R (Localization.Away (algebraMap R S f)) :=
        flat_away_of_flat f
      let : Module.Flat A
          (ULift.{max u w} (Localization.Away (algebraMap R S f))) := flat_ulift
      exact hmain (tor_one_isZero_of_flat_right K L)

private lemma noetherian_criteria :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (M : Type w) [AddCommGroup M] [Module R M] (f : R),
      IsGlueable M f :=
  by
    intro R _ _ M _ _ f
    let S := AdicCompletion (Ideal.span {f}) R
    let φ : R →+* S := algebraMap R S
    obtain ⟨_, hinj, hex, hsurj⟩ :=
      (adicCompletion_isGlueingPair_of_flat f).2
    have hshort : (beauvilleLaszloSequence f φ).ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · apply (ShortComplex.ab_exact_iff _).2
        intro x hx
        have hx' : awayDifference f φ x.down = 0 := ULift.up_injective hx
        obtain ⟨r, hr⟩ := (hex x.down).1 hx'
        refine ⟨ULift.up r, ?_⟩
        exact congrArg ULift.up hr
      · rw [AddCommGrpCat.mono_iff_injective]
        intro x y hxy
        apply ULift.down_injective
        apply hinj
        exact congrArg ULift.down hxy
      · rw [AddCommGrpCat.epi_iff_surjective]
        intro x
        obtain ⟨y, hy⟩ := hsurj x.down
        exact ⟨ULift.up y, congrArg ULift.up hy⟩
    exact (general_criteria R S M f hshort).2.2.2
      (AdicCompletion.flat_of_isNoetherian (Ideal.span {f}))

/-- Criteria ensuring that a module is glueable for a Beauville--Laszlo glueing pair.

For completion at `f`, glueability is equivalent to injectivity on `f`-power torsion.
Injectivity of `M[f] → M̂` is equivalent to
`M[f] ∩ ⋂ n ≥ 1, f ^ n M = 0` and implies glueability. For a general glueing pair
`R → S`, vanishing of `Tor₁(M, S_f)` is sufficient and is equivalent to
`Tor₁(M, S)` being `f`-power torsion. Consequently flat modules are glueable; if
`S` is flat over `R`, every module is glueable. The latter applies to completion over
a Noetherian ring. -/
@[stacks 0BNX]
public theorem glueable_criteria :
    (∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
      (f : R),
      (beauvilleLaszloSequence f
        (algebraMap R (AdicCompletion (Ideal.span {f}) R))).ShortExact →
        ((IsGlueable M f ↔
            Function.Injective
              (tensorProductPowerTorsionMap
                (S := AdicCompletion (Ideal.span {f}) R) M f)) ∧
          (Function.Injective
              (fun x : Submodule.torsionBy R M f ↦
                AdicCompletion.of (Ideal.span {f}) M x.1) ↔
            Submodule.torsionBy R M f ⊓
                (⨅ n : ℕ, (Ideal.span {f}) ^ (n + 1) • ⊤) = ⊥) ∧
          (Function.Injective
              (fun x : Submodule.torsionBy R M f ↦
                AdicCompletion.of (Ideal.span {f}) M x.1) →
            IsGlueable M f))) ∧
    (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
      (M : Type w) [AddCommGroup M] [Module R M] (f : R),
      (beauvilleLaszloSequence f (algebraMap R S)).ShortExact →
        ((IsZero
            (((Tor' (ModuleCat.{max u v w} (ULift.{max v w} R)) 1).obj
              (ModuleCat.of (ULift.{max v w} R) (ULift.{max u v} M))).obj
                (ModuleCat.of (ULift.{max v w} R)
                  (ULift.{max u w} (Localization.Away (algebraMap R S f))))) →
            IsGlueableFor (S := S) M f) ∧
          (IsZero
              (((Tor' (ModuleCat.{max u v w} (ULift.{max v w} R)) 1).obj
                (ModuleCat.of (ULift.{max v w} R) (ULift.{max u v} M))).obj
                  (ModuleCat.of (ULift.{max v w} R)
                    (ULift.{max u w} (Localization.Away (algebraMap R S f))))) ↔
            modulePowerTorsion
                (((Tor' (ModuleCat.{max u v w} (ULift.{max v w} R)) 1).obj
                  (ModuleCat.of (ULift.{max v w} R) (ULift.{max u v} M))).obj
                    (ModuleCat.of (ULift.{max v w} R) (ULift.{max u w} S)))
                (ULift.up f) = ⊤) ∧
          (Module.Flat R M → IsGlueableFor (S := S) M f) ∧
          (Module.Flat R S → IsGlueableFor (S := S) M f))) ∧
    (∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (M : Type w) [AddCommGroup M] [Module R M] (f : R),
      IsGlueable M f) := by
  exact ⟨completion_criteria, general_criteria, noetherian_criteria⟩

end

end BeauvilleLaszlo

end
