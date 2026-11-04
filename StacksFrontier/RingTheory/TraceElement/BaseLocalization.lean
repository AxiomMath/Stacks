module

public import StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization
public import StacksFrontier.RingTheory.TraceElement.FiniteFactor
public import StacksFrontier.RingTheory.TraceElement.Independence
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace

/-!
# Trace elements and localization of the base

Let `A → B` be a flat quasi-finite map of Noetherian rings which factors through the
localization `A_f` of the base away from an element `f`. A trace element of the relative
dualizing module of `B` over `A_f` is also one over `A`, under the identification of
Tag 0BT2, part (1).

## Main results

* `Stacks.Discriminant.baseChangeTargetAlgEquiv`: the identification `A_f ⊗_A B ≅ B` read as an
  equivalence of `A_f`-algebras, together with its pure-tensor formula.
* `Stacks.Discriminant.finiteProjectiveTrace_lmul_isLocalizationAway`: the trace of
  multiplication over an away localization of the base is the image of the trace over the base.
* `Stacks.Discriminant.linearMap_eq_of_isLocalization_away`: a functional on a finite module is
  determined by its image in an away localization, when the element acts invertibly on the
  module's ring.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
-/

@[expose] public section

universe u v w x y z s t r

open scoped TensorProduct

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- A pure tensor `a ⊗ b` is the product of `a` (as a scalar) and `1 ⊗ b`. -/
private theorem tmul_eq_algebraMap_mul_one_tmul {R S B : Type*} [CommRing R] [CommRing S]
    [CommRing B] [Algebra R S] [Algebra R B] (a : S) (b : B) :
    a ⊗ₜ[R] b = algebraMap S (S ⊗[R] B) a * ((1 : S) ⊗ₜ[R] b) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

section TargetEquiv

variable {A : Type u} {B : Type v} {Af : Type w}
  [CommRing A] [CommRing B] [CommRing Af]
  [Algebra A B] [Algebra A Af] [Algebra Af B] [IsScalarTower A Af B]

/-- For a localization `A_f` of `A` through which `A → B` factors, the left inclusion
`A_f → A_f ⊗_A B` is the composite of `A_f → B` with the right inclusion: the two agree on the
image of `A`, and `A_f` is generated over `A` by inverting `f`. -/
theorem isScalarTower_tensorProduct_of_isLocalizationAway
    (f : A) [IsLocalization.Away f Af] :
    letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    IsScalarTower Af B (Af ⊗[A] B) := by
  let : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
  ext a
  show (algebraMap A Af a) ⊗ₜ[A] (1 : B) =
    (1 : Af) ⊗ₜ[A] algebraMap Af B (algebraMap A Af a)
  rw [← IsScalarTower.algebraMap_apply A Af B a]
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a

/-- The identification `A_f ⊗_A B ≅ B` of
`Stacks.Discriminant.baseChangeTargetEquiv`, read as an equivalence of `A_f`-algebras. -/
noncomputable def baseChangeTargetAlgEquiv (f : A) [IsLocalization.Away f Af] :
    Af ⊗[A] B ≃ₐ[Af] B :=
  letI : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower Af B (Af ⊗[A] B) :=
    isScalarTower_tensorProduct_of_isLocalizationAway f
  (baseChangeTargetEquiv f).restrictScalars Af

/-- The identification `A_f ⊗_A B ≅ B` is multiplication. -/
theorem baseChangeTargetAlgEquiv_tmul (f : A) [IsLocalization.Away f Af] (a : Af) (b : B) :
    baseChangeTargetAlgEquiv f (a ⊗ₜ[A] b) = algebraMap Af B a * b := by
  let : Algebra B (Af ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Af B (Af ⊗[A] B) :=
    isScalarTower_tensorProduct_of_isLocalizationAway f
  have hright : baseChangeTargetAlgEquiv f ((1 : Af) ⊗ₜ[A] b) = b :=
    (baseChangeTargetEquiv f).commutes b
  rw [tmul_eq_algebraMap_mul_one_tmul, map_mul, AlgEquiv.commutes, hright]

end TargetEquiv

/-- The trace of multiplication over an away localization of the base is the image of the trace
over the base, for a module that is finite projective over both. -/
theorem finiteProjectiveTrace_lmul_isLocalizationAway
    {S : Type u} {Sf : Type v} {C : Type w} [CommRing S] [CommRing Sf] [CommRing C]
    [Algebra S Sf] [Algebra S C] [Algebra Sf C] [IsScalarTower S Sf C]
    (f : S) [IsLocalization.Away f Sf]
    [Module.Finite S C] [Module.Projective S C]
    [Module.Finite Sf C] [Module.Projective Sf C] (c : C) :
    finiteProjectiveTrace Sf C (Algebra.lmul Sf C c) =
      algebraMap S Sf (finiteProjectiveTrace S C (Algebra.lmul S C c)) :=
  finiteProjectiveTrace_lmul_algebraMap
    (baseChangeTargetAlgEquiv (A := S) (B := C) (Af := Sf) f).toLinearEquiv
    (fun a b => baseChangeTargetAlgEquiv_tmul f a b) c

/-- A functional on a module that is finite over `S` is determined by its image in the away
localization `S_f`, provided `f` acts invertibly on the module's ring. Each of finitely many
generators is annihilated by a power of `f`, and the largest of those powers kills the whole
difference, which is then invertible. -/
theorem linearMap_eq_of_isLocalization_away
    {S : Type u} {Sf : Type v} {C : Type w} [CommRing S] [CommRing Sf] [CommRing C]
    [Algebra S Sf] [Algebra S C] [Module.Finite S C]
    (f : S) [IsLocalization.Away f Sf] (hfC : IsUnit (algebraMap S C f))
    (p q : C →ₗ[S] S)
    (hpq : ∀ c, algebraMap S Sf (p c) = algebraMap S Sf (q c)) : p = q := by
  classical
  set δ : C →ₗ[S] S := p - q with hδ
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := S) (M := C)
  have hex (i : Fin n) : ∃ j : ℕ, f ^ j * δ (gen i) = 0 := by
    have hzero : algebraMap S Sf (δ (gen i)) = 0 := by simp [hδ, hpq]
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Sf (δ (gen i))).mp hzero
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff m.1 f).mp m.2
    exact ⟨j, by simpa [hj] using hm⟩
  set exponent : ℕ := Finset.univ.sup fun i => Classical.choose (hex i) with hexponent
  have hkillGen (i : Fin n) : f ^ exponent * δ (gen i) = 0 := by
    have hi : Classical.choose (hex i) ≤ exponent :=
      Finset.le_sup (f := fun i => Classical.choose (hex i)) (Finset.mem_univ i)
    exact pow_mul_eq_zero_of_le hi (Classical.choose_spec (hex i))
  have hscaled : (LinearMap.lsmul S S (f ^ exponent)).comp δ = 0 :=
    (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hgen).2 (by
      rintro ⟨x, hx⟩
      obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
      exact hkillGen i)
  have hkill (c : C) : f ^ exponent * δ c = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.lsmul_apply, smul_eq_mul,
      LinearMap.zero_apply] using LinearMap.congr_fun hscaled c
  have hunit := hfC.pow exponent
  have hinv : algebraMap S C (f ^ exponent) * (↑hunit.unit⁻¹ : C) = 1 := by
    rw [map_pow]
    exact hunit.mul_val_inv
  refine LinearMap.ext fun c => sub_eq_zero.mp ?_
  calc
    p c - q c = δ c := rfl
    _ = δ (algebraMap S C (f ^ exponent) * ((↑hunit.unit⁻¹ : C) * c)) := by
      rw [← mul_assoc, hinv, one_mul]
    _ = f ^ exponent * δ ((↑hunit.unit⁻¹ : C) * c) := by
      rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    _ = 0 := hkill _

/-- The structure map of a base-changed finite-open factorization, on a pure tensor. -/
theorem baseChange_algebraMap_tmul {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] (a : A₁) (m : F.middle) :
    algebraMap (FiniteOpenFactorization.baseChange F A₁).middle (A₁ ⊗[A] B) (a ⊗ₜ[A] m) =
      a ⊗ₜ[A] algebraMap F.middle B m := rfl

/-- The structure map of a finite-open factorization transported along an isomorphism of its
target. -/
theorem retargetFactorization_algebraMap {A : Type u} {D : Type v} {B : Type w}
    [CommRing A] [CommRing D] [CommRing B] [Algebra A D] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, x} A D) (eq : D ≃ₐ[A] B) (m : F.middle) :
    algebraMap (retargetFactorization F eq).middle B m = eq (algebraMap F.middle D m) := rfl

/-- **Stacks Project, Tag 0BT9.** A trace element of the relative dualizing module over a
localization of the base remains a trace element over the original base, under the
identification of Tag 0BT2, part (1).

The trace-element condition over `R` tests a decomposition `S ⊗_R B ≃ C × D` with `C` finite
over `S`. Since `f` becomes invertible in `B`, it is invertible in `C`, so the same decomposition
is visible over the localization `S_f`, where the condition over `A` applies. The two
restriction functionals to `C` differ by the localization map `S → S_f`, and a functional on a
finite module is determined by its image there. -/
@[stacks 0BT9 "trace_base_localization"]
theorem isTraceElement_of_isLocalization_away
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.QuasiFinite A B]
    (f : R) [IsLocalization.Away f A]
    (FR : FiniteOpenFactorization.{u, w, x} R B)
    (FA : FiniteOpenFactorization.{v, w, y} A B)
    (τ : dualizingModule FA) (hτ : IsTraceElement.{v, w, y, s, t, z} FA τ) :
    letI : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
    letI : Algebra.QuasiFinite R A :=
      Algebra.QuasiFinite.of_isLocalization (Submonoid.powers f)
    letI : Module.Flat R B := Module.Flat.trans R A B
    letI : Algebra.QuasiFinite R B := Algebra.QuasiFinite.trans R A B
    IsTraceElement.{u, w, x, s, t, z} FR
      ((dualizingModule_equiv_of_isLocalization_away f FR FA).symm τ) := by
  let : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
  let : Algebra.QuasiFinite R A := Algebra.QuasiFinite.of_isLocalization (Submonoid.powers f)
  let : Module.Flat R B := Module.Flat.trans R A B
  let : Algebra.QuasiFinite R B := Algebra.QuasiFinite.trans R A B
  have hfB : IsUnit (algebraMap R B f) := by
    rw [IsScalarTower.algebraMap_apply R A B f]
    exact (IsLocalization.Away.algebraMap_isUnit f).map (algebraMap A B)
  -- The factorization of `B` over `A` obtained from the given one over `R`.
  let FA0 : FiniteOpenFactorization.{v, w, max v x} A B :=
    retargetFactorization (FiniteOpenFactorization.baseChange FR A)
      (baseChangeTargetAlgEquiv f)
  let : Algebra R FA0.middle := (inferInstance : Algebra R (A ⊗[R] FR.middle))
  have : IsScalarTower R A FA0.middle :=
    (inferInstance : IsScalarTower R A (A ⊗[R] FR.middle))
  have hbase (b : B) :
      baseChangeTargetAlgEquiv (A := R) (B := B) (Af := A) f ((1 : A) ⊗ₜ[R] b) = b := by
    rw [baseChangeTargetAlgEquiv_tmul, map_one, one_mul]
  have hFA0map (n : FR.middle) :
      algebraMap FA0.middle B ((1 : A) ⊗ₜ[R] n) = algebraMap FR.middle B n :=
    (retargetFactorization_algebraMap _ _ _).trans
      ((congrArg (baseChangeTargetAlgEquiv f) (baseChange_algebraMap_tmul FR A 1 n)).trans
        (hbase _))
  let τR := (dualizingModule_equiv_of_isLocalization_away f FR FA).symm τ
  have hτ0 : IsTraceElement.{v, w, max v x, s, t, z} FA0
      (dualizingModule_equiv_of_isLocalization_away f FR FA0 τR) := by
    have hnat := dualizingModule_equiv_of_isLocalization_away_natural f FR FR FA FA0 τR
    rw [dualizingModuleEquiv_refl, LinearEquiv.refl_apply,
      (dualizingModule_equiv_of_isLocalization_away f FR FA).apply_symm_apply τ] at hnat
    rw [← hnat]
    exact (isTraceElement_congr FA FA0 τ).mp hτ
  intro S _ _ _ C D _ _ _ _ e hfinite
  let FRs := FiniteOpenFactorization.baseChange FR S
  let : Algebra FRs.middle C :=
    ((RingHom.fst C D).comp
      (e.toRingEquiv.toRingHom.comp FRs.algebraTarget.algebraMap)).toAlgebra
  have : Module.Finite S C := hfinite
  have hprojective : Module.Projective S C := projective_of_prodEquiv_baseChange e hfinite
  have : Module.Projective S C := hprojective
  obtain ⟨hmfinite, hmprojective⟩ :=
    finite_and_projective_of_prodEquiv_middle FRs e (fun _ => rfl) hfinite
  have : Module.Finite FRs.middle C := hmfinite
  have : Module.Projective FRs.middle C := hmprojective
  -- The localization of the test ring at `f`, over which the condition for `A` applies.
  let q : S := algebraMap R S f
  let Sf := Localization.Away q
  have hfSf : IsUnit (algebraMap R Sf f) := by
    rw [IsScalarTower.algebraMap_apply R S Sf f]
    exact IsLocalization.Away.algebraMap_isUnit q
  let : Algebra A Sf := (IsLocalization.Away.lift f hfSf).toAlgebra
  have : IsScalarTower R A Sf :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp f hfSf).symm
  have : IsNoetherianRing Sf :=
    IsLocalization.isNoetherianRing (Submonoid.powers q) Sf inferInstance
  -- `f` is invertible on the finite factor.
  have hfTensor : IsUnit (algebraMap S (S ⊗[R] B) q) := by
    have h : algebraMap S (S ⊗[R] B) q =
        Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B) (algebraMap R B f) := by
      show q ⊗ₜ[R] (1 : B) = (1 : S) ⊗ₜ[R] algebraMap R B f
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul f
    rw [h]
    exact hfB.map _
  have hfProd : IsUnit (algebraMap S (C × D) q) := by
    rw [← e.commutes]
    exact hfTensor.map e
  have hfC : IsUnit (algebraMap S C q) := by simpa using hfProd.map (RingHom.fst C D)
  have hfD : IsUnit (algebraMap S D q) := by simpa using hfProd.map (RingHom.snd C D)
  let : Algebra Sf C := (IsLocalization.Away.lift q hfC).toAlgebra
  let : Algebra Sf D := (IsLocalization.Away.lift q hfD).toAlgebra
  have : IsScalarTower S Sf C :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp q hfC).symm
  have : IsScalarTower S Sf D :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp q hfD).symm
  have hfinite' : Module.Finite Sf C := Module.Finite.of_restrictScalars_finite S Sf C
  -- The decomposition of the target carried over to the localized test ring.
  let eCancelA : (Sf ⊗[A] (A ⊗[R] B)) ≃ₐ[Sf] (Sf ⊗[R] B) :=
    Algebra.TensorProduct.cancelBaseChange R A Sf Sf B
  let eCancelS : (Sf ⊗[S] (S ⊗[R] B)) ≃ₐ[Sf] (Sf ⊗[R] B) :=
    Algebra.TensorProduct.cancelBaseChange R S Sf Sf B
  let eUpA : (Sf ⊗[A] (A ⊗[R] B)) ≃ₐ[Sf] (Sf ⊗[A] B) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : Sf ≃ₐ[Sf] Sf)
      (baseChangeTargetAlgEquiv (A := R) (B := B) (Af := A) f)
  let eUpS : (Sf ⊗[S] (S ⊗[R] B)) ≃ₐ[Sf] (Sf ⊗[S] (C × D)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : Sf ≃ₐ[Sf] Sf) e
  let eDown : (Sf ⊗[S] (C × D)) ≃ₐ[Sf] (C × D) :=
    baseChangeTargetAlgEquiv (A := S) (B := C × D) (Af := Sf) q
  let e' : (Sf ⊗[A] B) ≃ₐ[Sf] C × D :=
    ((eUpA.symm.trans eCancelA).trans eCancelS.symm).trans (eUpS.trans eDown)
  have hdecomp (b : B) : e' ((1 : Sf) ⊗ₜ[A] b) = e ((1 : S) ⊗ₜ[R] b) := by
    have h1 : eUpA ((1 : Sf) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] b)) = (1 : Sf) ⊗ₜ[A] b := by
      simp only [eUpA, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      exact congrArg ((1 : Sf) ⊗ₜ[A] ·) (hbase b)
    have h2 : eUpA.symm ((1 : Sf) ⊗ₜ[A] b) = (1 : Sf) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] b) :=
      eUpA.symm_apply_eq.2 h1.symm
    have h3 : e' ((1 : Sf) ⊗ₜ[A] b) =
        eDown (eUpS (eCancelS.symm (eCancelA (eUpA.symm ((1 : Sf) ⊗ₜ[A] b))))) := rfl
    rw [h3, h2]
    simp only [eCancelA, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul,
      eCancelS, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      eUpS, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      eDown, baseChangeTargetAlgEquiv_tmul, map_one, one_mul]
    rfl
  let FA0sf := FiniteOpenFactorization.baseChange FA0 Sf
  let : Algebra FA0sf.middle C :=
    ((RingHom.fst C D).comp
      (e'.toRingEquiv.toRingHom.comp FA0sf.algebraTarget.algebraMap)).toAlgebra
  obtain ⟨hprojectiveSf, hmfiniteSf, hmprojectiveSf, htraceSf⟩ := hτ0 Sf C D e' hfinite'
  have : Module.Projective Sf C := hprojectiveSf
  have : Module.Finite FA0sf.middle C := hmfiniteSf
  have : Module.Projective FA0sf.middle C := hmprojectiveSf
  -- The intermediate algebra over the localized test ring is the away localization, at the
  -- image of `f`, of the intermediate algebra over the test ring.
  let jM : (S ⊗[R] FR.middle) →+* (Sf ⊗[R] FR.middle) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S Sf)
      (AlgHom.id R FR.middle)).toRingHom
  have hjM (a : S) (m : FR.middle) : jM (a ⊗ₜ[R] m) = (algebraMap S Sf a) ⊗ₜ[R] m :=
    Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom R S Sf) (AlgHom.id R FR.middle) a m
  let algTensor : Algebra (S ⊗[R] FR.middle) (Sf ⊗[R] FR.middle) := jM.toAlgebra
  have : IsScalarTower S (S ⊗[R] FR.middle) (Sf ⊗[R] FR.middle) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show (algebraMap S Sf a) ⊗ₜ[R] (1 : FR.middle) = jM (a ⊗ₜ[R] (1 : FR.middle))
      rw [hjM]
  have hawayMf : IsLocalization.Away (algebraMap S (S ⊗[R] FR.middle) q)
      (Sf ⊗[R] FR.middle) := by
    show IsLocalization (Submonoid.powers (algebraMap S (S ⊗[R] FR.middle) q)) _
    rw [← Submonoid.map_powers (algebraMap S (S ⊗[R] FR.middle)) q]
    exact IsLocalization.tensorProduct_tensorProduct R FR.middle (Submonoid.powers q) Sf (by
      ext m
      show jM ((1 : S) ⊗ₜ[R] m) = (1 : Sf) ⊗ₜ[R] m
      rw [hjM, map_one])
  let eMiddle : FA0sf.middle ≃ₐ[Sf] (Sf ⊗[R] FR.middle) :=
    Algebra.TensorProduct.cancelBaseChange R A Sf Sf FR.middle
  let algMidTarget : Algebra FRs.middle FA0sf.middle :=
    (eMiddle.symm.toRingEquiv.toRingHom.comp jM).toAlgebra
  let algMidMf : Algebra FRs.middle (Sf ⊗[R] FR.middle) := algTensor
  have hawayN : IsLocalization.Away (algebraMap S FRs.middle q) FA0sf.middle := by
    have hequiv : (Sf ⊗[R] FR.middle) ≃ₐ[FRs.middle] FA0sf.middle :=
      AlgEquiv.ofRingEquiv (f := eMiddle.symm.toRingEquiv) (fun _ => rfl)
    have : IsLocalization.Away (algebraMap S FRs.middle q) (Sf ⊗[R] FR.middle) := hawayMf
    exact IsLocalization.isLocalization_of_algEquiv _ hequiv
  have halg (a : S) (m : FR.middle) :
      algebraMap FRs.middle FA0sf.middle (a ⊗ₜ[R] m) =
        (algebraMap S Sf a) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] m) := by
    show eMiddle.symm (jM (a ⊗ₜ[R] m)) = _
    rw [hjM]
    exact Algebra.TensorProduct.cancelBaseChange_symm_tmul R A Sf Sf FR.middle
      (algebraMap S Sf a) m
  have htargetN (m : S ⊗[R] FR.middle) :
      e' (algebraMap FA0sf.middle (Sf ⊗[A] B) (algebraMap FRs.middle FA0sf.middle m)) =
        e (algebraMap FRs.middle (S ⊗[R] B) m) := by
    induction m using TensorProduct.induction_on with
    | zero =>
      have hz : algebraMap FRs.middle FA0sf.middle (0 : S ⊗[R] FR.middle) = 0 := map_zero _
      have hz' : algebraMap FRs.middle (S ⊗[R] B) (0 : S ⊗[R] FR.middle) = 0 := map_zero _
      rw [hz, hz']
      simp
    | add m₁ m₂ h₁ h₂ =>
      have ha : algebraMap FRs.middle FA0sf.middle ((m₁ + m₂ : S ⊗[R] FR.middle)) =
          algebraMap FRs.middle FA0sf.middle m₁ +
            algebraMap FRs.middle FA0sf.middle m₂ := map_add _ _ _
      have ha' : algebraMap FRs.middle (S ⊗[R] B) ((m₁ + m₂ : S ⊗[R] FR.middle)) =
          algebraMap FRs.middle (S ⊗[R] B) m₁ +
            algebraMap FRs.middle (S ⊗[R] B) m₂ := map_add _ _ _
      rw [ha, ha', map_add, map_add, map_add, h₁, h₂]
    | tmul a n =>
      have h2 : algebraMap FA0sf.middle (Sf ⊗[A] B)
            ((algebraMap S Sf a) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] n)) =
          ((algebraMap S Sf a) ⊗ₜ[A] algebraMap FR.middle B n : Sf ⊗[A] B) :=
        (baseChange_algebraMap_tmul FA0 Sf (algebraMap S Sf a) ((1 : A) ⊗ₜ[R] n)).trans
          (congrArg ((algebraMap S Sf a) ⊗ₜ[A] ·) (hFA0map n))
      have h3 : algebraMap FRs.middle (S ⊗[R] B) (a ⊗ₜ[R] n) =
          (a ⊗ₜ[R] algebraMap FR.middle B n : S ⊗[R] B) :=
        baseChange_algebraMap_tmul FR S a n
      have h4 := tmul_eq_algebraMap_mul_one_tmul (R := A) (algebraMap S Sf a)
        (algebraMap FR.middle B n)
      have h5 := tmul_eq_algebraMap_mul_one_tmul (R := R) a (algebraMap FR.middle B n)
      calc
        e' (algebraMap FA0sf.middle (Sf ⊗[A] B)
              (algebraMap FRs.middle FA0sf.middle (a ⊗ₜ[R] n)))
            = e' (algebraMap Sf (Sf ⊗[A] B) (algebraMap S Sf a) *
                ((1 : Sf) ⊗ₜ[A] algebraMap FR.middle B n)) :=
          congrArg e'
            (((congrArg (algebraMap FA0sf.middle (Sf ⊗[A] B)) (halg a n)).trans h2).trans h4)
        _ = algebraMap Sf (C × D) (algebraMap S Sf a) *
              e ((1 : S) ⊗ₜ[R] algebraMap FR.middle B n) := by
          rw [map_mul, e'.commutes, hdecomp]
        _ = algebraMap S (C × D) a * e ((1 : S) ⊗ₜ[R] algebraMap FR.middle B n) := by
          rw [← IsScalarTower.algebraMap_apply S Sf (C × D) a]
        _ = e (algebraMap FRs.middle (S ⊗[R] B) (a ⊗ₜ[R] n)) := by
          rw [← e.commutes a, ← map_mul]
          exact congrArg e (h3.trans h5).symm
  have : IsScalarTower FRs.middle FA0sf.middle C :=
    IsScalarTower.of_algebraMap_eq fun m => by
      show (e (algebraMap FRs.middle (S ⊗[R] B) m)).1 =
        (e' (algebraMap FA0sf.middle (Sf ⊗[A] B)
          (algebraMap FRs.middle FA0sf.middle m))).1
      exact (congrArg Prod.fst (htargetN m)).symm
  -- The two restriction functionals differ by the localization map.
  let restrS := finiteFactorRestriction FR S C D e (fun _ => rfl) hfinite hprojective
    hmfinite hmprojective
  let restrSf := finiteFactorRestriction FA0 Sf C D e' (fun _ => rfl) hfinite' hprojectiveSf
    hmfiniteSf hmprojectiveSf
  have hres (ω : dualizingModule FR) (c : C) :
      algebraMap S Sf (restrS.1 (dualizingModule.baseChange FR S ω) c) =
        restrSf.1 (dualizingModule.baseChange FA0 Sf
          (dualizingModule_equiv_of_isLocalization_away f FR FA0 ω)) c := by
    refine dualizingModule.induction_on FR (motive := fun ω =>
      algebraMap S Sf (restrS.1 (dualizingModule.baseChange FR S ω) c) =
        restrSf.1 (dualizingModule.baseChange FA0 Sf
          (dualizingModule_equiv_of_isLocalization_away f FR FA0 ω)) c) ω ?_ ?_ ?_
    · simp
    · intro φ b
      let : Algebra FR.middle (A ⊗[R] FR.middle) := Algebra.TensorProduct.rightAlgebra
      let r : FR.middle →ₐ[R] (A ⊗[R] FR.middle) := Algebra.TensorProduct.includeRight
      let ψ : Module.Dual A (A ⊗[R] FR.middle) := φ.baseChange A
      have hrloc : let : Algebra FR.middle FA0.middle := r.toRingHom.toAlgebra
          IsLocalization.Away (algebraMap R FR.middle f) FA0.middle := by
        let : Algebra FR.middle FA0.middle := r.toRingHom.toAlgebra
        show IsLocalization.Away (algebraMap R FR.middle f) (A ⊗[R] FR.middle)
        infer_instance
      have hψ (m : FR.middle) :
          ψ (((1 : A) ⊗ₜ[R] m : A ⊗[R] FR.middle)) = algebraMap R A (φ m) :=
        (Algebra.algebraMap_eq_smul_one (φ m)).symm
      have hdual (m : S ⊗[R] FR.middle) :
          algebraMap S Sf ((Module.Dual.baseChange S φ) m) =
            (Module.Dual.baseChange Sf ψ) (algebraMap FRs.middle FA0sf.middle m) := by
        induction m using TensorProduct.induction_on with
        | zero =>
          have hz : algebraMap FRs.middle FA0sf.middle (0 : S ⊗[R] FR.middle) =
              (0 : Sf ⊗[A] (A ⊗[R] FR.middle)) := map_zero _
          rw [hz]
          simp
        | add m₁ m₂ h₁ h₂ =>
          have ha : algebraMap FRs.middle FA0sf.middle ((m₁ + m₂ : S ⊗[R] FR.middle)) =
              (algebraMap FRs.middle FA0sf.middle m₁ +
                algebraMap FRs.middle FA0sf.middle m₂ :
                  Sf ⊗[A] (A ⊗[R] FR.middle)) := map_add _ _ _
          have hb : (Module.Dual.baseChange Sf ψ)
                ((algebraMap FRs.middle FA0sf.middle m₁ +
                  algebraMap FRs.middle FA0sf.middle m₂ :
                    Sf ⊗[A] (A ⊗[R] FR.middle))) =
              (Module.Dual.baseChange Sf ψ) (algebraMap FRs.middle FA0sf.middle m₁) +
                (Module.Dual.baseChange Sf ψ)
                  (algebraMap FRs.middle FA0sf.middle m₂) := map_add _ _ _
          rw [ha, hb, map_add, map_add, h₁, h₂]
        | tmul a n =>
          have hL : (Module.Dual.baseChange S φ) (a ⊗ₜ[R] n) = φ n • a := rfl
          have hR : (Module.Dual.baseChange Sf ψ)
                ((algebraMap S Sf a) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] n)) =
              ψ (((1 : A) ⊗ₜ[R] n : A ⊗[R] FR.middle)) • (algebraMap S Sf a) := rfl
          rw [halg a n, hL, hR, hψ n, Algebra.smul_def, Algebra.smul_def, map_mul,
            ← IsScalarTower.algebraMap_apply R S Sf,
            ← IsScalarTower.algebraMap_apply R A Sf]
      have heq :=
        dualizingModule_equiv_of_isLocalization_away_tmul f FR FA0 r hrloc hFA0map φ ψ hψ b
      have hvalue := finiteProjectiveTrace_lmul_isLocalizationAway
        (S := FRs.middle) (Sf := FA0sf.middle) (C := C) (algebraMap S FRs.middle q)
        ((e ((1 : S) ⊗ₜ[R] b)).1 * c)
      calc
        algebraMap S Sf (restrS.1 (dualizingModule.baseChange FR S
              (dualizingModule.tmul FR φ b)) c) =
            algebraMap S Sf ((Module.Dual.baseChange S φ)
              (finiteProjectiveTrace FRs.middle C (Algebra.lmul FRs.middle C
                ((e ((1 : S) ⊗ₜ[R] b)).1 * c)))) :=
          congrArg (algebraMap S Sf)
            (restrS.2 (Module.Dual.baseChange S φ) ((1 : S) ⊗ₜ[R] b) c)
        _ = (Module.Dual.baseChange Sf ψ) (algebraMap FRs.middle FA0sf.middle
              (finiteProjectiveTrace FRs.middle C (Algebra.lmul FRs.middle C
                ((e ((1 : S) ⊗ₜ[R] b)).1 * c)))) := hdual _
        _ = (Module.Dual.baseChange Sf ψ)
              (finiteProjectiveTrace FA0sf.middle C (Algebra.lmul FA0sf.middle C
                ((e ((1 : S) ⊗ₜ[R] b)).1 * c))) :=
          congrArg (Module.Dual.baseChange Sf ψ) hvalue.symm
        _ = restrSf.1 (dualizingModule.baseChange FA0 Sf
              (dualizingModule_equiv_of_isLocalization_away f FR FA0
                (dualizingModule.tmul FR φ b))) c := by
          rw [heq]
          symm
          refine (restrSf.2 (Module.Dual.baseChange Sf ψ) ((1 : Sf) ⊗ₜ[A] b) c).trans ?_
          rw [hdecomp]
          rfl
    · intro ω₁ ω₂ h₁ h₂
      simp only [map_add, LinearMap.add_apply, h₁, h₂]
  have hpoint (c : C) :
      algebraMap S Sf (restrS.1 (dualizingModule.baseChange FR S τR) c) =
        algebraMap S Sf ((finiteProjectiveTrace S C).comp (Algebra.lmul S C).toLinearMap c) := by
    rw [hres τR c]
    refine (congrArg (fun k : Module.Dual Sf C => k c) htraceSf).trans ?_
    exact finiteProjectiveTrace_lmul_isLocalizationAway (S := S) (Sf := Sf) (C := C) q c
  exact ⟨hprojective, hmfinite, hmprojective,
    linearMap_eq_of_isLocalization_away q hfC _ _ hpoint⟩

end Stacks.Discriminant

end
