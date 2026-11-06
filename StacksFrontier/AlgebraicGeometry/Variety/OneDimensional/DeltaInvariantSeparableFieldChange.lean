module

public import Mathlib.RingTheory.TensorProduct.Quotient
import StacksFrontier.RingTheory.KrullDimension.QuotientHeight
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalPresentation
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationSeparableResidue
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Serre.Criterion

/-!
# The delta invariant is unchanged by a separable extension of the ground field

Let `k` be a field, let `X` be locally of finite type over `k`, and let `x` be a point at which
the local ring is reduced of dimension one and all residue fields of the normalization above `x`
are separable over `k`. Then the delta invariant of `X` at `x` equals the delta invariant of the
base change `X_K` at any one-dimensional point above `x`.

## Main results

* `AlgebraicGeometry.deltaInvariant_stalk_baseChange`: equality of the two delta invariants.

## Implementation notes

The base change is Mathlib's categorical pullback of the structure morphism along
`Spec K ⟶ Spec k`, and the delta invariant of a scheme at a point is the ring-theoretic
invariant of its stalk. Under the separability hypothesis the normalization becomes
geometrically regular above `x`, hence geometrically normal, so its base change is already
normal and computes the integral closure of the base-changed stalk; the two quotients defining
the invariants then have the same length.

## References

* [Stacks Project, Tag 0C3Y](https://stacks.math.columbia.edu/tag/0C3Y)
-/

@[expose] public noncomputable section

open CategoryTheory Limits CommRingCat
open AlgebraicGeometry
open IsLocalRing

universe u v

namespace AlgebraicGeometry

open scoped TensorProduct

private theorem isGeometricallyNormal_of_isGeometricallyRegular
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    (h : Algebra.IsGeometricallyRegular k R) : Algebra.IsGeometricallyNormal k R := by
  refine ⟨fun L _ _ => ?_⟩
  refine isNormalRing_tensorProduct_of_forall_fg_intermediateField fun F hF => ?_
  have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  have : Small.{u} F := Algebra.EssFiniteType.small_of_field k F
  have : IsRegularRing (F ⊗[k] R) := h.isRegularRing_tensorProduct F
  exact main_theorem0567 _

private lemma deltaInvariant_eq_of_integralClosure_baseChange
    {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (e : B ⊗[A] (integralClosure A (FractionRing A)) ≃ₐ[B]
      integralClosure B (FractionRing B))
    (hfiber : Module.length B (B ⧸ extendedMaximalIdeal A B) = 1) :
    Ring.deltaInvariant A = Ring.deltaInvariant B := by
  let C := integralClosure A (FractionRing A)
  let D := integralClosure B (FractionRing B)
  let fA : A →ₗ[A] C := Algebra.linearMap A C
  let fB : B →ₗ[B] D := Algebra.linearMap B D
  let lf : (B ⊗[A] A) →ₗ[B] (B ⊗[A] C) :=
    TensorProduct.AlgebraTensorModule.lTensor B B fA
  let rid := TensorProduct.AlgebraTensorModule.rid A B B
  have hcompat : e.toLinearEquiv.toLinearMap.comp lf = fB.comp rid.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b a
    show e (b ⊗ₜ[A] algebraMap A C a) =
      algebraMap B D (a • b)
    have ht : (b ⊗ₜ[A] algebraMap A C a) =
        algebraMap B (B ⊗[A] C) (a • b) := by
      show (b ⊗ₜ[A] algebraMap A C a) = (a • b) ⊗ₜ[A] (1 : C)
      simpa only [Algebra.smul_def, mul_one] using
        (TensorProduct.smul_tmul a b (1 : C)).symm
    rw [ht, e.commutes]
  let P : Submodule B (B ⊗[A] C) := LinearMap.range lf
  let Q : Submodule B D := LinearMap.range fB
  have hPQ : P.map e.toLinearEquiv.toLinearMap = Q := by
    dsimp only [P, Q]
    rw [← LinearMap.range_comp, hcompat,
      LinearMap.range_comp_of_range_eq_top _ rid.range]
  let eqv : ((B ⊗[A] C) ⧸ P) ≃ₗ[B] D ⧸ Q := Submodule.Quotient.equiv P Q
    e.toLinearEquiv hPQ
  have hbaseQuotient :
      B ⊗[A] (C ⧸ LinearMap.range fA) ≃ₗ[B]
        (B ⊗[A] C) ⧸ P := by
    let et0 := TensorProduct.tensorQuotientEquiv B (LinearMap.range fA)
    let Pbase : Submodule A (B ⊗[A] C) :=
      LinearMap.range (TensorProduct.map (LinearMap.id : B →ₗ[A] B)
        (Submodule.subtype (LinearMap.range fA)))
    have hPbase : Pbase = P.restrictScalars A := by
      show LinearMap.range (LinearMap.lTensor B
        (Submodule.subtype (LinearMap.range fA))) = LinearMap.range (LinearMap.lTensor B fA)
      exact (LinearMap.lTensor_range (Q := B) (g := fA)).symm
    let qP : ((B ⊗[A] C) ⧸ Pbase) ≃ₗ[A]
      ((B ⊗[A] C) ⧸ P.restrictScalars A) := Pbase.quotEquivOfEq _ hPbase
    let qR := Submodule.Quotient.restrictScalarsEquiv A P
    let etA := et0.trans (qP.trans qR)
    exact
      { toFun := etA
        invFun := etA.symm
        left_inv := etA.left_inv
        right_inv := etA.right_inv
        map_add' := etA.map_add
        map_smul' := by
          intro b x
          induction x using TensorProduct.induction_on with
          | zero => simp [etA]
          | add x y hx hy => simp [hx, hy]
          | tmul x y =>
            obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
            dsimp [etA]
            have hmk (z : B) (c : C) :
                qR (qP (et0 (z ⊗ₜ[A] Submodule.Quotient.mk c))) =
                  Submodule.Quotient.mk (z ⊗ₜ[A] c) := by
              simp [qP, qR, et0, TensorProduct.tensorQuotientEquiv_apply_mk_tmul]
            show qR (qP (et0 ((b * x) ⊗ₜ[A] Submodule.Quotient.mk y))) =
              b • qR (qP (et0 (x ⊗ₜ[A] Submodule.Quotient.mk y)))
            rw [hmk (b * x) y, hmk x y, ← Submodule.Quotient.mk_smul]
            congr 1 }
  calc
    Ring.deltaInvariant A = Module.length A (C ⧸ LinearMap.range fA) := rfl
    _ = Module.length A (C ⧸ LinearMap.range fA) *
          Module.length B (B ⧸ extendedMaximalIdeal A B) := by rw [hfiber, mul_one]
    _ = Module.length B (B ⊗[A] (C ⧸ LinearMap.range fA)) :=
      length_baseChange_eq_length_mul_length_quotient A B
        (C ⧸ LinearMap.range fA)
    _ = Module.length B (D ⧸ Q) := (hbaseQuotient.trans eqv).length_eq
    _ = Ring.deltaInvariant B := rfl

private theorem isFractionRing_of_injective_map
    {B C : Type u} [CommRing B] [Nontrivial B] [CommRing C] [Algebra B C]
    (fQ : C →+* FractionRing B) (hfQinj : Function.Injective fQ)
    (hfQB : ∀ b : B, fQ (algebraMap B C b) = algebraMap B (FractionRing B) b) :
    letI : Algebra C (FractionRing B) := fQ.toAlgebra
    IsFractionRing C (FractionRing B) := by
  have hBqinj : Function.Injective (algebraMap B (FractionRing B)) :=
    IsLocalization.injective (FractionRing B) le_rfl
  have hBtoC : Function.Injective (algebraMap B C) := fun x y hxy =>
    hBqinj (by rw [← hfQB, ← hfQB, hxy])
  have hreg (s : B) (hs : s ∈ nonZeroDivisors B) :
      algebraMap B C s ∈ nonZeroDivisors C := by
    refine mem_nonZeroDivisors_iff_right.mpr fun c hcs => ?_
    have hz : fQ c * algebraMap B (FractionRing B) s = 0 := by
      simpa [map_mul, hfQB] using congrArg fQ hcs
    have hc : fQ c = 0 :=
      (IsLocalization.map_units (FractionRing B) ⟨s, hs⟩).mul_left_eq_zero.mp
        (by simpa [mul_comm] using hz)
    apply hfQinj
    show fQ c = fQ 0
    simpa using hc
  let : Algebra C (FractionRing B) := fQ.toAlgebra
  let : IsScalarTower B C (FractionRing B) := IsScalarTower.of_algebraMap_eq fun b => by
    show algebraMap B (FractionRing B) b = fQ (algebraMap B C b)
    exact (hfQB b).symm
  refine ⟨?_, ?_, ?_⟩
  · intro c
    obtain ⟨⟨b, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors B) (fQ c)
    by_contra hunit
    have hb : b ∉ nonZeroDivisors B := by
      intro hb
      have hbunit := IsLocalization.map_units (FractionRing B) ⟨b, hb⟩
      have hmulunit : IsUnit (fQ c * algebraMap B (FractionRing B) s) := by
        rw [hcs]
        exact hbunit
      exact hunit (IsUnit.mul_iff.mp hmulunit |>.1)
    have hbad : ∃ t : B, t ≠ 0 ∧ b * t = 0 := by
      by_contra hh
      have hregb : b ∈ nonZeroDivisors B := by
        refine mem_nonZeroDivisors_iff_right.mpr fun t htb => ?_
        by_contra ht
        exact hh ⟨t, ht, by simpa [mul_comm] using htb⟩
      exact hb hregb
    obtain ⟨t, ht, hbt⟩ := hbad
    have hst0 : (s : B) * t ≠ 0 := by
      intro hst
      have hts : t * (s : B) = 0 := by simpa [mul_comm] using hst
      exact ht ((mem_nonZeroDivisors_iff_right.mp s.2) t hts)
    have hzero : fQ c * fQ (algebraMap B C ((s : B) * t)) = 0 := by
      calc
        _ = fQ c * (algebraMap B (FractionRing B) s *
            algebraMap B (FractionRing B) t) := by
          rw [hfQB, map_mul]
        _ = (fQ c * algebraMap B (FractionRing B) s) *
            algebraMap B (FractionRing B) t := by ring
        _ = algebraMap B (FractionRing B) b * algebraMap B (FractionRing B) t := by
          rw [hcs]
        _ = algebraMap B (FractionRing B) ((b : B) * t) := (map_mul _ _ _).symm
        _ = 0 := by rw [hbt, map_zero]
    have hcprod : c * algebraMap B C (s * t) = 0 := hfQinj (by
      simpa [map_mul] using hzero)
    have hzero' : algebraMap B C ((s : B) * t) * c = 0 := by
      simpa [mul_comm] using hcprod
    have := (mem_nonZeroDivisors_iff_right.mp c.2)
      (algebraMap B C ((s : B) * t)) hzero'
    exact hst0 (hBtoC (by simpa using this))
  · intro z
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (nonZeroDivisors B) z
    refine ⟨⟨algebraMap B C b, ⟨algebraMap B C (s : B), hreg s s.2⟩⟩, ?_⟩
    show z * fQ (algebraMap B C s) = fQ (algebraMap B C b)
    rw [hfQB, hfQB]
    exact hbs
  · intro x y hxy
    exact ⟨1, by simp [hfQinj hxy]⟩

private noncomputable def integralClosureTensorProductEquivOfIsNormal
    (A B : Type u) [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra A B] [Module.Flat A B]
    (h : IsNormalRing
      (B ⊗[A] integralClosure A (FractionRing A))) :
    B ⊗[A] integralClosure A (FractionRing A) ≃ₐ[B]
      integralClosure B (FractionRing B) := by
  let NA := integralClosure A (FractionRing A)
  let NB := integralClosure B (FractionRing B)
  let C := B ⊗[A] NA
  let ι : NA →ₗ[A] FractionRing A := NA.val.toLinearMap
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hNDZ : ∀ a : A, a ∈ nonZeroDivisors A →
      algebraMap A B a ∈ nonZeroDivisors B := by
    intro a ha
    refine mem_nonZeroDivisors_iff_right.mpr fun b hb => ?_
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha
    simpa only [Algebra.smul_def, mul_comm, zero_mul] using hb
  have hWle : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro _ ⟨a, ha, rfl⟩
    exact hNDZ a ha
  let T := B ⊗[A] FractionRing A
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) T :=
    IsLocalization.tensor (FractionRing A) (nonZeroDivisors A)
  have hu : ∀ y : Algebra.algebraMapSubmonoid B (nonZeroDivisors A),
      IsUnit (algebraMap B (FractionRing B) y) := fun y =>
    IsLocalization.map_units (FractionRing B) ⟨y.1, hWle y.2⟩
  let F : T →+* FractionRing B := IsLocalization.lift hu
  have hFc (b : B) : F (algebraMap B T b) = algebraMap B (FractionRing B) b :=
    IsLocalization.lift_eq hu b
  have hBqinj : Function.Injective (algebraMap B (FractionRing B)) :=
    IsLocalization.injective (FractionRing B) le_rfl
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) z
    have ha : algebraMap B (FractionRing B) a = 0 := by
      rw [← hFc a, ← hs, map_mul, hz, zero_mul]
    have ha0 : a = 0 := hBqinj (by rw [ha, map_zero])
    have hz0 : z * algebraMap B T (s : B) = 0 := by
      rw [hs, ha0, map_zero]
    exact (IsLocalization.map_units T s).mul_left_eq_zero.mp hz0
  let FA : T →ₐ[B] FractionRing B := { F with commutes' := hFc }
  let φ : FractionRing A →ₐ[A] FractionRing B :=
    (FA.restrictScalars A).comp Algebra.TensorProduct.includeRight
  let α : C →ₐ[B] T := Algebra.TensorProduct.map (AlgHom.id B B) NA.val
  have hα : α.toLinearMap = LinearMap.baseChange B ι := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b a
    change (b ⊗ₜ[A] (a : FractionRing A)) = b ⊗ₜ[A] (a : FractionRing A)
    rfl
  have hαinj : Function.Injective α := by
    change Function.Injective α.toLinearMap
    rw [hα, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ι hιinj
  let g : C →ₐ[B] FractionRing B := FA.comp α
  have hginj : Function.Injective g := hFinj.comp hαinj
  have hgmem : ∀ z : C, g z ∈ NB := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [g]
    | add z w hz hw =>
      rw [map_add]
      exact NB.add_mem hz hw
    | tmul b a =>
      have hz : (b ⊗ₜ[A] a : C) = b • (1 ⊗ₜ[A] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hgx : g (1 ⊗ₜ[A] a) = φ (a : FractionRing A) := by
        change F (1 ⊗ₜ[A] (a : FractionRing A)) = F (1 ⊗ₜ[A] (a : FractionRing A))
        rfl
      rw [hz, map_smul, hgx]
      have ha : (φ (a : FractionRing A) : FractionRing B) ∈ NB :=
        (a.property.map φ).tower_top (A := B)
      have hb : algebraMap B (FractionRing B) b ∈ NB := (algebraMap B NB b).property
      simpa [Algebra.smul_def] using NB.mul_mem hb ha
  let E : C →ₐ[B] NB := g.codRestrict NB hgmem
  have hEinj : Function.Injective E := fun _ _ he => hginj
    (congrArg Subtype.val he)
  let fQ : C →+* FractionRing B := (algebraMap NB (FractionRing B)).comp E.toRingHom
  have hfQB (b : B) : fQ (algebraMap B C b) = algebraMap B (FractionRing B) b := by
    simp [fQ]
  have hfQinj : Function.Injective fQ := fun _ _ he => hEinj (Subtype.ext he)
  letI : Algebra C (FractionRing B) := fQ.toAlgebra
  letI : IsScalarTower B C (FractionRing B) := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap B (FractionRing B) b = fQ (algebraMap B C b)
    exact (hfQB b).symm
  letI : IsFractionRing C (FractionRing B) :=
    isFractionRing_of_injective_map fQ hfQinj hfQB
  have hIC : IsIntegrallyClosedIn C (FractionRing B) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing B)).mp h.isIntegrallyClosed
  have hEsurj : Function.Surjective E := by
    intro y
    obtain ⟨z, hz⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral
      (R := C) (A := FractionRing B) (x := (y : FractionRing B))
      (y.property.tower_top (A := C))
    exact ⟨z, Subtype.ext hz⟩
  exact AlgEquiv.ofBijective E ⟨hEinj, hEsurj⟩

private lemma ringKrullDim_quotient_map_maximalIdeal_eq_zero
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hdim : ringKrullDim B = ringKrullDim A) :
    ringKrullDim (B ⧸ extendedMaximalIdeal A B) = 0 := by
  have hheight :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [show (maximalIdeal B).height = (maximalIdeal A).height by
    exact_mod_cast (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B)).trans
      (hdim.trans (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).symm)] at hheight
  have hfiber := WithTop.add_left_cancel (x := (maximalIdeal A).height)
    Ideal.height_ne_top_of_isPrime
    (hheight.symm.trans (add_zero _).symm)
  show ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) = 0
  rw [IsLocalRing.ringKrullDim_quotient_eq_height_map_maximalIdeal
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne, hfiber]
  norm_num

private lemma length_fiber_eq_one_of_isReduced
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hdim : ringKrullDim B = ringKrullDim A)
    (hred : _root_.IsReduced (B ⧸ extendedMaximalIdeal A B)) :
    Module.length B (B ⧸ extendedMaximalIdeal A B) = 1 := by
  let I := extendedMaximalIdeal A B
  let F := B ⧸ I
  have hdimF : ringKrullDim F = 0 :=
    ringKrullDim_quotient_map_maximalIdeal_eq_zero A B hdim
  let : Nontrivial F := Ideal.Quotient.nontrivial_iff.mpr
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  let : IsLocalRing F := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let : _root_.IsReduced F := hred
  have hFle : Ring.KrullDimLE 0 F :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero).2 hdimF
  have hfield : IsField F := hFle.isField_of_isReduced
  let : Field F := hfield.toField
  have hImax : I.IsMaximal := by
    simpa using RingHom.ker_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  show Module.length B (B ⧸ I) = 1
  rw [IsLocalRing.eq_maximalIdeal hImax]
  show Module.length B (IsLocalRing.ResidueField B) = 1
  rw [Module.length_eq_of_surjective (M := IsLocalRing.ResidueField B)
    (IsLocalRing.residue_surjective (R := B))]
  simp

private noncomputable def localizationAtMinimalPrimeEquivResidueField
    (A : Type u) [CommRing A] [_root_.IsReduced A]
    (p : minimalPrimes A) (hp : p.1.IsPrime) :
      @Localization.AtPrime A _ p.1 hp ≃ₐ[A] @Ideal.ResidueField A _ p.1 hp := by
  letI : p.1.IsPrime := hp
  letI : Field (@Localization.AtPrime A _ p.1 hp) :=
    (isField_localizationAtPrime_of_minimal A p.1 p.2).toField
  let f : @Localization.AtPrime A _ p.1 hp →ₐ[A] @Ideal.ResidueField A _ p.1 hp :=
    IsScalarTower.toAlgHom A (@Localization.AtPrime A _ p.1 hp)
      (@Ideal.ResidueField A _ p.1 hp)
  exact AlgEquiv.ofBijective f ⟨f.toRingHom.injective, IsLocalRing.residue_surjective⟩

private noncomputable def minimalPrimeResidueFieldProductEquivFractionRing
    (A : Type u) [CommRing A] [_root_.IsReduced A] [Finite (minimalPrimes A)] :
    Stacks.NormalizationStalkAmbient.minimalPrimeResidueFieldProduct A ≃ₐ[A] FractionRing A := by
  letI : (p : minimalPrimes A) → (p.1).IsPrime := fun p => p.2.1.1
  let e := (Finite.equivFin (minimalPrimes A)).symm
  let q : Fin (Nat.card (minimalPrimes A)) → Ideal A := fun i => (e i : Ideal A)
  have hunion : (⋃ i, (q i : Set A)) = ⋃ p ∈ minimalPrimes A, (p : Set A) := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i =>
        Set.subset_biUnion_of_mem (s := minimalPrimes A) (e i).2
    · intro x hx
      obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      change x ∈ (e i : Ideal A)
      have hval : (e i : Ideal A) = p :=
        congrArg (fun z : minimalPrimes A => (z : Ideal A)) hi
      rw [hval]
      exact hpx
  have hzd : zeroDivisorsSet A = ⋃ i, (q i : Set A) := by
    have hsets : zeroDivisorsSet A = zeroDivisorSet A :=
      Set.ext fun x => mem_zeroDivisorsSet_iff x
    rw [hsets, ← iUnion_minimalPrimes_eq_zeroDivisors A, hunion]
  let eFrac := Classical.choice (total_fraction_ring_isoProd_localization_atPrime
    (Nat.card (minimalPrimes A)) q (fun i => (e i).2)
    (fun i j hij => e.injective (Subtype.ext hij)) hzd)
  let eLoc : (∀ i : Fin (Nat.card (minimalPrimes A)), Localization.AtPrime (q i)) ≃ₐ[A]
      (∀ p : minimalPrimes A, Localization.AtPrime (p : Ideal A)) :=
    AlgEquiv.piCongrLeft A (fun p : minimalPrimes A =>
      Localization.AtPrime (p : Ideal A)) e
  let eRes : (∀ p : minimalPrimes A, Localization.AtPrime (p : Ideal A)) ≃ₐ[A]
      Stacks.NormalizationStalkAmbient.minimalPrimeResidueFieldProduct A :=
    AlgEquiv.piCongrRight fun p =>
      localizationAtMinimalPrimeEquivResidueField A p p.2.1.1
  exact ((eFrac.trans eLoc).trans eRes).symm

private noncomputable def minimalPrimeResidueFieldProductRingEquivFractionRing
    (A : Type u) [CommRing A] [_root_.IsReduced A] [Finite (minimalPrimes A)] :
    Stacks.NormalizationStalkAmbient.minimalPrimeResidueFieldProduct A ≃+* FractionRing A :=
  (minimalPrimeResidueFieldProductEquivFractionRing A).toRingEquiv

private lemma minimalPrimeResidueFieldProductRingEquivFractionRing_commutes
    (A : Type u) [CommRing A] [_root_.IsReduced A] [Finite (minimalPrimes A)] (a : A) :
    minimalPrimeResidueFieldProductRingEquivFractionRing A
      (Stacks.NormalizationStalkAmbient.minimalPrimeResidueFieldProductHom A a) =
      algebraMap A (FractionRing A) a :=
  (minimalPrimeResidueFieldProductEquivFractionRing A).commutes a

private theorem isNormalRing_of_normal_maximal_localizations
    {R : Type*} [CommRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], IsNormalRing (Localization.AtPrime m)) :
    IsNormalRing R := by
  intro q hq
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q hq.ne_top
  let : m.IsMaximal := hm
  let S := Localization.AtPrime m
  let Q : Ideal S := q.map (algebraMap R S)
  have hdisj : Disjoint (m.primeCompl : Set R) (q : Set R) := by
    rw [Set.disjoint_left]
    intro r hr hq'
    exact hr (hqm hq')
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    m.primeCompl S q hq hdisj
  let : Q.IsPrime := hQ
  have hunder : Q.comap (algebraMap R S) = q :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl S hq hdisj
  let T := Localization.AtPrime Q
  have hloc : IsLocalization.AtPrime T q := by
    have ht : IsLocalization.AtPrime T (Q.comap (algebraMap R S)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := m.primeCompl) T Q
    simpa [hunder] using ht
  let : IsLocalization q.primeCompl T := hloc
  let e : Localization.AtPrime q ≃+* T :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) T
  have hT' : IsDomain T ∧ IsIntegrallyClosed T := by
    let : Algebra S T := inferInstance
    let : IsLocalization.AtPrime T Q := inferInstance
    exact (h m).atPrime Q T
  let : IsDomain T := hT'.1
  let : IsIntegrallyClosed T := hT'.2
  exact ⟨Function.Injective.isDomain e.toRingHom e.injective,
    IsIntegrallyClosed.of_equiv e.symm⟩

/- `stalkMap_isIso_of_flat_preimmersion` stood here, one of four private copies of one
statement. All four are replaced by the public
`AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`,
`StacksFrontier/AlgebraicGeometry/Pullback/StalkFromSpecStalk.lean:68`, whose proof is the same
and which every one of the four modules already imported. -/

/-- The local ring at a point of a base change `Z_K` is a localization of the tensor product
`O_{Z,a} ⊗[k] K`, compatibly with the map from `O_{Z,a}`. -/
private lemma exists_isLocalization_tensorProduct_stalk
    {k K : Type u} [Field k] [Field K] [Algebra k K] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    (z : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    letI : Algebra k (Z.presheaf.stalk
        (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z)) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk
          (g.base (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z))) :=
        StructureSheaf.stalkAlgebra k
          (g.base (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z))
      ((g.stalkMap (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z)).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk
          (g.base (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z))))).toAlgebra
    ∃ φ : Z.presheaf.stalk (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z) ⊗[k]
        K →+* (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk z,
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
        ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap z).hom ∧
      letI : Algebra (Z.presheaf.stalk
          (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z) ⊗[k] K)
        ((pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk z) := φ.toAlgebra
      ∃ M : Submonoid (Z.presheaf.stalk
          (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z) ⊗[k] K),
        IsLocalization M ((pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk z) := by
  let h := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pZ := pullback.fst g h
  let pK := pullback.snd g h
  let a := pZ z
  let b : PrimeSpectrum K := pK z
  have hh : g a = h b := by
    simpa [a, b] using congrArg (fun j : pullback g h ⟶ Spec (.of k) => j z)
      pullback.condition
  let R := (Spec (.of k)).presheaf.stalk (g.base a)
  let A := Z.presheaf.stalk a
  let B := (Spec (.of K)).presheaf.stalk b
  let algebraKR : Algebra k R := StructureSheaf.stalkAlgebra k (g.base a)
  let algebraRA : Algebra R A := (g.stalkMap a).hom.toAlgebra
  let : Algebra R A := algebraRA
  let algebraKA : Algebra k A := ((g.stalkMap a).hom.comp
    (algebraMap k R)).toAlgebra
  let : Algebra k A := algebraKA
  have towerKRA : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  let algebraKB : Algebra K B := StructureSheaf.stalkAlgebra K b
  let algebraBaseB : Algebra k B :=
    ((algebraMap K B).comp (algebraMap k K)).toAlgebra
  have towerKKB : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  let algebraRB : Algebra R B := ((eqToHom
    (congrArg (Spec (.of k)).presheaf.stalk hh)) ≫ h.stalkMap b).hom.toAlgebra
  let : Algebra R B := algebraRB
  have towerKRB : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq'
    (stalkMap_spec_comp_algebraMap b (g.base a) hh).symm
  let z₀ : PrimeSpectrum k := g.base a
  have locR : IsLocalization.AtPrime R z₀.asIdeal := by
    show IsLocalization.AtPrime ((structurePresheafInCommRingCat k).stalk z₀)
      z₀.asIdeal
    infer_instance
  have locB : IsLocalization.AtPrime B b.asIdeal := by
    show IsLocalization.AtPrime ((structurePresheafInCommRingCat K).stalk b) b.asIdeal
    infer_instance
  have hr : Function.Bijective (algebraMap k R) :=
    Field.localization_map_bijective (M := z₀.asIdeal.primeCompl) (by simp)
  have hb : Function.Bijective (algebraMap K B) :=
    Field.localization_map_bijective (M := b.asIdeal.primeCompl) (by simp)
  let eB : K ≃ₐ[k] B := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K B) hb
  have compatible : TensorProduct.CompatibleSMul k R A B :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective A B hr.surjective
  let e : A ⊗[k] K ≃ₐ[A] A ⊗[R] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eB).trans
      (Algebra.TensorProduct.equivOfCompatibleSMul k R A A B).symm
  obtain ⟨φ, hleft, _, M, hM⟩ := BaseChangeStalk.pullback_stalk_isLocalization g h z
  change Submonoid (A ⊗[R] B) at M
  refine ⟨φ.comp e.toRingEquiv.toRingHom, ?_, ?_⟩
  · rw [← hleft]
    ext x
    change φ (e (x ⊗ₜ[k] 1)) = φ (x ⊗ₜ[R] 1)
    simp [e]
    rfl
  · let C := (pullback g h : Scheme.{u}).presheaf.stalk z
    let : Algebra (A ⊗[R] B) C := φ.toAlgebra
    let : IsLocalization M C := hM
    let : Algebra (A ⊗[k] K) C := (φ.comp e.toRingEquiv.toRingHom).toAlgebra
    exact ⟨M.comap e.toRingEquiv, IsLocalization.of_ringEquiv_left e.toRingEquiv
      (Submonoid.map_comap_eq_self_of_surjective e.surjective) fun _ => rfl⟩

private lemma isNormalRing_pullbackStalk_of_isGeometricallyNormal
    {k K : Type u} [Field k] [Field K] [Algebra k K]
  {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) (a : Z)
  (z : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
  (hza : pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z = a)
  (hgeo :
    letI : Algebra k (Z.presheaf.stalk a) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (g.base a)) :=
        StructureSheaf.stalkAlgebra k (g.base a)
      ((g.stalkMap a).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base a)))).toAlgebra
    Algebra.IsGeometricallyNormal k (Z.presheaf.stalk a)) :
  IsNormalRing
    ((pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}).presheaf.stalk z) := by
  subst hza
  obtain ⟨φ, -, M, hM⟩ := exists_isLocalization_tensorProduct_stalk g z
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base (pullback.fst g _ z))) :=
    StructureSheaf.stalkAlgebra k _
  let : Algebra k (Z.presheaf.stalk (pullback.fst g _ z)) :=
    ((g.stalkMap _).hom.comp (algebraMap k _)).toAlgebra
  let : Algebra _ ((pullback g _ : Scheme.{u}).presheaf.stalk z) := φ.toAlgebra
  have := hM
  exact (IsNormalRing.congr (Algebra.TensorProduct.comm _ K _).toRingEquiv
    (hgeo.isNormalRing_tensorProduct K)).isLocalization M _


private lemma stalkResidue_algebraMap (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k ((Spec (.of k)).presheaf.stalk (f x)) :=
      StructureSheaf.stalkAlgebra k (f x)
    (X.residue x).hom.comp ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f x)))) =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
  show ((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec (.of k)).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x ≫ X.residue x).hom = _
  rw [← Scheme.residue_residueFieldMap f x, ← Category.assoc
    ((Spec (.of k)).presheaf.germ ⊤ (f x) trivial)]
  show ((Scheme.ΓSpecIso (.of k)).inv ≫
    (Spec (.of k)).Γevaluation (f x) ≫ f.residueFieldMap x).hom = _
  rw [Scheme.Γevaluation_naturality]

private lemma residueField_geometricallyReduced_of_separable_above
    (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (ν : Z ⟶ X) (z : Z) (x : X) (hx : ν z = x)
    (hsep : letI : Algebra k (Z.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Z.Γevaluation z).hom.toAlgebra
      Algebra.IsSeparableExtension k (Z.residueField z)) :
    letI : Algebra k (X.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (f x)) :=
        StructureSheaf.stalkAlgebra k (f x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f x)))).toAlgebra
    Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  subst x
  let : Algebra k (X.presheaf.stalk (ν z)) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f (ν z))) :=
      StructureSheaf.stalkAlgebra k (f (ν z))
    ((f.stalkMap (ν z)).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f (ν z))))).toAlgebra
  let : Algebra k (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Z.Γevaluation z).hom.toAlgebra
  let : Algebra k (X.residueField (ν z)) :=
    inferInstanceAs (Algebra k (IsLocalRing.ResidueField (X.presheaf.stalk (ν z))))
  let i : X.residueField (ν z) →ₐ[k] Z.residueField z :=
    { (ν.residueFieldMap z).hom with
      commutes' := by
        intro a
        have hc := stalkResidue_algebraMap k f (ν z)
        have hn := Scheme.Γevaluation_naturality ν z
        have hh : (ν.residueFieldMap z).hom.comp
            (algebraMap k (X.residueField (ν z))) =
            algebraMap k (Z.residueField z) := by
          rw [show algebraMap k (X.residueField (ν z)) =
            ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (ν z)).hom
            from hc]
          show ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            X.Γevaluation (ν z) ≫ ν.residueFieldMap z).hom = _
          rw [hn]
          rfl
        exact DFunLike.congr_fun hh a }
  have : Algebra.IsGeometricallyReduced k (Z.residueField z) := by
    rw [Algebra.isGeometricallyReduced_field_iff]
    have : _root_.IsReduced (Z.residueField z ⊗[k] AlgebraicClosure k) :=
      Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
        (Or.inl hsep)
    exact isReduced_of_injective
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) (Z.residueField z))
      (AlgEquiv.injective _)
  exact Algebra.IsGeometricallyReduced.of_injective i i.injective

private lemma isReduced_closedFiber_of_geometricallyReduced_residueField
    {k K : Type u} [Field k] [Field K] [Algebra k K]
  {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) (a : Z)
  (z : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
  (hza : pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z = a)
  (hgeo :
    letI : Algebra k (Z.presheaf.stalk a) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (g.base a)) :=
        StructureSheaf.stalkAlgebra k (g.base a)
      ((g.stalkMap a).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (g.base a)))).toAlgebra
    Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField (Z.presheaf.stalk a))) :
  let A := Z.presheaf.stalk
    (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))) z)
  let C := (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk z
  letI : Algebra A C :=
    ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap z).hom.toAlgebra
  _root_.IsReduced (C ⧸ (maximalIdeal A).map (algebraMap A C)) := by
  intro A C
  subst hza
  obtain ⟨φ, hleft, M, hM⟩ := exists_isLocalization_tensorProduct_stalk g z
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g.base (pullback.fst g _ z))) :=
    StructureSheaf.stalkAlgebra k _
  let : Algebra k A := ((g.stalkMap _).hom.comp (algebraMap k _)).toAlgebra
  let : Algebra A C := ((pullback.fst g _).stalkMap z).hom.toAlgebra
  let : Algebra (↑A ⊗[k] K) C := φ.toAlgebra
  have := hM
  let I := maximalIdeal A
  let J := I.map (algebraMap A (↑A ⊗[k] K))
  have : _root_.IsReduced ((↑A ⧸ I) ⊗[k] K) := by
    have : Algebra.IsGeometricallyReduced k (↑A ⧸ I) := hgeo
    exact isReduced_of_injective (Algebra.TensorProduct.comm k (↑A ⧸ I) K) (AlgEquiv.injective _)
  have : _root_.IsReduced ((↑A ⊗[k] K) ⧸ J) :=
    isReduced_of_injective _
      (Algebra.TensorProduct.quotientTensorEquiv (R := k) k K A I).symm.injective
  have hmap : (J.map (algebraMap (↑A ⊗[k] K) C)).IsRadical := by
    rw [← Ideal.radical_eq_iff, ← IsLocalization.map_radical M C,
      ((Ideal.isRadical_iff_quotient_reduced J).mpr inferInstance).radical]
  rw [Ideal.map_map, show (algebraMap _ C).comp (algebraMap A (↑A ⊗[k] K)) = algebraMap A C from
    hleft] at hmap
  exact (Ideal.isRadical_iff_quotient_reduced _).mp hmap

-- Keep the scheme-morphism instance used by the accepted statement despite the proof imports.
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The delta invariant of a reduced one-dimensional point whose normalization has separable
residue fields is unchanged at any one-dimensional point above it after extending the field. -/
@[stacks 0C3Y]
public lemma deltaInvariant_stalk_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y = x)
    (hred : _root_.IsReduced (X.presheaf.stalk x))
    (hdimX : ringKrullDim (X.presheaf.stalk x) = 1)
    (hsep :
      let Xnorm := normalizationSchemeOverField k f
      let ν := normalizationOverField k f
      ∀ x' : Xnorm, ν x' = x →
        letI : Algebra k (Xnorm.residueField x') :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫ Xnorm.Γevaluation x').hom.toAlgebra
        Algebra.IsSeparableExtension k (Xnorm.residueField x'))
    (hdimY : ringKrullDim
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y)
        = 1) :
    Ring.deltaInvariant (X.presheaf.stalk x) =
      Ring.deltaInvariant
        ((pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk y) := by
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p : (pullback f g : Scheme.{u}) ⟶ X := pullback.fst f g
  subst x
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : LocallyOfFiniteType (pullback.snd f g) := inferInstance
  let : IsLocallyNoetherian (pullback f g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
  have hgeomReg :=
    isGeometricallyRegularAt_normalization_of_residueField_isSeparable
      k f (p y) hdimX hsep
  let Xn := normalizationSchemeOverField k f
  let ν := normalizationOverField k f
  have : IsFinite ν :=
    isFinite_normalizationOverField k f
  have : LocallyOfFiniteType (ν ≫ f) := inferInstance
  have : IsLocallyNoetherian Xn := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ f)
  have hregularStalk : ∀ x' : Xn, ν x' = p y →
      let : Algebra k (Xn.presheaf.stalk x') :=
        let : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
          StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
        (((ν ≫ f).stalkMap x').hom.comp
          (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
      Algebra.IsGeometricallyRegular k (Xn.presheaf.stalk x') := by
    intro x' hx'
    exact ((geometricallyRegularAt_tfae k Xn (ν ≫ f) x').out 1 3).mp
      (hgeomReg x' hx')
  have hnormalStalk : ∀ x' : Xn, ν x' = p y →
      let : Algebra k (Xn.presheaf.stalk x') :=
        let : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
          StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
        (((ν ≫ f).stalkMap x').hom.comp
          (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
      Algebra.IsGeometricallyNormal k (Xn.presheaf.stalk x') := by
    intro x' hx'
    let : Algebra k (Xn.presheaf.stalk x') :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')) :=
        StructureSheaf.stalkAlgebra k ((ν ≫ f).base x')
      (((ν ≫ f).stalkMap x').hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk ((ν ≫ f).base x')))).toAlgebra
    exact isGeometricallyNormal_of_isGeometricallyRegular (hregularStalk x' hx')
  have hnormalAfterBaseChange : ∀ x' : Xn, ν x' = p y →
      ∀ z : (pullback (ν ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
        pullback.fst (ν ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) z = x' →
        IsNormalRing
          ((pullback (ν ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
            Scheme.{u}).presheaf.stalk z) := by
    intro x' hx' z hz
    exact isNormalRing_pullbackStalk_of_isGeometricallyNormal
      (ν ≫ f) x' z hz (hnormalStalk x' hx')
  let A := X.presheaf.stalk (p y)
  let B := (pullback f g : Scheme.{u}).presheaf.stalk y
  let : Algebra A B := (p.stalkMap y).hom.toAlgebra
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k f
  let (q : minimalPrimes (↑A)) : q.1.IsPrime := q.2.1.1
  let D := Stacks.NormalizationStalkAmbient.minimalPrimeResidueFieldProduct (↑A)
  let : Algebra (↑A) D :=
    (Stacks.NormalizationStalkAmbient.minimalPrimeResidueFieldProductHom (↑A)).toAlgebra
  let N := integralClosure (↑A) D
  let : Algebra A N := inferInstance
  obtain ⟨eChart, heChart⟩ :=
    exists_iso_pullback_normalization_fromSpecStalk X hX (p y)
  let baseChangeChart := @pullback_baseChange_spec A B N
    (inferInstance : CommRing A) (inferInstance : CommRing B) (inferInstance : CommRing N)
    (inferInstance : Algebra A B) (inferInstance : Algebra A N)
    X Xn (Scheme.normalization X hX) (X.fromSpecStalk (p y))
  obtain ⟨eTensor⟩ := baseChangeChart eChart heChart
  have hSpecMap :
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ X.fromSpecStalk (p y) =
        (pullback f g : Scheme.{u}).fromSpecStalk y ≫ p := by
    show Spec.map (p.stalkMap y) ≫ X.fromSpecStalk (p.base y) = _
    exact Scheme.SpecMap_stalkMap_fromSpecStalk (f := p) (x := y)
  let eMap := pullback.congrHom
    (rfl : Scheme.normalization X hX = Scheme.normalization X hX) hSpecMap
  let eMapOver : Over.mk
      (pullback.snd (Scheme.normalization X hX)
        (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ X.fromSpecStalk (p y))) ≅
    Over.mk (pullback.snd (Scheme.normalization X hX)
        ((pullback f g : Scheme.{u}).fromSpecStalk y ≫ p)) :=
    Over.isoMk eMap (by
      dsimp [eMap, pullback.congrHom, pullback.map]
      rw [pullback.lift_snd]
      simp)
  let eActual := eMapOver.symm.trans eTensor
  let C := (↑B) ⊗[↑A] N
  let : Algebra (↑B) C := Algebra.TensorProduct.leftAlgebra
    (R := (↑A)) (S := (↑B)) (A := (↑B)) (B := N)
  let : Algebra.IsIntegral (↑A) N := inferInstance
  let : Algebra.IsIntegral (↑B) C := Algebra.IsIntegral.tensorProduct (↑A) (↑B) N
  have hnormalC : IsNormalRing C := by
    apply isNormalRing_of_normal_maximal_localizations
    intro m hm
    let : m.IsMaximal := hm
    let q : PrimeSpectrum C := ⟨m, hm.isPrime⟩
    let r : Spec (.of B) ⟶ (pullback f g : Scheme.{u}) :=
      (pullback f g : Scheme.{u}).fromSpecStalk y
    let j := r ≫ p
    let localPullback := pullback ν j
    let zP : localPullback := eActual.inv.left q
    let b : PrimeSpectrum B := pullback.snd ν j zP
    have hb : b.asIdeal = q.asIdeal.comap (algebraMap B C) := by
      have he : eActual.hom.left zP = q := by
        show eActual.hom.left (eActual.inv.left q) = q
        exact congrArg (fun h => h.left q) eActual.inv_hom_id
      have hOver := congrArg (fun t => t zP) eActual.hom.w
      have hOver' : Spec.map (CommRingCat.ofHom (algebraMap B C))
          (eActual.hom.left zP) = b := by
        simpa [Scheme.Hom.comp_apply, b] using hOver
      rw [he] at hOver'
      have hb' : Spec.map (CommRingCat.ofHom (algebraMap B C)) q = b := hOver'
      rw [← hb']
      rfl
    have hmb : (q.asIdeal.comap (algebraMap B C)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) q.asIdeal
    have hbclosed : b = IsLocalRing.closedPoint (CommRingCat.of B) := by
      apply PrimeSpectrum.ext
      rw [hb]
      exact IsLocalRing.eq_maximalIdeal hmb
    have hrb : r b = y := by
      rw [hbclosed]
      exact Scheme.fromSpecStalk_closedPoint
    let qBase := pullback ν p
    let tIso : pullback (pullback.snd ν p) r ≅ localPullback :=
      pullbackLeftPullbackSndIso ν p r
    let t : localPullback ⟶ qBase := tIso.inv ≫ pullback.fst (pullback.snd ν p) r
    let aIso : qBase ≅ pullback (ν ≫ f) g :=
      pullbackRightPullbackFstIso f g ν
    let zQ := t zP
    let zG := aIso.hom zQ
    let x' := pullback.fst (ν ≫ f) g zG
    have hxpoint : x' = pullback.fst ν j zP := by
      have ha : aIso.hom ≫ pullback.fst (ν ≫ f) g = pullback.fst ν p :=
        pullbackRightPullbackFstIso_hom_fst f g ν
      have ht : tIso.inv ≫ pullback.fst (pullback.snd ν p) r ≫
          pullback.fst ν p = pullback.fst ν j :=
        pullbackLeftPullbackSndIso_inv_fst ν p r
      calc
        x' = pullback.fst ν p (t zP) := by
          show (pullback.fst (ν ≫ f) g) (aIso.hom zQ) = _
          rw [← Scheme.Hom.comp_apply, ha]
        _ = pullback.fst ν j zP := by
          show (tIso.inv ≫ pullback.fst (pullback.snd ν p) r ≫
            pullback.fst ν p) zP = _
          exact congrArg (fun h => h zP) ht
    have hx' : ν x' = p y := by
      rw [hxpoint]
      have hcond := congrArg (fun h : pullback ν j ⟶ X => h zP)
        (pullback.condition (f := ν) (g := j))
      have hcond' : ν (pullback.fst ν j zP) = j b := by
        simpa [b] using hcond
      rw [hcond']
      show p (r b) = p y
      rw [hrb]
    have hnormalG : IsNormalRing
        ((pullback (ν ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk zG) :=
      hnormalAfterBaseChange x' hx' zG rfl
    have : Flat r := flat_fromSpecStalk (pullback f g) y
    have : IsPreimmersion r := inferInstance
    have : Flat (pullback.fst (pullback.snd ν p) r) := inferInstance
    have : IsPreimmersion (pullback.fst (pullback.snd ν p) r) := inferInstance
    have ht : IsIso (t.stalkMap zP) := by
      dsimp [t]
      rw [Scheme.Hom.stalkMap_comp]
      have : IsIso
          ((pullback.fst (pullback.snd ν p) r).stalkMap (tIso.inv zP)) :=
        isIso_stalkMap_of_flat_isPreimmersion _ _
      have : IsIso (tIso.inv.stalkMap zP) := inferInstance
      infer_instance
    let zQ' : qBase := zQ
    have ha : IsIso (aIso.hom.stalkMap zQ') := inferInstance
    let eS := (Spec.stalkIso (.of C) q).commRingCatIsoToRingEquiv
    let eT := (asIso (t.stalkMap zP)).commRingCatIsoToRingEquiv
    let eA := (asIso (aIso.hom.stalkMap zQ')).commRingCatIsoToRingEquiv
    let ePiso := (Over.forget (Spec (.of B))).mapIso eActual
    have hq : ePiso.hom zP = q := by
      show eActual.hom.left zP = q
      exact congrArg (fun h => h.left q) eActual.inv_hom_id
    have ePst : (Spec (.of C)).presheaf.stalk q ≃+*
        localPullback.presheaf.stalk zP := by
      rw [← hq]
      exact (asIso (ePiso.hom.stalkMap zP)).commRingCatIsoToRingEquiv
    let eLoc : Localization.AtPrime m ≃+*
        (pullback (ν ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk zG :=
      eS.symm.trans (ePst.trans (eT.symm.trans eA.symm))
    exact IsNormalRing.congr eLoc.symm hnormalG
  let : _root_.IsReduced (↑A) := hred
  let : Finite (minimalPrimes (↑A)) :=
    Stacks.StalkMinimalPrimes.Basic.finite_minimalPrimes_stalk X hX (p y)
  let eD : D ≃ₐ[↑A] FractionRing (↑A) :=
    AlgEquiv.ofRingEquiv (f := minimalPrimeResidueFieldProductRingEquivFractionRing (↑A))
      (minimalPrimeResidueFieldProductRingEquivFractionRing_commutes (↑A))
  let NA := integralClosure (↑A) (FractionRing (↑A))
  let eN : N ≃ₐ[↑A] NA :=
    ((integralClosure (↑A) D).equivMapOfInjective eD.toAlgHom eD.injective).trans
      (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv eD))
  let eC : C ≃ₐ[↑B] (↑B) ⊗[↑A] NA :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : (↑B) ≃ₐ[↑B] (↑B)) eN
  have hnormalStd : IsNormalRing ((↑B) ⊗[↑A] NA) :=
    IsNormalRing.congr eC.toRingEquiv hnormalC
  let : IsLocalHom (algebraMap (↑A) (↑B)) := by
    show IsLocalHom (p.stalkMap y).hom
    exact p.toLRSHom.prop y
  let : Flat g := (Flat.SpecMap_iff).2
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))
  let : Flat p := by infer_instance
  let : Module.Flat (↑A) (↑B) := Flat.stalkMap p y
  let eStd := integralClosureTensorProductEquivOfIsNormal (↑A) (↑B) hnormalStd
  have hgeoResidue :
      let : Algebra k A :=
        let : Algebra k ((Spec (.of k)).presheaf.stalk (f (p y))) :=
          StructureSheaf.stalkAlgebra k (f (p y))
        ((f.stalkMap (p y)).hom.comp
          (algebraMap k ((Spec (.of k)).presheaf.stalk (f (p y))))).toAlgebra
      Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField A) := by
    have : Surjective ν :=
      Scheme.surjective_normalization X hX
    obtain ⟨x', hx'⟩ := Surjective.surj (f := ν) (p y)
    exact residueField_geometricallyReduced_of_separable_above k f ν x' (p y) hx'
      (hsep x' hx')
  have hredFiber : _root_.IsReduced ((↑B) ⧸ extendedMaximalIdeal (↑A) (↑B)) :=
    isReduced_closedFiber_of_geometricallyReduced_residueField f (p y) y rfl hgeoResidue
  have hfiber : Module.length (↑B) ((↑B) ⧸ extendedMaximalIdeal (↑A) (↑B)) = 1 :=
    length_fiber_eq_one_of_isReduced (↑A) (↑B)
      (hdimY.trans hdimX.symm) hredFiber
  exact deltaInvariant_eq_of_integralClosure_baseChange eStd hfiber

end AlgebraicGeometry

end
