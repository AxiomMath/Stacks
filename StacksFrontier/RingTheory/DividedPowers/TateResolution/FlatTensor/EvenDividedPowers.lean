module

public import Mathlib.Algebra.MvPolynomial.Counit
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenSubalgebra
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.FlatTensor.EvenSubalgebra

/-!
# Divided powers on the base-changed even subalgebra

The positive even part of the even subalgebra is an ideal. Divided powers on it extend to
its image in `evenSubalgebra 𝒜 ⊗[R] P` (through the flat polynomial presentation of `P`), and
transport to the even subalgebra of the base-changed grading. This file also computes these
divided powers on pure tensors and shows that they respect the grading.
-/

@[expose] public section

namespace DividedPowers.TateResolution

open TensorProduct

universe u v w x y

private def positiveEvenIdeal
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜] :
    Ideal (evenSubalgebra 𝒜) where
  carrier := {x | (x : A) ∈ positiveEvenPart 𝒜}
  zero_mem' := (positiveEvenPart 𝒜).zero_mem
  add_mem' := fun hx hy ↦ (positiveEvenPart 𝒜).add_mem hx hy
  smul_mem' := fun a _x hx ↦ evenPart_mul_positiveEvenPart 𝒜 a.property hx

private theorem positiveEvenIdeal_tensorHom_le
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let B := evenSubalgebra 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    ((positiveEvenIdeal 𝒜).map
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)).map
        E.toRingHom ≤ positiveEvenIdeal (R := P) 𝒜' := by
  intro 𝒜' B E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  rw [Ideal.map_map]
  apply Ideal.map_le_iff_le_comap.mpr
  intro b hb
  show ((E : B ⊗[R] P →+* evenSubalgebra (R := P) 𝒜')
    ((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P) b)) ∈
      positiveEvenIdeal (R := P) 𝒜'
  show ((evenSubalgebraTensorHom 𝒜 (b ⊗ₜ[R] (1 : P)) :
    evenSubalgebra (R := P) 𝒜') : P ⊗[R] A) ∈ positiveEvenPart 𝒜'
  rw [evenSubalgebraTensorHom_tmul, positiveEvenPart_baseChange]
  exact Submodule.tmul_mem_baseChange_of_mem 1 hb

private theorem positiveEvenIdeal_tensorHom_eq
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let B := evenSubalgebra 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    ((positiveEvenIdeal 𝒜).map
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)).map
        E.toRingHom = positiveEvenIdeal (R := P) 𝒜' := by
  intro 𝒜' B E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let J : Ideal (evenSubalgebra (R := P) 𝒜') :=
    ((positiveEvenIdeal 𝒜).map
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)).map E.toRingHom
  apply le_antisymm (positiveEvenIdeal_tensorHom_le 𝒜)
  intro z hz
  have hpos : (z : P ⊗[R] A) ∈ (positiveEvenPart 𝒜).baseChange P := by
    change (z : P ⊗[R] A) ∈ positiveEvenPart 𝒜' at hz
    rwa [positiveEvenPart_baseChange] at hz
  rw [Submodule.baseChange_eq_span] at hpos
  have hev : ∀ t ∈ Submodule.span P (TensorProduct.mk R P A 1 ''
      (positiveEvenPart 𝒜 : Set A)), t ∈ evenPart 𝒜' := fun t ht ↦
    positiveEvenPart_le_evenPart 𝒜' <| by
      rwa [positiveEvenPart_baseChange, Submodule.baseChange_eq_span]
  have hspan : ∀ t : P ⊗[R] A,
      t ∈ Submodule.span P (TensorProduct.mk R P A 1 ''
        (positiveEvenPart 𝒜 : Set A)) →
      ∀ ht : t ∈ evenPart 𝒜',
        (⟨t, ht⟩ : evenSubalgebra (R := P) 𝒜') ∈ J := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨a, ha, rfl⟩
        intro heven
        let b : B := ⟨a, positiveEvenPart_le_evenPart 𝒜 ha⟩
        have hb : E (b ⊗ₜ[R] (1 : P)) ∈ J :=
          Ideal.mem_map_of_mem E.toRingHom
            (Ideal.mem_map_of_mem _ ha)
        convert hb using 1
        apply Subtype.ext
        show (1 : P) ⊗ₜ[R] a =
          ((evenSubalgebraTensorHom 𝒜 (b ⊗ₜ[R] (1 : P)) :
            evenSubalgebra (R := P) 𝒜') : P ⊗[R] A)
        rw [evenSubalgebraTensorHom_tmul]
    | zero => exact fun _ ↦ J.zero_mem
    | add t s ht hs iht ihs =>
        intro heven
        have ht' := hev t ht
        have hs' := hev s hs
        have heq : (⟨t + s, heven⟩ : evenSubalgebra (R := P) 𝒜') =
            (⟨t, ht'⟩ : evenSubalgebra (R := P) 𝒜') + ⟨s, hs'⟩ :=
          Subtype.ext rfl
        rw [heq]
        exact J.add_mem (iht ht') (ihs hs')
    | smul p t ht iht =>
        intro heven
        have ht' := hev t ht
        have heq : (⟨p • t, heven⟩ : evenSubalgebra (R := P) 𝒜') =
            algebraMap P (evenSubalgebra (R := P) 𝒜') p * ⟨t, ht'⟩ := by
          apply Subtype.ext
          simp [Algebra.smul_def]
        rw [heq]
        exact J.mul_mem_left _ (iht ht')
  exact hspan z hpos z.property

private def positiveEvenProjection
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] :
    evenSubalgebra 𝒜 →ₗ[R]
      (Submodule.restrictScalars R (positiveEvenIdeal 𝒜)) where
  toFun x := by
    let z : A := (x : A) - (GradedAlgebra.proj 𝒜 0) x
    have hz : z ∈ positiveEvenPart 𝒜 :=
      sub_proj_zero_mem_positive 𝒜 x x.property
    exact ⟨⟨z, positiveEvenPart_le_evenPart 𝒜 hz⟩, hz⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change (x : A) + (y : A) - (GradedAlgebra.proj 𝒜 0) ((x : A) + (y : A)) =
      ((x : A) - (GradedAlgebra.proj 𝒜 0) x) +
        ((y : A) - (GradedAlgebra.proj 𝒜 0) y)
    rw [map_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    change r • (x : A) - (GradedAlgebra.proj 𝒜 0) (r • (x : A)) =
      r • ((x : A) - (GradedAlgebra.proj 𝒜 0) x)
    rw [map_smul, smul_sub]

private theorem positiveEvenProjection_comp_subtype
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] :
    (positiveEvenProjection 𝒜).comp
      (Submodule.restrictScalars R (positiveEvenIdeal 𝒜)).subtype =
        LinearMap.id := by
  ext x
  show (x : A) - (GradedAlgebra.proj 𝒜 0) x = x
  rw [proj_zero_of_positive 𝒜 x x.property, sub_zero]

private theorem positiveEvenIdeal_tensor_kernel
    {R : Type u} {A : Type w} {P : Type v} {Q : Type x}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] [CommRing Q] [Algebra R Q]
    (q : P →ₐ[R] Q) (hq : Function.Surjective q) :
    (LinearMap.lTensor (evenSubalgebra 𝒜) q.toLinearMap).ker ⊓
      Submodule.restrictScalars R
        ((positiveEvenIdeal 𝒜).map
          (Algebra.TensorProduct.includeLeftRingHom :
            evenSubalgebra 𝒜 →+* evenSubalgebra 𝒜 ⊗[R] P)) =
      ((LinearMap.rTensor P
          (Submodule.restrictScalars R (positiveEvenIdeal 𝒜)).subtype).comp
        (LinearMap.lTensor
          (Submodule.restrictScalars R (positiveEvenIdeal 𝒜))
          q.toLinearMap.ker.subtype)).range := by
  have hmap : Submodule.restrictScalars R
      ((positiveEvenIdeal 𝒜).map
        (Algebra.TensorProduct.includeLeftRingHom :
          evenSubalgebra 𝒜 →+* evenSubalgebra 𝒜 ⊗[R] P)) =
        (LinearMap.rTensor P
          (Submodule.restrictScalars R (positiveEvenIdeal 𝒜)).subtype).range :=
    Ideal.map_includeLeft_eq (positiveEvenIdeal 𝒜)
  rw [hmap]
  exact ker_lTensor_inter_range_of_split
    (Submodule.restrictScalars R (positiveEvenIdeal 𝒜)).subtype
    (positiveEvenProjection 𝒜)
    (positiveEvenProjection_comp_subtype 𝒜) q.toLinearMap hq

private theorem positiveEvenIdeal_kernel_le_mul
    {R : Type u} {A : Type w} {P : Type v} {Q : Type x}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] [CommRing Q] [Algebra R Q]
    (q : P →ₐ[R] Q) (hq : Function.Surjective q) :
    let B := evenSubalgebra 𝒜
    let I := positiveEvenIdeal 𝒜
    let f := Algebra.TensorProduct.map (AlgHom.id R B) q
    let I' := I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)
    let J' := (RingHom.ker q.toRingHom).map
      (Algebra.TensorProduct.includeRight : P →ₐ[R] B ⊗[R] P)
    RingHom.ker f.toRingHom ⊓ I' ≤ I' * J' := by
  intro B I f I' J' z hz
  have hz' : z ∈ (LinearMap.lTensor B q.toLinearMap).ker ⊓
      Submodule.restrictScalars R I' := hz
  rw [positiveEvenIdeal_tensor_kernel 𝒜 q hq] at hz'
  exact tensorIdealKernel_range_le_mul I q hz'

private theorem positiveEvenIdeal_kernel_isSubDPIdeal
    {R : Type u} {A : Type w} {P : Type v} {Q : Type x}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P] [CommRing Q] [Algebra R Q]
    (q : P →ₐ[R] Q) (hq : Function.Surjective q)
    (δ : _root_.DividedPowers
      ((positiveEvenIdeal 𝒜).map
        (Algebra.TensorProduct.includeLeftRingHom :
          evenSubalgebra 𝒜 →+* evenSubalgebra 𝒜 ⊗[R] P))) :
    let B := evenSubalgebra 𝒜
    let f := Algebra.TensorProduct.map (AlgHom.id R B) q
    let I' := (positiveEvenIdeal 𝒜).map
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] P)
    δ.IsSubDPIdeal (RingHom.ker f.toRingHom ⊓ I') := by
  intro B f I'
  let J' : Ideal (B ⊗[R] P) :=
    (RingHom.ker q.toRingHom).map
      (Algebra.TensorProduct.includeRight : P →ₐ[R] B ⊗[R] P)
  have hker : RingHom.ker f.toRingHom = J' :=
    Algebra.TensorProduct.lTensor_ker q hq
  have hle : RingHom.ker f.toRingHom ⊓ I' ≤ I' * J' :=
    positiveEvenIdeal_kernel_le_mul 𝒜 q hq
  have hprod : δ.IsSubDPIdeal (I' • J') :=
    (DividedPowers.SubDPIdeal.prod (hI := δ) J').toIsSubDPIdeal
  refine ⟨inf_le_right, ?_⟩
  intro n hn z hz
  have hzProd : z ∈ I' • J' := by
    simpa only [smul_eq_mul] using hle hz
  have hdpowProd : δ.dpow n z ∈ I' * J' := by
    simpa only [smul_eq_mul] using hprod.dpow_mem n hn hzProd
  exact ⟨hker.symm ▸ Ideal.mul_le_right hdpowProd,
    δ.dpow_mem hn hz.2⟩

private noncomputable def dividedPowers_on_evenTensor
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜)) :
    _root_.DividedPowers
      ((positiveEvenIdeal 𝒜).map
        (Algebra.TensorProduct.includeLeftRingHom :
          evenSubalgebra 𝒜 →+* evenSubalgebra 𝒜 ⊗[R] P)) := by
  let B := evenSubalgebra 𝒜
  let T := MvPolynomial P R
  let q : T →ₐ[R] P := MvPolynomial.ACounit R P
  letI : Module.Flat R T := inferInstance
  let fT : B →+* B ⊗[R] T := Algebra.TensorProduct.includeLeftRingHom
  let fP : B →+* B ⊗[R] P := Algebra.TensorProduct.includeLeftRingHom
  let g : B ⊗[R] T →+* B ⊗[R] P :=
    (Algebra.TensorProduct.map (AlgHom.id R B) q).toRingHom
  let δT : _root_.DividedPowers ((positiveEvenIdeal 𝒜).map fT) :=
    Classical.choose (dividedPowers_extends_to_flatTensor
      (P := T) (positiveEvenIdeal 𝒜) γ)
  have hcomp : g.comp fT = fP := by
    ext b
    simp [g, fT, fP]
  have hideal : (((positiveEvenIdeal 𝒜).map fT).map g) =
      (positiveEvenIdeal 𝒜).map fP := by
    rw [Ideal.map_map, hcomp]
  exact _root_.DividedPowers.Quotient.OfSurjective.dividedPowers δT
    (Algebra.TensorProduct.map_surjective (AlgHom.id R B) q
      (fun b ↦ ⟨b, rfl⟩) (MvPolynomial.ACounit_surjective R P))
    hideal.symm (positiveEvenIdeal_kernel_isSubDPIdeal 𝒜 q
      (MvPolynomial.ACounit_surjective R P) δT)

private theorem dividedPowers_on_evenTensor_isDPMorphism
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜)) :
    _root_.DividedPowers.IsDPMorphism γ
      (dividedPowers_on_evenTensor 𝒜 γ)
      (Algebra.TensorProduct.includeLeftRingHom :
        evenSubalgebra 𝒜 →+* evenSubalgebra 𝒜 ⊗[R] P) := by
  let B := evenSubalgebra 𝒜
  let T := MvPolynomial P R
  let q : T →ₐ[R] P := MvPolynomial.ACounit R P
  let : Module.Flat R T := inferInstance
  let fT : B →+* B ⊗[R] T := Algebra.TensorProduct.includeLeftRingHom
  let fP : B →+* B ⊗[R] P := Algebra.TensorProduct.includeLeftRingHom
  let g : B ⊗[R] T →+* B ⊗[R] P :=
    (Algebra.TensorProduct.map (AlgHom.id R B) q).toRingHom
  let δT : _root_.DividedPowers ((positiveEvenIdeal 𝒜).map fT) :=
    Classical.choose (dividedPowers_extends_to_flatTensor
      (P := T) (positiveEvenIdeal 𝒜) γ)
  have hT : _root_.DividedPowers.IsDPMorphism γ δT fT :=
    Classical.choose_spec (dividedPowers_extends_to_flatTensor
      (P := T) (positiveEvenIdeal 𝒜) γ)
  have hcomp : g.comp fT = fP := by
    ext b
    simp [g, fT, fP]
  have hideal : (((positiveEvenIdeal 𝒜).map fT).map g) =
      (positiveEvenIdeal 𝒜).map fP := by
    rw [Ideal.map_map, hcomp]
  let δP : _root_.DividedPowers ((positiveEvenIdeal 𝒜).map fP) :=
    _root_.DividedPowers.Quotient.OfSurjective.dividedPowers δT
      (Algebra.TensorProduct.map_surjective (AlgHom.id R B) q
        (fun b ↦ ⟨b, rfl⟩) (MvPolynomial.ACounit_surjective R P))
      hideal.symm (positiveEvenIdeal_kernel_isSubDPIdeal 𝒜 q
        (MvPolynomial.ACounit_surjective R P) δT)
  have hP : _root_.DividedPowers.IsDPMorphism δT δP g :=
    _root_.DividedPowers.Quotient.OfSurjective.isDPMorphism δT
      (Algebra.TensorProduct.map_surjective (AlgHom.id R B) q
        (fun b ↦ ⟨b, rfl⟩) (MvPolynomial.ACounit_surjective R P))
      hideal.symm (positiveEvenIdeal_kernel_isSubDPIdeal 𝒜 q
        (MvPolynomial.ACounit_surjective R P) δT)
  have hm : _root_.DividedPowers.IsDPMorphism γ δP (g.comp fT) :=
    hP.comp δP hT
  unfold dividedPowers_on_evenTensor
  dsimp only
  simpa only [hcomp] using hm

private theorem dividedPowers_on_evenTensor_dpow_tmul
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (n : ℕ) (x : evenSubalgebra 𝒜) (hx : x ∈ positiveEvenIdeal 𝒜)
    (p : P) :
    (dividedPowers_on_evenTensor 𝒜 γ).dpow n (x ⊗ₜ[R] p) =
      (1 ⊗ₜ[R] p) ^ n * (γ.dpow n x ⊗ₜ[R] (1 : P)) :=
  dividedPowers_flatTensor_dpow_tmul (positiveEvenIdeal 𝒜) γ
    (dividedPowers_on_evenTensor 𝒜 γ)
    (dividedPowers_on_evenTensor_isDPMorphism 𝒜 γ) n x hx p

private noncomputable def dividedPowersOnBaseChangedEven
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜)) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    _root_.DividedPowers (positiveEvenIdeal 𝒜') := by
  intro 𝒜'
  letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  exact _root_.DividedPowers.ofRingEquiv
    (positiveEvenIdeal_tensorHom_eq 𝒜)
    (dividedPowers_on_evenTensor 𝒜 γ)

private theorem dividedPowersOnBaseChangedEven_dpow_apply
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (n : ℕ) (z : evenSubalgebra 𝒜 ⊗[R] P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    (dividedPowersOnBaseChangedEven 𝒜 γ).dpow n (E z) =
      E ((dividedPowers_on_evenTensor 𝒜 γ).dpow n z) := by
  intro 𝒜' E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  exact @_root_.DividedPowers.ofRingEquiv_dpow_apply _ _ _ _ _ _ E.toRingEquiv
    (positiveEvenIdeal_tensorHom_eq 𝒜) (dividedPowers_on_evenTensor 𝒜 γ) n z

private theorem dividedPowersOnBaseChangedEven_dpow_tmul_one
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (n : ℕ) (b : evenSubalgebra 𝒜) (hb : b ∈ positiveEvenIdeal 𝒜) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    (dividedPowersOnBaseChangedEven 𝒜 γ).dpow n (E (b ⊗ₜ[R] (1 : P))) =
      E (γ.dpow n b ⊗ₜ[R] (1 : P)) := by
  intro 𝒜' E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  rw [dividedPowersOnBaseChangedEven_dpow_apply,
    dividedPowers_on_evenTensor_dpow_tmul 𝒜 γ n b hb 1]
  simp
  rfl

private theorem dividedPowersOnBaseChangedEven_dpow_tmul
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (n : ℕ) (b : evenSubalgebra 𝒜) (hb : b ∈ positiveEvenIdeal 𝒜) (p : P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    (dividedPowersOnBaseChangedEven 𝒜 γ).dpow n (E (b ⊗ₜ[R] p)) =
      E ((1 ⊗ₜ[R] p) ^ n * (γ.dpow n b ⊗ₜ[R] (1 : P))) := by
  intro 𝒜' E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  rw [dividedPowersOnBaseChangedEven_dpow_apply,
    dividedPowers_on_evenTensor_dpow_tmul 𝒜 γ n b hb p]

private def evenDpow
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (n : ℕ) (x : evenSubalgebra 𝒜) :
    evenSubalgebra 𝒜 := by
  refine ⟨γ.dpow n x, ?_⟩
  by_cases hx : (x : A) ∈ positiveEvenPart 𝒜
  · by_cases hn : n = 0
    · simpa only [hn, γ.dpow_zero hx] using
        (evenSubalgebra 𝒜).one_mem
    · exact positiveEvenPart_le_evenPart 𝒜 (γ.dpow_mem hn hx)
  · rw [γ.dpow_null hx]
    exact (evenPart 𝒜).zero_mem

private theorem evenDpow_coe
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (n : ℕ) (x : evenSubalgebra 𝒜) :
    ((evenDpow 𝒜 γ n x : evenSubalgebra 𝒜) : A) = γ.dpow n x := rfl

private def dividedPowersOnEven
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) : _root_.DividedPowers (positiveEvenIdeal 𝒜) where
  dpow := evenDpow 𝒜 γ
  dpow_null hx := Subtype.ext (γ.dpow_null hx)
  dpow_zero hx := Subtype.ext (γ.dpow_zero hx)
  dpow_one hx := Subtype.ext (γ.dpow_one hx)
  dpow_mem hn hx := γ.dpow_mem hn hx
  dpow_add := by
    intro n x y hx hy
    apply Subtype.ext
    simpa only [evenDpow_coe, Subalgebra.coe_add, Subalgebra.coe_mul,
      AddSubmonoidClass.coe_finsetSum] using γ.dpow_add hx hy
  dpow_mul := by
    intro n x y hy
    apply Subtype.ext
    by_cases hn : n = 0
    · have hxy := evenPart_mul_positiveEvenPart 𝒜 x.property hy
      simp only [hn, evenDpow_coe, Subalgebra.coe_mul,
        γ.dpow_zero hxy, γ.dpow_zero hy, pow_zero, one_mul]
    · simpa only [evenDpow_coe, Subalgebra.coe_mul, Subalgebra.coe_pow] using
        γ.dpow_mul_even hn x.property hy
  mul_dpow := by
    intro m n x hx
    apply Subtype.ext
    simpa only [evenDpow_coe, Subalgebra.coe_mul, SubringClass.coe_natCast] using
      (γ.dpow_mul (n := m) (m := n) hx)
  dpow_comp := by
    intro m n x hn hx
    apply Subtype.ext
    by_cases hm : m = 0
    · subst m
      have hinner := γ.dpow_mem hn hx
      simp [evenDpow_coe, γ.dpow_zero hx, γ.dpow_zero hinner,
        Nat.uniformBell_zero_left]
    · have hbell : Nat.uniformBell m n =
          (m * n).factorial / (m.factorial * n.factorial ^ m) := by
        rw [Nat.uniformBell_eq_div m hn]
        congr 1
        ac_rfl
      have hγ := γ.dpow_dpow (m := n) (n := m) hn hm hx
      simpa only [evenDpow_coe, Subalgebra.coe_mul, SubringClass.coe_natCast,
        hbell] using hγ

private theorem dividedPowersOnBaseChangedEven_dpow_tmul_of_zero
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (n : ℕ) (b : evenSubalgebra 𝒜) (hb : b ∈ positiveEvenIdeal 𝒜)
    (hzero : γ.dpow n b = 0) (p : P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    (dividedPowersOnBaseChangedEven 𝒜 γ).dpow n (E (b ⊗ₜ[R] p)) = 0 := by
  intro 𝒜' E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  rw [dividedPowersOnBaseChangedEven_dpow_tmul 𝒜 γ n b hb p, hzero]
  simp

private theorem dividedPowersOnBaseChangedEven_dpow_tmul_grade
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜)
    (n d : ℕ) (hn : n ≠ 0)
    (b : evenSubalgebra 𝒜) (hb : b ∈ positiveEvenIdeal 𝒜)
    (hbgrade : (b : A) ∈ 𝒜 (2 * d)) (p : P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    let E := evenSubalgebraTensorEquiv (P := P) 𝒜
    (((dividedPowersOnBaseChangedEven 𝒜 (dividedPowersOnEven 𝒜 γ)).dpow n
      (E (b ⊗ₜ[R] p)) : evenSubalgebra 𝒜') : P ⊗[R] A) ∈
        𝒜' (2 * n * d) := by
  intro 𝒜' E
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  have hdpow : (γ.dpow n (b : A)) ∈ 𝒜 (2 * n * d) :=
    γ.dpow_mem_grade hn hb hbgrade
  rw [dividedPowersOnBaseChangedEven_dpow_tmul 𝒜
    (dividedPowersOnEven 𝒜 γ) n b hb p]
  show ((E ((1 ⊗ₜ[R] p) ^ n *
    ((dividedPowersOnEven 𝒜 γ).dpow n b ⊗ₜ[R] (1 : P))) :
      evenSubalgebra 𝒜') : P ⊗[R] A) ∈ 𝒜' (2 * n * d)
  rw [map_mul, map_pow]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
  rw [show ((E (1 ⊗ₜ[R] p) : evenSubalgebra 𝒜') : P ⊗[R] A) =
      p ⊗ₜ[R] (1 : A) by
        show ((evenSubalgebraTensorHom 𝒜 (1 ⊗ₜ[R] p) :
          evenSubalgebra 𝒜') : P ⊗[R] A) = p ⊗ₜ[R] (1 : A)
        exact evenSubalgebraTensorHom_tmul 𝒜 (1 : evenSubalgebra 𝒜) p,
    show ((E ((dividedPowersOnEven 𝒜 γ).dpow n b ⊗ₜ[R] (1 : P)) :
      evenSubalgebra 𝒜') : P ⊗[R] A) =
      (1 : P) ⊗ₜ[R] γ.dpow n b by
        show ((evenSubalgebraTensorHom 𝒜
          ((dividedPowersOnEven 𝒜 γ).dpow n b ⊗ₜ[R] (1 : P)) :
          evenSubalgebra 𝒜') : P ⊗[R] A) = (1 : P) ⊗ₜ[R] γ.dpow n b
        simpa only [dividedPowersOnEven, evenDpow_coe] using evenSubalgebraTensorHom_tmul 𝒜
          ((dividedPowersOnEven 𝒜 γ).dpow n b) (1 : P)]
  have hpow (m : ℕ) : (p ⊗ₜ[R] (1 : A)) ^ m = (p ^ m) ⊗ₜ[R] (1 : A) := by
    induction m with
    | zero => simp only [pow_zero, Algebra.TensorProduct.one_def]
    | succ m ih => rw [pow_succ, ih, pow_succ,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [hpow n, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact Submodule.tmul_mem_baseChange_of_mem (p ^ n) hdpow

private theorem dividedPowers_dpow_add_grade
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    (δ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (d : ℕ) (x y : evenSubalgebra 𝒜)
    (hxI : x ∈ positiveEvenIdeal 𝒜) (hyI : y ∈ positiveEvenIdeal 𝒜)
    (hx : ∀ n : ℕ, ((δ.dpow n x : evenSubalgebra 𝒜) : A) ∈ 𝒜 (2 * n * d))
    (hy : ∀ n : ℕ, ((δ.dpow n y : evenSubalgebra 𝒜) : A) ∈ 𝒜 (2 * n * d))
    (n : ℕ) :
    ((δ.dpow n (x + y) : evenSubalgebra 𝒜) : A) ∈ 𝒜 (2 * n * d) := by
  rw [δ.dpow_add hxI hyI]
  have hsum : (∑ ij ∈ Finset.antidiagonal n,
      ((δ.dpow ij.1 x : evenSubalgebra 𝒜) : A) *
        ((δ.dpow ij.2 y : evenSubalgebra 𝒜) : A)) ∈ 𝒜 (2 * n * d) := by
    apply Submodule.sum_mem
    intro ij hij
    have hmul := SetLike.mul_mem_graded (hx ij.1) (hy ij.2)
    have hdegree : 2 * ij.1 * d + 2 * ij.2 * d = 2 * n * d := by
      have h := Finset.mem_antidiagonal.mp hij
      rw [← h]
      ring
    exact hdegree ▸ hmul
  simpa only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul] using hsum

private theorem dividedPowers_dpow_smul_grade
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    (δ : _root_.DividedPowers (positiveEvenIdeal 𝒜))
    (d : ℕ) (r : R) (x : evenSubalgebra 𝒜)
    (hxI : x ∈ positiveEvenIdeal 𝒜)
    (hx : ∀ n : ℕ, ((δ.dpow n x : evenSubalgebra 𝒜) : A) ∈ 𝒜 (2 * n * d))
    (n : ℕ) :
    ((δ.dpow n (r • x) : evenSubalgebra 𝒜) : A) ∈ 𝒜 (2 * n * d) := by
  have heq : ((δ.dpow n (r • x) : evenSubalgebra 𝒜) : A) =
      r ^ n • ((δ.dpow n x : evenSubalgebra 𝒜) : A) := by
    rw [Algebra.smul_def, δ.dpow_mul hxI]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap]
    rw [← map_pow]
    exact (Algebra.smul_def (r ^ n) ((δ.dpow n x : evenSubalgebra 𝒜) : A)).symm
  rw [heq]
  exact (𝒜 (2 * n * d)).smul_mem (r ^ n) (hx n)

theorem eq_zero_of_mem_grade_zero_and_positiveEvenPart
    {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {x : A} (hx0 : x ∈ 𝒜 0) (hxpos : x ∈ positiveEvenPart 𝒜) : x = 0 := by
  have hproj : (GradedAlgebra.proj 𝒜 0) x = x := by
    simpa only [GradedAlgebra.proj_apply] using
      (DirectSum.decompose_of_mem_same 𝒜 hx0)
  rw [← hproj]
  exact proj_zero_of_positive 𝒜 x hxpos

private theorem dividedPowersOnBaseChangedEven_dpow_mem_positive_grade
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) (d n : ℕ) (hn : n ≠ 0)
    (x : evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P))
    (hx : (x : P ⊗[R] A) ∈ (𝒜 (2 * (d + 1))).baseChange P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    (((dividedPowersOnBaseChangedEven 𝒜 (dividedPowersOnEven 𝒜 γ)).dpow n x :
      evenSubalgebra 𝒜') : P ⊗[R] A) ∈ 𝒜' (2 * n * (d + 1)) := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  let δ := dividedPowersOnBaseChangedEven (P := P) 𝒜 (dividedPowersOnEven 𝒜 γ)
  let E := evenSubalgebraTensorEquiv (P := P) 𝒜
  have grade_pos {z : P ⊗[R] A}
      (hz : z ∈ 𝒜' (2 * (d + 1))) : z ∈ positiveEvenPart 𝒜' :=
    Submodule.mem_iSup_of_mem d hz
  have hgr : ∀ z ∈ Submodule.span P (TensorProduct.mk R P A 1 ''
      (𝒜 (2 * (d + 1)) : Set A)), z ∈ 𝒜' (2 * (d + 1)) := fun z hz ↦ by
    change z ∈ (𝒜 (2 * (d + 1))).baseChange P
    rwa [Submodule.baseChange_eq_span]
  have full : ∀ b : evenSubalgebra 𝒜', (b : P ⊗[R] A) ∈ 𝒜' (2 * (d + 1)) →
      (∀ k : ℕ, k ≠ 0 → ((δ.dpow k b : evenSubalgebra 𝒜') : P ⊗[R] A) ∈
        𝒜' (2 * k * (d + 1))) →
      ∀ k : ℕ, ((δ.dpow k b : evenSubalgebra 𝒜') : P ⊗[R] A) ∈ 𝒜' (2 * k * (d + 1)) := by
    intro b hb h k
    by_cases hk : k = 0
    · subst k
      rw [δ.dpow_zero (grade_pos hb)]
      simpa using SetLike.one_mem_graded 𝒜'
    · exact h k hk
  have H : ∀ z : P ⊗[R] A, z ∈ 𝒜' (2 * (d + 1)) →
      ∀ b : evenSubalgebra 𝒜', (b : P ⊗[R] A) = z →
      ∀ m : ℕ, m ≠ 0 → ((δ.dpow m b : evenSubalgebra 𝒜') : P ⊗[R] A) ∈
        𝒜' (2 * m * (d + 1)) := by
    intro z hz
    change z ∈ (𝒜 (2 * (d + 1))).baseChange P at hz
    rw [Submodule.baseChange_eq_span] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨a, ha, rfl⟩
        intro b hb m hm
        let aEven : evenSubalgebra 𝒜 :=
          ⟨a, positiveEvenPart_le_evenPart 𝒜
            (Submodule.mem_iSup_of_mem d ha)⟩
        have haI : aEven ∈ positiveEvenIdeal 𝒜 :=
          Submodule.mem_iSup_of_mem d ha
        have hE : ((E (aEven ⊗ₜ[R] (1 : P)) : evenSubalgebra 𝒜') :
            P ⊗[R] A) = 1 ⊗ₜ[R] a := evenSubalgebraTensorHom_tmul 𝒜 aEven 1
        obtain rfl : b = E (aEven ⊗ₜ[R] (1 : P)) := Subtype.ext (hb.trans hE.symm)
        exact dividedPowersOnBaseChangedEven_dpow_tmul_grade 𝒜 γ m (d + 1)
          hm aEven haI ha 1
    | zero =>
        intro b hb m hm
        obtain rfl : b = 0 := Subtype.ext hb
        rw [δ.dpow_eval_zero hm]
        exact (𝒜' (2 * m * (d + 1))).zero_mem
    | add z t hz ht ihz iht =>
        intro b hb m hm
        have hz' := hgr z hz
        have ht' := hgr t ht
        let bz : evenSubalgebra 𝒜' :=
          ⟨z, positiveEvenPart_le_evenPart 𝒜' (grade_pos hz')⟩
        let bt : evenSubalgebra 𝒜' :=
          ⟨t, positiveEvenPart_le_evenPart 𝒜' (grade_pos ht')⟩
        have hb' : b = bz + bt := Subtype.ext hb
        rw [hb']
        exact dividedPowers_dpow_add_grade 𝒜' δ (d + 1) bz bt
          (grade_pos hz') (grade_pos ht') (full bz hz' (ihz bz rfl))
          (full bt ht' (iht bt rfl)) m
    | smul p z hz ih =>
        intro b hb m hm
        have hz' := hgr z hz
        let bz : evenSubalgebra 𝒜' :=
          ⟨z, positiveEvenPart_le_evenPart 𝒜' (grade_pos hz')⟩
        have hb' : b = p • bz := Subtype.ext hb
        rw [hb']
        exact dividedPowers_dpow_smul_grade 𝒜' δ (d + 1) p bz
          (grade_pos hz') (full bz hz' (ih bz rfl)) m
  exact H x hx x rfl n hn

private theorem dividedPowersOnBaseChangedEven_dpow_mem_grade
    {R : Type u} {A : Type w} {P : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜]
    [CommRing P] [Algebra R P]
    (γ : DividedPowerStructure 𝒜) (n d : ℕ) (hn : n ≠ 0)
    (x : evenSubalgebra (R := P) (fun i => (𝒜 i).baseChange P))
    (hxI : (x : P ⊗[R] A) ∈
      positiveEvenPart (fun i => (𝒜 i).baseChange P))
    (hx : (x : P ⊗[R] A) ∈ (𝒜 (2 * d)).baseChange P) :
    let 𝒜' : ℕ → Submodule P (P ⊗[R] A) := fun i => (𝒜 i).baseChange P
    letI : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
    (((dividedPowersOnBaseChangedEven 𝒜 (dividedPowersOnEven 𝒜 γ)).dpow n x :
      evenSubalgebra 𝒜') : P ⊗[R] A) ∈ 𝒜' (2 * n * d) := by
  intro 𝒜'
  let : IsStrictlyGradedComm 𝒜' := strictlyGradedComm_baseChange 𝒜
  cases d with
  | zero =>
      have hx0 : (x : P ⊗[R] A) = 0 :=
        eq_zero_of_mem_grade_zero_and_positiveEvenPart 𝒜'
          (by simpa using hx) hxI
      obtain rfl : x = 0 := Subtype.ext hx0
      rw [(dividedPowersOnBaseChangedEven 𝒜
        (dividedPowersOnEven 𝒜 γ)).dpow_eval_zero hn]
      exact (𝒜' (2 * n * 0)).zero_mem
  | succ d =>
      simpa only [Nat.succ_eq_add_one] using
        dividedPowersOnBaseChangedEven_dpow_mem_positive_grade 𝒜 γ d n hn x hx

end DividedPowers.TateResolution
