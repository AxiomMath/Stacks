module

public import StacksFrontier.Deformation.Examples.Geometric.Smoothing.GlobalCompleteIntersection
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.Artinian.Basic
public import StacksFrontier.RingTheory.Artinian.TFAE
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.TFAE
public import StacksFrontier.RingTheory.Nagata.PowerSeries
public import StacksFrontier.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient

/-!
# Smoothing a finite-dimensional local complete intersection over a field

A finite-dimensional local complete intersection `A` over a field `k` is the special fibre of a
finite flat `k⟦X⟧`-algebra whose generic fibre, over `k⸨X⸩`, is étale. Such an `A` is a global
complete intersection, so the smoothing of global complete intersections applies; localizing
the witness at the prime corresponding to the closed point of the special fibre makes it finite
over `k⟦X⟧`, by henselianity of `k⟦X⟧` and quasi-finiteness over its maximal ideal, and the
generic fibre, being finite and smooth over `k⸨X⸩`, is étale. A general finite-dimensional
local complete intersection is the product of its localizations at its maximal ideals, so the
product of the witnesses smooths it.

## Main results

* `Deformation.Examples.Smoothing.exists_finite_powerSeries_specialFiber_etale_genericFiber`:
  a finite-dimensional local complete intersection over `k` is the special fibre of a finite
  flat `k⟦X⟧`-algebra with étale generic fibre.

## References

* [Stacks Project, Tag 0E7W](https://stacks.math.columbia.edu/tag/0E7W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w

namespace Deformation.Examples.Smoothing

/-! ### Smoothing a finite-dimensional local complete intersection -/

/-- A finite smooth algebra over a field is étale. This is checked after extending to an
algebraic closure: smoothness makes the base change reduced, and a finite reduced algebra over
an algebraically closed field is a finite product of copies of that field. -/
private theorem etale_of_finite_of_smooth (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [Algebra.Smooth K A] : Algebra.Etale K A := by
  let Kbar := AlgebraicClosure K
  let : Algebra K Kbar := inferInstance
  let : Algebra Kbar (Kbar ⊗[K] A) :=
    Algebra.TensorProduct.leftAlgebra (R := K) (S := Kbar) (A := Kbar) (B := A)
  let : Module.Finite Kbar (Kbar ⊗[K] A) := inferInstance
  let : Algebra.Smooth Kbar (Kbar ⊗[K] A) := inferInstance
  have hred : IsReduced (Kbar ⊗[K] A) := Algebra.isReduced_of_smooth Kbar _
  let : IsReduced (Kbar ⊗[K] A) := hred
  let : IsArtinianRing (Kbar ⊗[K] A) := IsArtinianRing.of_finite Kbar (Kbar ⊗[K] A)
  let : Finite (MaximalSpectrum (Kbar ⊗[K] A)) := inferInstance
  let ePi := IsArtinianRing.equivPi (Kbar ⊗[K] A)
  let eField (m : MaximalSpectrum (Kbar ⊗[K] A)) : Kbar ≃ₐ[Kbar]
      ((Kbar ⊗[K] A) ⧸ m.asIdeal) := by
    let L := (Kbar ⊗[K] A) ⧸ m.asIdeal
    let : Module.Finite Kbar L := inferInstance
    let : Algebra.IsIntegral Kbar L := inferInstance
    exact AlgEquiv.ofBijective (IsScalarTower.toAlgHom Kbar Kbar L)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Kbar))
  let e : (Kbar ⊗[K] A) ≃ₐ[Kbar]
      (∀ m : MaximalSpectrum (Kbar ⊗[K] A), Kbar) :=
    (ePi.restrictScalars Kbar).trans
      (AlgEquiv.piCongrRight fun m => (eField m).symm)
  let : Algebra.Etale Kbar (Kbar ⊗[K] A) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Kbar

/-- A quotient of a product of rings by a product of ideals is the product of the quotients. -/
private noncomputable def piQuotientAlgEquiv {R : Type*} [CommRing R] {ι : Type*}
    (B : ι → Type*) [∀ i, CommRing (B i)]
    [∀ i, Algebra R (B i)] (I : ∀ i, Ideal (B i)) :
    ((∀ i, B i) ⧸ Ideal.pi I) ≃ₐ[R] ∀ i, B i ⧸ I i := by
  classical
  let f : (∀ i, B i) →ₐ[R] ∀ i, B i ⧸ I i :=
    AlgHom.pi fun i => (Ideal.Quotient.mkₐ R (I i)).comp (Pi.evalAlgHom R B i)
  have hf : Function.Surjective f := by
    intro x
    choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
    exact ⟨y, by ext i; simp [f, hy i]⟩
  have hker : RingHom.ker f = Ideal.pi I := by
    ext x
    rw [RingHom.mem_ker]
    change f x = 0 ↔ ∀ i, x i ∈ I i
    constructor
    · intro hx i
      have hxi := congrArg (fun y => y i) hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [f] using hxi)
    · intro hx
      ext i
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)
  exact (Ideal.quotientEquivAlgOfEq R hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

/-- A finite type local complete intersection over a field which is already local is a global
complete intersection. -/
private theorem isGlobalCompleteIntersection_of_isCompleteIntersection {k : Type u} [Field k]
    {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
    [Algebra.FiniteType k A] (hA : IsCompleteIntersection k A) :
    IsGlobalCompleteIntersection k A := by
  let m := IsLocalRing.maximalIdeal A
  let : IsLocalization m.primeCompl A := IsLocalization.of_le_isUnit (by
    intro x hx
    exact IsLocalRing.notMem_maximalIdeal.mp hx)
  obtain ⟨g, hg, hG⟩ :=
    ((IsCompleteIntersection.localization_atPrime_tfae.{u, v, 0, v} k A m A).out 1 3).mp hA
  have hgu : IsUnit g := IsLocalRing.notMem_maximalIdeal.mp hg
  let : IsLocalization (Submonoid.powers g) A := IsLocalization.of_le_isUnit (by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact hgu.pow n)
  exact gci_transport k
    ((IsLocalization.algEquiv (R := A) (Submonoid.powers g)
      (Localization.Away g) A).restrictScalars k) hG

/-- If the special fibre of a `k⟦X⟧`-algebra is finite over `k`, then the fibre over the
maximal ideal of `k⟦X⟧` is finite over its residue field. -/
private theorem finite_residueField_fiber_of_finite_specialFiber {k : Type u} [Field k]
    {C : Type w} [CommRing C] [Algebra (PowerSeries k) C] [Algebra k C]
    [IsScalarTower k (PowerSeries k) C]
    (hC : Module.Finite k
      (C ⧸ Ideal.span ({algebraMap (PowerSeries k) C PowerSeries.X} : Set C))) :
    Module.Finite (IsLocalRing.maximalIdeal (PowerSeries k)).ResidueField
      ((IsLocalRing.maximalIdeal (PowerSeries k)).Fiber C) := by
  let : (IsLocalRing.maximalIdeal (PowerSeries k)).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal (PowerSeries k)
  let eQuotRes : (PowerSeries k ⧸ IsLocalRing.maximalIdeal (PowerSeries k))
      ≃ₐ[PowerSeries k] (IsLocalRing.maximalIdeal (PowerSeries k)).ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom (PowerSeries k)
        (PowerSeries k ⧸ IsLocalRing.maximalIdeal (PowerSeries k))
        (IsLocalRing.maximalIdeal (PowerSeries k)).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField
        (IsLocalRing.maximalIdeal (PowerSeries k)))
  let J : Ideal C := (IsLocalRing.maximalIdeal (PowerSeries k)).map
    (algebraMap (PowerSeries k) C)
  have hJ : J = Ideal.span
      ({algebraMap (PowerSeries k) C PowerSeries.X} : Set C) := by
    change (IsLocalRing.maximalIdeal (PowerSeries k)).map (algebraMap (PowerSeries k) C) = _
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span]
    simp only [Set.image_singleton]
  let eTen : TensorProduct (PowerSeries k)
      (IsLocalRing.maximalIdeal (PowerSeries k)).ResidueField C
      ≃ₐ[PowerSeries k]
      TensorProduct (PowerSeries k)
        (PowerSeries k ⧸ IsLocalRing.maximalIdeal (PowerSeries k)) C :=
    Algebra.TensorProduct.congr eQuotRes.symm
      (AlgEquiv.refl (R := PowerSeries k) (A₁ := C))
  let eQuot := Algebra.TensorProduct.quotientTensorEquiv (R := PowerSeries k)
    (S := PowerSeries k) (T := C) (A := PowerSeries k)
    (IsLocalRing.maximalIdeal (PowerSeries k))
  let eLid := Algebra.TensorProduct.lid (PowerSeries k) C
  let Iprod : Ideal (TensorProduct (PowerSeries k) (PowerSeries k) C) :=
    Ideal.map (algebraMap (PowerSeries k) (TensorProduct (PowerSeries k) (PowerSeries k) C))
      (IsLocalRing.maximalIdeal (PowerSeries k))
  have hIprod : Ideal.map
      (eLid.toRingEquiv : TensorProduct (PowerSeries k) (PowerSeries k) C →+* C)
      Iprod = J := by
    simp only [Iprod]
    rw [Ideal.map_map]
    congr 1
    ext x
    simp [eLid, Algebra.smul_def]
  let eQuotLidRing : (TensorProduct (PowerSeries k) (PowerSeries k) C ⧸ Iprod) ≃+* (C ⧸ J) :=
    Ideal.quotientEquiv Iprod J eLid.toRingEquiv hIprod.symm
  let eQuotLid : (TensorProduct (PowerSeries k) (PowerSeries k) C ⧸ Iprod)
      ≃ₐ[PowerSeries k] (C ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := eQuotLidRing) (by
      intro x
      change eQuotLidRing (Ideal.Quotient.mk Iprod
        (algebraMap (PowerSeries k) (TensorProduct (PowerSeries k) (PowerSeries k) C) x)) =
        Ideal.Quotient.mk J (algebraMap (PowerSeries k) C x)
      change Ideal.quotientEquiv Iprod J eLid.toRingEquiv hIprod.symm _ = _
      rw [Ideal.quotientEquiv_mk]
      change Ideal.Quotient.mk J (x • (1 : C)) =
        Ideal.Quotient.mk J (algebraMap (PowerSeries k) C x)
      congr 1
      simp [Algebra.smul_def])
  let eFinal : (C ⧸ J) ≃ₐ[k]
      C ⧸ Ideal.span ({algebraMap (PowerSeries k) C PowerSeries.X} : Set C) :=
    Ideal.quotientEquivAlgOfEq k hJ
  let eFiber : (IsLocalRing.maximalIdeal (PowerSeries k)).Fiber C ≃ₐ[k]
      C ⧸ Ideal.span ({algebraMap (PowerSeries k) C PowerSeries.X} : Set C) :=
    (eTen.restrictScalars k).trans (eQuot.restrictScalars k) |>.trans
      ((eQuotLid.restrictScalars k).trans eFinal)
  have hFin : Module.Finite k ((IsLocalRing.maximalIdeal (PowerSeries k)).Fiber C) :=
    Module.Finite.of_surjective eFiber.symm.toLinearMap eFiber.symm.surjective
  let : Module.Finite k ((IsLocalRing.maximalIdeal (PowerSeries k)).Fiber C) := hFin
  exact Module.Finite.of_restrictScalars_finite k
    ((IsLocalRing.maximalIdeal (PowerSeries k)).ResidueField)
    ((IsLocalRing.maximalIdeal (PowerSeries k)).Fiber C)

/-- The smoothing of a finite-dimensional local global complete intersection over a field: it is
the special fibre of a finite flat power-series algebra with étale generic fibre. -/
private theorem exists_finite_flat_smoothing_of_isGlobalCompleteIntersection
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [FiniteDimensional k A] [IsLocalRing A]
    (hA : IsGlobalCompleteIntersection k A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B),
      Module.Finite (PowerSeries k) B ∧ Module.Flat (PowerSeries k) B ∧
        Nonempty ((B ⧸ Ideal.span
          ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)) ≃ₐ[k] A) ∧
        Algebra.Etale (LaurentSeries k)
          (TensorProduct (PowerSeries k) (LaurentSeries k) B) := by
  classical
  obtain ⟨C, _, _, _, _, hFlat, hFT, hSpecial, hSmooth, _⟩ :=
    exists_flat_powerSeries_specialFiber_smooth_genericFiber k A hA
  let I : Ideal C := Ideal.span
    ({algebraMap (PowerSeries k) C PowerSeries.X} : Set C)
  let E := C ⧸ I
  let e : E ≃ₐ[k] A := hSpecial.some
  let : IsLocalRing E := e.symm.toRingEquiv.isLocalRing
  let q : Ideal C := Ideal.comap (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal E)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  have hMapX : algebraMap (PowerSeries k) E PowerSeries.X = 0 := by
    change Ideal.Quotient.mk I (algebraMap (PowerSeries k) C PowerSeries.X) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hMaxMap : (IsLocalRing.maximalIdeal (PowerSeries k)).map
      (algebraMap (PowerSeries k) E) = ⊥ := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span]
    simp [hMapX]
  have hqOver : q.comap (algebraMap (PowerSeries k) C) =
      IsLocalRing.maximalIdeal (PowerSeries k) := by
    apply le_antisymm
    · intro x hx
      by_contra hnot
      have hu : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hnot
      have huE : IsUnit (algebraMap (PowerSeries k) E x) := hu.map _
      have hxE : algebraMap (PowerSeries k) E x ∈ IsLocalRing.maximalIdeal E := by
        simpa [q] using hx
      exact (IsLocalRing.notMem_maximalIdeal.mpr huE) hxE
    · intro x hx
      apply Ideal.mem_comap.mpr
      have hxMap : algebraMap (PowerSeries k) E x ∈
          (IsLocalRing.maximalIdeal (PowerSeries k)).map (algebraMap (PowerSeries k) E) :=
        Ideal.mem_map_of_mem _ hx
      rw [hMaxMap] at hxMap
      have hxZero : algebraMap (PowerSeries k) E x = 0 := Ideal.mem_bot.mp hxMap
      change algebraMap (PowerSeries k) E x ∈ IsLocalRing.maximalIdeal E
      rw [hxZero]
      exact (IsLocalRing.maximalIdeal E).zero_mem
  let : q.LiesOver (IsLocalRing.maximalIdeal (PowerSeries k)) := ⟨hqOver.symm⟩
  let : Module.Finite k A := inferInstance
  have hSpecialFinite : Module.Finite k E :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hFiberFinite : Module.Finite (IsLocalRing.maximalIdeal (PowerSeries k)).ResidueField
      ((IsLocalRing.maximalIdeal (PowerSeries k)).Fiber C) :=
    finite_residueField_fiber_of_finite_specialFiber hSpecialFinite
  have hqf : Algebra.QuasiFiniteAt (PowerSeries k) q :=
    (quasiFiniteAt_forall_iff_finite_fiber (R := PowerSeries k) (S := C)
      (IsLocalRing.maximalIdeal (PowerSeries k))).mpr hFiberFinite q hqOver
  let B := Localization.AtPrime q
  let : CommRing B := inferInstance
  let : Algebra C B := inferInstance
  let : Algebra (PowerSeries k) B := inferInstance
  let : IsScalarTower (PowerSeries k) C B := inferInstance
  let : IsLocalization.AtPrime B q := inferInstance
  let : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  let : HenselianLocalRing (PowerSeries k) :=
    henselianLocalRing_of_isAdicComplete_maximalIdeal (PowerSeries k)
  have hLoc : HenselianLocalRing B ∧ Module.Finite (PowerSeries k) B :=
    ((HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt
      (PowerSeries k)).2.2.1 C hFT q hqf B)
  let : Module.Finite (PowerSeries k) B := hLoc.2
  let : Module.Flat (PowerSeries k) C := hFlat
  let : Module.Flat C B := IsLocalization.flat (R := C) (S := B) q.primeCompl
  have hFlatB : Module.Flat (PowerSeries k) B := Module.Flat.trans (PowerSeries k) C B
  let JB : Ideal B := I.map (algebraMap C B)
  have hJB : JB = Ideal.span
      ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B) := by
    dsimp [JB, I]
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    congr 1
  let mE := IsLocalRing.maximalIdeal E
  let : mE.IsMaximal := IsLocalRing.maximalIdeal.isMaximal E
  have hcomap : mE.comap (Ideal.Quotient.mk I) = q := rfl
  let : IsLocalization.AtPrime (B ⧸ JB) mE :=
    isLocalization_atPrime_quotient q B I mE hcomap
  let : IsLocalization mE.primeCompl E := IsLocalization.of_le_isUnit (by
    intro x hx
    exact IsLocalRing.notMem_maximalIdeal.mp hx)
  let : IsScalarTower k (PowerSeries k) E := inferInstance
  let : IsScalarTower (PowerSeries k) E (B ⧸ JB) :=
    IsScalarTower.of_algebraMap_eq' (R := PowerSeries k) (S := E) (A := B ⧸ JB) rfl
  let : IsScalarTower k (PowerSeries k) (B ⧸ JB) := inferInstance
  let : IsScalarTower k E (B ⧸ JB) := by
    apply IsScalarTower.of_algebraMap_eq' (R := k) (S := E) (A := B ⧸ JB)
    ext x
    simp only [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply k (PowerSeries k) (B ⧸ JB),
      IsScalarTower.algebraMap_apply (PowerSeries k) E (B ⧸ JB),
      IsScalarTower.algebraMap_apply k (PowerSeries k) E]
  let eLoc : (B ⧸ JB) ≃ₐ[E] E :=
    IsLocalization.algEquiv mE.primeCompl (B ⧸ JB) E
  let eFinal : (B ⧸ Ideal.span
      ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)) ≃ₐ[k] (B ⧸ JB) :=
    Ideal.quotientEquivAlgOfEq k hJB.symm
  have hSpecialB : Nonempty ((B ⧸ Ideal.span
      ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)) ≃ₐ[k] A) := by
    let eLocK : (B ⧸ JB) ≃ₐ[k] E := AlgEquiv.restrictScalars k eLoc
    exact ⟨eFinal.trans (eLocK.trans e)⟩
  let T := TensorProduct (PowerSeries k) (LaurentSeries k) C
  let U := TensorProduct (PowerSeries k) (LaurentSeries k) B
  let : Algebra T U :=
    (Algebra.TensorProduct.map (AlgHom.id (PowerSeries k) (LaurentSeries k))
      (IsScalarTower.toAlgHom (PowerSeries k) C B)).toAlgebra
  let : IsScalarTower (LaurentSeries k) T U :=
    IsScalarTower.of_algebraMap_eq' (R := LaurentSeries k) (S := T) (A := U) (by
      apply RingHom.ext
      intro x
      simp [T, U, RingHom.algebraMap_toAlgebra])
  let : IsScalarTower (PowerSeries k) T U :=
    IsScalarTower.of_algebraMap_eq' (R := PowerSeries k) (S := T) (A := U) (by
      apply RingHom.ext
      intro x
      simp [T, U, RingHom.algebraMap_toAlgebra])
  let M' := q.primeCompl.map
    (Algebra.TensorProduct.includeRight (R := PowerSeries k) (A := LaurentSeries k))
  let : IsLocalization M' U := by
    dsimp [M']
    exact IsLocalization.tensorProduct_tensorProduct_right (PowerSeries k)
      (LaurentSeries k) q.primeCompl B (by
        ext
        simp [RingHom.algebraMap_toAlgebra])
  let : Algebra.Smooth (LaurentSeries k) T := hSmooth
  let : Algebra.FormallySmooth T U := Algebra.FormallySmooth.of_isLocalization M'
  have hSmoothUFormally : Algebra.FormallySmooth (LaurentSeries k) U :=
    Algebra.FormallySmooth.comp (LaurentSeries k) T U
  let : Module.Finite (LaurentSeries k) U :=
    Module.Finite.base_change (PowerSeries k) (LaurentSeries k) B
  let : Algebra.Smooth (LaurentSeries k) U :=
    ⟨hSmoothUFormally, (Algebra.FinitePresentation.of_finiteType).mp
      (Module.Finite.finiteType U)⟩
  have hEtaleU : Algebra.Etale (LaurentSeries k) U := etale_of_finite_of_smooth _ U
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    hLoc.2, hFlatB, hSpecialB, hEtaleU⟩

/-- **Stacks 0E7W.** A finite-dimensional local complete intersection `A` over a field `k` is
the special fibre `B/XB` of a finite flat `k⟦X⟧`-algebra `B` whose generic fibre
`k⸨X⸩ ⊗[k⟦X⟧] B` is étale over `k⸨X⸩`. -/
@[stacks 0E7W "the smoothing of a finite local complete intersection"]
public theorem exists_finite_powerSeries_specialFiber_etale_genericFiber
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    [FiniteDimensional k A] (hA : IsLocalCompleteIntersection k A) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B),
      Module.Finite (PowerSeries k) B ∧ Module.Flat (PowerSeries k) B ∧
        Nonempty
          ((B ⧸ Ideal.span ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)) ≃ₐ[k] A) ∧
      Algebra.Etale (LaurentSeries k)
          (TensorProduct (PowerSeries k) (LaurentSeries k) B) := by
  classical
  let : Module.Finite k A := inferInstance
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : Finite (MaximalSpectrum A) := inferInstance
  let : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hFactor (m : MaximalSpectrum A) := by
    let Fm := Localization.AtPrime m.asIdeal
    have hsurj : Function.Surjective (algebraMap A Fm) :=
      IsArtinianRing.localization_surjective m.asIdeal.primeCompl Fm
    let : Module.Finite k Fm := Module.Finite.of_surjective
      (IsScalarTower.toAlgHom k A Fm).toLinearMap hsurj
    let : Algebra.FiniteType k Fm := Module.Finite.finiteType Fm
    let : m.asIdeal.IsMaximal := m.isMaximal
    have hAll := ((IsLocalCompleteIntersection.tfae k A).out 1 3).mp hA
    exact exists_finite_flat_smoothing_of_isGlobalCompleteIntersection (k := k) (A := Fm)
      (isGlobalCompleteIntersection_of_isCompleteIntersection (k := k) (A := Fm)
        (hAll m.asIdeal Fm))
  choose B hComm hPS hk hTower hProps using hFactor
  let (m : MaximalSpectrum A) : CommRing (B m) := hComm m
  let (m : MaximalSpectrum A) : Algebra (PowerSeries k) (B m) := hPS m
  let (m : MaximalSpectrum A) : Algebra k (B m) := hk m
  let (m : MaximalSpectrum A) : IsScalarTower k (PowerSeries k) (B m) := hTower m
  let (m : MaximalSpectrum A) : Module.Finite (PowerSeries k) (B m) := (hProps m).1
  let P := ∀ m : MaximalSpectrum A, B m
  let : CommRing P := inferInstance
  let : Algebra (PowerSeries k) P := inferInstance
  let : Algebra k P := inferInstance
  let : IsScalarTower k (PowerSeries k) P := inferInstance
  have hFiniteP : Module.Finite (PowerSeries k) P := inferInstance
  have hFlatP : Module.Flat (PowerSeries k) P := by
    have hFlatSum : Module.Flat (PowerSeries k) (DirectSum (MaximalSpectrum A) B) :=
      (Module.Flat.directSum_iff (R := PowerSeries k) (M := B)).2
        fun m => (hProps m).2.1
    let : Module.Flat (PowerSeries k) (DirectSum (MaximalSpectrum A) B) := hFlatSum
    exact Module.Flat.of_linearEquiv
      (DirectSum.linearEquivFunOnFintype (PowerSeries k) (MaximalSpectrum A) B).symm
  let J : ∀ m : MaximalSpectrum A, Ideal (B m) := fun m => Ideal.span
    ({algebraMap (PowerSeries k) (B m) PowerSeries.X} : Set (B m))
  let Pfiber := P ⧸ Ideal.span
    ({algebraMap (PowerSeries k) P PowerSeries.X} : Set P)
  have hDenom : Ideal.span
      ({algebraMap (PowerSeries k) P PowerSeries.X} : Set P) = Ideal.pi J := by
    rw [← Ideal.pi_span]
    congr 1
  let eDenom : Pfiber ≃ₐ[k] P ⧸ Ideal.pi J :=
    Ideal.quotientEquivAlgOfEq k hDenom
  have hSpecial : Nonempty (Pfiber ≃ₐ[k] A) :=
    ⟨eDenom.trans ((piQuotientAlgEquiv (R := k) (B := B) J).trans
      ((AlgEquiv.piCongrRight fun m => ((hProps m).2.2.1).some).trans
        ((MaximalSpectrum.toPiLocalizationEquiv A).restrictScalars k).symm))⟩
  let (m : MaximalSpectrum A) : Algebra.Etale (LaurentSeries k)
      (TensorProduct (PowerSeries k) (LaurentSeries k) (B m)) := (hProps m).2.2.2
  let : Algebra.Etale (LaurentSeries k)
      (TensorProduct (PowerSeries k) (LaurentSeries k) P) :=
    Algebra.Etale.of_equiv
      (Algebra.TensorProduct.piRight (PowerSeries k) (LaurentSeries k)
        (LaurentSeries k) B).symm
  exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance,
    hFiniteP, hFlatP, hSpecial, inferInstance⟩

end Deformation.Examples.Smoothing

end
