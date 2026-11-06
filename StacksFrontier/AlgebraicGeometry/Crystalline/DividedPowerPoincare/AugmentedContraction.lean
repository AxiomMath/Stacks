module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.DifferentialsBasis
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.SquareZeroDerivations
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.DifferentialsBasis

/-!
# The divided power Poincaré lemma: the contraction of the augmented de Rham complex

The third part of `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`: the augmented
divided power de Rham complex `0 → A → P → Ω¹_{P/A,δ} → Ω²_{P/A,δ} → ⋯` of
`P = A⟨x_w : w ∈ W⟩` (`Crystalline.augmentedDividedPowerDeRhamComplex`), its splitting into the
subcomplexes indexed by multi-indices, the Koszul contraction on each of them, and the resulting
`Crystalline.augmentedDividedPowerDeRhamComplex_contractible`.

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
* [Stacks Project, Tag 0626](https://stacks.math.columbia.edu/tag/0626)
-/
@[expose] public section

universe u v w uA uW uM

namespace Crystalline

attribute [local implicit_reducible] RestrictScalars

open DividedPowers
open scoped TensorProduct

section OrdinaryExactness

open CategoryTheory
open scoped RightActions

variable (A : Type u) [CommRing A] (W : Type w)

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing
attribute [local instance low] setIndexedDividedPowerPolynomialCommRing
attribute [local instance low] coefficientDividedPowerRingAlgebra
attribute [local instance low] setIndexedDividedPowerPolynomialAlgebra'
attribute [local instance low] setIndexedDividedPowerPolynomialDividedPowerRingAlgebra
attribute [local instance low] indexedDividedPowerPolynomialFinsuppModule
attribute [local instance low] indexedDividedPowerPolynomialFinsuppModuleOp
attribute [local instance low] indexedDividedPowerPolynomialFinsuppCentral

open scoped ExteriorAlgebra
open Module

/-- The terms of the augmented divided power de Rham complex. -/
public noncomputable def augmentedDividedPowerDeRhamTerm (n : ℕ) :
    ModuleCat.{max u w} A :=
  match n with
  | 0 => ModuleCat.of A
      (LinearMap.range (Algebra.linearMap A (setIndexedDividedPowerPolynomialAlgebra A W)))
  | i + 1 => ModuleCat.of A
      (RestrictScalars A (setIndexedDividedPowerPolynomialAlgebra A W)
        (dividedPowerDifferentialForms (A := A)
          (B := setIndexedDividedPowerPolynomialAlgebra A W) (polynomialDividedPowers A W) i))

/-- The augmentation followed by the divided power de Rham differential. -/
public noncomputable def augmentedDividedPowerDeRhamDifferential (n : ℕ) :
    augmentedDividedPowerDeRhamTerm A W n ⟶
      augmentedDividedPowerDeRhamTerm A W (n + 1) :=
  match n with
  | 0 => ModuleCat.ofHom <|
      ((exteriorPower.zeroEquiv (setIndexedDividedPowerPolynomialAlgebra A W)
        (dividedPowerDifferentials (A := A)
          (B := setIndexedDividedPowerPolynomialAlgebra A W)
          (polynomialDividedPowers A W))).symm.toLinearMap.restrictScalars A).comp
        (Submodule.subtype
          (LinearMap.range (Algebra.linearMap A (setIndexedDividedPowerPolynomialAlgebra A W))))
  | i + 1 => ModuleCat.ofHom <|
      (dividedPowerDeRhamComplex (A := A)
        (B := setIndexedDividedPowerPolynomialAlgebra A W)
        (polynomialDividedPowers A W)).differential i

attribute [local implicit_reducible] augmentedDividedPowerDeRhamTerm
  augmentedDividedPowerDeRhamDifferential

/-- Under the canonical identification of the degree-zero term with `A`, the first
differential is the usual coefficient-map augmentation into degree-zero forms. -/
public theorem augmentedDividedPowerDeRhamDifferential_coefficient (a : A) :
    augmentedDividedPowerDeRhamDifferential A W 0 (coefficientLinearEquiv A W a) =
      (exteriorPower.zeroEquiv (setIndexedDividedPowerPolynomialAlgebra A W)
        (dividedPowerDifferentials (A := A)
          (B := setIndexedDividedPowerPolynomialAlgebra A W)
          (polynomialDividedPowers A W))).symm
        (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a) := by
  rfl

/-- The degree-zero part of an exterior power is recovered by `exteriorPower.zeroEquiv`. -/
private theorem zeroEquiv_smul_ιMulti {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (v : Fin 0 → M) :
    exteriorPower.zeroEquiv R M (r • exteriorPower.ιMulti R 0 v) = r := by
  rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

-- The degree-zero case passes through the `exteriorPower.zeroEquiv` identification.
/-- The augmented differential squares to zero. -/
theorem augmentedDividedPowerDeRhamDifferential_comp (n : ℕ) :
      augmentedDividedPowerDeRhamDifferential A W n ≫
      augmentedDividedPowerDeRhamDifferential A W (n + 1) = 0 := by
  ext x
  cases n with
  | zero =>
    have hCR : (coefficientDividedPowerRing A).commRing =
        (inferInstance : CommRing A) := rfl
    have hComm :
        (DividedPowerAlgebra.ringCon (↑(coefficientDividedPowerRing A))
          (W →₀ ↑(coefficientDividedPowerRing A))).instCommRingQuotient =
        (DividedPowerAlgebra.ringCon A (W →₀ A)).instCommRingQuotient := by
      cases hCR
      rfl
    cases hCR
    let Bq := DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
      (W →₀ ↑(coefficientDividedPowerRing A))
    have hB : Bq = setIndexedDividedPowerPolynomialAlgebra A W := rfl
    let q : ↑(coefficientDividedPowerRing A) →+* Bq :=
      (RingCon.mkₐ (↑(coefficientDividedPowerRing A))
        (DividedPowerAlgebra.ringCon (↑(coefficientDividedPowerRing A))
          (W →₀ ↑(coefficientDividedPowerRing A)))).toRingHom.comp
        (MvPolynomial.C : ↑(coefficientDividedPowerRing A) →+*
          MvPolynomial (ℕ × (W →₀ ↑(coefficientDividedPowerRing A)))
            ↑(coefficientDividedPowerRing A))
    let c : A →+* ↑(coefficientDividedPowerRing A) := RingHom.id A
    let : Algebra A (↑(coefficientDividedPowerRing A)) := c.toAlgebra
    let qStd : A →+* Bq :=
      (RingCon.mkₐ A (DividedPowerAlgebra.ringCon A (W →₀ A))).toRingHom.comp
        (MvPolynomial.C : A →+* MvPolynomial (ℕ × (W →₀ A)) A)
    let instOrig : Algebra A Bq := qStd.toAlgebra
    let C : (inst : Algebra A Bq) →
        @DividedPowerDeRhamComplex A Bq _ _ inst
          (dividedPowerPolynomialIdeal (coefficientDividedPowerRing A).ideal W)
          (polynomialDividedPowers A W) := fun inst => by
      let : Algebra A Bq := inst
      exact @dividedPowerDeRhamComplex A Bq _ _ inst
        (dividedPowerPolynomialIdeal (coefficientDividedPowerRing A).ideal W)
        (polynomialDividedPowers A W)
    let : Algebra A Bq := instOrig
    obtain ⟨a, ha⟩ := x.2
    have hx : x = ⟨(Algebra.linearMap A Bq) a, ⟨a, rfl⟩⟩ := by
      apply Subtype.ext
      exact ha.symm
    subst x
    have hqa : (q.comp c) a = algebraMap A Bq a := by
      change (q.comp c) a = qStd a
      rfl
    have hcoeff : dividedPowerDifferential (A := A) (polynomialDividedPowers A W)
        ((q.comp c) a) = 0 := by
      have hd : KaehlerDifferential.D A
          (DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
            (W →₀ ↑(coefficientDividedPowerRing A))) ((q.comp c) a) = 0 := by
        convert (KaehlerDifferential.D A
          (DividedPowerAlgebra (↑(coefficientDividedPowerRing A))
            (W →₀ ↑(coefficientDividedPowerRing A)))).map_algebraMap a using 1
        rfl
      simpa [dividedPowerDifferential] using congrArg
        ((dividedPowerDifferentialRelations (A := A)
          (polynomialDividedPowers A W)).mkQ) hd
    have hg := (C instOrig).differential_generator 0
      (fun _ : Fin 1 => (q.comp c) a)
    have hvec : (fun _ : Fin 1 => dividedPowerDifferential (A := A)
        (polynomialDividedPowers A W) ((q.comp c) a) :
          Fin 1 → dividedPowerDifferentials (A := A) (B := Bq)
            (polynomialDividedPowers A W)) = fun _ => 0 := by
      funext j
      exact hcoeff
    have hg0 : ((C instOrig).differential 0)
        ((q.comp c) a • exteriorPower.ιMulti Bq 0
          (fun j => dividedPowerDifferential (A := A)
            (polynomialDividedPowers A W) ((q.comp c) a))) = 0 := by
      rw [hg, hvec]
      exact (exteriorPower.ιMulti Bq 1).map_coord_zero
        (m := fun _ => (0 : dividedPowerDifferentials (A := A) (B := Bq)
          (polynomialDividedPowers A W))) (i := 0) rfl
    have harg : (exteriorPower.zeroEquiv Bq
        (dividedPowerDifferentials (A := A) (B := Bq)
          (polynomialDividedPowers A W))).symm (algebraMap A Bq a) =
        (q.comp c) a • exteriorPower.ιMulti Bq 0
          (fun j : Fin 0 => dividedPowerDifferential (A := A)
            (polynomialDividedPowers A W) ((q.comp c) a)) := by
      rw [← hqa]
      apply (exteriorPower.zeroEquiv Bq (dividedPowerDifferentials (A := A) (B := Bq)
        (polynomialDividedPowers A W))).injective
      rw [LinearEquiv.apply_symm_apply, zeroEquiv_smul_ιMulti]
    let restrictEquiv := RestrictScalars.addEquiv A Bq
      (dividedPowerDifferentialForms (A := A) (B := Bq)
        (polynomialDividedPowers A W) 0)
    have harg' := congrArg restrictEquiv.symm harg
    have hg1 := congrArg ((C instOrig).differential 0) harg'
    have hg0' : ((C instOrig).differential 0)
        (restrictEquiv.symm ((q.comp c) a • exteriorPower.ιMulti Bq 0
          (fun j : Fin 0 => dividedPowerDifferential (A := A)
            (polynomialDividedPowers A W) ((q.comp c) a)))) = 0 := by
      simpa [restrictEquiv, RestrictScalars.addEquiv, AddEquiv.refl,
        Equiv.refl] using hg0
    have hg2 : ((C instOrig).differential 0)
        (restrictEquiv.symm ((exteriorPower.zeroEquiv Bq
          (dividedPowerDifferentials (A := A) (B := Bq)
            (polynomialDividedPowers A W))).symm (algebraMap A Bq a))) = 0 := by
      calc
        _ = ((C instOrig).differential 0)
            (restrictEquiv.symm ((q.comp c) a • exteriorPower.ιMulti Bq 0
              (fun j : Fin 0 => dividedPowerDifferential (A := A)
                (polynomialDividedPowers A W) ((q.comp c) a)))) := hg1
        _ = 0 := hg0'
    cases hComm
    let instStd : Algebra A Bq :=
      (DividedPowerAlgebra.ringCon A (W →₀ A)).instAlgebraQuotient
    have hAlgStd : instOrig = instStd := by
      apply Algebra.algebra_ext
      intro b
      rfl
    let P : (inst : Algebra A Bq) → Prop := fun inst => by
      let (priority := 10000) : Algebra A Bq := inst
      let r := RestrictScalars.addEquiv A Bq
        (dividedPowerDifferentialForms (A := A) (B := Bq)
          (polynomialDividedPowers A W) 0)
      exact ((C inst).differential 0)
        (r.symm ((exteriorPower.zeroEquiv Bq
          (dividedPowerDifferentials (A := A) (B := Bq)
            (polynomialDividedPowers A W))).symm (algebraMap A Bq a))) = 0
    have hOrig : P instOrig := by
      simpa [P, restrictEquiv] using hg2
    have hStd : P instStd := (congrArg P hAlgStd).mp hOrig
    let (priority := 10000) : Algebra A Bq := instStd
    convert hStd using 1 <;> rfl
  | succ n =>
    change ((dividedPowerDeRhamComplex (A := A)
      (B := setIndexedDividedPowerPolynomialAlgebra A W)
      (polynomialDividedPowers A W)).differential (n + 1)).comp
      ((dividedPowerDeRhamComplex (A := A)
        (B := setIndexedDividedPowerPolynomialAlgebra A W)
        (polynomialDividedPowers A W)).differential n) x = 0
    exact congrArg (fun f => f x) (dividedPowerDeRhamComplex_differential_squared
        (A := A) (B := setIndexedDividedPowerPolynomialAlgebra A W)
        (polynomialDividedPowers A W) n)

/-- The augmented divided power de Rham cochain complex, indexed with the augmentation
in degree zero. -/
public noncomputable def augmentedDividedPowerDeRhamComplex :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  CochainComplex.of (augmentedDividedPowerDeRhamTerm A W)
    (augmentedDividedPowerDeRhamDifferential A W)
    (augmentedDividedPowerDeRhamDifferential_comp A W)

private noncomputable def augmentedContractionOne :
    augmentedDividedPowerDeRhamTerm A W 1 ⟶
      augmentedDividedPowerDeRhamTerm A W 0 :=
  ModuleCat.ofHom <|
    (coefficientLinearEquiv A W).toLinearMap.comp <|
      (dividedPowerPolynomialAugmentation A W).toLinearMap.comp <|
        ((exteriorPower.zeroEquiv (setIndexedDividedPowerPolynomialAlgebra A W)
          (dividedPowerDifferentials (A := A)
            (B := setIndexedDividedPowerPolynomialAlgebra A W)
            (polynomialDividedPowers A W))).toLinearMap.restrictScalars A)

private theorem augmentedContractionOne_leftInverse :
    augmentedDividedPowerDeRhamDifferential A W 0 ≫
      augmentedContractionOne A W = 𝟙 _ := by
  ext x
  obtain ⟨a, ha⟩ := x.2
  have hx : x = coefficientLinearEquiv A W a := by
    apply Subtype.ext
    exact ha.symm
  subst x
  change coefficientLinearEquiv A W
      (dividedPowerPolynomialAugmentation A W
        ((exteriorPower.zeroEquiv (setIndexedDividedPowerPolynomialAlgebra A W)
          (dividedPowerDifferentials (A := A)
            (B := setIndexedDividedPowerPolynomialAlgebra A W) (polynomialDividedPowers A W)))
          ((exteriorPower.zeroEquiv (setIndexedDividedPowerPolynomialAlgebra A W)
            (dividedPowerDifferentials (A := A)
              (B := setIndexedDividedPowerPolynomialAlgebra A W)
              (polynomialDividedPowers A W))).symm
            (algebraMap A (setIndexedDividedPowerPolynomialAlgebra A W) a)))) =
      coefficientLinearEquiv A W a
  rw [LinearEquiv.apply_symm_apply]
  congr 1
  exact (dividedPowerPolynomialAugmentation A W).commutes a

noncomputable section
/-- The linear order on `W` given by a well-ordering of `W`. -/
local instance : LinearOrder W := by
  classical
  exact linearOrderOfSTO WellOrderingRel

private theorem image_fin_cons {I : Type*} [DecidableEq I] {n : ℕ}
    (i : I) (v : Fin n → I) :
    Finset.univ.image (Fin.cons i v) = insert i (Finset.univ.image v) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨k, rfl⟩
    exact Fin.cases (Or.inl rfl) (fun k => Or.inr ⟨k, rfl⟩) k
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨k.succ, rfl⟩

private theorem exteriorWedgeLeft_ιMulti
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M) (n : ℕ) (v : Fin n → M) :
    exteriorWedgeLeft e n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti R (n + 1) (Fin.cons e v) := by
  apply Subtype.ext
  simp only [exteriorWedgeLeft, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.mulLeft_apply, exteriorPower.ιMulti_apply_coe,
    Koszul.ιMulti_succ_apply, Fin.cons_zero, Fin.tail_cons]

private theorem exteriorWedgeLeft_sum_ιMulti
    {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype I]
    (e : I → M) (n : ℕ) (v : Fin n → M) :
    exteriorWedgeLeft (∑ i, e i) n (exteriorPower.ιMulti R n v) =
      ∑ i, exteriorPower.ιMulti R (n + 1) (Fin.cons (e i) v) := by
  apply Subtype.ext
  simp only [exteriorWedgeLeft, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.mulLeft_apply, exteriorPower.ιMulti_apply_coe,
    Submodule.coe_sum, Koszul.ιMulti_succ_apply, Fin.cons_zero, Fin.tail_cons,
    map_sum, Finset.sum_mul]

private theorem lower_multiIndex_insert {I : Type*} [DecidableEq I]
    (K : I →₀ ℕ) (s : Finset I) (i : I) (hi : i ∉ s) :
    (K - finsetMultiIndex s).erase i +
      Finsupp.single i ((K - finsetMultiIndex s) i - 1) =
      K - finsetMultiIndex (insert i s) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [finsetMultiIndex_apply, Finsupp.erase_same, hi]
  · simp [Finsupp.erase_ne hji, Finsupp.single_eq_of_ne hji,
      finsetMultiIndex_apply, hji]

private theorem support_sub_finsetMultiIndex_subset {I : Type*}
    (K : I →₀ ℕ) (s : Finset I) :
    (K - finsetMultiIndex s).support ⊆ K.support := by
  intro i hi
  simp only [Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply] at *
  omega

private theorem mem_finset_of_notMem_sub_support {I : Type*}
    (K : I →₀ ℕ) (s : Finset I) (i : I)
    (hi : i ∈ K.support) (hni : i ∉ (K - finsetMultiIndex s).support) : i ∈ s := by
  classical
  simp only [Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply, not_not,
    finsetMultiIndex_apply] at *
  split_ifs at hni with hs
  · exact hs
  · omega

private abbrev dpRing :=
  setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W

private abbrev dpForms (n : ℕ) :=
  dividedPowerDifferentialForms (A := A) (B := ↑(dpRing A W)) (dpRing A W).dividedPowers n

private def dpD (n : ℕ) : dpForms A W n →ₗ[A] dpForms A W (n + 1) :=
  (dividedPowerDeRhamComplex (A := A) (B := ↑(dpRing A W))
    (dpRing A W).dividedPowers).differential n

private def dpDx (i : W) := dividedPowerDifferential (A := A) (dpRing A W).dividedPowers
  (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)

private def sectorSubset (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard K.support n) : Set.powersetCard W n :=
  Set.powersetCard.map n (Function.Embedding.subtype _) I

private def sectorBasis (K : W →₀ ℕ) (n : ℕ) :
    Basis (Set.powersetCard K.support n) A (⋀[A]^n (K.support →₀ A)) :=
  (Finsupp.basisSingleOne (R := A) (ι := K.support)).exteriorPower n

private def dpSectorMap (K : W →₀ ℕ) (n : ℕ) :
    (⋀[A]^n (K.support →₀ A)) →ₗ[A] dpForms A W n :=
  (sectorBasis A W K n).constr A fun I =>
    dividedPowerDifferentialFormsABasis A W n
      (K - finsetMultiIndex (sectorSubset W K n I).val, sectorSubset W K n I)

private theorem dpSectorMap_basis (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard K.support n) :
    dpSectorMap A W K n (sectorBasis A W K n I) =
      dividedPowerDifferentialFormsABasis A W n
        (K - finsetMultiIndex (sectorSubset W K n I).val, sectorSubset W K n I) :=
  Module.Basis.constr_basis _ _ _ _

private theorem dpSectorMap_basis_wedge (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard K.support n) :
    dpSectorMap A W K n (sectorBasis A W K n I) =
      (dividedPowerPolynomialMonomial A
        (K - finsetMultiIndex (sectorSubset W K n I).val) : ↑(dpRing A W)) •
      exteriorPower.ιMulti (↑(dpRing A W)) n
        (dpDx A W ∘ Subtype.val ∘ Set.powersetCard.ofFinEmbEquiv.symm I) := by
  rw [dpSectorMap_basis, dividedPowerDifferentialFormsABasis_apply_monomial]
  unfold exteriorPower.ιMulti_family
  congr 2
  exact congrArg (fun q => dpDx A W ∘ q)
    (Set.powersetCard.ofFinEmbEquiv_symm_map I (OrderEmbedding.subtype _)).symm

private theorem dpSectorMap_ιMulti (K : W →₀ ℕ) (n : ℕ)
    (v : Fin n → K.support) :
    dpSectorMap A W K n
      (exteriorPower.ιMulti A n (fun j => Finsupp.single (v j) 1)) =
      (dividedPowerPolynomialMonomial A
        (K - finsetMultiIndex (Finset.univ.image (Subtype.val ∘ v))) : ↑(dpRing A W)) •
        exteriorPower.ιMulti (↑(dpRing A W)) n (dpDx A W ∘ Subtype.val ∘ v) := by
  classical
  by_cases hv : Function.Injective v
  · let f : (Fin n → K.support) → dpForms A W n := fun v =>
      (dividedPowerPolynomialMonomial A
        (K - finsetMultiIndex (Finset.univ.image (Subtype.val ∘ v))) : ↑(dpRing A W)) •
        exteriorPower.ιMulti (↑(dpRing A W)) n (dpDx A W ∘ Subtype.val ∘ v)
    have hf (v : Fin n → K.support) (σ : Equiv.Perm (Fin n)) :
        f (v ∘ σ) = σ.sign • f v := by
      have hi : Finset.univ.image (Subtype.val ∘ (v ∘ σ)) =
          Finset.univ.image (Subtype.val ∘ v) := by
        ext i
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
        constructor
        · rintro ⟨a, ha⟩
          exact ⟨σ a, ha⟩
        · rintro ⟨a, ha⟩
          exact ⟨σ.symm a, by simpa only [σ.apply_symm_apply] using ha⟩
      dsimp only [f]
      rw [hi]
      simp only [← Function.comp_assoc, AlternatingMap.map_perm]
      exact smul_comm _ _ _
    have hm : dpSectorMap A W K n =
        ((Finsupp.basisSingleOne (R := A) (ι := K.support)).exteriorPower n).constr A
          (fun I => f (Set.powersetCard.ofFinEmbEquiv.symm I)) := by
      apply (sectorBasis A W K n).ext
      intro I
      rw [dpSectorMap_basis_wedge]
      rw [sectorBasis, Module.Basis.constr_basis]
      dsimp only [f]
      congr 4
      ext i
      simp only [sectorSubset, Set.powersetCard.val_map, Finset.mem_map,
        Function.Embedding.coe_subtype, Finset.mem_image, Finset.mem_univ, true_and,
        Function.comp_apply]
      constructor
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨k, rfl⟩ :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I j).mpr hj
        exact ⟨k, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨_, (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem I _).mp
          ⟨j, rfl⟩, rfl⟩
    rw [hm]
    exact Module.Basis.exteriorPower_constr_ιMulti _ _ _ hf v hv
  · have hl : exteriorPower.ιMulti A n (fun j => Finsupp.single (v j) (1 : A)) = 0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ fun h =>
        hv (Function.Injective.of_comp (f := fun a : K.support => Finsupp.single a (1 : A)) h)
    have hr : exteriorPower.ιMulti (↑(dpRing A W)) n
        (dpDx A W ∘ Subtype.val ∘ v) = 0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ fun h =>
        hv (Function.Injective.of_comp (f := dpDx A W ∘ Subtype.val) h)
    rw [hl, hr, map_zero, smul_zero]
private def sectorLiftSubset (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard W n) (hI : I.val ⊆ K.support) :
    Set.powersetCard K.support n :=
  ⟨I.val.subtype (· ∈ K.support), by
    change (I.val.subtype (· ∈ K.support)).card = n
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr (fun i hi => hI hi)]
    exact I.property⟩

private theorem sectorSubset_lift (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard W n) (hI : I.val ⊆ K.support) :
    sectorSubset W K n (sectorLiftSubset W K n I hI) = I := by
  apply Subtype.ext
  exact Finset.subtype_map_of_mem (fun i hi => hI hi)

private theorem sectorSubset_supported (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard K.support n) : (sectorSubset W K n I).val ⊆ K.support := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact j.property

private theorem sectorLiftSubset_map (K : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard K.support n) :
    sectorLiftSubset W K n (sectorSubset W K n I)
      (sectorSubset_supported W K n I) = I := by
  apply Subtype.ext
  ext i
  simp [sectorLiftSubset, sectorSubset]

private def sectorVector (K : W →₀ ℕ) : K.support →₀ A :=
  ∑ i : K.support, Finsupp.single i 1

-- The coefficient-ring identifications require unfolding the divided power algebra.
private theorem dpSectorMap_differential_ιMulti (K : W →₀ ℕ) (n : ℕ)
    (v : Fin n → K.support) :
    (dpD A W) n
        (dpSectorMap A W K n (exteriorPower.ιMulti A n (fun j => Finsupp.single (v j) 1))) =
      dpSectorMap A W K (n + 1)
        (exteriorWedgeLeft (sectorVector A W K) n
          (exteriorPower.ιMulti A n (fun j => Finsupp.single (v j) 1))) := by
  classical
  let s := Finset.univ.image (Subtype.val ∘ v)
  let L := K - finsetMultiIndex s
  let wedge (i : W) := exteriorPower.ιMulti (↑(dpRing A W)) (n + 1)
    (Fin.cons (dpDx A W i) (dpDx A W ∘ Subtype.val ∘ v))
  have hz (i : W) (hi : i ∈ s) : wedge i = 0 := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := j.succ)
    · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at *
      rw [hj]
    · exact (Fin.succ_ne_zero j).symm
  have hr : dpSectorMap A W K (n + 1)
        (exteriorWedgeLeft (sectorVector A W K) n
          (exteriorPower.ιMulti A n (fun j => Finsupp.single (v j) 1))) =
      ∑ i ∈ K.support,
        (dividedPowerPolynomialMonomial A (K - finsetMultiIndex (insert i s)) : ↑(dpRing A W)) •
          wedge i := by
    rw [sectorVector, exteriorWedgeLeft_sum_ιMulti, map_sum]
    rw [← Finset.sum_coe_sort K.support]
    apply Finset.sum_congr rfl
    intro i _
    have hvec := Fin.comp_cons (fun i : K.support => Finsupp.single i (1 : A)) i v
    refine (congrArg (fun z => dpSectorMap A W K (n + 1)
      (exteriorPower.ιMulti A (n + 1) z)) hvec.symm).trans ?_
    have hh := dpSectorMap_ιMulti A W K (n + 1) (Fin.cons i v)
    change dpSectorMap A W K (n + 1)
      (exteriorPower.ιMulti A (n + 1)
        ((fun a : K.support => Finsupp.single a (1 : A)) ∘ Fin.cons i v)) = _ at hh
    simpa only [Fin.comp_cons, image_fin_cons, Function.comp_assoc] using hh
  rw [dpSectorMap_ιMulti, hr]
  have hd := dividedPowerDeRhamDifferential_monomial A W n L (Subtype.val ∘ v)
  refine hd.trans ?_
  change (∑ i ∈ L.support,
      (dividedPowerPolynomialMonomial A (L.erase i + Finsupp.single i (L i - 1)) : ↑(dpRing A W)) •
        wedge i) = _
  calc
    _ = ∑ i ∈ K.support,
        (dividedPowerPolynomialMonomial A (L.erase i + Finsupp.single i (L i - 1)) :
          ↑(dpRing A W)) •
          wedge i := by
      apply Finset.sum_subset (support_sub_finsetMultiIndex_subset K s)
      intro i hi hni
      rw [hz i (mem_finset_of_notMem_sub_support K s i hi hni), smul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · rw [hz i his, smul_zero, smul_zero]
      · rw [lower_multiIndex_insert K s i his]

private theorem dpSectorMap_differential (K : W →₀ ℕ) (n : ℕ)
    (x : ⋀[A]^n (K.support →₀ A)) :
    (dpD A W) n
        (dpSectorMap A W K n x) =
      dpSectorMap A W K (n + 1) (exteriorWedgeLeft (sectorVector A W K) n x) := by
  suffices ((dpD A W) n).comp
      (dpSectorMap A W K n) =
      (dpSectorMap A W K (n + 1)).comp (exteriorWedgeLeft (sectorVector A W K) n) from
    DFunLike.congr_fun this x
  apply (sectorBasis A W K n).ext
  intro I
  change _ = _
  simp only [LinearMap.comp_apply, sectorBasis, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family]
  exact dpSectorMap_differential_ιMulti A W K n (Set.powersetCard.ofFinEmbEquiv.symm I)

private def sectorFunctional (K : W →₀ ℕ) : Module.Dual A (K.support →₀ A) :=
  if h : K.support.Nonempty then
    Finsupp.lapply (⟨h.choose, h.choose_spec⟩ : K.support)
  else 0

private theorem sectorFunctional_vector (K : W →₀ ℕ) (hK : K.support.Nonempty) :
    sectorFunctional A W K (sectorVector A W K) = 1 := by
  classical
  simp [sectorFunctional, hK, sectorVector, Finsupp.single_apply]

private def dpFormsHomotopy (n : ℕ) : dpForms A W (n + 1) →ₗ[A] dpForms A W n :=
  (dividedPowerDifferentialFormsABasis A W (n + 1)).constr A fun z =>
    let K := z.1 + finsetMultiIndex z.2.val
    let I := sectorLiftSubset W K (n + 1) z.2
      (subset_support_add_finsetMultiIndex z.2.val z.1)
    dpSectorMap A W K n
      (Koszul.d (sectorFunctional A W K) n (sectorBasis A W K (n + 1) I))

private theorem dpFormsHomotopy_basis_of_total (n : ℕ) (L : W →₀ ℕ)
    (I : Set.powersetCard W (n + 1)) (K : W →₀ ℕ)
    (hK : L + finsetMultiIndex I.val = K) (hI : I.val ⊆ K.support) :
    dpFormsHomotopy A W n (dividedPowerDifferentialFormsABasis A W (n + 1) (L, I)) =
      dpSectorMap A W K n (Koszul.d (sectorFunctional A W K) n
        (sectorBasis A W K (n + 1) (sectorLiftSubset W K (n + 1) I hI))) := by
  subst K
  exact Module.Basis.constr_basis _ _ _ _

private theorem dpFormsHomotopy_sectorMap (K : W →₀ ℕ) (n : ℕ)
    (x : ⋀[A]^(n + 1) (K.support →₀ A)) :
    dpFormsHomotopy A W n (dpSectorMap A W K (n + 1) x) =
      dpSectorMap A W K n (Koszul.d (sectorFunctional A W K) n x) := by
  suffices (dpFormsHomotopy A W n).comp (dpSectorMap A W K (n + 1)) =
      (dpSectorMap A W K n).comp (Koszul.d (sectorFunctional A W K) n) from
    DFunLike.congr_fun this x
  apply (sectorBasis A W K (n + 1)).ext
  intro I
  simp only [LinearMap.comp_apply, dpSectorMap_basis]
  rw [dpFormsHomotopy_basis_of_total A W n _ _ K
    (finsetMultiIndex_sub_add _ K (sectorSubset_supported W K (n + 1) I))
    (sectorSubset_supported W K (n + 1) I), sectorLiftSubset_map]

private theorem exteriorWedgeLeft_contract_zero
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (e : M) (he : φ e = 1) (x : ⋀[R]^0 M) :
    Koszul.d φ 0 (exteriorWedgeLeft e 0 x) = x := by
  have hx : Koszul.contraction φ (x : ExteriorAlgebra R M) = 0 := by
    obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv R M).symm.surjective x
    simp only [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul_of_tower,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply, map_smul,
      Koszul.contraction, CliffordAlgebra.contractLeft_one, smul_zero]
  apply Subtype.ext
  change Koszul.contraction φ (ExteriorAlgebra.ι R e * (x : ExteriorAlgebra R M)) = _
  have h := koszul_scalar_eq_homotopy φ e (x : ExteriorAlgebra R M)
  simpa only [he, one_smul, hx, mul_zero, add_zero] using h.symm

private theorem dpSectorMap_lift_basis (L : W →₀ ℕ) (n : ℕ)
    (I : Set.powersetCard W n) :
    let K := L + finsetMultiIndex I.val
    dpSectorMap A W K n (sectorBasis A W K n
      (sectorLiftSubset W K n I (subset_support_add_finsetMultiIndex I.val L))) =
      dividedPowerDifferentialFormsABasis A W n (L, I) := by
  dsimp only
  rw [dpSectorMap_basis, sectorSubset_lift, add_tsub_cancel_right]

private theorem dpFormsHomotopy_identity (n : ℕ) (x : dpForms A W (n + 1)) :
    ((dpD A W) n
        (dpFormsHomotopy A W n x) : dpForms A W (n + 1)) +
      dpFormsHomotopy A W (n + 1)
        ((dpD A W) (n + 1) x) = x := by
  let d : (n : ℕ) → dpForms A W n →ₗ[A] dpForms A W (n + 1) := fun n =>
    (dpD A W) n
  suffices (d n).comp (dpFormsHomotopy A W n) +
      (dpFormsHomotopy A W (n + 1)).comp (d (n + 1)) = LinearMap.id from
    DFunLike.congr_fun this x
  apply (dividedPowerDifferentialFormsABasis A W (n + 1)).ext
  rintro ⟨L, I⟩
  let K := L + finsetMultiIndex I.val
  let J := sectorLiftSubset W K (n + 1) I (subset_support_add_finsetMultiIndex I.val L)
  let y := sectorBasis A W K (n + 1) J
  have hy : dpSectorMap A W K (n + 1) y =
      dividedPowerDifferentialFormsABasis A W (n + 1) (L, I) := dpSectorMap_lift_basis A W L _ I
  have hK : K.support.Nonempty := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < I.val.card by rw [I.property]; omega)
    exact ⟨i, subset_support_add_finsetMultiIndex I.val L hi⟩
  change dpD A W n (dpFormsHomotopy A W n _) +
    dpFormsHomotopy A W (n + 1) (dpD A W (n + 1) _) = _
  rw [← hy, dpFormsHomotopy_sectorMap]
  have h₁ := dpSectorMap_differential A W K n (Koszul.d (sectorFunctional A W K) n y)
  have h₂ := (congrArg (dpFormsHomotopy A W (n + 1))
    (dpSectorMap_differential A W K (n + 1) y)).trans
    (dpFormsHomotopy_sectorMap A W K (n + 1) (exteriorWedgeLeft (sectorVector A W K) (n + 1) y))
  calc
    _ = dpSectorMap A W K (n + 1)
        (exteriorWedgeLeft (sectorVector A W K) n (Koszul.d (sectorFunctional A W K) n y)) +
        dpSectorMap A W K (n + 1)
          (Koszul.d (sectorFunctional A W K) (n + 1)
            (exteriorWedgeLeft (sectorVector A W K) (n + 1) y)) := congrArg₂ (· + ·) h₁ h₂
    _ = dpSectorMap A W K (n + 1) _ := (map_add _ _ _).symm
    _ = _ := by
      apply congrArg (dpSectorMap A W K (n + 1))
      exact (add_comm _ _).trans (exteriorWedgeLeft_contract
        (sectorFunctional A W K) (sectorVector A W K) (sectorFunctional_vector A W K hK) n y)

private def dpConstantProjection : dpForms A W 0 →ₗ[A] dpForms A W 0 :=
  (dividedPowerDifferentialFormsABasis A W 0).constr A fun z =>
    if z.1 = 0 then dividedPowerDifferentialFormsABasis A W 0 z else 0

private theorem dpConstantProjection_basis (L : W →₀ ℕ) (I : Set.powersetCard W 0) :
    dpConstantProjection A W (dividedPowerDifferentialFormsABasis A W 0 (L, I)) =
      if L = 0 then dividedPowerDifferentialFormsABasis A W 0 (L, I) else 0 :=
  Module.Basis.constr_basis _ _ _ _

private theorem dpDifferential_basis_zero (n : ℕ) (I : Set.powersetCard W n) :
    (dpD A W) n
      (dividedPowerDifferentialFormsABasis A W n (0, I)) = 0 := by
  rw [dividedPowerDifferentialFormsABasis_apply_monomial]
  dsimp only [exteriorPower.ιMulti_family]
  have hh := dividedPowerDeRhamDifferential_monomial A W n 0
    (Set.powersetCard.ofFinEmbEquiv.symm I)
  simp only [Finsupp.support_zero, Finset.sum_empty] at hh
  exact hh

private theorem dpFormsHomotopy_zero (x : dpForms A W 0) :
    dpConstantProjection A W x + dpFormsHomotopy A W 0
      ((dpD A W) 0 x) = x := by
  let d : dpForms A W 0 →ₗ[A] dpForms A W 1 :=
    (dpD A W) 0
  suffices dpConstantProjection A W + (dpFormsHomotopy A W 0).comp d = LinearMap.id from
    DFunLike.congr_fun this x
  apply (dividedPowerDifferentialFormsABasis A W 0).ext
  rintro ⟨L, I⟩
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    dpConstantProjection_basis]
  by_cases hL : L = 0
  · subst L
    change _ + dpFormsHomotopy A W 0
      ((dpD A W) 0 _) = _
    rw [dpDifferential_basis_zero, map_zero, add_zero]
    simp only [ite_true]
  · rw [ite_eq_right hL, zero_add]
    let K := L + finsetMultiIndex I.val
    let J := sectorLiftSubset W K 0 I (subset_support_add_finsetMultiIndex I.val L)
    let y := sectorBasis A W K 0 J
    have hy : dpSectorMap A W K 0 y =
        dividedPowerDifferentialFormsABasis A W 0 (L, I) := dpSectorMap_lift_basis A W L _ I
    have hI : I.val = ∅ := Finset.card_eq_zero.mp I.property
    have hK : K.support.Nonempty := by
      have hk : K = L := by simp only [K, hI, finsetMultiIndex, Finset.sum_empty, add_zero]
      rw [hk]
      exact Finsupp.support_nonempty_iff.mpr hL
    rw [← hy]
    dsimp only [d]
    rw [dpSectorMap_differential, dpFormsHomotopy_sectorMap,
      exteriorWedgeLeft_contract_zero (sectorFunctional A W K) (sectorVector A W K)
        (sectorFunctional_vector A W K hK)]

private theorem augmentation_monomial (K : W →₀ ℕ) :
    dividedPowerPolynomialAugmentation A W (dividedPowerPolynomialMonomial A K) =
      if K = 0 then 1 else 0 := by
  classical
  by_cases hK : K = 0
  · simp [hK, dividedPowerPolynomialMonomial_zero]
  · rw [ite_eq_right hK]
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hK
    unfold dividedPowerPolynomialMonomial Finsupp.prod
    rw [map_prod]
    apply Finset.prod_eq_zero hi
    simp [dividedPowerPolynomialAugmentation, dividedPowersBot_dpow_eq,
      Finsupp.mem_support_iff.mp hi]

private theorem zeroEquiv_basis (K : W →₀ ℕ) (I : Set.powersetCard W 0) :
    exteriorPower.zeroEquiv (↑(dpRing A W))
      (dividedPowerDifferentials (A := A) (dpRing A W).dividedPowers)
      (dividedPowerDifferentialFormsABasis A W 0 (K, I)) =
      dividedPowerPolynomialMonomial A K := by
  rw [dividedPowerDifferentialFormsABasis_apply_monomial]
  exact zeroEquiv_smul_ιMulti (R := ↑(dpRing A W)) _ _

private def dpAugmentation : (↑(dpRing A W)) →ₗ[A] A where
  toFun := dividedPowerPolynomialAugmentation A W
  map_add' := (dividedPowerPolynomialAugmentation A W).map_add
  map_smul' a p := by
    change dividedPowerPolynomialAugmentation A W
      ((indexedDividedPowerPolynomialCoefficientMap A W) a * p) =
      a * dividedPowerPolynomialAugmentation A W p
    rw [map_mul]
    have hc : dividedPowerPolynomialAugmentation A W
        ((indexedDividedPowerPolynomialCoefficientMap A W) a) = a :=
      (dividedPowerPolynomialAugmentation A W).commutes a
    rw [hc]

private def dpAugmentationProjection : dpForms A W 0 →ₗ[A] dpForms A W 0 :=
  let e := exteriorPower.zeroEquiv (↑(dpRing A W))
    (dividedPowerDifferentials (A := A) (dpRing A W).dividedPowers)
  (e.symm.toLinearMap.restrictScalars A).comp
    ((Algebra.linearMap A (↑(dpRing A W))).comp
      ((dpAugmentation A W).comp
        (e.toLinearMap.restrictScalars A)))

private theorem augmentedProjection_eq (x : dpForms A W 0) :
    dpAugmentationProjection A W x =
      dpConstantProjection A W x := by
  suffices dpAugmentationProjection A W =
      dpConstantProjection A W from DFunLike.congr_fun this x
  apply (dividedPowerDifferentialFormsABasis A W 0).ext
  rintro ⟨K, I⟩
  rw [dpConstantProjection_basis]
  change (exteriorPower.zeroEquiv (↑(dpRing A W))
      (dividedPowerDifferentials (A := A) (dpRing A W).dividedPowers)).symm
      (algebraMap A (↑(dpRing A W))
        (dividedPowerPolynomialAugmentation A W
          (exteriorPower.zeroEquiv (↑(dpRing A W))
            (dividedPowerDifferentials (A := A) (dpRing A W).dividedPowers)
            (dividedPowerDifferentialFormsABasis A W 0 (K, I))))) = _
  rw [zeroEquiv_basis, augmentation_monomial]
  by_cases hK : K = 0
  · subst K
    simp only [ite_true, map_one]
    apply (exteriorPower.zeroEquiv (↑(dpRing A W))
      (dividedPowerDifferentials (A := A) (dpRing A W).dividedPowers)).injective
    rw [LinearEquiv.apply_symm_apply, zeroEquiv_basis, dividedPowerPolynomialMonomial_zero]
  · simp only [ite_eq_right hK, map_zero]

private def nativeContractionData (A P : Type*) [CommRing A] [CommRing P] [Algebra A P]
    {J : Ideal P} (δ : DividedPowers J) (ε : P → A) : Prop :=
  let F := fun n => dividedPowerDifferentialForms (A := A) δ n
  let d : (n : ℕ) → F n →ₗ[A] F (n + 1) := (dividedPowerDeRhamComplex (A := A) δ).differential
  let e := exteriorPower.zeroEquiv P (dividedPowerDifferentials (A := A) δ)
  let p : F 0 → F 0 := fun x => e.symm (algebraMap A P (ε (e x)))
  ∃ h : (n : ℕ) → F (n + 1) →ₗ[A] F n,
    (∀ n (x : F (n + 1)), d n (h n x) + h (n + 1) (d (n + 1) x) = x) ∧
    (∀ (x : F 0), p x + h 0 (d 0 x) = x)
private def restrictedContractionData (A P : Type*) [CommRing A] [CommRing P] [Algebra A P]
    {J : Ideal P} (δ : DividedPowers J) (ε : P → A) : Prop :=
  let F := fun n => RestrictScalars A P (dividedPowerDifferentialForms (A := A) δ n)
  let d : (n : ℕ) → F n →ₗ[A] F (n + 1) := (dividedPowerDeRhamComplex (A := A) δ).differential
  let e := exteriorPower.zeroEquiv P (dividedPowerDifferentials (A := A) δ)
  let p : F 0 → F 0 := fun x => e.symm (algebraMap A P (ε (e x)))
  ∃ h : (n : ℕ) → F (n + 1) →ₗ[A] F n,
    (∀ n (x : F (n + 1)), d n (h n x) + h (n + 1) (d (n + 1) x) = x) ∧
    (∀ (x : F 0), p x + h 0 (d 0 x) = x)
private theorem restrictContraction (A P : Type*) [CommRing A] [CommRing P] [Algebra A P]
    {J : Ideal P} (δ : DividedPowers J) (ε : P → A)
    (h : nativeContractionData A P δ ε) : restrictedContractionData A P δ ε :=
  h

private theorem nativePolynomialContraction :
    nativeContractionData A (↑(dpRing A W)) (dpRing A W).dividedPowers
    (dividedPowerPolynomialAugmentation A W) := by
  refine ⟨dpFormsHomotopy A W, dpFormsHomotopy_identity A W, ?_⟩
  intro x
  change dpAugmentationProjection A W x + dpFormsHomotopy A W 0 (dpD A W 0 x) = x
  rw [augmentedProjection_eq]
  exact dpFormsHomotopy_zero A W x

private def dividedPowerContractionData
    (inst : Algebra A (setIndexedDividedPowerPolynomialAlgebra A W)) : Prop :=
  @restrictedContractionData A (setIndexedDividedPowerPolynomialAlgebra A W) _ _ inst _
    (polynomialDividedPowers A W) (dividedPowerPolynomialAugmentation A W)

private theorem dividedPowerContractionData_custom : dividedPowerContractionData A W
    (indexedDividedPowerPolynomialCoefficientMap A W).toAlgebra := by
  have h := restrictContraction A (↑(dpRing A W)) (dpRing A W).dividedPowers
    (dividedPowerPolynomialAugmentation A W) (nativePolynomialContraction A W)
  dsimp +instances only [dividedPowerContractionData, dpRing,
    setIndexedDividedPowerPolynomialDividedPowerRing,
    polynomialDividedPowers, coefficientDividedPowerRing,
    setIndexedDividedPowerPolynomialDividedPowerRingAlgebra] at h ⊢
  exact h

private theorem dividedPowerContractionData_standard :
    dividedPowerContractionData A W inferInstance := by
  have hAlg : (indexedDividedPowerPolynomialCoefficientMap A W).toAlgebra =
      (inferInstance : Algebra A (setIndexedDividedPowerPolynomialAlgebra A W)) := by
    apply Algebra.algebra_ext
    intro a
    rfl
  exact (congrArg (dividedPowerContractionData A W) hAlg).mp
    (dividedPowerContractionData_custom A W)

private theorem cochain_contractible_of_homotopies
    {V : Type*} [Category V] [Preadditive V] (C : CochainComplex V ℕ)
    (h : ∀ n, C.X (n + 1) ⟶ C.X n)
    (h0 : C.d 0 1 ≫ h 0 = 𝟙 (C.X 0))
    (hs : ∀ n, h n ≫ C.d n (n + 1) + C.d (n + 1) (n + 2) ≫ h (n + 1) =
      𝟙 (C.X (n + 1))) : Nonempty (Homotopy (𝟙 C) 0) := by
  let hh : ∀ i j, (ComplexShape.up ℕ).Rel j i → (C.X i ⟶ C.X j) :=
    fun i j hij => eqToHom (congrArg C.X hij.symm) ≫ h j
  have he : Homotopy.nullHomotopicMap' hh = 𝟙 C := by
    ext i
    cases i with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₀ := 1) rfl
        (fun l hl => Nat.noConfusion hl)]
      simpa only [hh, eqToHom_refl, Category.id_comp, HomologicalComplex.id_f] using h0
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f (k₂ := n) (k₀ := n + 2) rfl rfl]
      simpa only [hh, eqToHom_refl, Category.id_comp, HomologicalComplex.id_f, add_comm] using hs n
  exact ⟨(Homotopy.ofEq he.symm).trans (Homotopy.nullHomotopy' hh)⟩


private theorem augmentedComplex_d (n : ℕ) :
    (augmentedDividedPowerDeRhamComplex A W).d n (n + 1) =
      augmentedDividedPowerDeRhamDifferential A W n :=
  CochainComplex.of_d _ _ n

private theorem augmentedComplex_contractible :
    Nonempty (Homotopy (𝟙 (augmentedDividedPowerDeRhamComplex A W)) 0) := by
  obtain ⟨h, hpos, hzero⟩ := dividedPowerContractionData_standard A W
  let C := augmentedDividedPowerDeRhamComplex A W
  let H : ∀ n, C.X (n + 1) ⟶ C.X n
    | 0 => augmentedContractionOne A W
    | n + 1 => ModuleCat.ofHom (h n)
  apply cochain_contractible_of_homotopies C H
  · rw [augmentedComplex_d]
    exact augmentedContractionOne_leftInverse A W
  · intro n
    rw [augmentedComplex_d, augmentedComplex_d]
    cases n with
    | zero =>
      ext x
      exact hzero x
    | succ n =>
      ext x
      exact hpos n x

end

/-- The augmented divided power de Rham complex
`0 → A → P → Ω¹_{P/A,δ} → Ω²_{P/A,δ} → ⋯` of a divided power polynomial algebra
`P = A⟨x_w : w ∈ W⟩` is homotopy equivalent to zero as a complex of `A`-modules. -/
public alias augmentedDividedPowerDeRhamComplex_contractible := augmentedComplex_contractible

end OrdinaryExactness

end Crystalline

end
