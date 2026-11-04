module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow.GaloisDegree
import all StacksFrontier.NumberTheory.Cyclotomic.OneAddPow.GaloisDegree

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Polynomial

section CyclotomicQuotientRamification

open scoped IntermediateField

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uK uL

private theorem scaled_monic_reduction
    (A : Type*) [CommRing A] [IsLocalRing A]
    (P : Polynomial A) (hP : P.Monic) (π : A)
    (hπ : IsLocalRing.residue A π = 0) (k : ℕ) (hk : 0 < k) :
    (P.scaleRoots (π ^ k)).map (IsLocalRing.residue A) =
      (Polynomial.X : Polynomial (IsLocalRing.ResidueField A)) ^ P.natDegree := by
  have hlead : IsLocalRing.residue A P.leadingCoeff ≠ 0 := by simp [hP.leadingCoeff]
  rw [Polynomial.map_scaleRoots P (π ^ k) (IsLocalRing.residue A) hlead]
  have hp0 : IsLocalRing.residue A (π ^ k) = 0 := by
    rw [map_pow, hπ, zero_pow hk.ne']
  rw [hp0, Polynomial.scaleRoots_zero]
  have hm := hP.map (IsLocalRing.residue A)
  rw [hm.leadingCoeff, one_smul]
  congr 1
  exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead

private theorem minpoly_eq_of_irreducible_reduction
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (Q : Polynomial A) (hQm : Q.Monic)
    (hred : Irreducible (Q.map (IsLocalRing.residue A)))
    (y : L) (hy : Polynomial.aeval y Q = 0) : minpoly A y = Q := by
  have hint : IsIntegral A y := ⟨Q, hQm, hy⟩
  have hQi : Irreducible (Q.map (algebraMap A K)) :=
    hQm.irreducible_iff_irreducible_map_fraction_map.mp
      (Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue A) Q hQm hred)
  have hyK : Polynomial.aeval y (Q.map (algebraMap A K)) = 0 := by
    rwa [Polynomial.aeval_map_algebraMap]
  have hK : Q.map (algebraMap A K) = minpoly K y :=
    minpoly.eq_of_irreducible_of_monic hQi hyK (hQm.map (algebraMap A K))
  have hminmap : (minpoly A y).map (algebraMap A K) = minpoly K y := by
    have h := minpoly.isIntegrallyClosed_eq_field_fractions
      (R := A) (S := L) K L (s := y) hint
    simpa using h.symm
  apply Polynomial.map_injective _ (IsFractionRing.injective A K)
  rw [hminmap, hK]

/-- The structure map `A → L` is injective when `L` is a field extension of a fraction field of
`A`. -/
private theorem algebraMap_injective_of_tower
    (A K L : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    Function.Injective (algebraMap A L) := by
  rw [IsScalarTower.algebraMap_eq A K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)

/-- The generator of `Algebra.adjoin.powerBasis'` has the same minimal polynomial as `y`. -/
private theorem minpoly_adjoin_powerBasis_gen
    {A L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Module.IsTorsionFree A L] {y : L} (hint : IsIntegral A y) {Q : Polynomial A}
    (hmin : minpoly A y = Q) :
    minpoly A (Algebra.adjoin.powerBasis' hint).gen = Q := by
  have hval : algebraMap (Algebra.adjoin A {y}) L (Algebra.adjoin.powerBasis' hint).gen = y := by
    rw [Algebra.adjoin.powerBasis'_gen]
    rfl
  rw [← minpoly.algebraMap_eq (Subtype.val_injective (p := (· ∈ Algebra.adjoin A {y})))
    (Algebra.adjoin.powerBasis' hint).gen, hval, hmin]

private theorem adjoin_closed_fibre_isField
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (Q : Polynomial A)
    (hred : Irreducible (Q.map (IsLocalRing.residue A)))
    (y : L) (hint : IsIntegral A y) (hmin : minpoly A y = Q) :
    IsField (↥(Algebra.adjoin A {y}) ⧸
      Ideal.map (algebraMap A ↥(Algebra.adjoin A {y}))
        (IsLocalRing.maximalIdeal A)) := by
  have htors : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_injective_of_tower A K L)
  let S := Algebra.adjoin A {y}
  let pb : PowerBasis A ↥S := Algebra.adjoin.powerBasis' hint
  have hgenmin := minpoly_adjoin_powerBasis_gen hint hmin
  have hquot := pb.quotientEquivQuotientMinpolyMap (IsLocalRing.maximalIdeal A)
  rw [hgenmin] at hquot
  have hmax : (Ideal.span {Q.map (IsLocalRing.residue A)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hred
  have hfield : IsField
      (Polynomial (IsLocalRing.ResidueField A) ⧸
        Ideal.span {Q.map (IsLocalRing.residue A)}) :=
    (Ideal.Quotient.field _).toIsField
  exact MulEquiv.isField hfield hquot.toRingEquiv.toMulEquiv

private theorem adjoin_isDVR_of_closed_fibre_field
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (y : L) (hint : IsIntegral A y)
    (hfield : IsField (↥(Algebra.adjoin A {y}) ⧸
      Ideal.map (algebraMap A ↥(Algebra.adjoin A {y}))
        (IsLocalRing.maximalIdeal A))) :
    IsDiscreteValuationRing ↥(Algebra.adjoin A {y}) := by
  let S := Algebra.adjoin A {y}
  let J : Ideal ↥S := Ideal.map (algebraMap A ↥S) (IsLocalRing.maximalIdeal A)
  have hfin : Module.Finite A ↥S := Algebra.finite_adjoin_simple_of_isIntegral hint
  have hintS : Algebra.IsIntegral A ↥S := Algebra.IsIntegral.of_finite A ↥S
  have hJmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  have hlocal : IsLocalRing ↥S := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨J, hJmax, ?_⟩
    intro M hM
    have hcomap : (Ideal.comap (algebraMap A ↥S) M).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hcm : Ideal.comap (algebraMap A ↥S) M = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal hcomap
    have hle : J ≤ M := by
      show Ideal.map (algebraMap A ↥S) (IsLocalRing.maximalIdeal A) ≤ M
      rw [← hcm]
      exact Ideal.map_comap_le
    exact (hJmax.eq_of_le hM.ne_top hle).symm
  have hnoeth : IsNoetherianRing ↥S := IsNoetherianRing.of_finite A ↥S
  have hJeq : IsLocalRing.maximalIdeal ↥S = J :=
    (IsLocalRing.eq_maximalIdeal hJmax).symm
  obtain ⟨π, hπ⟩ := IsPrincipalIdealRing.principal (R := A)
    (IsLocalRing.maximalIdeal A)
  have hJprinc : Submodule.IsPrincipal (IsLocalRing.maximalIdeal ↥S) := by
    rw [hJeq]
    show Submodule.IsPrincipal
      (Ideal.map (algebraMap A ↥S) (IsLocalRing.maximalIdeal A))
    rw [hπ, Ideal.map_span]
    exact ⟨⟨algebraMap A ↥S π, by rw [Set.image_singleton]⟩⟩
  have hinj : Function.Injective (algebraMap A ↥S) := by
    have hcomp : (Subtype.val : ↥S → L) ∘ (algebraMap A ↥S) = algebraMap A L := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one]
    apply Function.Injective.of_comp
    rw [hcomp]
    exact algebraMap_injective_of_tower A K L
  have hnotfield : ¬IsField ↥S := fun hS =>
    IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj hS)
  exact ((IsDiscreteValuationRing.TFAE ↥S hnotfield).out 5 1).mp hJprinc

private theorem adjoin_isFractionRing
    (A K L : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (y : L) (hint : IsIntegral A y)
    (hgen : Algebra.adjoin K {y} = ⊤) :
    IsFractionRing ↥(Algebra.adjoin A {y}) L := by
  let S := Algebra.adjoin A {y}
  obtain ⟨Q, hQm, hy⟩ := hint
  have hyK : IsIntegral K y := by
    refine ⟨Q.map (algebraMap A K), hQm.map _, ?_⟩
    show Polynomial.aeval y (Q.map (algebraMap A K)) = 0
    rwa [Polynomial.aeval_map_algebraMap]
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop' hyK hgen
  have hpbgen : pb.gen = y := PowerBasis.ofAdjoinEqTop'_gen hyK hgen
  have hbmem : ∀ i : Fin pb.dim, pb.basis i ∈ S := by
    intro i
    rw [pb.basis_eq_pow, hpbgen]
    exact pow_mem (Algebra.self_mem_adjoin_singleton A _) i
  apply IsFractionRing.of_field
  intro z
  let c := pb.basis.repr z
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A)
    (Finset.univ : Finset (Fin pb.dim)) (fun i => c i)
  have hdz : (algebraMap A L (d : A)) * z ∈ S := by
    rw [← Algebra.smul_def]
    have hzsum : z = ∑ i, c i • pb.basis i := (pb.basis.sum_repr z).symm
    rw [hzsum, Finset.smul_sum]
    apply Subalgebra.sum_mem
    intro i _
    obtain ⟨aᵢ, haᵢ⟩ := hd i (Finset.mem_univ i)
    have hstep : (d : A) • c i • pb.basis i = aᵢ • pb.basis i := by
      rw [← smul_assoc, ← haᵢ, IsScalarTower.algebraMap_smul]
    rw [hstep]
    exact Subalgebra.smul_mem _ (hbmem i) aᵢ
  refine ⟨⟨_, hdz⟩, algebraMap A ↥S (d : A), ?_⟩
  have hd0 : algebraMap A L (d : A) ≠ 0 := by
    rw [← map_zero (algebraMap A L)]
    exact (algebraMap_injective_of_tower A K L).ne (nonZeroDivisors.coe_ne_zero d)
  show z = (algebraMap A L (d : A) * z) /
    (algebraMap A L (d : A))
  rw [mul_comm, mul_div_assoc, div_self hd0, mul_one]

private theorem integralClosure_eq_adjoin
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (y : L) (hint : IsIntegral A y)
    (hgen : Algebra.adjoin K {y} = ⊤)
    (hdvr : IsDiscreteValuationRing ↥(Algebra.adjoin A {y})) :
    integralClosure A L = Algebra.adjoin A {y} := by
  let S := Algebra.adjoin A {y}
  let : IsDiscreteValuationRing ↥S := hdvr
  let : IsFractionRing ↥S L := adjoin_isFractionRing A K L y hint hgen
  apply le_antisymm
  · intro x hx
    rw [mem_integralClosure_iff] at hx
    have hxS : IsIntegral ↥S x := hx.tower_top
    obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxS
    rw [← hs]
    exact s.2
  · exact adjoin_le_integralClosure hint

private theorem adjoin_smul_eq_top
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (c : K) (hc : c ≠ 0) (z : L)
    (hgen : Algebra.adjoin K {z} = ⊤) :
    Algebra.adjoin K {(algebraMap K L c) * z} = ⊤ := by
  let S := Algebra.adjoin K {(algebraMap K L c) * z}
  have hy : (algebraMap K L c) * z ∈ S :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have hcS : algebraMap K L c⁻¹ ∈ S := S.algebraMap_mem _
  have hz : z ∈ S := by
    have hcL : algebraMap K L c ≠ 0 := by
      simpa using (algebraMap K L).injective.ne hc
    have heq : z = algebraMap K L c⁻¹ * ((algebraMap K L c) * z) := by
      rw [map_inv₀, ← mul_assoc, inv_mul_cancel₀ hcL,
        one_mul]
    rw [heq]
    exact S.mul_mem hcS hy
  have hle : Algebra.adjoin K {z} ≤ S := Algebra.adjoin_le (by simpa using hz)
  rw [hgen] at hle
  exact le_antisymm le_top hle

private theorem integralClosure_eq_adjoin_of_irreducible_reduction
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (Q : Polynomial A) (hQm : Q.Monic)
    (hred : Irreducible (Q.map (IsLocalRing.residue A)))
    (y : L) (hy : Polynomial.aeval y Q = 0)
    (hgen : Algebra.adjoin K {y} = ⊤) :
    ∃ _hdvr : IsDiscreteValuationRing ↥(Algebra.adjoin A {y}),
      integralClosure A L = Algebra.adjoin A {y} := by
  have hint : IsIntegral A y := ⟨Q, hQm, hy⟩
  have hmin : minpoly A y = Q :=
    minpoly_eq_of_irreducible_reduction A K L Q hQm hred y hy
  have hfield := adjoin_closed_fibre_isField A K L Q hred y hint hmin
  have hdvr := adjoin_isDVR_of_closed_fibre_field A K L y hint hfield
  exact ⟨hdvr, integralClosure_eq_adjoin A K L y hint hgen hdvr⟩

private theorem adjoin_uniformizer_of_closed_fibre_field
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type*) [Field L] [Algebra A L]
    (y : L) (hdvr : IsDiscreteValuationRing ↥(Algebra.adjoin A {y}))
    (hfield : IsField (↥(Algebra.adjoin A {y}) ⧸
      Ideal.map (algebraMap A ↥(Algebra.adjoin A {y}))
        (IsLocalRing.maximalIdeal A)))
    (π : A) (hπ : Irreducible π) :
    Irreducible (algebraMap A ↥(Algebra.adjoin A {y}) π) := by
  let S := Algebra.adjoin A {y}
  let : IsDiscreteValuationRing ↥S := hdvr
  let J : Ideal ↥S := Ideal.map (algebraMap A ↥S) (IsLocalRing.maximalIdeal A)
  have hJmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  have hJeq : IsLocalRing.maximalIdeal ↥S = J :=
    (IsLocalRing.eq_maximalIdeal hJmax).symm
  have hπspan : IsLocalRing.maximalIdeal A = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  rw [hJeq]
  show Ideal.map (algebraMap A ↥S) (IsLocalRing.maximalIdeal A) =
    Ideal.span {algebraMap A ↥S π}
  rw [hπspan, Ideal.map_span, Set.image_singleton]

private theorem ramificationIdx_eq_one_of_uniformizer
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B]
    (π : A) (hπ : Irreducible π)
    (hπB : Irreducible (algebraMap A B π)) :
    Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) = 1 := by
  have hπspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hπBspan :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (algebraMap A B π)).mp hπB
  have hmap : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B := by
    rw [hπspan, Ideal.map_span, Set.image_singleton, ← hπBspan]
  have htop : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap]
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hbot : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [hmap, hπBspan]
    intro h
    exact hπB.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  rw [← hmap]
  exact Ideal.ramificationIdx'_map_self_eq_one htop hbot

private theorem adjoin_closed_fibre_finrank
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (y : L) (hint : IsIntegral A y) :
    Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
      (↥(Algebra.adjoin A {y}) ⧸
        Ideal.map (algebraMap A ↥(Algebra.adjoin A {y}))
          (IsLocalRing.maximalIdeal A)) = (minpoly A y).natDegree := by
  have htors : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_injective_of_tower A K L)
  let S := Algebra.adjoin A {y}
  let pb : PowerBasis A ↥S := Algebra.adjoin.powerBasis' hint
  let : Module.Finite A ↥S := pb.finite
  let : Module.Free A ↥S := Module.Free.of_basis pb.basis
  rw [IsLocalRing.finrank_quotient_map, pb.finrank]
  exact Algebra.adjoin.powerBasis'_dim hint

private theorem purelyInseparable_of_adjoin_root_pow
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (x : E) (a : F) (hx : x ^ p = algebraMap F E a)
    (hgen : Algebra.adjoin F {x} = ⊤) : IsPurelyInseparable F E := by
  have hint : IsIntegral F x := by
    refine ⟨Polynomial.X ^ p - Polynomial.C a,
      Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).pos.ne', ?_⟩
    simp [hx]
  have htop : F⟮x⟯ = (⊤ : IntermediateField F E) :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hint.isAlgebraic).mpr hgen
  have hroot : x ^ p ∈ (algebraMap F E).range := ⟨a, hx.symm⟩
  have hpure : IsPurelyInseparable F ↥F⟮x⟯ :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E p).mpr
      ⟨1, by simpa using hroot⟩
  rw [htop] at hpure
  exact (IntermediateField.topEquiv : ↥(⊤ : IntermediateField F E) ≃ₐ[F] E).isPurelyInseparable

private theorem purelyInseparable_binomial_quotient
    (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : F) (ha : ¬∃ b : F, a = b ^ p) :
    IsPurelyInseparable F
      (Polynomial F ⧸ Ideal.span {Polynomial.X ^ p - Polynomial.C a}) := by
  let f : Polynomial F := Polynomial.X ^ p - Polynomial.C a
  have hirr : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) fun b hb => ha ⟨b, hb.symm⟩
  let : Fact (Irreducible f) := ⟨hirr⟩
  let x : AdjoinRoot f := AdjoinRoot.root f
  have hx : x ^ p = algebraMap F (AdjoinRoot f) a := by
    have hroot : Polynomial.aeval x f = 0 := by
      show Polynomial.aeval (AdjoinRoot.root f) f = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    exact sub_eq_zero.mp (by simpa [f, x] using hroot)
  have hgen : Algebra.adjoin F {x} = ⊤ := by
    have := (AdjoinRoot.powerBasis hirr.ne_zero).adjoin_gen_eq_top
    rwa [AdjoinRoot.powerBasis_gen] at this
  exact purelyInseparable_of_adjoin_root_pow F (AdjoinRoot f) p x a hx hgen

private theorem residue_extension_of_irreducible_reduction
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (Q : Polynomial A) (hQm : Q.Monic) (hQd : Q.natDegree = p)
    (a : A) (ha : ¬∃ b : IsLocalRing.ResidueField A,
      IsLocalRing.residue A a = b ^ p)
    (hred : Q.map (IsLocalRing.residue A) =
      Polynomial.X ^ p - Polynomial.C (IsLocalRing.residue A a))
    (y : L) (hy : Polynomial.aeval y Q = 0)
    (hgen : Algebra.adjoin K {y} = ⊤) (π : A) (hπ : Irreducible π) :
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A L),
      letI := hDVR
      let mB := IsLocalRing.maximalIdeal (integralClosure A L)
      ∃ _ : mB.LiesOver (IsLocalRing.maximalIdeal A),
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) mB = 1 ∧
          letI := Ideal.Quotient.algebraOfLiesOver mB (IsLocalRing.maximalIdeal A)
          IsPurelyInseparable (A ⧸ IsLocalRing.maximalIdeal A) ((integralClosure A L) ⧸ mB) ∧
            Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) ((integralClosure A L) ⧸ mB) = p := by
  have hirr : Irreducible (Q.map (IsLocalRing.residue A)) := by
    rw [hred]
    exact X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) fun b hb => ha ⟨b, hb.symm⟩
  obtain ⟨hdvr, hclosure⟩ :=
    integralClosure_eq_adjoin_of_irreducible_reduction A K L Q hQm hirr y hy hgen
  let result : Subalgebra A L → Prop := fun S =>
    ∃ hDVR : IsDiscreteValuationRing ↥S,
      let := hDVR
      let mB := IsLocalRing.maximalIdeal ↥S
      ∃ _ : mB.LiesOver (IsLocalRing.maximalIdeal A),
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) mB = 1 ∧
          let := Ideal.Quotient.algebraOfLiesOver mB (IsLocalRing.maximalIdeal A)
          IsPurelyInseparable (A ⧸ IsLocalRing.maximalIdeal A) (↥S ⧸ mB) ∧
            Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (↥S ⧸ mB) = p
  show result (integralClosure A L)
  rw [hclosure]
  dsimp only [result]
  let S := Algebra.adjoin A {y}
  let : IsDiscreteValuationRing ↥S := hdvr
  have hint : IsIntegral A y := ⟨Q, hQm, hy⟩
  let : Module.Finite A ↥S := Algebra.finite_adjoin_simple_of_isIntegral hint
  have hmin := minpoly_eq_of_irreducible_reduction A K L Q hQm hirr y hy
  have hfield := adjoin_closed_fibre_isField A K L Q hirr y hint hmin
  let mS := IsLocalRing.maximalIdeal ↥S
  let J := Ideal.map (algebraMap A ↥S) (IsLocalRing.maximalIdeal A)
  have hJ : J = mS := IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _ hfield)
  have hcomax : (mS.comap (algebraMap A ↥S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal mS
  let : mS.LiesOver (IsLocalRing.maximalIdeal A) := ⟨(IsLocalRing.eq_maximalIdeal hcomax).symm⟩
  refine ⟨hdvr, inferInstance, ?_, ?_⟩
  · exact ramificationIdx_eq_one_of_uniformizer A ↥S π hπ
      (adjoin_uniformizer_of_closed_fibre_field A L y hdvr hfield π hπ)
  let e : (↥S ⧸ J) ≃ₐ[A ⧸ (IsLocalRing.maximalIdeal A)] (↥S ⧸ mS) :=
    { __ := Ideal.quotEquivOfEq hJ
      commutes' := by
        rintro ⟨x⟩
        rfl }
  have htors : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_injective_of_tower A K L)
  let pb : PowerBasis A ↥S := Algebra.adjoin.powerBasis' hint
  have hgenmin := minpoly_adjoin_powerBasis_gen hint hmin
  let : CharP (A ⧸ IsLocalRing.maximalIdeal A) p :=
    inferInstanceAs (CharP (IsLocalRing.ResidueField A) p)
  have epb := pb.quotientEquivQuotientMinpolyMap (IsLocalRing.maximalIdeal A)
  rw [hgenmin, show Q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) =
    Polynomial.X ^ p - Polynomial.C (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)
      from hred] at epb
  let : IsPurelyInseparable (A ⧸ IsLocalRing.maximalIdeal A)
      (Polynomial (A ⧸ IsLocalRing.maximalIdeal A) ⧸
        Ideal.span {Polynomial.X ^ p -
          Polynomial.C (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)}) :=
    purelyInseparable_binomial_quotient (A ⧸ IsLocalRing.maximalIdeal A) p _ ha
  let epb' : (↥S ⧸ J) ≃ₐ[A ⧸ (IsLocalRing.maximalIdeal A)]
      (Polynomial (A ⧸ IsLocalRing.maximalIdeal A) ⧸
        Ideal.span {Polynomial.X ^ p -
          Polynomial.C (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a)}) :=
    { __ := epb.toRingEquiv
      commutes' := by
        rintro ⟨x⟩
        exact epb.commutes x }
  have hpure : IsPurelyInseparable (A ⧸ IsLocalRing.maximalIdeal A) (↥S ⧸ J) :=
    epb'.symm.isPurelyInseparable
  refine ⟨e.isPurelyInseparable, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq]
  exact (adjoin_closed_fibre_finrank A K L y hint).trans (by rw [hmin, hQd])

/-- A polynomial satisfying `intProp` has degree `p`. -/
private theorem natDegree_eq_of_intProp
    {A : Type*} [CommRing A] [Nontrivial A] (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A) (hP : intProp f P) :
    P.natDegree = p := by
  have hcp : P.coeff p = 1 := by simpa using hP.2.2.2 p (Fact.out : p.Prime).pos le_rfl
  exact le_antisymm hP.2.1 (Polynomial.le_natDegree_of_ne_zero (by simp [hcp]))

/-- Subtracting a constant from a monic polynomial of positive degree keeps it monic. -/
private theorem monic_sub_C_of_natDegree_pos
    {A : Type*} [CommRing A] {g : Polynomial A} (hg : g.Monic) (hd : 0 < g.natDegree) (a : A) :
    (g - Polynomial.C a).Monic :=
  hg.sub_of_left
    (lt_of_le_of_lt Polynomial.degree_C_le (Polynomial.natDegree_pos_iff_degree_pos.mp hd))

private theorem scaled_root_polynomial
    (A K L : Type*) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (hP : intProp f P) (ξ : K) (z : L)
    (hz : Polynomial.aeval z P = algebraMap K L ξ)
    (π a : A) (hπ : π ≠ 0) (k : ℕ)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ (k * p) * algebraMap A K a) :
    (P.scaleRoots (π ^ k) - Polynomial.C a).Monic ∧
      (P.scaleRoots (π ^ k) - Polynomial.C a).natDegree = p ∧
      Polynomial.aeval ((algebraMap A L π) ^ k * z)
        (P.scaleRoots (π ^ k) - Polynomial.C a) = 0 := by
  let Q : Polynomial A := P.scaleRoots (π ^ k) - Polynomial.C a
  have hPm : P.Monic := monic_cyclotomic_quotient f P hP
  have hsm : (P.scaleRoots (π ^ k)).Monic := by
    simpa only [Polynomial.Monic, Polynomial.leadingCoeff_scaleRoots] using hPm
  have hPd : P.natDegree = p := natDegree_eq_of_intProp p f P hP
  have hQm : Q.Monic := monic_sub_C_of_natDegree_pos hsm
    (by rw [Polynomial.natDegree_scaleRoots, hPd]; exact (Fact.out : p.Prime).pos) a
  have hπK : algebraMap A K π ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hπ
  have hπL : algebraMap A L π ≠ 0 := by
    simpa using (algebraMap_injective_of_tower A K L).ne hπ
  have hroot : Polynomial.aeval ((algebraMap A L π) ^ k * z) Q = 0 := by
    dsimp [Q]
    rw [map_sub, Polynomial.aeval_C]
    have hscale := Polynomial.scaleRoots_aeval_smul (r := z) (s := π ^ k) (p := P)
    simp only [Algebra.smul_def, map_pow] at hscale
    rw [hscale, hz, hξ, hPd]
    simp only [map_mul, map_pow, map_inv₀]
    rw [← IsScalarTower.algebraMap_apply A K L π, ← IsScalarTower.algebraMap_apply A K L a,
      ← pow_mul, ← mul_assoc, ← mul_pow]
    simp [hπL]
  exact ⟨hQm,
    by simp only [Polynomial.natDegree_sub_C, Polynomial.natDegree_scaleRoots, hPd], hroot⟩

/-- Let `A` be a mixed-characteristic discrete valuation ring containing a primitive
`p`-th root of unity, and let `P` be the cyclotomic quotient polynomial of Tag 09F2.
If `L = K[z]` with `P(z) = ξ`, then `L / K` is Galois and is either trivial,
unramified of degree `p`, totally ramified with ramification index `p`, or weakly
unramified with purely inseparable residue extension of degree `p`.

Moreover, for a uniformizer `π` of `A`, an integral `ξ` gives one of the first two
cases; a pole of positive order not divisible by `p` gives the totally ramified case;
and a pole whose order is divisible by `p` and whose leading coefficient is not a
`p`-th power in the residue field gives the weakly unramified, residually inseparable
case. -/
@[stacks 09F3]
theorem isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (ξ : K) (z : L)
    (hz : Polynomial.aeval z P = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (π : A) (hπ : Irreducible π) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      let residuallyInseparable : Prop :=
        ∃ hDVR : IsDiscreteValuationRing B,
          letI := hDVR
          let mB := IsLocalRing.maximalIdeal B
          ∃ _ : mB.LiesOver mA,
            Ideal.ramificationIdx' mA mB = 1 ∧
              letI := Ideal.Quotient.algebraOfLiesOver mB mA
              IsPurelyInseparable (A ⧸ mA) (B ⧸ mB) ∧
                Module.finrank (A ⧸ mA) (B ⧸ mB) = p
      IsGalois K L ∧
        (trivial ∨ unramified ∨ totallyRamified ∨ residuallyInseparable) ∧
        ((∃ a : A, ξ = algebraMap A K a) → trivial ∨ unramified) ∧
        (∀ (n : ℕ) (a : A), 0 < n → ¬p ∣ n → IsUnit a →
          ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a → totallyRamified) ∧
        (∀ (n : ℕ) (a : A), 0 < n → p ∣ n →
          (¬∃ b : IsLocalRing.ResidueField A, IsLocalRing.residue A a = b ^ p) →
          ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a →
            residuallyInseparable)  := by
  obtain ⟨hfin, hgal, hdegree⟩ :=
    cyclotomic_galois_and_degree A K L p f P hP.1 ξ z hz hgen
  refine ⟨hfin, ?_⟩
  have hcases := IsDiscreteValuationRing.ramification_cases_of_isGalois_of_finrank_dvd_prime
    A K L p (Fact.out : p.Prime) hdegree
  refine ⟨hgal, hcases, ?_, ?_, ?_⟩
  · rintro ⟨a, rfl⟩
    have hroot : Polynomial.aeval z (P - Polynomial.C a) = 0 := by
      rw [map_sub, Polynomial.aeval_C, hz, ← IsScalarTower.algebraMap_apply, sub_self]
    have hmon : (P - Polynomial.C a).Monic :=
      monic_sub_C_of_natDegree_pos (monic_cyclotomic_quotient f P hP.1)
        (by rw [natDegree_eq_of_intProp p f P hP.1]; exact (Fact.out : p.Prime).pos) a
    have hsep : ((P - Polynomial.C a).map (IsLocalRing.residue A)).Separable := by
      rw [Polynomial.map_sub, Polynomial.map_C, map_residue_cyclotomic_quotient A K p f P hP.2.2.1]
      have heq : (Polynomial.X ^ p - Polynomial.X - Polynomial.C (IsLocalRing.residue A a)) =
          Polynomial.C (1 : IsLocalRing.ResidueField A) * Polynomial.X ^ p +
            Polynomial.C (-1) * Polynomial.X + Polynomial.C (-IsLocalRing.residue A a) := by
        simp only [Polynomial.C_1, one_mul, Polynomial.C_neg]
        ring
      rw [heq]
      exact Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C' p p 1 (-1) _
        (dvd_refl p) isUnit_neg_one
    exact unramified_or_trivial_of_separable_reduction A K L p (Fact.out : p.Prime)
      _ hmon hsep z hroot hgen hdegree
  · intro n a hn hnp ha hξ
    exact IsDiscreteValuationRing.totally_ramified_of_coprime_pole A K L p n
      (Fact.out : p.Prime) hn hnp hdegree π a hπ ha P (monic_cyclotomic_quotient f P hP.1)
      (natDegree_eq_of_intProp p f P hP.1) ξ z hz hξ
  · intro n a hn hnp ha hξ
    obtain ⟨k, rfl⟩ := hnp
    have hk : 0 < k := Nat.pos_of_mul_pos_left hn
    have hξ' : ξ = (algebraMap A K π)⁻¹ ^ (k * p) * algebraMap A K a := by
      simpa only [Nat.mul_comm] using hξ
    obtain ⟨hQm, hQd, hroot⟩ :=
      scaled_root_polynomial A K L p f P hP.1 ξ z hz π a hπ.ne_zero k hξ'
    have hπ0 : IsLocalRing.residue A π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    have hPd : P.natDegree = p := natDegree_eq_of_intProp p f P hP.1
    have hred : (P.scaleRoots (π ^ k) - Polynomial.C a).map (IsLocalRing.residue A) =
        Polynomial.X ^ p - Polynomial.C (IsLocalRing.residue A a) := by
      rw [Polynomial.map_sub, Polynomial.map_C,
        scaled_monic_reduction A P (monic_cyclotomic_quotient f P hP.1) π hπ0 k hk, hPd]
    have hπK : algebraMap A K π ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
    have hgen' : Algebra.adjoin K {(algebraMap A L π) ^ k * z} = ⊤ := by
      simpa only [map_pow, ← IsScalarTower.algebraMap_apply] using
        adjoin_smul_eq_top K L ((algebraMap A K π) ^ k) (pow_ne_zero _ hπK) z hgen
    exact residue_extension_of_irreducible_reduction A K L p _ hQm hQd a ha
      hred _ hroot hgen' π hπ

end CyclotomicQuotientRamification
