module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.GoingDown
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation
public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleBaseChange
public import StacksFrontier.RingTheory.Flat.NonZeroDivisors

/-!
# Flat base change of a tame symbol preparation

Let `(A, 𝔪) → (A', 𝔪')` be a flat local homomorphism of Noetherian local rings with
`dim(A) = dim(A') = 1`.

* The closed fibre `A' / 𝔪A'` has dimension zero (dimension formula for a flat local
  homomorphism), hence finite length, and `𝔪'^k ⊆ 𝔪A'` for some `k`.
* If `A ⊆ B` is a finite extension with `B / A` annihilated by a power of `𝔪` and with local
  factorizations `a_i = u_{i,j} π_j ^ {e_{i,j}}` at the maximal ideals of `B` (the data of
  Stacks 0EAG), then `A' ⊆ B' = A' ⊗_A B` is again such an extension: it is finite, injective by
  flatness, `B' / A'` is annihilated by a power of `𝔪'`, and at a maximal ideal `𝔪'` of `B'`
  lying over `𝔪_j` the images of the factorizations in `B_j` are factorizations in `B'_{𝔪'}`.
  The images of the parameters remain nonzerodivisors because `B_j → B'_{𝔪'}` is flat.

## Main definitions

* `AlgebraicGeometry.TameSymbolPreparation.underIdeal` — the ideal of `B` under an ideal of
  `A' ⊗_A B`.
* `AlgebraicGeometry.TameSymbolPreparation.localMap` — the local homomorphism
  `B_{𝔮 ∩ B} → (A' ⊗_A B)_𝔮`.
* `AlgebraicGeometry.TameSymbolPreparation.baseChange` — the base change of a preparation.

## Main results

* `Stacks.Chow.ringKrullDim_closedFibre_eq_zero`, `Stacks.Chow.isFiniteLength_closedFibre`,
  `Stacks.Chow.exists_maximalIdeal_pow_le_closedFibre` — the closed fibre.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w

namespace Stacks.Chow

section ClosedFibre

variable {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [IsNoetherianRing A]
  [IsNoetherianRing A'] [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']
  [IsLocalHom (algebraMap A A')]

/-- The closed fibre `S / 𝔪S` of a local homomorphism is a local ring. -/
private theorem isLocalRing_closedFibre {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
  haveI : Nontrivial (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- **The closed fibre of a flat local homomorphism of one-dimensional Noetherian local rings
has dimension zero**, by the dimension formula `dim A' = dim A + dim A'/𝔪A'`. -/
theorem ringKrullDim_closedFibre_eq_zero (hdim : ringKrullDim A = 1)
    (hdim' : ringKrullDim A' = 1) :
    ringKrullDim (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) = 0 := by
  have hlie : (maximalIdeal A').LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A A')).symm⟩
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal A')
  have heq : (maximalIdeal A').height = (maximalIdeal A).height := by
    exact_mod_cast (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A')).trans
      (hdim'.trans (hdim.symm.trans
        (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).symm))
  rw [heq] at hheight
  have hfib := WithTop.add_left_cancel (x := (maximalIdeal A).height)
    Ideal.height_ne_top_of_isPrime (hheight.symm.trans (add_zero _).symm)
  have := isLocalRing_closedFibre (R := A) (S := A')
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hfib
  exact_mod_cast (IsLocalRing.maximalIdeal_height_eq_ringKrullDim).symm.trans
    (congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) hfib)

/-- The closed fibre `A' / 𝔪A'` of a flat local homomorphism of one-dimensional Noetherian local
rings is Artinian. -/
theorem isArtinianRing_closedFibre (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1) :
    IsArtinianRing (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) := by
  have : Ring.KrullDimLE 0 (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) :=
    Ring.krullDimLE_iff.mpr (by rw [ringKrullDim_closedFibre_eq_zero hdim hdim']; rfl)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- The closed fibre `A' / 𝔪A'` of a flat local homomorphism of one-dimensional Noetherian local
rings has finite length over `A'`. -/
theorem isFiniteLength_closedFibre (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1) :
    IsFiniteLength A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) := by
  have := isArtinianRing_closedFibre hdim hdim'
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_quotient _, isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := Ideal.map (algebraMap A A') (maximalIdeal A)))⟩

/-- A power of `𝔪'` lies in `𝔪A'`. -/
theorem exists_maximalIdeal_pow_le_closedFibre (hdim : ringKrullDim A = 1)
    (hdim' : ringKrullDim A' = 1) :
    ∃ k : ℕ, maximalIdeal A' ^ k ≤ Ideal.map (algebraMap A A') (maximalIdeal A) := by
  set I := Ideal.map (algebraMap A A') (maximalIdeal A)
  have := isArtinianRing_closedFibre hdim hdim'
  have : IsLocalRing (A' ⧸ I) := isLocalRing_closedFibre (R := A) (S := A')
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (A' ⧸ I)).mp inferInstance
  refine ⟨n, ?_⟩
  have hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A') ^ n = ⊥ := by
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hn
  rw [← Ideal.map_pow] at hmap
  have hle := Ideal.map_le_iff_le_comap.mp hmap.le
  change maximalIdeal A' ^ n ≤ RingHom.ker (Ideal.Quotient.mk I) at hle
  simpa only [Ideal.mk_ker] using hle

end ClosedFibre

end Stacks.Chow

namespace AlgebraicGeometry.TameSymbolPreparation

section BaseChange

variable {A : Type u} {A' : Type v} {B : Type w} [CommRing A] [CommRing A'] [CommRing B]
  [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [IsLocalHom (algebraMap A A')] [Algebra A B]
  {r : ℕ} {a : Fin r → A}

/-- The ideal of `B` under an ideal of `A' ⊗_A B`. -/
def underIdeal (Q : Ideal (A' ⊗[A] B)) : Ideal B :=
  Q.comap (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B)).toRingHom

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- For `x : A`, the images of `x` in `A' ⊗_A B` through `B` and through `A'` agree. -/
theorem includeRight_algebraMap (x : A) :
    Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B) (algebraMap A B x) =
      algebraMap A' (A' ⊗[A] B) (algebraMap A A' x) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A A' (A' ⊗[A] B)]

/-- Over a finite extension, the ideal of `B` under a maximal ideal of `A' ⊗_A B` is maximal. -/
theorem underIdeal_isMaximal (P : TameSymbolPreparation a B) (Q : Ideal (A' ⊗[A] B))
    [Q.IsMaximal] : (underIdeal Q).IsMaximal := by
  let := P.finite
  have hA' : Q.comap (algebraMap A' (A' ⊗[A] B)) = maximalIdeal A' :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
  have hA : (underIdeal Q).comap (algebraMap A B) = maximalIdeal A := by
    have h : (underIdeal Q).comap (algebraMap A B) =
        (Q.comap (algebraMap A' (A' ⊗[A] B))).comap (algebraMap A A') := by
      ext x
      show Algebra.TensorProduct.includeRight (algebraMap A B x) ∈ Q ↔ _
      rw [includeRight_algebraMap]
      rfl
    rw [h, hA']
    exact IsLocalRing.maximalIdeal_comap (algebraMap A A')
  have : (underIdeal Q).IsPrime := Ideal.comap_isPrime _ _
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hA]; infer_instance)

/-- The local homomorphism `B_{𝔮 ∩ B} → (A' ⊗_A B)_𝔮` at a maximal ideal `𝔮` of `A' ⊗_A B`. -/
noncomputable def localMap (P : TameSymbolPreparation a B) (Q : Ideal (A' ⊗[A] B))
    [Q.IsMaximal] :
    haveI := P.underIdeal_isMaximal Q
    Localization.AtPrime (underIdeal Q) →+* Localization.AtPrime Q :=
  haveI := P.underIdeal_isMaximal Q
  Localization.localRingHom (underIdeal Q) Q _ rfl

/-- `localMap` sends the image of `b : B` in `B_{𝔮 ∩ B}` to the image of `1 ⊗ b` in
`(A' ⊗_A B)_𝔮`. -/
theorem localMap_algebraMap (P : TameSymbolPreparation a B) (Q : Ideal (A' ⊗[A] B))
    [Q.IsMaximal] (b : B) :
    haveI := P.underIdeal_isMaximal Q
    P.localMap Q (algebraMap B (Localization.AtPrime (underIdeal Q)) b) =
      algebraMap (A' ⊗[A] B) (Localization.AtPrime Q)
        (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B) b) :=
  have := P.underIdeal_isMaximal Q
  Localization.localRingHom_to_map _ _ _ rfl b

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- `B → A' ⊗_A B` is flat when `A'` is flat over `A`. -/
theorem flat_includeRight [Module.Flat A A'] :
    (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B)).toRingHom.Flat := by
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let e : (A' ⊗[A] B) ≃ₐ[B] (B ⊗[A] A') :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A A' B).toRingEquiv)
      (by intro b; simp [Algebra.TensorProduct.right_algebraMap_apply])
  have : Module.Flat B (A' ⊗[A] B) := Module.Flat.of_linearEquiv e.toLinearEquiv
  exact RingHom.flat_algebraMap_iff.mpr this

/-- `localMap` sends nonzerodivisors to nonzerodivisors. -/
theorem isRegular_localMap [Module.Flat A A'] (P : TameSymbolPreparation a B)
    (Q : Ideal (A' ⊗[A] B)) [Q.IsMaximal]
    {x : haveI := P.underIdeal_isMaximal Q; Localization.AtPrime (underIdeal Q)}
    (hx : IsRegular x) : IsRegular (P.localMap Q x) := by
  have := P.underIdeal_isMaximal Q
  have hf : (P.localMap Q).Flat := RingHom.Flat.localRingHom flat_includeRight Q _ rfl
  let := (P.localMap Q).toAlgebra
  have : Module.Flat _ _ := hf
  exact isRegular_iff_mem_nonZeroDivisors.mpr
    (algebraMap_mem_nonZeroDivisors_of_flat (isRegular_iff_mem_nonZeroDivisors.mp hx))

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
/-- The base change `A' ⊗_A A → A' ⊗_A B` of `A → B` is the composite of `A' ⊗_A A ≃ A'` with
`A' → A' ⊗_A B`. -/
theorem baseChange_linearMap_apply (x : A' ⊗[A] A) :
    (LinearMap.baseChange A' (Algebra.linearMap A B)) x =
      algebraMap A' (A' ⊗[A] B) ((TensorProduct.rid A A') x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a =>
    simp only [LinearMap.baseChange_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul,
      Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    calc t ⊗ₜ[A] (algebraMap A B) a = t ⊗ₜ[A] (a • (1 : B)) := by simp [Algebra.smul_def]
      _ = (a • t) ⊗ₜ[A] (1 : B) := TensorProduct.tmul_smul (R := A) a t (1 : B)
      _ = ((algebraMap A A') a * t) ⊗ₜ[A] (1 : B) := by simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsLocalHom (algebraMap A A')] in
/-- If `𝔪'^k ⊆ 𝔪A'`, then `(A' ⊗_A B) / A'` is annihilated by a power of `𝔪'`. -/
theorem exists_baseChange_annihilated (P : TameSymbolPreparation a B)
    (hk : ∃ k : ℕ, maximalIdeal A' ^ k ≤ Ideal.map (algebraMap A A') (maximalIdeal A)) :
    ∃ k : ℕ, maximalIdeal A' ^ k • (⊤ : Submodule A' (A' ⊗[A] B)) ≤
      LinearMap.range (Algebra.linearMap A' (A' ⊗[A] B)) := by
  obtain ⟨n, hn⟩ := P.quotient_annihilated_by_maximalIdeal_power
  obtain ⟨k, hk⟩ := hk
  refine ⟨k * n, ?_⟩
  have h1 : maximalIdeal A' ^ (k * n) ≤ Ideal.map (algebraMap A A') (maximalIdeal A ^ n) := by
    rw [pow_mul, Ideal.map_pow]
    gcongr
  have h2 : Ideal.map (algebraMap A A') (maximalIdeal A ^ n) • (⊤ : Submodule A' (A' ⊗[A] B)) ≤
      LinearMap.range (LinearMap.baseChange A' (Algebra.linearMap A B)) := by
    rw [ArtinReesBaseChange.ideal_smul_top, ArtinReesBaseChange.range_baseChange]
    exact ArtinReesBaseChange.baseChange_mono hn
  have h3 : LinearMap.range (LinearMap.baseChange A' (Algebra.linearMap A B)) ≤
      LinearMap.range (Algebra.linearMap A' (A' ⊗[A] B)) := by
    rintro _ ⟨c, rfl⟩
    exact ⟨TensorProduct.rid A A' c, (baseChange_linearMap_apply c).symm⟩
  exact (Submodule.smul_mono h1 le_rfl).trans (h2.trans h3)

/-- **The base change of a preparation along a flat local homomorphism.** Let `A → A'` be flat
and local with `𝔪'^k ⊆ 𝔪A'` for some `k`, and let `a'_i` be the image of `a_i`. At a maximal
ideal `𝔮` of `A' ⊗_A B`, lying over the maximal ideal `𝔮 ∩ B` of `B`, the parameter, the unit
parts and the exponents are the images of those of `P` at `𝔮 ∩ B`. -/
noncomputable def baseChange [Module.Flat A A'] (P : TameSymbolPreparation a B)
    (a' : Fin r → A') (ha' : ∀ i, algebraMap A A' (a i) = a' i)
    (hk : ∃ k : ℕ, maximalIdeal A' ^ k ≤ Ideal.map (algebraMap A A') (maximalIdeal A)) :
    TameSymbolPreparation a' (A' ⊗[A] B) where
  finite := by let := P.finite; infer_instance
  algebraMap_injective :=
    Algebra.TensorProduct.includeLeft_injective (S := A') P.algebraMap_injective
  quotient_annihilated_by_maximalIdeal_power := P.exists_baseChange_annihilated hk
  parameter Q _ :=
    haveI := P.underIdeal_isMaximal Q
    P.localMap Q (P.parameter (underIdeal Q))
  parameter_isRegular Q _ :=
    haveI := P.underIdeal_isMaximal Q
    P.isRegular_localMap Q (P.parameter_isRegular _)
  factorUnit Q _ i :=
    haveI := P.underIdeal_isMaximal Q
    Units.map (P.localMap Q).toMonoidHom (P.factorUnit (underIdeal Q) i)
  exponent Q _ i :=
    haveI := P.underIdeal_isMaximal Q
    P.exponent (underIdeal Q) i
  factorization Q _ i := by
    have := P.underIdeal_isMaximal Q
    have h := congrArg (P.localMap Q) (P.factorization (underIdeal Q) i)
    rw [map_mul, map_pow, localMap_algebraMap, includeRight_algebraMap, ha' i] at h
    exact h

end BaseChange

end AlgebraicGeometry.TameSymbolPreparation
