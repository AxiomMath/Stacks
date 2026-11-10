module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.JacobsonInverse
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing two semilocal one-dimensional domains

Two Noetherian one-dimensional semilocal subrings of a common fraction field glue along their
intersection as soon as their multiplication map over the integers is surjective. Surjectivity
produces an element of each ring which is a unit there and lies in the Jacobson radical of the
other; each ring is then a localization of the intersection away from that element, so the two
spectra are open subschemes. They cover, because the two elements sum to a unit, and the
relative tensor product is the common fraction field.

## Main definitions

* `Subring.intersectionTensorProductTo`: the multiplication map from the tensor product over
  the intersection of two subrings to the ambient commutative ring.

## Main results

* `Subring.isOpenImmersion_specMap_inf_left` and `Subring.isOpenImmersion_specMap_inf_right`
  give the two open immersions.
* `Subring.range_specMap_inf_left_union_right` says that these open immersions cover the
  spectrum.
* `Subring.intersectionTensorProductTo_bijective` identifies the relative tensor product with
  the common fraction field.

## Implementation notes

The two rings are represented as subrings of `K`, and hence their fibre product is their
infimum. Semilocality is represented by finiteness of the maximal spectrum. The source's
equality `K = A ⊗_R B` is stated as bijectivity of its canonical multiplication map.

## References

* [Stacks Project, Tag 09N3](https://stacks.math.columbia.edu/tag/09N3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Subring

universe u

/-- The canonical multiplication map from the tensor product of two subrings over their
intersection to the ambient commutative ring. -/
public def intersectionTensorProductTo {K : Type u} [CommRing K] (A B : Subring K) :
    let _ := ((A ⊓ B : Subring K).inclusion inf_le_left).toAlgebra
    let _ := ((A ⊓ B : Subring K).inclusion inf_le_right).toAlgebra
    TensorProduct (A ⊓ B : Subring K) A B →+* K := by
  let _ := ((A ⊓ B : Subring K).inclusion inf_le_left).toAlgebra
  let _ := ((A ⊓ B : Subring K).inclusion inf_le_right).toAlgebra
  let _ : IsScalarTower (A ⊓ B : Subring K) A K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let _ : IsScalarTower (A ⊓ B : Subring K) B K :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom (A ⊓ B : Subring K) A K)
    (IsScalarTower.toAlgHom (A ⊓ B : Subring K) B K)).toRingHom

variable {K : Type u} [Field K] (A B : Subring K)
  [IsFractionRing A K] [IsFractionRing B K]
  [IsNoetherianRing A] [IsNoetherianRing B]
  [Finite (MaximalSpectrum A)] [Finite (MaximalSpectrum B)]

private lemma localizationAway_of_powers_clearing
    {R S : Type u} [CommSemiring R] [CommSemiring S] [Algebra R S] (x : R)
    (hx : IsUnit (algebraMap R S x))
    (hinj : Function.Injective (algebraMap R S))
    (hclear : ∀ s : S, ∃ n : ℕ, ∃ r : R,
      s * algebraMap R S x ^ n = algebraMap R S r) :
    IsLocalization.Away x S := by
  refine IsLocalization.Away.mk x hx hclear fun a b hab ↦ ?_
  obtain rfl := hinj hab
  exact ⟨0, by simp⟩

/-- A ring of Krull dimension one has dimension at most one. -/
private theorem dimensionLEOne_of_ringKrullDim_eq_one {R : Type*} [CommRing R] [IsDomain R]
    (h : ringKrullDim R = 1) : Ring.DimensionLEOne R :=
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp only [h, Nat.cast_one, le_refl])
  ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩

private lemma surjective_tensorProduct_lift_comm
    {K : Type*} [CommRing K] (A B : Subring K)
    (h : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Function.Surjective
      (Algebra.TensorProduct.lift (B := A) B.subtype.toIntAlgHom
        A.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  let e := Algebra.TensorProduct.comm ℤ A B
  have he :
      (Algebra.TensorProduct.lift (B := A) B.subtype.toIntAlgHom
        A.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)).comp e.toAlgHom =
      Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _) := by
    apply Algebra.TensorProduct.ext <;> ext <;> simp [e]
  intro x
  obtain ⟨t, rfl⟩ := h x
  exact ⟨e t, DFunLike.congr_fun he t⟩

private lemma exists_inf_isUnit_left_mem_jacobson_right {K : Type u} [Field K]
    (A B : Subring K) (tA : A) (tB : B) (htA : tA ∈ Ring.jacobson A)
    (htB : tB ∈ Ring.jacobson B) (htAB : (tA : K) * (tB : K) = 1) :
    ∃ r : (A ⊓ B : Subring K),
      IsUnit (Subring.inclusion (inf_le_left : A ⊓ B ≤ A) r) ∧
      Subring.inclusion (inf_le_right : A ⊓ B ≤ B) r ∈ Ring.jacobson B := by
  have huA : IsUnit (1 + tA) := by
    simpa [add_comm] using Ring.isUnit_add_of_isUnit_of_mem_jacobson isUnit_one htA
  have huB : IsUnit (1 + tB) := by
    simpa [add_comm] using Ring.isUnit_add_of_isUnit_of_mem_jacobson isUnit_one htB
  let uA : Aˣ := huA.unit
  let uB : Bˣ := huB.unit
  let rA : A := (uA⁻¹ : Aˣ)
  let uBInv : B := (uB⁻¹ : Bˣ)
  let rB : B := tB * uBInv
  have hrAB : (rB : K) = (rA : K) := by
    have hInvB : (uBInv : K) * (uB : K) = 1 :=
      congrArg (fun z : B => (z : K)) (Units.inv_mul uB)
    have hUnitB : (uB : K) = 1 + (tB : K) :=
      congrArg (fun z : B => (z : K)) huB.unit_spec
    have hUnitA : (uA : K) = 1 + (tA : K) :=
      congrArg (fun z : A => (z : K)) huA.unit_spec
    have hmul : (rB : K) * (uA : K) = 1 := by
      change (tB : K) * (uBInv : K) * (uA : K) = 1
      rw [hUnitA]
      calc
        (tB : K) * (uBInv : K) * (1 + (tA : K)) = (uBInv : K) * (1 + (tB : K)) := by
          linear_combination (uBInv : K) * htAB
        _ = 1 := by rw [← hUnitB, hInvB]
    have hmul' : (rA : K) * (uA : K) = 1 :=
      congrArg (fun z : A => (z : K)) (Units.inv_mul uA)
    exact (eq_inv_of_mul_eq_one_left hmul).trans
      (eq_inv_of_mul_eq_one_left hmul').symm
  let r : (A ⊓ B : Subring K) := ⟨(rA : K), Subring.mem_inf.2 ⟨rA.2, hrAB ▸ rB.2⟩⟩
  have hrmapA : Subring.inclusion (inf_le_left : A ⊓ B ≤ A) r = rA := Subtype.ext rfl
  have hrmapB : Subring.inclusion (inf_le_right : A ⊓ B ≤ B) r = rB :=
    Subtype.ext hrAB.symm
  refine ⟨r, ?_, ?_⟩
  · rw [hrmapA]
    exact Units.isUnit (uA⁻¹ : Aˣ)
  · rw [hrmapB]
    exact (Ring.jacobson B).mul_mem_right uBInv htB

private lemma exists_inf_localization_elements
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1)
    (h_surj : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    ∃ r s : (A ⊓ B : Subring K),
      IsUnit (Subring.inclusion (inf_le_left : A ⊓ B ≤ A) r) ∧
      (Subring.inclusion (inf_le_right : A ⊓ B ≤ B) r ∈ Ring.jacobson B) ∧
      IsUnit (Subring.inclusion (inf_le_right : A ⊓ B ≤ B) s) ∧
      (Subring.inclusion (inf_le_left : A ⊓ B ≤ A) s ∈ Ring.jacobson A) := by
  classical
  let _ : Algebra (A ⊓ B : Subring K) A :=
    (Subring.inclusion (inf_le_left : A ⊓ B ≤ A)).toAlgebra
  let _ : Algebra (A ⊓ B : Subring K) B :=
    (Subring.inclusion (inf_le_right : A ⊓ B ≤ B)).toAlgebra
  obtain ⟨a, ha0, haInv⟩ :=
    Ring.exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective
      A (fun _ : Unit => B) (fun _ => hB) (fun _ => h_surj)
  obtain ⟨aInv, haInvK, haInvJac⟩ := haInv Unit.unit
  rw [Ideal.jacobson_bot] at haInvJac
  obtain ⟨b, hb0, hbInv⟩ :=
    Ring.exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective
      B (fun _ : Unit => A) (fun _ => hA)
      (fun _ => surjective_tensorProduct_lift_comm A B h_surj)
  obtain ⟨bInv, hbInvK, hbInvJac⟩ := hbInv Unit.unit
  rw [Ideal.jacobson_bot] at hbInvJac
  let tA : A := a * bInv
  let tB : B := b * aInv
  have htA : tA ∈ Ring.jacobson A := (Ring.jacobson A).mul_mem_left a hbInvJac
  have htB : tB ∈ Ring.jacobson B := (Ring.jacobson B).mul_mem_left b haInvJac
  have htAB : (tA : K) * (tB : K) = 1 := by
    simp only [tA, tB, Subring.coe_mul]
    rw [haInvK, hbInvK]
    have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
    have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
    field_simp
  obtain ⟨r, hrA, hrB⟩ := exists_inf_isUnit_left_mem_jacobson_right A B tA tB htA htB htAB
  obtain ⟨s, hsB, hsA⟩ := exists_inf_isUnit_left_mem_jacobson_right B A tB tA htB htA
    ((mul_comm _ _).trans htAB)
  let s' : (A ⊓ B : Subring K) := ⟨(s : K), (inf_comm B A).le s.2⟩
  have hsB' : Subring.inclusion (inf_le_right : A ⊓ B ≤ B) s' =
      Subring.inclusion (inf_le_left : B ⊓ A ≤ B) s := Subtype.ext rfl
  have hsA' : Subring.inclusion (inf_le_left : A ⊓ B ≤ A) s' =
      Subring.inclusion (inf_le_right : B ⊓ A ≤ A) s := Subtype.ext rfl
  exact ⟨r, s', hrA, hrB, by rwa [hsB'], by rwa [hsA']⟩

private lemma exists_pow_mul_mem_inf_of_jacobson {K : Type u} [Field K]
    (A B : Subring K) [IsFractionRing B K] (hB : ringKrullDim B = 1)
    (x : (A ⊓ B : Subring K))
    (hxB : (Subring.inclusion (inf_le_right : A ⊓ B ≤ B) x) ∈ Ring.jacobson B)
    (z : A) :
    ∃ n : ℕ, ∃ q : (A ⊓ B : Subring K),
      (q : K) = (x : K) ^ n * (z : K) := by
  have := dimensionLEOne_of_ringKrullDim_eq_one hB
  let xB : B := Subring.inclusion (inf_le_right : A ⊓ B ≤ B) x
  obtain ⟨n, y, hy⟩ := Ring.exists_algebraMap_eq_pow_mul xB hxB (z : K)
  have hxA : (x : K) ^ n * (z : K) ∈ A := mul_mem (pow_mem (Subring.mem_inf.mp x.2).1 n) z.2
  have hxBmem : (x : K) ^ n * (z : K) ∈ B := by
    have hy' : algebraMap B K y = (x : K) ^ n * (z : K) := hy
    rw [← hy']
    exact y.2
  exact ⟨n, ⟨(x : K) ^ n * (z : K), (Subring.mem_inf).2 ⟨hxA, hxBmem⟩⟩, rfl⟩

private lemma isLocalizationAway_inf_left {K : Type u} [Field K]
    (A B : Subring K) [IsFractionRing B K] [Algebra (A ⊓ B : Subring K) A]
    (hmap : algebraMap (A ⊓ B : Subring K) A =
      Subring.inclusion (inf_le_left : A ⊓ B ≤ A))
    (hB : ringKrullDim B = 1) (r : (A ⊓ B : Subring K))
    (hrA : IsUnit (algebraMap (A ⊓ B : Subring K) A r))
    (hrB : Subring.inclusion (inf_le_right : A ⊓ B ≤ B) r ∈ Ring.jacobson B) :
    IsLocalization.Away r A := by
  have hinj : Function.Injective (algebraMap (A ⊓ B : Subring K) A) := by
    rw [hmap]
    exact Subring.inclusion_injective _
  refine localizationAway_of_powers_clearing r hrA hinj fun z ↦ ?_
  obtain ⟨n, q, hq⟩ := exists_pow_mul_mem_inf_of_jacobson A B hB r hrB z
  refine ⟨n, q, Subtype.ext ?_⟩
  rw [hmap]
  change (z : K) * (r : K) ^ n = (q : K)
  exact (mul_comm _ _).trans hq.symm

private lemma isLocalizationAway_inf_right {K : Type u} [Field K]
    (A B : Subring K) [IsFractionRing A K] [Algebra (A ⊓ B : Subring K) B]
    (hmap : algebraMap (A ⊓ B : Subring K) B =
      Subring.inclusion (inf_le_right : A ⊓ B ≤ B))
    (hA : ringKrullDim A = 1) (s : (A ⊓ B : Subring K))
    (hsB : IsUnit (algebraMap (A ⊓ B : Subring K) B s))
    (hsA : Subring.inclusion (inf_le_left : A ⊓ B ≤ A) s ∈ Ring.jacobson A) :
    IsLocalization.Away s B := by
  have hinj : Function.Injective (algebraMap (A ⊓ B : Subring K) B) := by
    rw [hmap]
    exact Subring.inclusion_injective _
  refine localizationAway_of_powers_clearing s hsB hinj fun z ↦ ?_
  let s' : (B ⊓ A : Subring K) := ⟨(s : K), (inf_comm A B).le s.2⟩
  have hsA' : Subring.inclusion (inf_le_right : B ⊓ A ≤ A) s' =
      Subring.inclusion (inf_le_left : A ⊓ B ≤ A) s := Subtype.ext rfl
  obtain ⟨n, q, hq⟩ := exists_pow_mul_mem_inf_of_jacobson B A hA s' (hsA' ▸ hsA) z
  let q' : (A ⊓ B : Subring K) := ⟨(q : K), (inf_comm B A).le q.2⟩
  refine ⟨n, q', Subtype.ext ?_⟩
  rw [hmap]
  change (z : K) * (s : K) ^ n = (q : K)
  exact (mul_comm _ _).trans hq.symm

private lemma isUnit_inf_of_isUnit_inclusions {K : Type u} [Field K]
    (A B : Subring K) (x : (A ⊓ B : Subring K))
    (hA : IsUnit (Subring.inclusion (inf_le_left : A ⊓ B ≤ A) x))
    (hB : IsUnit (Subring.inclusion (inf_le_right : A ⊓ B ≤ B) x)) :
    IsUnit x := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let aInv : A := (a⁻¹ : Aˣ)
  let bInv : B := (b⁻¹ : Bˣ)
  have haK : (aInv : K) * (x : K) = 1 := by
    have h := congrArg (fun q : A => (q : K)) (Units.inv_mul a)
    rwa [ha] at h
  have hbK : (bInv : K) * (x : K) = 1 := by
    have h := congrArg (fun q : B => (q : K)) (Units.inv_mul b)
    rwa [hb] at h
  have hab : (aInv : K) = (bInv : K) := by
    calc
      (aInv : K) = (aInv : K) * ((bInv : K) * (x : K)) := by rw [hbK, mul_one]
      _ = (bInv : K) * ((aInv : K) * (x : K)) := by ring
      _ = (bInv : K) := by rw [haK, mul_one]
  let q : (A ⊓ B : Subring K) :=
    ⟨(aInv : K), (Subring.mem_inf).2 ⟨aInv.2, hab ▸ bInv.2⟩⟩
  exact isUnit_iff_exists_inv.mpr ⟨q, Subtype.ext ((mul_comm _ _).trans haK)⟩

/-- The left-hand subring gives an open immersion into the spectrum of the intersection. -/
@[stacks 09N3 "the open immersion from A"]
public theorem isOpenImmersion_specMap_inf_left
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1)
    (h_surj : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    IsOpenImmersion
      (Scheme.Spec.map
        (CommRingCat.ofHom ((A ⊓ B : Subring K).inclusion inf_le_left)).op) := by
  let _ : Algebra (A ⊓ B : Subring K) A :=
    (Subring.inclusion (inf_le_left : A ⊓ B ≤ A)).toAlgebra
  let _ : Algebra (A ⊓ B : Subring K) B :=
    (Subring.inclusion (inf_le_right : A ⊓ B ≤ B)).toAlgebra
  obtain ⟨r, s, hrA, hrB, hsB, hsA⟩ :=
    exists_inf_localization_elements A B hA hB h_surj
  have _ : IsLocalization.Away r A := isLocalizationAway_inf_left A B rfl hB r hrA hrB
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization
    (R := (A ⊓ B : Subring K)) (S := A) r

/-- The right-hand subring gives an open immersion into the spectrum of the intersection. -/
@[stacks 09N3 "the open immersion from B"]
public theorem isOpenImmersion_specMap_inf_right
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1)
    (h_surj : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    IsOpenImmersion
      (Scheme.Spec.map
        (CommRingCat.ofHom ((A ⊓ B : Subring K).inclusion inf_le_right)).op) := by
  let _ : Algebra (A ⊓ B : Subring K) A :=
    (Subring.inclusion (inf_le_left : A ⊓ B ≤ A)).toAlgebra
  let _ : Algebra (A ⊓ B : Subring K) B :=
    (Subring.inclusion (inf_le_right : A ⊓ B ≤ B)).toAlgebra
  obtain ⟨r, s, hrA, hrB, hsB, hsA⟩ :=
    exists_inf_localization_elements A B hA hB h_surj
  have _ : IsLocalization.Away s B := isLocalizationAway_inf_right A B rfl hA s hsB hsA
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization
    (R := (A ⊓ B : Subring K)) (S := B) s

/-- The images of the two spectra cover the spectrum of the intersection. -/
@[stacks 09N3 "the covering assertion"]
public theorem range_specMap_inf_left_union_right
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1)
    (h_surj : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Set.range
        (Scheme.Spec.map
          (CommRingCat.ofHom ((A ⊓ B : Subring K).inclusion inf_le_left)).op).base ∪
      Set.range
        (Scheme.Spec.map
          (CommRingCat.ofHom ((A ⊓ B : Subring K).inclusion inf_le_right)).op).base =
      Set.univ := by
  let _ : Algebra (A ⊓ B : Subring K) A :=
    (Subring.inclusion (inf_le_left : A ⊓ B ≤ A)).toAlgebra
  let _ : Algebra (A ⊓ B : Subring K) B :=
    (Subring.inclusion (inf_le_right : A ⊓ B ≤ B)).toAlgebra
  obtain ⟨r, s, hrA, hrB, hsB, hsA⟩ :=
    exists_inf_localization_elements A B hA hB h_surj
  have _ : IsLocalization.Away r A := isLocalizationAway_inf_left A B rfl hB r hrA hrB
  have _ : IsLocalization.Away s B := isLocalizationAway_inf_right A B rfl hA s hsB hsA
  have hsumA : IsUnit ((Subring.inclusion (inf_le_left : A ⊓ B ≤ A)) (r + s)) := by
    change IsUnit ((Subring.inclusion (inf_le_left : A ⊓ B ≤ A) r) +
      (Subring.inclusion (inf_le_left : A ⊓ B ≤ A) s))
    exact Ring.isUnit_add_of_isUnit_of_mem_jacobson hrA hsA
  have hsumB : IsUnit ((Subring.inclusion (inf_le_right : A ⊓ B ≤ B)) (r + s)) := by
    change IsUnit ((Subring.inclusion (inf_le_right : A ⊓ B ≤ B) r) +
      (Subring.inclusion (inf_le_right : A ⊓ B ≤ B) s))
    simpa [add_comm] using Ring.isUnit_add_of_isUnit_of_mem_jacobson hsB hrB
  have hsumR := isUnit_inf_of_isUnit_inclusions A B (r + s) hsumA hsumB
  change Set.range (PrimeSpectrum.comap
      (algebraMap (A ⊓ B : Subring K) A)) ∪
    Set.range (PrimeSpectrum.comap
      (algebraMap (A ⊓ B : Subring K) B)) = Set.univ
  rw [PrimeSpectrum.localization_away_comap_range A r,
    PrimeSpectrum.localization_away_comap_range B s]
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hr : r ∈ p.asIdeal
  · exact Or.inr fun hs ↦
      p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (p.asIdeal.add_mem hr hs) hsumR)
  · exact Or.inl hr

/-- Multiplication identifies the tensor product over the intersection with the common fraction
field. -/
@[stacks 09N3 "the tensor-product assertion"]
public theorem intersectionTensorProductTo_bijective
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1)
    (h_surj : Function.Surjective
      (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
        B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    Function.Bijective (intersectionTensorProductTo A B) := by
  let R : Subring K := A ⊓ B
  let _ : Algebra R A := (Subring.inclusion (inf_le_left : R ≤ A)).toAlgebra
  let _ : Algebra R B := (Subring.inclusion (inf_le_right : R ≤ B)).toAlgebra
  let _ : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let _ : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨r, s, hrA, hrB, hsB, hsA⟩ :=
    exists_inf_localization_elements A B hA hB h_surj
  have _ : IsLocalization.Away r A := isLocalizationAway_inf_left A B rfl hB r hrA hrB
  have := dimensionLEOne_of_ringKrullDim_eq_one hB
  let rB : B := Subring.inclusion (inf_le_right : R ≤ B) r
  have hrBK0 : algebraMap B K rB ≠ 0 := fun h ↦ hrA.ne_zero (IsFractionRing.injective A K h)
  have : IsLocalization.Away rB K :=
    localizationAway_of_powers_clearing rB (isUnit_iff_ne_zero.mpr hrBK0)
      (IsFractionRing.injective B K) fun z ↦ by
        obtain ⟨n, y, hy⟩ := Ring.exists_algebraMap_eq_pow_mul rB hrB z
        refine ⟨n, y, ?_⟩
        change (z : K) * (r : K) ^ n = (y : K)
        exact (mul_comm _ _).trans hy.symm
  let T : Type _ := TensorProduct R A B
  let _ : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let _ : IsScalarTower R B T := Algebra.TensorProduct.right_isScalarTower
  have hmapB : algebraMap R B r = rB := Subtype.ext rfl
  have : IsLocalization.Away rB T := by
    rw [← hmapB]
    infer_instance
  let eTotal : T ≃ₐ[B] K := IsLocalization.algEquiv (Submonoid.powers rB) T K
  have he : eTotal.toRingHom = intersectionTensorProductTo A B := by
    apply IsLocalization.ringHom_ext (Submonoid.powers rB)
    ext b
    change eTotal (algebraMap B T b) =
      intersectionTensorProductTo A B (algebraMap B T b)
    rw [eTotal.commutes]
    change algebraMap B K b =
      Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom R A K)
        (IsScalarTower.toAlgHom R B K) ((1 : A) ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.productMap_right_apply]
    rfl
  rw [← he]
  exact eTotal.bijective

end Subring
