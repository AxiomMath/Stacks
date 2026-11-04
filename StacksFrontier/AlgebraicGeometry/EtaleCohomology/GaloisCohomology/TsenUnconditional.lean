module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Tsen
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Tsen

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.BrauerGroupCField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldFiniteExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldSystems
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.HomogeneousZeros
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tsen's theorem

A finitely generated field extension of transcendence degree `r` of an algebraically closed
field is a \(C_r\) field, and has the \(C_r\) property for systems of forms.

## Main results

* `exists_nonzero_common_zero_of_isHomogeneous_mvPolynomial`: over a polynomial ring in `r`
  variables over an algebraically closed field, `s` homogeneous forms of degree `d > 0` in
  `n > s * d ^ r` variables have a nontrivial common zero.
* `isCFieldForSystems_of_isFractionRing_mvPolynomial`: the fraction field of a polynomial ring
  in `r` variables over an algebraically closed field is \(C_r\) for systems of forms.
* `isCFieldForSystems_of_essFiniteType_trdeg_eq`: a finitely generated extension of
  transcendence degree `r` of an algebraically closed field is \(C_r\) for systems of forms.
* `isCField_of_essFiniteType_trdeg_eq`: such an extension is a \(C_r\) field.
-/

@[expose] public noncomputable section

universe u

/-- If `s * d ^ r < n` then, however large the shift `D`, `s` times the `r`-th power of
`d * e + D` is eventually beaten by `n` times the `r`-th power of `e`. -/
theorem exists_pos_mul_add_pow_lt_general {s d n r : ℕ} (hn : s * d ^ r < n) (D : ℕ) :
    ∃ e, 0 < e ∧ s * (d * e + D) ^ r < n * e ^ r := by
  obtain _ | q := r
  · exact ⟨1, one_pos, by simpa using hn⟩
  set m := s * ((q + 1) * (d + 1) ^ q) + 1 with hm
  have hm1 : 0 < m := by omega
  have key : s * (d * m + 1) ^ (q + 1) < n * m ^ (q + 1) := by
    have h1 : (d * m + 1) ^ (q + 1) ≤ (d * m) ^ (q + 1) + (q + 1) * (d * m + 1) ^ q :=
      Nat.add_one_pow_succ_le _ _
    have h2 : (q + 1) * (d * m + 1) ^ q ≤ (q + 1) * ((d + 1) ^ q * m ^ q) := by
      refine Nat.mul_le_mul_left _ ?_
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) _
    have h3 : s * ((q + 1) * ((d + 1) ^ q * m ^ q)) < m * m ^ q :=
      calc s * ((q + 1) * ((d + 1) ^ q * m ^ q)) = s * ((q + 1) * (d + 1) ^ q) * m ^ q := by ring
        _ < m * m ^ q := Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl (Nat.pow_pos hm1)
    have h4 : (d * m) ^ (q + 1) = d ^ (q + 1) * m ^ (q + 1) := mul_pow _ _ _
    have h5 : s * (d ^ (q + 1) * m ^ (q + 1)) + m ^ (q + 1) ≤ n * m ^ (q + 1) :=
      calc s * (d ^ (q + 1) * m ^ (q + 1)) + m ^ (q + 1)
          = (s * d ^ (q + 1) + 1) * m ^ (q + 1) := by ring
        _ ≤ n * m ^ (q + 1) := Nat.mul_le_mul_right _ hn
    have h6 : m * m ^ q = m ^ (q + 1) := (pow_succ' m q).symm
    have h7 : s * (d * m + 1) ^ (q + 1)
        ≤ s * (d * m) ^ (q + 1) + s * ((q + 1) * ((d + 1) ^ q * m ^ q)) := by
      rw [← mul_add]
      exact Nat.mul_le_mul_left _ (h1.trans (Nat.add_le_add_left h2 _))
    rw [h4] at h7
    omega
  refine ⟨(D + 1) * m, by positivity, ?_⟩
  calc s * (d * ((D + 1) * m) + D) ^ (q + 1) ≤ s * ((D + 1) * (d * m + 1)) ^ (q + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by nlinarith) _)
    _ = (D + 1) ^ (q + 1) * (s * (d * m + 1) ^ (q + 1)) := by rw [mul_pow]; ring
    _ < (D + 1) ^ (q + 1) * (n * m ^ (q + 1)) := Nat.mul_lt_mul_of_le_of_lt le_rfl key
      (Nat.pow_pos (Nat.succ_pos D))
    _ = n * ((D + 1) * m) ^ (q + 1) := by rw [mul_pow]; ring

namespace MvPolynomial

variable {σ τ k : Type*} [CommSemiring k]

namespace IsCoeffHomogeneous

end IsCoeffHomogeneous

end MvPolynomial

/-- **Tsen's dimension count.** Over a polynomial ring in `r` variables over an algebraically
closed field, a family of homogeneous polynomials of degree `d > 0` in `n` variables, indexed by
a finite type of cardinality `s` with `s * d ^ r < n`, has a common zero whose entries are
polynomials, not all zero. -/
theorem exists_nonzero_common_zero_of_isHomogeneous_mvPolynomial
    (k : Type*) [Field k] [IsAlgClosed k] {r n d : ℕ} {S : Type*} [Fintype S] (hd : 0 < d)
    (hdn : Fintype.card S * d ^ r < n)
    (f : S → MvPolynomial (Fin n) (MvPolynomial (Fin r) k))
    (hf : ∀ i, (f i).IsHomogeneous d) :
    ∃ α : Fin n → MvPolynomial (Fin r) k, α ≠ 0 ∧ ∀ i, MvPolynomial.eval α (f i) = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, D = Finset.univ.sup fun i =>
      (f i).support.sup fun ν => ((f i).coeff ν).totalDegree := ⟨_, rfl⟩
  obtain ⟨e, he, hcount⟩ := exists_pos_mul_add_pow_lt_general hdn D
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = (MvPolynomial.C
      (σ := Fin n × (Fin r → Fin e)) (R := k)) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ :
      ∃ β : Fin n → MvPolynomial (Fin r) (MvPolynomial (Fin n × (Fin r → Fin e)) k),
      β = fun i => genericBoundedPolynomial k i := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : S → MvPolynomial (Fin r) (MvPolynomial (Fin n × (Fin r → Fin e)) k),
      ∀ i, g i = MvPolynomial.eval₂ (MvPolynomial.map cc) β (f i) := ⟨_, fun _ => rfl⟩
  have hgHC : ∀ i, (g i).IsCoeffHomogeneous d := by
    intro i
    rw [hg, hcc, hβ]
    exact MvPolynomial.IsCoeffHomogeneous.eval₂ (hf i) _ fun l =>
      isCoeffHomogeneous_genericBoundedPolynomial k l
  have hdegg : ∀ i j, (g i).degreeOf j < d * e + D := by
    intro i j
    have hb : ∀ ν ∈ (f i).support,
        (MvPolynomial.map cc ((f i).coeff ν) * ∏ l ∈ ν.support, β l ^ ν l).degreeOf j
          ≤ D + d * (e - 1) := by
      intro ν hν
      refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) (Nat.add_le_add ?_ ?_)
      · calc (MvPolynomial.map cc ((f i).coeff ν)).degreeOf j
            ≤ ((f i).coeff ν).degreeOf j := MvPolynomial.degreeOf_le_iff.mpr fun m hm =>
                MvPolynomial.le_degreeOf_of_mem_support j
                  (MvPolynomial.support_map_subset _ _ hm)
          _ ≤ ((f i).coeff ν).totalDegree := MvPolynomial.degreeOf_le_totalDegree _ j
          _ ≤ (f i).support.sup fun ν => ((f i).coeff ν).totalDegree :=
              Finset.le_sup (f := fun ν => ((f i).coeff ν).totalDegree) hν
          _ ≤ D := by
              rw [hD]
              exact Finset.le_sup
                (f := fun i => (f i).support.sup fun ν => ((f i).coeff ν).totalDegree)
                (Finset.mem_univ i)
      · calc (∏ l ∈ ν.support, β l ^ ν l).degreeOf j
            ≤ ∑ l ∈ ν.support, (β l ^ ν l).degreeOf j := MvPolynomial.degreeOf_prod_le _ _ _
          _ ≤ ∑ l ∈ ν.support, ν l * (e - 1) := Finset.sum_le_sum fun l _ =>
                le_trans (MvPolynomial.degreeOf_pow_le _ _ _) (Nat.mul_le_mul_left _
                  (hβ ▸ degreeOf_genericBoundedPolynomial_le k l j))
          _ = (∑ l ∈ ν.support, ν l) * (e - 1) := Finset.sum_mul .. |>.symm
          _ = d * (e - 1) := by rw [← (hf i).degree_eq_sum_deg_support hν]
    have hle : (g i).degreeOf j ≤ D + d * (e - 1) := by
      rw [hg, MvPolynomial.eval₂_eq]
      exact le_trans (MvPolynomial.degreeOf_sum_le _ _ _) (Finset.sup_le hb)
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hmul : d * (e' + 1 - 1) + d = d * (e' + 1) := by rw [Nat.add_sub_cancel]; ring
    omega
  have hsupp : ∀ i ν, (g i).coeff ν ≠ 0 →
      ∃ w : Fin r → Fin (d * e + D), boxExponent w = ν := by
    intro i ν hν
    refine ⟨fun j => ⟨ν j, ?_⟩, Finsupp.ext fun j => rfl⟩
    exact lt_of_le_of_lt (MvPolynomial.le_degreeOf_of_mem_support j
      (MvPolynomial.mem_support_iff.mpr hν)) (hdegg i j)
  obtain ⟨a, ha0, ha⟩ := exists_nonzero_common_zero_of_isHomogeneous_of_card_lt k
    (fun _ : S × (Fin r → Fin (d * e + D)) => d) (fun p => (g p.1).coeff (boxExponent p.2))
    (fun _ => hd) (fun p => hgHC p.1 _) (by simpa [Fintype.card_prod] using hcount)
  refine ⟨fun l => MvPolynomial.map (MvPolynomial.eval a) (β l), ?_, fun i => ?_⟩
  · obtain ⟨⟨i₀, b₀⟩, hib⟩ := Function.ne_iff.mp ha0
    intro hcon
    have h2 := congrArg (MvPolynomial.coeff (boxExponent b₀)) (congrFun hcon i₀)
    simp only [hβ, MvPolynomial.coeff_map, coeff_genericBoundedPolynomial, MvPolynomial.eval_X,
      Pi.zero_apply, MvPolynomial.coeff_zero] at h2
    exact hib h2
  · have hCid : ((MvPolynomial.eval a).comp cc) = RingHom.id k := by
      rw [hcc]
      exact RingHom.ext fun x => by simp
    have hcomp : (MvPolynomial.map (MvPolynomial.eval a)).comp (MvPolynomial.map cc)
        = RingHom.id (MvPolynomial (Fin r) k) :=
      RingHom.ext fun c => by
        rw [RingHom.comp_apply, MvPolynomial.map_map, hCid, MvPolynomial.map_id,
          RingHom.id_apply]
    have hcl := MvPolynomial.eval₂_comp_left (MvPolynomial.map (MvPolynomial.eval a))
      (MvPolynomial.map cc) β (f i)
    rw [hcomp, MvPolynomial.eval₂_id] at hcl
    have hzero : MvPolynomial.map (MvPolynomial.eval a) (g i) = 0 := by
      refine MvPolynomial.ext _ _ fun ν => ?_
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hν : (g i).coeff ν = 0
      · simp [hν]
      · obtain ⟨w, rfl⟩ := hsupp i ν hν
        exact ha (i, w)
    rw [← hg] at hcl
    exact hcl ▸ hzero

/-- **Tsen's theorem for rational function fields, for systems of forms.** A fraction field of
the polynomial ring in `r` variables over an algebraically closed field has the \(C_r\)
property for systems of forms. -/
theorem isCFieldForSystems_of_isFractionRing_mvPolynomial (k : Type*) [Field k] [IsAlgClosed k]
    {r : ℕ} (K : Type*) [Field K] [Algebra (MvPolynomial (Fin r) k) K]
    [IsFractionRing (MvPolynomial (Fin r) k) K] : IsCFieldForSystems K r := by
  classical
  intro s d n hd hsn f hf
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin r) k) K) :=
    IsFractionRing.injective _ _
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (MvPolynomial (Fin r) k))
    (Finset.univ.biUnion fun i => (f i).support.image fun ν => (f i).coeff ν)
  obtain ⟨h, hh⟩ : ∃ h : Fin s → MvPolynomial (Fin n) K, ∀ i,
      h i = MvPolynomial.C (algebraMap (MvPolynomial (Fin r) k) K (b : _)) * f i :=
    ⟨_, fun _ => rfl⟩
  have hint : ∀ i ν, ∃ y, algebraMap (MvPolynomial (Fin r) k) K y = (h i).coeff ν := by
    intro i ν
    by_cases hν : ν ∈ (f i).support
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hν⟩)
      exact ⟨y, by rw [hh, MvPolynomial.coeff_C_mul, hy, Algebra.smul_def]⟩
    · refine ⟨0, ?_⟩
      rw [hh, MvPolynomial.coeff_C_mul, MvPolynomial.notMem_support_iff.mp hν, map_zero,
        mul_zero]
  have hlift : ∀ i, ∃ q : MvPolynomial (Fin n) (MvPolynomial (Fin r) k),
      MvPolynomial.map (algebraMap (MvPolynomial (Fin r) k) K) q = h i := fun i =>
    (MvPolynomial.mem_range_map_iff_coeffs_subset (f := algebraMap (MvPolynomial (Fin r) k) K)
      (x := h i)).mpr fun c hc => by
        obtain ⟨ν, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
        exact hint i ν
  choose f' hf' using hlift
  have hf'hom : ∀ i, (f' i).IsHomogeneous d := fun i =>
    MvPolynomial.IsHomogeneous.of_map hinj (by rw [hf' i, hh i]; exact (hf i).C_mul _)
  obtain ⟨α, hα0, hα⟩ := exists_nonzero_common_zero_of_isHomogeneous_mvPolynomial k hd
    (by simpa using hsn) f' hf'hom
  refine ⟨fun l => algebraMap (MvPolynomial (Fin r) k) K (α l), ?_, fun i => ?_⟩
  · exact fun hcon => hα0 (funext fun l => hinj (by simpa using congrFun hcon l))
  · have hev :
        MvPolynomial.eval (fun l => algebraMap (MvPolynomial (Fin r) k) K (α l)) (h i) = 0 := by
      rw [← hf' i, MvPolynomial.eval_map]
      exact (MvPolynomial.eval₂_comp _ _ _).symm.trans (by rw [hα i, map_zero])
    rw [hh i] at hev
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hev
    exact (mul_eq_zero.mp hev).resolve_left
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero b))

/-- **Tsen's theorem, field-theoretic form, for systems of forms.** A finitely generated field
extension of transcendence degree `r` of an algebraically closed field `k` has the \(C_r\)
property for systems of forms.

A transcendence basis has `r` elements, the subfield `E` it generates is a rational function
field in `r` variables (`AlgebraicIndependent.aevalEquivField`), and `K` is algebraic and
finitely generated over `E`, hence finite over it. The rational case is the dimension count
above, and the property passes to the finite extension `K/E` by
`IsCFieldForSystems.of_module_finite`. -/
@[sga "4½ Arcata 3.2.3" "special case"]
theorem isCFieldForSystems_of_essFiniteType_trdeg_eq (k : Type*) [Field k] [IsAlgClosed k]
    (K : Type*) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] {r : ℕ}
    (h : Algebra.trdeg k K = r) : IsCFieldForSystems K r := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  obtain ⟨σ⟩ := Cardinal.mk_eq_nat_iff.mp (hs.cardinalMk_eq_trdeg.trans h)
  have hx : IsTranscendenceBasis k ((Subtype.val : s → K) ∘ σ.symm) := hs.comp_equiv σ.symm
  let E := IntermediateField.adjoin k (Set.range ((Subtype.val : s → K) ∘ σ.symm))
  have : Algebra.IsAlgebraic E K := hx.isAlgebraic_field
  have : Algebra.EssFiniteType E K := Algebra.EssFiniteType.of_comp k E K
  have : Module.Finite E K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hE : IsCFieldForSystems E r :=
    (isCFieldForSystems_of_isFractionRing_mvPolynomial k
      (FractionRing (MvPolynomial (Fin r) k))).of_ringEquiv hx.1.aevalEquivField.toRingEquiv
  exact hE.of_module_finite E K

/-- **Tsen's theorem, field-theoretic form.** A finitely generated field extension of
transcendence degree `r` of an algebraically closed field is a \(C_r\) field. -/
@[sga "4½ Arcata 3.2.3" "special case"]
theorem isCField_of_essFiniteType_trdeg_eq (k : Type*) [Field k] [IsAlgClosed k]
    (K : Type*) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] {r : ℕ}
    (h : Algebra.trdeg k K = r) : IsCField K r :=
  (isCFieldForSystems_of_essFiniteType_trdeg_eq k K h).isCField

