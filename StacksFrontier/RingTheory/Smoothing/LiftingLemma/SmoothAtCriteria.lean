module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Noetherian.Spec
public import StacksFrontier.RingTheory.Smooth.NaiveCotangentCriterion
public import StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation
public import StacksFrontier.RingTheory.Smoothing.StandardElementAtSmoothPrime

/-!
# Lifting lemma: Jacobian and smoothness criteria

Auxiliary lemmas for `Stacks.Smoothing.exists_finitePresentation_lift_smoothAt`
(Stacks Project, Tag 07CP): partial derivatives of relations, non-vanishing of the
Jacobian of a chart, coordinates of solutions of linear relations, flatness and
smoothness at a prime, and the vanishing of chart relations in a local ring.
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.NaiveCotangentCriterion

open scoped Pointwise

universe u v w

open MvPolynomial in
private lemma pderiv_rename_inr {R σ τ : Type*} [CommRing R]
    (p : MvPolynomial σ R) (j : τ) :
    pderiv (Sum.inr j) (rename (Sum.inl : σ → σ ⊕ τ) p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

open MvPolynomial in
lemma chart_jacobian_notMem
    {R A σ τ δ κ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype δ] [Fintype κ] [DecidableEq δ] [DecidableEq κ]
    (P : Algebra.Presentation R A (σ ⊕ τ) (δ ⊕ κ))
    (cols : δ ↪ σ) (rows : δ → τ) (rest : κ ↪ τ)
    (hdis : ∀ d k, rows d ≠ rest k)
    (π : R) (F : δ → MvPolynomial σ R) (a : MvPolynomial σ R)
    (H : κ → δ → MvPolynomial σ R) (Q : κ → MvPolynomial (σ ⊕ τ) R)
    (hF : ∀ d, P.relation (Sum.inl d) =
      rename Sum.inl (F d) - C π * X (Sum.inr (rows d)))
    (hQ : ∀ k, P.relation (Sum.inr k) =
      rename Sum.inl a * X (Sum.inr (rest k)) -
      (∑ d, rename Sum.inl (H k d) * X (Sum.inr (rows d))) - C π * Q k)
    (q : Ideal A) [q.IsPrime]
    (hπ : algebraMap R A π ∈ q)
    (ha : aeval P.val (rename Sum.inl a) ∉ q)
    (hdet : aeval P.val (rename Sum.inl
      (Matrix.det fun d e : δ => pderiv (cols e) (F d))) ∉ q) :
    (Algebra.PreSubmersivePresentation.mk P
      (Sum.map cols rest) (Function.Embedding.sumMap cols rest).injective).jacobian ∉ q := by
  classical
  let f : MvPolynomial (σ ⊕ τ) R →+* A ⧸ q :=
    (Ideal.Quotient.mk q).comp (aeval P.val).toRingHom
  have hfπ : f (C π) = 0 := by
    show Ideal.Quotient.mk q ((aeval P.val) (C π)) = 0
    rw [aeval_C]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hπ
  let T := Algebra.PreSubmersivePresentation.mk P
    (Sum.map cols rest) (Function.Embedding.sumMap cols rest).injective
  let B : Matrix δ δ (A ⧸ q) := fun d e => f (rename Sum.inl (pderiv (cols e) (F d)))
  let Z : Matrix κ δ (A ⧸ q) := fun k d => f (pderiv (Sum.inl (cols d)) (P.relation (Sum.inr k)))
  have hM : (T.jacobiMatrix.transpose).map f =
      Matrix.fromBlocks B 0 Z (Matrix.diagonal fun _ : κ => f (rename Sum.inl a)) := by
    ext i j
    cases i with
    | inl d =>
      cases j with
      | inl e =>
        simp [T, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
          Matrix.transpose_apply, Matrix.fromBlocks, B, hF,
          pderiv_rename Sum.inl_injective]
      | inr k =>
        simp [T, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
          Matrix.transpose_apply, Matrix.fromBlocks, hF, pderiv_rename_inr, hdis]
    | inr k =>
      cases j with
      | inl d =>
        simp [T, Algebra.PreSubmersivePresentation.jacobiMatrix_apply, Matrix.fromBlocks, Z]
      | inr l =>
        by_cases hkl : k = l <;> simp [T, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
          Matrix.transpose_apply, hQ, pderiv_rename_inr, hfπ,
          hdis, rest.injective.eq_iff, Matrix.fromBlocks, Matrix.diagonal,
          hkl]
  have hB : B.det ≠ 0 := by
    have hh : B.det = f (rename Sum.inl
        (Matrix.det fun d e : δ => pderiv (cols e) (F d))) :=
      (RingHom.map_det (f.comp (rename (Sum.inl : σ → σ ⊕ τ)).toRingHom)
        (fun d e : δ => pderiv (cols e) (F d))).symm
    rw [hh]
    exact Ideal.Quotient.eq_zero_iff_mem.not.mpr hdet
  have ha' : f (rename Sum.inl a) ≠ 0 := Ideal.Quotient.eq_zero_iff_mem.not.mpr ha
  intro hj
  have hz : f T.jacobiMatrix.det = 0 := by
    show Ideal.Quotient.mk q ((aeval P.val) T.jacobiMatrix.det) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det] at hj
    rw [T.algebraMap_eq] at hj
    change (aeval T.val) T.jacobiMatrix.det ∈ q at hj
    exact hj
  rw [← Matrix.det_transpose, RingHom.map_det] at hz
  change ((T.jacobiMatrix.transpose).map f).det = 0 at hz
  rw [hM, Matrix.det_fromBlocks_zero₁₂, Matrix.det_diagonal] at hz
  exact (mul_ne_zero hB (Finset.prod_ne_zero_iff.mpr fun _ _ => ha')) hz

lemma exists_coordinates_of_linear_relations
    {A τ : Type*} [CommRing A] [Fintype τ] [DecidableEq τ]
    (V : Finset τ) (d : τ → V → A) (z : τ → A) (a : A)
    (H : τ → V → A) (ha : IsUnit a)
    (hdet : IsUnit (Matrix.det fun i j : V => d i.1 j))
    (hd : ∀ l j, a * d l j = ∑ t : V, H l t * d t.1 j)
    (hz : ∀ l, l ∉ V → a * z l = ∑ t : V, H l t * z t.1) :
    ∃ v : V → A, ∀ l, z l = ∑ j : V, d l j * v j := by
  classical
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hdet) (fun j : V => z j.1)
  have hsv (j : V) : z j.1 = ∑ t : V, d j.1 t * v t :=
    (congrFun hv j).symm
  refine ⟨v, fun l => ?_⟩
  by_cases hl : l ∈ V
  · exact hsv ⟨l, hl⟩
  apply ha.mul_left_cancel
  rw [hz l hl, Finset.mul_sum]
  simp_rw [← mul_assoc, hd, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← hsv]

lemma relation_of_coordinates
    {A τ δ κ : Type*} [CommRing A] [Fintype δ] [Fintype κ]
    (d : τ → δ → A) (z : τ → A) (v : δ → A)
    (hv : ∀ l, z l = ∑ j : δ, d l j * v j)
    (b : A) (H : κ → A) (s : κ → τ) (l : τ)
    (hd : ∀ j, b * d l j = ∑ t : κ, H t * d (s t) j) :
    b * z l = ∑ t : κ, H t * z (s t) := by
  simp_rw [hv, Finset.mul_sum, ← mul_assoc, hd, Finset.sum_mul]
  rw [Finset.sum_comm]


private lemma annihilator_square_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (π : R)
    (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0) :
    ∀ s : S, s * algebraMap R S π = 0 ↔ s * (algebraMap R S π) ^ 2 = 0 := by
  have h : Ideal.torsionOf R R π = Ideal.torsionOf R R (π ^ 2) := by
    ext r
    simpa [Ideal.mem_torsionOf_iff, smul_eq_mul] using hR r
  have h' := congrArg (Ideal.map (algebraMap R S)) h
  rw [ann_extension_eq_ann_baseChange_elem, ann_extension_eq_ann_baseChange_elem] at h'
  intro s
  have hs := congrArg (fun I : Ideal S => s ∈ I) h'
  simp only [Ideal.mem_torsionOf_iff] at hs
  have heq (x : R) :
      (s • ((1 : S) ⊗ₜ[R] x) = 0) ↔ s * algebraMap R S x = 0 := by
    constructor
    · intro hx
      have hy := congrArg (TensorProduct.AlgebraTensorModule.rid R S S) hx
      simpa [TensorProduct.AlgebraTensorModule.rid, Algebra.smul_def, mul_comm] using hy
    · intro hx
      apply (TensorProduct.AlgebraTensorModule.rid R S S).injective
      simpa [TensorProduct.AlgebraTensorModule.rid, Algebra.smul_def, mul_comm] using hx
  rw [heq π, heq (π ^ 2)] at hs
  simpa [map_pow] using hs

lemma eq_zero_of_mul_pi_eq_zero_of_mem_pi
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (s : S) (hs : s ∈ Ideal.span {algebraMap R S π})
    (hzero : s * algebraMap R S π = 0) : s = 0 := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hs
  have hsq : t * (algebraMap R S π) ^ 2 = 0 := by
    calc
      t * (algebraMap R S π) ^ 2 =
          ((algebraMap R S π) * t) * algebraMap R S π := by ring
      _ = 0 := by simpa only [← ht] using hzero
  have hlin := (annihilator_square_of_flat π hR t).mpr hsq
  simpa [ht, mul_comm] using hlin

lemma smoothAt_of_isSmoothAt
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime]
    (hq : Algebra.IsSmoothAt R q) : Algebra.SmoothAt R A q := by
  obtain ⟨a, ha, hs⟩ :=
    @Algebra.IsSmoothAt.exists_notMem_smooth R A _ _ _ _ q _ hq
  exact ⟨a, ha, hs⟩

lemma mvPolynomial_divisible_of_map_quotient_zero
    {R σ : Type*} [CommRing R] (a : R) (p : MvPolynomial σ R)
    (hp : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {a})) p = 0) :
    ∃ q : MvPolynomial σ R, p = MvPolynomial.C a * q := by
  classical
  have hcoeff (d : σ →₀ ℕ) : ∃ b : R, p.coeff d = a * b := by
    have hd := congrArg (fun q : MvPolynomial σ (R ⧸ Ideal.span {a}) => q.coeff d) hp
    have hd' : Ideal.Quotient.mk (Ideal.span {a}) (p.coeff d) = 0 := by
      simpa [MvPolynomial.coeff_map] using hd
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
      ((Ideal.Quotient.eq_zero_iff_mem).mp hd')
    exact ⟨b, by simpa [mul_comm] using hb⟩
  choose b hb using hcoeff
  refine ⟨∑ d ∈ p.support, MvPolynomial.monomial d (b d), ?_⟩
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum]
  simp_rw [MvPolynomial.C_mul_monomial, ← hb]

private lemma pderiv_mem_of_mem_ideal_sq
    {R σ : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R))
    (i : σ) {f : MvPolynomial σ R} (hf : f ∈ I ^ 2) :
    MvPolynomial.pderiv i f ∈ I := by
  rw [pow_two] at hf
  induction hf using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b hb =>
      rw [MvPolynomial.pderiv_mul]
      exact I.add_mem (I.mul_mem_left _ hb) (I.mul_mem_right _ ha)
  | add a b ha hb ih₁ ih₂ =>
      rw [map_add]
      exact I.add_mem ih₁ ih₂

lemma pderiv_relation_mod_pi
    {R σ τ : Type*} [CommRing R] [Fintype τ]
    (π : R) (F : τ → MvPolynomial σ R) (V : Finset τ)
    (a : MvPolynomial σ R) (H : V → MvPolynomial σ R)
    (l : τ) (T E : MvPolynomial σ R)
    (hT : T ∈ (Ideal.span (Set.range F)) ^ 2)
    (hrel : a * F l - (∑ j : V, H j * F j.1) - T =
      MvPolynomial.C (π ^ 2) * E) (i : σ) :
    a * MvPolynomial.pderiv i (F l) -
      (∑ j : V, H j * MvPolynomial.pderiv i (F j.1)) ∈
        Ideal.span (Set.range F) ⊔ Ideal.span {MvPolynomial.C π} := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span (Set.range F)
  let J : Ideal (MvPolynomial σ R) := I ⊔ Ideal.span {MvPolynomial.C π}
  let q : MvPolynomial σ R →+* MvPolynomial σ R ⧸ J := Ideal.Quotient.mk J
  have hF (j : τ) : q (F j) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))
  have hT' : q (MvPolynomial.pderiv i T) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.mem_sup_left (pderiv_mem_of_mem_ideal_sq I i hT))
  have hπ : q (MvPolynomial.C π) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  have hπsq : q (MvPolynomial.C (π ^ 2)) = 0 := by
    rw [MvPolynomial.C_pow, map_pow, hπ]
    norm_num
  have hd := congrArg (MvPolynomial.pderiv i) hrel
  simp only [map_sub, map_sum, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C, zero_mul, zero_add] at hd
  have hqd := congrArg q hd
  simp only [map_sub, map_add, map_mul, map_sum, hF, hT', hπsq,
    mul_zero, zero_mul, zero_add, sub_zero] at hqd
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  show q (a * MvPolynomial.pderiv i (F l) -
    (∑ j : V, H j * MvPolynomial.pderiv i (F j.1))) = 0
  simpa only [map_sub, map_mul, map_sum] using hqd

lemma chart_relation_identity {A : Type*} [CommRing A]
    {α β γ : Type*} [Fintype α] [Fintype β]
    (p a e : A) (G z : γ → A) (H : α → A) (Q : β → A)
    (row : α → γ) (fst snd : β → γ) (l : γ)
    (h : a * G l - (∑ j, H j * G (row j)) -
      (∑ b, Q b * (G (fst b) * G (snd b))) = p ^ 2 * e) :
    p * (a * z l - (∑ j, H j * z (row j)) -
      p * (e + ∑ b, Q b * (z (fst b) * z (snd b)))) =
      -a * (G l - p * z l) +
        (∑ j, H j * (G (row j) - p * z (row j))) +
        (∑ b, Q b * ((G (fst b) - p * z (fst b)) * G (snd b) +
          p * z (fst b) * (G (snd b) - p * z (snd b)))) := by
  have hh : (∑ j, H j * (G (row j) - p * z (row j))) =
      (∑ j, H j * G (row j)) - p * (∑ j, H j * z (row j)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq : (∑ b, Q b * ((G (fst b) - p * z (fst b)) * G (snd b) +
          p * z (fst b) * (G (snd b) - p * z (snd b)))) =
      (∑ b, Q b * (G (fst b) * G (snd b))) -
        p ^ 2 * (∑ b, Q b * (z (fst b) * z (snd b))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hh, hq]
  linear_combination h

private lemma quadratic_relation_as_linear
    {A β : Type*} [CommRing A] [Fintype β]
    (p : A) (Q : β × β → A) (r G z : β → A) :
    (∑ ab : β × β,
      Q ab * (r ab.1 * G ab.2 + p * z ab.1 * r ab.2)) =
      ∑ j : β,
        ((∑ b : β, Q (j, b) * G b) +
          (∑ a : β, Q (a, j) * p * z a)) * r j := by
  have hleft :
      (∑ a : β, ∑ b : β, Q (a, b) * (r a * G b)) =
        ∑ a : β, (∑ b : β, Q (a, b) * G b) * r a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hright :
      (∑ a : β, ∑ b : β, Q (a, b) * (p * z a * r b)) =
        ∑ b : β, (∑ a : β, Q (a, b) * p * z a) * r b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hleft, hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma map_ideal_eq_of_le_colon_of_isUnit
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I J : Ideal A) (s : A) (hIJ : I ≤ J)
    (hJI : J ≤ I.colon {s}) (hs : IsUnit (f s)) :
    I.map f = J.map f := by
  apply le_antisymm
  · exact Ideal.map_mono hIJ
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have hxs : x * s ∈ I := (Submodule.mem_colon_singleton).mp (hJI hx)
    have hmul : f s * f x ∈ I.map f := by
      rw [mul_comm, ← map_mul]
      exact Ideal.mem_map_of_mem f hxs
    exact (I.map f).smul_mem_iff_of_isUnit hs |>.mp (by
      simpa only [smul_eq_mul] using hmul)

lemma flat_atPrime_of_isSmoothAt
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime]
    [Algebra.IsSmoothAt R q] : Module.Flat R (Localization.AtPrime q) := by
  obtain ⟨a, ha, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth (R := R) q
  let V := Localization.Away a
  let U := Localization.AtPrime q
  have hle : Submonoid.powers a ≤ q.primeCompl := Submonoid.powers_le.mpr ha
  have hu (s : Submonoid.powers a) : IsUnit (algebraMap A U s) :=
    IsLocalization.map_units U (⟨s, hle s.property⟩ : q.primeCompl)
  let f : V →ₐ[A] U := IsLocalization.liftAlgHom
    (f := IsScalarTower.toAlgHom A A U) hu
  let : Algebra V U := f.toAlgebra
  let : IsScalarTower A V U := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun x => (f.commutes x).symm)
  let : IsScalarTower R V U := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun x => ((f.restrictScalars R).commutes x).symm)
  let : IsLocalization (q.primeCompl.map (algebraMap A V)) U :=
    IsLocalization.isLocalization_of_submonoid_le V U
      (Submonoid.powers a) q.primeCompl hle
  let : Algebra.Smooth R V := hs
  let : Module.Flat V U := IsLocalization.flat U (q.primeCompl.map (algebraMap A V))
  exact Module.Flat.trans R V U

lemma isSmoothAt_of_presentation_jacobian_notMem
    {R A ι σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Finite ι] [Finite σ] (P : Algebra.Presentation R A ι σ)
    (q : Ideal A) [q.IsPrime] (e : σ ↪ ι)
    (he : (Algebra.PreSubmersivePresentation.mk P e e.injective).jacobian ∉ q) :
    Algebra.IsSmoothAt R q := by
  let : Algebra.FinitePresentation R A := P.finitePresentation_of_isFinite
  let g : A := (Algebra.PreSubmersivePresentation.mk P e e.injective).jacobian
  have hunit : IsUnit (algebraMap A (Localization.Away g) g) :=
    IsLocalization.map_units (Localization.Away g)
      (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)
  have hj : IsUnit ((Algebra.PreSubmersivePresentation.localizationAway
      (Localization.Away g) g).comp
        (Algebra.PreSubmersivePresentation.mk P e e.injective)).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact hunit.mul hunit
  let : Algebra.IsStandardSmooth R (Localization.Away g) :=
    (Algebra.SubmersivePresentation.mk _ hj).isStandardSmooth
  have hs : Algebra.Smooth R (Localization.Away g) := inferInstance
  exact isSmoothAt_of_smooth_away q he hs

private lemma det_fromBlocks_notMem_of_upperRight_mem
    {A : Type*} [CommRing A] {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (q : Ideal A) [q.IsPrime]
    (X : Matrix ι ι A) (Y : Matrix ι κ A)
    (Z : Matrix κ ι A) (W : Matrix κ κ A)
    (hY : ∀ i j, Y i j ∈ q) (hX : X.det ∉ q) (hW : W.det ∉ q) :
    (Matrix.fromBlocks X Y Z W).det ∉ q := by
  let f : A →+* A ⧸ q := Ideal.Quotient.mk q
  have hYzero : Y.map f = 0 := by
    ext i j
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hY i j)
  intro hdet
  have hz : f (Matrix.fromBlocks X Y Z W).det = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hdet
  rw [RingHom.map_det] at hz
  change ((Matrix.fromBlocks X Y Z W).map f).det = 0 at hz
  rw [Matrix.fromBlocks_map, hYzero,
    Matrix.det_fromBlocks_zero₁₂] at hz
  change (f.mapMatrix X).det * (f.mapMatrix W).det = 0 at hz
  rw [← RingHom.map_det, ← RingHom.map_det] at hz
  exact mul_ne_zero
    ((Ideal.Quotient.eq_zero_iff_mem).not.mpr hX)
    ((Ideal.Quotient.eq_zero_iff_mem).not.mpr hW) hz

lemma isSmoothAt_of_factorization_through_formallySmooth
    {R A P : Type*} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] [Algebra.FormallySmooth R P]
    (q : Ideal A) [q.IsPrime]
    (h : A →ₐ[R] P) (f : P →ₐ[R] Localization.AtPrime q)
    (hf : f.comp h = IsScalarTower.toAlgHom R A (Localization.AtPrime q)) :
    Algebra.IsSmoothAt R q := by
  let M := q.primeCompl.map h.toMonoidHom
  let W := Localization M
  let T := Localization.AtPrime q
  let h' : A →ₐ[R] W := (IsScalarTower.toAlgHom R P W).comp h
  have hgu (s : q.primeCompl) : IsUnit (h' s) :=
    IsLocalization.map_units W (⟨h s, ⟨s, s.property, rfl⟩⟩ : M)
  let G : T →ₐ[R] W := IsLocalization.liftAlgHom hgu
  have hfu (s : M) : IsUnit (f s) := by
    obtain ⟨a, ha, hea⟩ := s.property
    change h a = s at hea
    rw [← hea, show f (h a) = algebraMap A T a from DFunLike.congr_fun hf a]
    exact IsLocalization.map_units T (⟨a, ha⟩ : q.primeCompl)
  let F : W →ₐ[R] T := IsLocalization.liftAlgHom hfu
  have hFG : F.comp G = AlgHom.id R T := by
    apply IsLocalization.algHom_ext q.primeCompl
    ext a
    show F (G (algebraMap A T a)) = algebraMap A T a
    rw [show G (algebraMap A T a) = h' a from IsLocalization.lift_eq hgu a]
    show F (algebraMap P W (h a)) = algebraMap A T a
    exact (IsLocalization.lift_eq hfu (h a)).trans (DFunLike.congr_fun hf a)
  let : Algebra.FormallySmooth R W := Algebra.FormallySmooth.comp R P W
  exact formallySmooth_of_retraction F G hFG

lemma isSmoothAt_of_surjective_of_localized_kernel
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (q : Ideal B) [q.IsPrime]
    (hsm : Algebra.IsSmoothAt R (q.comap f.toRingHom))
    (hker : RingHom.ker f.toRingHom ≤
      RingHom.ker (algebraMap A (Localization.AtPrime (q.comap f.toRingHom)))) :
    Algebra.IsSmoothAt R q := by
  let p := q.comap f.toRingHom
  let U := Localization.AtPrime p
  let V := Localization.AtPrime q
  let ι : A →ₐ[R] U := IsScalarTower.toAlgHom R A U
  let κ : B →ₐ[R] V := IsScalarTower.toAlgHom R B V
  let g : B →ₐ[R] U := f.liftOfSurjective hf ι hker
  have hg (x : A) : g (f x) = ι x := AlgHom.liftOfSurjective_apply ..
  have hfu (a : p.primeCompl) : IsUnit ((κ.comp f) a) :=
    IsLocalization.map_units V (⟨f a, a.property⟩ : q.primeCompl)
  let F : U →ₐ[R] V := IsLocalization.liftAlgHom hfu
  let : Algebra.FormallySmooth R U := hsm
  refine isSmoothAt_of_factorization_through_formallySmooth q g F ?_
  ext b
  obtain ⟨a, rfl⟩ := hf b
  change F (g (f a)) = algebraMap B V (f a)
  rw [hg]
  exact IsLocalization.lift_eq hfu a

private lemma zero_of_unit_linear_relations_in_maximalIdeal
    {A ι : Type*} [CommRing A] [IsLocalRing A] [Fintype ι]
    (x : ι → A) (a : A) (ha : IsUnit a)
    (H : ι → ι → A)
    (hH : ∀ i j, H i j ∈ IsLocalRing.maximalIdeal A)
    (hrel : ∀ i, a * x i = ∑ j, H i j * x j) :
    ∀ i, x i = 0 := by
  let I : Ideal A := Ideal.span (Set.range x)
  have hfg : I.FG := Submodule.fg_span (Set.finite_range x)
  have hle : I ≤ IsLocalRing.maximalIdeal A * I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (Ideal.unit_mul_mem_iff_mem _ ha).mp
    rw [hrel i]
    apply Ideal.sum_mem
    intro j _
    exact Ideal.mul_mem_mul (hH i j) (Ideal.subset_span ⟨j, rfl⟩)
  have hbot : I = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal A) I hfg
      (by simpa only [Ideal.smul_eq_mul] using hle)
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  intro i
  have hi : x i ∈ I := Ideal.subset_span ⟨i, rfl⟩
  rw [hbot] at hi
  simpa using hi

lemma relations_vanish_of_chart_equations
    {A γ : Type*} [CommRing A] [IsLocalRing A] [Fintype γ]
    (V : Finset γ) (π a : A) (r G z p : γ → A)
    (H : γ → V → A) (Q : γ → γ × γ → A)
    (ha : IsUnit a)
    (hsel : ∀ j : V, r j.1 = 0)
    (hp : ∀ l, l ∉ V → p l = 0)
    (hG : ∀ j, G j ∈ IsLocalRing.maximalIdeal A)
    (hπz : ∀ j, π * z j ∈ IsLocalRing.maximalIdeal A)
    (hidentity : ∀ l, l ∉ V → π * p l = -a * r l +
      (∑ j : V, H l j * r j.1) +
      (∑ ab : γ × γ,
        Q l ab * (r ab.1 * G ab.2 + π * z ab.1 * r ab.2))) :
    ∀ l, r l = 0 := by
  classical
  let B : γ → γ → A := fun l j =>
    if l ∈ V then 0 else
      (∑ b : γ, Q l (j, b) * G b) +
        (∑ b : γ, Q l (b, j) * π * z b)
  have hB (l j : γ) : B l j ∈ IsLocalRing.maximalIdeal A := by
    by_cases hl : l ∈ V
    · simp only [B, ite_eq_left hl]
      exact Ideal.zero_mem _
    · simp only [B, ite_eq_right hl]
      apply Ideal.add_mem
      · apply Ideal.sum_mem
        intro b _
        exact (IsLocalRing.maximalIdeal A).mul_mem_left _ (hG b)
      · apply Ideal.sum_mem
        intro b _
        have hb := hπz b
        have hmul : Q l (b, j) * (π * z b) ∈ IsLocalRing.maximalIdeal A :=
          (IsLocalRing.maximalIdeal A).mul_mem_left _ hb
        simpa only [mul_assoc] using hmul
  have hlin (l : γ) : a * r l = ∑ j : γ, B l j * r j := by
    by_cases hl : l ∈ V
    · have hr : r l = 0 := hsel ⟨l, hl⟩
      simp [B, hl, hr]
    · have hs : (∑ j : V, H l j * r j.1) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [hsel j]
      have hp0 := hp l hl
      have hid := hidentity l hl
      rw [hp0, mul_zero, hs, add_zero,
        quadratic_relation_as_linear π (Q l) r G z] at hid
      simp only [B, ite_eq_right hl]
      linear_combination hid
  exact zero_of_unit_linear_relations_in_maximalIdeal r a ha B hB hlin

end Stacks.Smoothing

end
