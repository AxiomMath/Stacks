module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# An infinite family of points meets the diagonal in its closure

Let `A` be a ring and `k` a field. Given pairwise distinct prime ideals of `A` whose residue
fields are `k`-algebras, the closure of the off-diagonal residue-field products in
`Spec(A ⊗ℤ A)` meets the diagonal.

## Main definitions

* `AlgebraicGeometry.Space.Decent.residuePairMap` is the ring map from `A ⊗ℤ A` to the
  tensor product over `k` of two residue fields of the family.
* `AlgebraicGeometry.Space.Decent.diagonalMap` is the multiplication map from `A ⊗ℤ A`
  to `A`.

## Main results

* `AlgebraicGeometry.Space.Decent.closure_iUnion_range_residuePairMap_meets_diagonal` is the
  infinite-points lemma.

## Implementation notes

The image of a disjoint union of spectra is represented as the union of the ranges of the
corresponding maps on prime spectra. The diagonal is likewise the range of the map on
spectra induced by multiplication `A ⊗ℤ A → A`.

The proof produces a point of the diagonal in the closure from a maximal ideal of the
product `∏ n, κ(p n)` containing the ideal of finitely supported families. Mathlib's
`PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite` forms that same ideal
inside its proof but exposes neither it nor the containment, so the two private lemmas
producing it are stated here.

## References

* [Stacks Project, Tag 088I](https://stacks.math.columbia.edu/tag/088I)
-/

@[expose] public section

open scoped TensorProduct
open Set

universe u v w

namespace AlgebraicGeometry.Space.Decent

variable (A : Type u) [CommRing A]
variable (k : Type v) [Field k]
variable (p : ℕ+ → PrimeSpectrum A)
variable [∀ n, Algebra k (p n).asIdeal.ResidueField]

/-- A field containing, as a `k`-algebra, every member of a finite subfamily of a family of
field extensions of `k`. -/
private structure CommonFieldOver (k : Type v) [Field k] (ι : Type u) (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] (s : Finset ι) where
  /-- The underlying type of the common extension. -/
  carrier : Type (max v w)
  /-- Its field structure. -/
  fieldInst : Field carrier
  /-- Its `k`-algebra structure. -/
  algebraInst : Algebra k carrier
  /-- The embedding of each member of the subfamily. -/
  emb : ∀ i, i ∈ s → K i →ₐ[k] carrier

/-- Any finite subfamily of a family of field extensions of `k` admits a common extension. -/
private lemma exists_common_field_over_finset {ι : Type u} (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] (s : Finset ι) :
    Nonempty (CommonFieldOver k ι K s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨⟨ULift.{max v w} k, inferInstance, inferInstance, fun i hi => by simp at hi⟩⟩
  | @insert i s his ih =>
      obtain ⟨h⟩ := ih
      let : Field h.carrier := h.fieldInst
      let : Algebra k h.carrier := h.algebraInst
      obtain ⟨L, hL, hLK, hLE, hLi, hkl, hki⟩ :=
        exists_common_extension k h.carrier (K i)
      let : Field L := hL
      let : Algebra k L := hLK
      let : Algebra h.carrier L := hLE
      let : Algebra (K i) L := hLi
      let : IsScalarTower k h.carrier L := hkl
      let : IsScalarTower k (K i) L := hki
      refine ⟨⟨L, hL, hLK, fun j hj => ?_⟩⟩
      by_cases hji : j = i
      · subst j
        exact IsScalarTower.toAlgHom k (K i) L
      · exact (IsScalarTower.toAlgHom k h.carrier L).comp (h.emb j (by simpa [hji] using hj))

/-- The ideal of finitely supported families in a product of commutative rings. -/
private noncomputable def finiteSupportIdeal {ι : Type*} (K : ι → Type*)
    [∀ i, CommRing (K i)] : Ideal (∀ i, K i) := by
  classical
  exact
    { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
      smul_mem' := by
        rintro r _ ⟨x, rfl⟩
        refine ⟨.mk x.support fun i ↦ r i * x i, funext fun i ↦ ?_⟩
        simp only [DFinsupp.coeFnAddMonoidHom]
        by_cases hi : i ∈ x.support
        · simp [hi]
        · simp [DFinsupp.notMem_support_iff.mp hi] }

/-- In an infinite product of fields, the ideal of finitely supported families is contained
in a maximal ideal. -/
private lemma exists_maximal_over_finiteSupportIdeal {ι : Type*} (K : ι → Type*)
    [∀ i, Field (K i)] [Infinite ι] :
    ∃ I : Ideal (∀ i, K i), I.IsMaximal ∧ finiteSupportIdeal K ≤ I := by
  classical
  refine (finiteSupportIdeal K).exists_le_maximal fun h => ?_
  obtain ⟨x, hx⟩ := (Ideal.eq_top_iff_one _).mp h
  obtain ⟨i, hi⟩ := x.support.exists_notMem
  simpa [DFinsupp.coeFnAddMonoidHom, DFinsupp.notMem_support_iff.mp hi] using congr_fun hx i

/-- A family with finite support lies in the ideal of finitely supported families. -/
private lemma finite_support_mem_finiteSupportIdeal {ι : Type*} (K : ι → Type*)
    [∀ i, CommRing (K i)] (x : ∀ i, K i) (hx : {i | x i ≠ 0}.Finite) :
    x ∈ finiteSupportIdeal K := by
  classical
  let s := hx.toFinset
  let y : Π₀ i, K i := DFinsupp.mk s (fun i : (↑s : Set ι) => x i.1)
  refine ⟨y, ?_⟩
  ext i
  by_cases hi : i ∈ s
  · simp [DFinsupp.coeFnAddMonoidHom, y, s, hi]
  · have hxi : x i = 0 := by simpa [s] using hi
    simp [DFinsupp.coeFnAddMonoidHom, y, s, hi, hxi]

/-- A family outside an ideal containing the finitely supported families has infinite
support. -/
private lemma infinite_support_of_not_mem_finiteSupportIdeal {ι : Type*} (K : ι → Type*)
    [∀ i, CommRing (K i)] (M : Ideal (∀ i, K i))
    (hM : finiteSupportIdeal K ≤ M) (x : ∀ i, K i) (hx : x ∉ M) :
    {i | x i ≠ 0}.Infinite :=
  fun hfinite => hx (hM (finite_support_mem_finiteSupportIdeal K x hfinite))

/-- There is no pair of families of `r`-tuples over a field, indexed by `r + 1` elements,
whose pairings are nonzero on the diagonal and vanish off it. -/
private lemma scalar_matrix_no_offDiagonal {L : Type*} [Field L] (r : ℕ)
    (a b : Fin (r + 1) → Fin r → L)
    (hdiag : ∀ i, (∑ t, a i t * b i t) ≠ 0)
    (hoff : ∀ i j, i ≠ j → (∑ t, a i t * b j t) = 0) : False := by
  let F : (Fin (r + 1) → L) →ₗ[L] (Fin r → L) :=
    { toFun := fun c t => ∑ i, c i * a i t
      map_add' x y := by
        ext t
        simp [Finset.sum_add_distrib, add_mul]
      map_smul' c x := by
        ext t
        simp [Finset.mul_sum, mul_assoc] }
  obtain ⟨c, hc, hcn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := F) (by simp))
  have hcval : ∀ j, c j = 0 := by
    intro j
    have hsum : (∑ t, (F c) t * b j t) = 0 := by simp [LinearMap.mem_ker.mp hc]
    have hfactor : (∑ t, (F c) t * b j t) = ∑ i, c i * (∑ t, a i t * b j t) := by
      simp only [F, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    have hsparse : (∑ i, c i * (∑ t, a i t * b j t)) = c j * (∑ t, a j t * b j t) :=
      Finset.sum_eq_single j (fun i _ hij => by simp [hoff i j hij]) (by simp)
    rw [hfactor, hsparse] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right (hdiag j)
  exact hcn (funext hcval)

section Family

variable {ι : Type*} (q : ι → PrimeSpectrum A)
variable [∀ i, Algebra k (q i).asIdeal.ResidueField]

/-- The map from `A ⊗ℤ A` to the tensor product of the residue fields at two
members of the family. -/
noncomputable def residuePairMap (n m : ι) :
    A ⊗[ℤ] A →+* (q n).asIdeal.ResidueField ⊗[k] (q m).asIdeal.ResidueField := by
  letI : Algebra ℤ ((q n).asIdeal.ResidueField ⊗[k] (q m).asIdeal.ResidueField) :=
    Ring.toIntAlgebra _
  exact (Algebra.TensorProduct.productMap
    (((Algebra.TensorProduct.includeLeft
      (R := k) (S := k) (A := (q n).asIdeal.ResidueField)
      (B := (q m).asIdeal.ResidueField)).toRingHom.comp
        (algebraMap A (q n).asIdeal.ResidueField)).toIntAlgHom)
    (((Algebra.TensorProduct.includeRight
      (R := k) (A := (q n).asIdeal.ResidueField)
      (B := (q m).asIdeal.ResidueField)).toRingHom.comp
        (algebraMap A (q m).asIdeal.ResidueField)).toIntAlgHom)).toRingHom

end Family

/-- The multiplication map inducing the diagonal `Spec(A) → Spec(A ⊗ℤ A)`. -/
noncomputable def diagonalMap : A ⊗[ℤ] A →+* A :=
  (Algebra.TensorProduct.productMap
    (RingHom.id A).toIntAlgHom (RingHom.id A).toIntAlgHom).toRingHom

/-- Evaluating `residuePairMap` through a common extension of the two residue fields is the
product map of the two evaluations. -/
private lemma residuePairMap_commonField_eval (n m : ℕ+) {L : Type*} [Field L]
    [Algebra k L] (en : (p n).asIdeal.ResidueField →ₐ[k] L)
    (em : (p m).asIdeal.ResidueField →ₐ[k] L) :
    (Algebra.TensorProduct.lift en em (fun _ _ => Commute.all _ _)).toRingHom.comp
        (residuePairMap A k p n m) =
      (Algebra.TensorProduct.productMap
        ((en.toRingHom.comp (algebraMap A (p n).asIdeal.ResidueField)).toIntAlgHom)
        ((em.toRingHom.comp
          (algebraMap A (p m).asIdeal.ResidueField)).toIntAlgHom)).toRingHom := by
  classical
  let : Algebra ℤ L := Ring.toIntAlgebra _
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [residuePairMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The closure of the union of the off-diagonal products of residue-field spectra
meets the diagonal in `Spec(A ⊗ℤ A)`. -/
@[stacks 088I]
lemma closure_iUnion_range_residuePairMap_meets_diagonal (_hp : Function.Injective p) :
    (closure (⋃ n, ⋃ m, ⋃ (_ : n ≠ m),
        range (PrimeSpectrum.comap (residuePairMap A k p n m))) ∩
      range (PrimeSpectrum.comap (diagonalMap A))).Nonempty := by
  classical
  let K : ℕ+ → Type u := fun n => (p n).asIdeal.ResidueField
  let B : Type u := ∀ n, K n
  let : ∀ n, Field (K n) := fun n => inferInstance
  let : ∀ n, Algebra k (K n) := fun n => inferInstance
  let ρ : ∀ n, A →+* K n := fun n => algebraMap A (K n)
  let f : A →+* B := RingHom.pi ρ
  obtain ⟨M, hM, hMF⟩ := exists_maximal_over_finiteSupportIdeal K
  let : Field (B ⧸ M) := Ideal.Quotient.field M
  let fbar : A →+* B ⧸ M := (Ideal.Quotient.mk M).comp f
  let q : PrimeSpectrum A := PrimeSpectrum.comap fbar ⊥
  let : Algebra ℤ A := Ring.toIntAlgebra _
  let : Algebra ℤ B := Ring.toIntAlgebra _
  let δ : A ⊗[ℤ] A →+* B :=
    (Algebra.TensorProduct.productMap f.toIntAlgHom f.toIntAlgHom).toRingHom
  have hfactor (z : A ⊗[ℤ] A) : Ideal.Quotient.mk M (δ z) = fbar (diagonalMap A z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [δ, fbar, diagonalMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨PrimeSpectrum.comap (diagonalMap A) q, ?_, q, rfl⟩
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.mem_zeroLocus]
  intro x hx
  rw [SetLike.mem_coe, PrimeSpectrum.mem_vanishingIdeal] at hx
  by_contra hxnot
  obtain ⟨r, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq x
  obtain ⟨s, hsSub, hsCard⟩ :=
    (infinite_support_of_not_mem_finiteSupportIdeal K M hMF (δ x)
      fun h => hxnot ((hfactor x).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h)))
      |>.exists_subset_card_eq (r + 1)
  let e : s ≃ Fin (r + 1) := s.equivFinOfCardEq hsCard
  obtain ⟨hL⟩ := exists_common_field_over_finset k K s
  let : Field hL.carrier := hL.fieldInst
  let : Algebra k hL.carrier := hL.algebraInst
  let nfun : Fin (r + 1) → ℕ+ := fun i => (e.symm i).1
  let en (i : Fin (r + 1)) : K (nfun i) →ₐ[k] hL.carrier :=
    hL.emb (nfun i) (e.symm i).2
  let eval (i : Fin (r + 1)) : A →+* hL.carrier :=
    (en i).toRingHom.comp (ρ (nfun i))
  let av : Fin (r + 1) → Fin r → hL.carrier := fun i t => eval i (a t)
  let bv : Fin (r + 1) → Fin r → hL.carrier := fun i t => eval i (b t)
  have hdiag : ∀ i, (∑ t, av i t * bv i t) ≠ 0 := by
    intro i hzero
    have hdi : δ x (nfun i) ≠ 0 := hsSub (e.symm i).2
    have hbase : δ x (nfun i) = ∑ t, ρ (nfun i) (a t) * ρ (nfun i) (b t) := by
      rw [hab]
      change (Pi.evalRingHom K (nfun i)) (δ (∑ t, a t ⊗ₜ[ℤ] b t)) = _
      simp only [δ, map_sum]
      change (∑ t, f (a t) (nfun i) * f (b t) (nfun i)) = _
      rfl
    have heq : en i (δ x (nfun i)) = ∑ t, av i t * bv i t := by
      rw [hbase]
      simp [av, bv, eval]
    exact hdi ((en i).injective (by simpa using heq.trans hzero))
  have hoff : ∀ i j, i ≠ j → (∑ t, av i t * bv j t) = 0 := by
    intro i j hij
    let ni := nfun i
    let nj := nfun j
    have hne : ni ≠ nj := fun heq => hij (e.symm.injective (Subtype.ext heq))
    let ev := Algebra.TensorProduct.lift (en i) (en j) (fun _ _ => Commute.all _ _)
    let pt : PrimeSpectrum (K ni ⊗[k] K nj) := PrimeSpectrum.comap ev.toRingHom ⊥
    have hmem : x ∈ (PrimeSpectrum.comap (residuePairMap A k p ni nj) pt).asIdeal := by
      apply hx
      simp only [Set.mem_iUnion]
      exact ⟨ni, nj, hne, pt, rfl⟩
    have hev : ev (residuePairMap A k p ni nj x) = 0 := by
      simpa [pt, PrimeSpectrum.comap_asIdeal] using hmem
    have hscalar :
        (Algebra.TensorProduct.productMap
          ((en i).toRingHom.comp (ρ ni)).toIntAlgHom
          ((en j).toRingHom.comp (ρ nj)).toIntAlgHom).toRingHom x = 0 := by
      rwa [← residuePairMap_commonField_eval A k p ni nj (en i) (en j)]
    rw [hab] at hscalar
    simpa [av, bv, eval, ni, nj, ρ] using hscalar
  exact scalar_matrix_no_offDiagonal r av bv hdiag hoff

end AlgebraicGeometry.Space.Decent

end
