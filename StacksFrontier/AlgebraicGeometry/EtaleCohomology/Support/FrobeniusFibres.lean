module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibres of an injective Frobenius-semilinear map

Let `k` be an algebraically closed field of characteristic `p > 0` and let `V` be a
finite-dimensional `k`-vector space. If `F` is an injective additive endomorphism of `V` which
is semilinear for the `p`-power Frobenius, then every fibre of `F - 1` has exactly
`p ^ finrank k V` elements.

This is the counting input to the Artin–Schreier description of étale cohomology in
characteristic `p`: the scalar case `p = 1`-dimensional is the fibre count of `t ↦ t ^ p - t`,
and the general case reduces to it in a basis of `F`-fixed vectors.

## Main results

* `AlgebraicGeometry.natCard_fiber_sub_id_eq` — every fibre of `F - 1` has `p ^ finrank k V`
  elements.

## Implementation notes

Frobenius semilinearity is stated explicitly on an additive homomorphism rather than through
the semilinear-map bundling, because that is the form in which the endomorphism arises and the
form the consumers use.

The proof constructs a basis of `F`-fixed vectors. A nonzero fixed vector comes from a minimal
linear dependence among the successive iterates `F^[i] x`: the dependence yields an additive
polynomial of degree `p ^ (n+1)` whose derivative is `0`, so subtracting `X` gives a separable
polynomial with a nonzero root, and that root assembles a fixed vector. Applying the
construction to the quotient by the span of the fixed vectors shows that the fixed vectors span
`V`. In a fixed basis the fibres of `F - 1` are products of fibres of the scalar
Artin–Schreier map `t ↦ t ^ p - t`, each of which has exactly `p` elements.

## References

* [Stacks Project, Tag 0A3L](https://stacks.math.columbia.edu/tag/0A3L)
-/

@[expose] public section

open Polynomial

namespace AlgebraicGeometry

/-- An injective Frobenius-semilinear endomorphism of a finite-dimensional space over an
algebraically closed field is surjective. -/
private lemma frobeniusSemilinear_surjective
    {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (p : ℕ) (hp : 0 < p) [FiniteDimensional k V]
    (F : V →+ V) (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v)
    (hF_injective : Function.Injective F) : Function.Surjective F := by
  classical
  let b := Module.finBasis k V
  have hli : LinearIndependent k (fun i : Fin (Module.finrank k V) => F (b i)) :=
    b.linearIndependent.map_of_surjective_injectiveₛ (fun c : k => c ^ p) F
      (fun c => IsAlgClosed.exists_pow_nat_eq c hp) hF_injective hF
  have hspan : Submodule.span k (Set.range fun i : Fin (Module.finrank k V) => F (b i)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  let W : Submodule k V := {
    carrier := Set.range F
    zero_mem' := ⟨0, map_zero F⟩
    add_mem' := by
      rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, map_add F a b⟩
    smul_mem' := by
      rintro c _ ⟨v, rfl⟩
      obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hp
      exact ⟨d • v, by rw [hF, hd]⟩ }
  have hW : W = ⊤ := top_unique <| by
    rw [← hspan]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ⟨b i, rfl⟩)
  exact fun y => show y ∈ W by simp [hW]

/-- A polynomial whose derivative is `-1` is separable. -/
private lemma separable_of_derivative_eq_neg_one {k : Type*} [Field k] {P : k[X]}
    (hder : derivative P = -1) : P.Separable := by
  rw [separable_def, hder]
  exact isCoprime_one_right.neg_right

/-- A polynomial of degree greater than one whose derivative is `-1` is separable, hence has a
nonzero root over an algebraically closed field. -/
private lemma exists_nonzero_root {k : Type*} [Field k] [IsAlgClosed k]
    (P : k[X]) (hdeg : 1 < P.natDegree) (hder : derivative P = -1) :
    ∃ t : k, t ≠ 0 ∧ P.eval t = 0 := by
  classical
  have hcard := Polynomial.card_rootSet_eq_natDegree (separable_of_derivative_eq_neg_one hder)
    (IsAlgClosed.splits (P.map (algebraMap k k)))
  by_contra! h
  have he : ∀ x : P.rootSet k, (x : k) = 0 := by
    intro x
    by_contra hx
    exact h x hx ((Polynomial.mem_rootSet.mp x.property).2)
  have : Fintype.card (P.rootSet k) ≤ 1 :=
    Fintype.card_le_one_iff.mpr fun x y => Subtype.ext ((he x).trans (he y).symm)
  omega

/-- The additive polynomial attached to a linear dependence among the iterates of a
Frobenius-semilinear map: `Q 0 = 0` and `Q (i+1) = (Q i) ^ p + a i * X ^ p`. -/
private noncomputable def orbitPolynomial {k : Type*} [Field k] (p : ℕ) (a : ℕ → k) : ℕ → k[X]
  | 0 => 0
  | i + 1 => (orbitPolynomial p a i) ^ p + C (a i) * X ^ p

/-- The orbit polynomial of a dependence with nonzero leading coefficient has degree
`p ^ (i+1)`. -/
private lemma orbitPolynomial_degree {k : Type*} [Field k] (p : ℕ) (hp : 1 < p)
    (a : ℕ → k) (ha : a 0 ≠ 0) (i : ℕ) :
    (orbitPolynomial p a (i + 1)).natDegree = p ^ (i + 1) := by
  induction i with
  | zero => simp [orbitPolynomial, (zero_lt_one.trans hp).ne', natDegree_C_mul ha]
  | succ i ih =>
    have hlt : (C (a (i + 1)) * X ^ p).natDegree <
        (orbitPolynomial p a (i + 1) ^ p).natDegree := by
      calc
        (C (a (i + 1)) * X ^ p).natDegree ≤ p := natDegree_C_mul_X_pow_le _ _
        _ < (orbitPolynomial p a (i + 1) ^ p).natDegree := by
          rw [natDegree_pow, ih]
          have : 1 < p ^ (i + 1) := one_lt_pow₀ hp (by omega)
          nlinarith
    rw [orbitPolynomial, natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_pow, ih]
    simp [pow_succ, mul_comm]

/-- The orbit polynomial is additive, so its derivative vanishes in characteristic `p`. -/
private lemma orbitPolynomial_derivative {k : Type*} [Field k] (p : ℕ) [CharP k p]
    (a : ℕ → k) (i : ℕ) : derivative (orbitPolynomial p a i) = 0 := by
  cases i with
  | zero => simp [orbitPolynomial]
  | succ i => simp [orbitPolynomial, derivative_pow, derivative_mul]

/-- A nonzero vector generates a minimal linear dependence among its iterates under an injective
Frobenius-semilinear map, with nonzero coefficient in degree zero. -/
private lemma cyclic_relation {k V : Type*} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (p : ℕ) (hp : 0 < p) (F : V →+ V)
    (hF : ∀ c : k, ∀ v : V, F (c • v) = c ^ p • F v)
    (hinj : Function.Injective F) (x : V) (hx : x ≠ 0) :
    ∃ (n : ℕ) (v : ℕ → V) (a : ℕ → k),
      (∀ i, F (v i) = v (i + 1)) ∧
      LinearIndependent k (fun i : Fin (n + 1) => v i) ∧
      a 0 ≠ 0 ∧ v (n + 1) = ∑ i ∈ Finset.range (n + 1), a i • v i := by
  classical
  let v : ℕ → V := fun i => F^[i] x
  have hv : ∀ i, F (v i) = v (i + 1) := fun i => (Function.iterate_succ_apply' F i x).symm
  have hex : ∃ n, ¬ LinearIndependent k (fun i : Fin (n + 1) => v i) := by
    refine ⟨Module.finrank k V, fun h => ?_⟩
    have := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  generalize hmdef : Nat.find hex = m
  have hbad : ¬ LinearIndependent k (fun i : Fin (m + 1) => v i) := hmdef ▸ Nat.find_spec hex
  have hli : LinearIndependent k (fun i : Fin m => v i) := by
    cases hm : m with
    | zero => exact linearIndependent_empty_type
    | succ j =>
      have hj : j < Nat.find hex := by omega
      simpa only [hm, not_not] using Nat.find_min hex hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := m) <| by
    rintro rfl
    refine hbad ?_
    change LinearIndependent k (fun i : Fin 1 => v i)
    rw [linearIndependent_unique_iff]
    simpa [v] using hx
  have hdep : v (n + 1) ∈ Submodule.span k (Set.range (fun i : Fin (n + 1) => v i)) := by
    rw [linearIndependent_finSucc'] at hbad
    by_contra h
    exact hbad ⟨hli, h⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hdep
  have hshift : LinearIndependent k (fun i : Fin (n + 1) => v (i + 1)) := by
    have h := hli.map_of_surjective_injectiveₛ
      (fun c : k => c ^ p) F (fun c => IsAlgClosed.exists_pow_nat_eq c hp) hinj hF
    change LinearIndependent k (fun i : Fin (n + 1) => F (v i)) at h
    simpa only [hv] using h
  have ha0 : a 0 ≠ 0 := by
    intro ha0
    have hnmem := (linearIndependent_finSucc'.mp hshift).2
    apply hnmem
    change v (n + 1) ∈ Submodule.span k (Set.range (fun i : Fin n => v (i + 1)))
    rw [← ha, Fin.sum_univ_succ, ha0, zero_smul, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  let a' : ℕ → k := fun i => if h : i < n + 1 then a ⟨i, h⟩ else 0
  refine ⟨n, v, a', hv, hli, ?_, ?_⟩
  · simpa [a'] using ha0
  · rw [← ha, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [show a' i = a i from dite_eq_left i.isLt]

/-- A minimal dependence among the iterates produces a nonzero `F`-fixed vector. -/
private lemma fixedVector_of_cyclic_relation
    {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (p : ℕ) [CharP k p] (hp : 1 < p) (F : V →+ V)
    (hF : ∀ c : k, ∀ v : V, F (c • v) = c ^ p • F v)
    (n : ℕ) (v : ℕ → V) (a : ℕ → k)
    (hv : ∀ i, F (v i) = v (i + 1))
    (hli : LinearIndependent k (fun i : Fin (n + 1) => v i))
    (ha : a 0 ≠ 0) (hrel : v (n + 1) = ∑ i ∈ Finset.range (n + 1), a i • v i) :
    ∃ w : V, w ≠ 0 ∧ F w = w := by
  classical
  let Q := orbitPolynomial p a
  have hdeg : 1 < (Q (n + 1)).natDegree := by
    rw [orbitPolynomial_degree p hp a ha]
    exact one_lt_pow₀ hp (by omega)
  obtain ⟨t, ht, hroot⟩ := exists_nonzero_root (Q (n + 1) - X)
    (by rwa [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hdeg)])
    (by simp only [derivative_sub, orbitPolynomial_derivative, derivative_X, zero_sub, Q])
  let c : ℕ → k := fun i => (Q i).eval t
  have hc0 : c 0 = 0 := by simp [c, Q, orbitPolynomial]
  have hcn : c (n + 1) = t := sub_eq_zero.mp (by simpa only [eval_sub, eval_X] using hroot)
  have hc : ∀ i, c (i + 1) = c i ^ p + a i * t ^ p := fun i => by simp [c, Q, orbitPolynomial]
  let w := ∑ i ∈ Finset.range (n + 1), c (i + 1) • v i
  refine ⟨w, ?_, ?_⟩
  · intro hw
    have hz : ∑ i : Fin (n + 1), c (i + 1) • v i = 0 := by
      rwa [Fin.sum_univ_eq_sum_range (fun i => c (i + 1) • v i)]
    exact ht (hcn.symm.trans (Fintype.linearIndependent_iff.mp hli _ hz (Fin.last n)))
  · calc
      F w = ∑ i ∈ Finset.range (n + 1), c (i + 1) ^ p • v (i + 1) := by
        simp only [w, map_sum, hF, hv]
      _ = (∑ i ∈ Finset.range n, c (i + 1) ^ p • v (i + 1)) + t ^ p • v (n + 1) := by
        rw [Finset.sum_range_succ, hcn]
      _ = (∑ i ∈ Finset.range (n + 1), c i ^ p • v i) +
          ∑ i ∈ Finset.range (n + 1), (a i * t ^ p) • v i := by
        rw [Finset.sum_range_succ', hc0, zero_pow (by omega : p ≠ 0), zero_smul,
          add_zero, hrel, Finset.smul_sum]
        simp only [smul_smul, mul_comm]
      _ = w := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [← add_smul, ← hc]

/-- An injective Frobenius-semilinear map on a nonzero space has a nonzero fixed vector. -/
private lemma exists_nonzero_fixedVector
    {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (p : ℕ) [CharP k p] (hp : 1 < p)
    (F : V →+ V) (hF : ∀ c : k, ∀ v : V, F (c • v) = c ^ p • F v)
    (hinj : Function.Injective F) (x : V) (hx : x ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ F w = w := by
  obtain ⟨n, v, a, hv, hli, ha, hrel⟩ := cyclic_relation p (by omega) F hF hinj x hx
  exact fixedVector_of_cyclic_relation p hp F hF n v a hv hli ha hrel

/-- The Artin–Schreier polynomial `X ^ p - X - C c` has degree `p`. -/
private lemma natDegree_pow_sub_X_sub_C {k : Type*} [Field k] (p : ℕ) (hp : 1 < p) (c : k) :
    (X ^ p - X - C c : k[X]).natDegree = p := by
  rw [natDegree_sub_C, natDegree_sub_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow p
  · simpa using hp

/-- Over an algebraically closed field the scalar Artin–Schreier map `t ↦ t ^ p - t` is
surjective. -/
private lemma exists_pow_sub_eq {k : Type*} [Field k] [IsAlgClosed k]
    (p : ℕ) (hp : 1 < p) (c : k) : ∃ t : k, t ^ p - t = c := by
  have hd := natDegree_pow_sub_X_sub_C p hp c
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (X ^ p - X - C c : k[X])
    (natDegree_pos_iff_degree_pos.mp (by omega)).ne'
  exact ⟨t, sub_eq_zero.mp (by simpa only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] using ht)⟩

/-- On the span of the `F`-fixed vectors, `F - 1` is surjective. -/
private lemma sub_id_surjective_on_fixed_span
    {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (p : ℕ) (hp : 1 < p) (F : V →+ V)
    (hF : ∀ c : k, ∀ v : V, F (c • v) = c ^ p • F v)
    {y : V} (hy : y ∈ Submodule.span k {v | F v = v}) :
    ∃ x ∈ Submodule.span k {v | F v = v}, F x - x = y := by
  suffices h : ∀ c : k, ∃ x ∈ Submodule.span k {v | F v = v}, F x - x = c • y by
    simpa using h 1
  induction hy using Submodule.span_induction with
  | mem v hv =>
    intro c
    obtain ⟨t, ht⟩ := exists_pow_sub_eq p hp c
    refine ⟨t • v, Submodule.smul_mem _ _ (Submodule.subset_span hv), ?_⟩
    rw [hF, hv, ← sub_smul, ht]
  | zero => exact fun c => ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y hx hy ihx ihy =>
    intro c
    obtain ⟨u, hu, he⟩ := ihx c
    obtain ⟨v, hv, hf⟩ := ihy c
    refine ⟨u + v, Submodule.add_mem _ hu hv, ?_⟩
    rw [map_add, add_sub_add_comm, he, hf, smul_add]
  | smul a x hx ih =>
    intro c
    simpa only [smul_smul] using ih (c * a)

/-- The fixed vectors of an injective Frobenius-semilinear map span the whole space. -/
@[sga "7 XXII 1.1.10" "partial"]
private lemma span_fixedVectors_eq_top
    {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (p : ℕ) [Fact p.Prime] [CharP k p]
    (F : V →+ V) (hF : ∀ c : k, ∀ v : V, F (c • v) = c ^ p • F v)
    (hinj : Function.Injective F) : Submodule.span k {v | F v = v} = ⊤ := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let W := Submodule.span k {v | F v = v}
  let f : V →ₛₗ[frobenius k p] V := { F with map_smul' := hF }
  have hstable : W ≤ Submodule.comap f W := by
    apply Submodule.span_le.mpr
    intro v hv
    change F v ∈ W
    rw [hv]
    exact Submodule.subset_span hv
  let r : W →+ W := {
    toFun := fun x => ⟨F x, hstable x.property⟩
    map_zero' := Subtype.ext (map_zero F)
    map_add' := fun x y => Subtype.ext (map_add F (x : V) (y : V)) }
  have hr : ∀ c : k, ∀ x : W, r (c • x) = c ^ p • r x :=
    fun c x => Subtype.ext (hF c x)
  have hrinj : Function.Injective r := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have hrsurj := frobeniusSemilinear_surjective p (by omega) r hr hrinj
  let g := W.mapQ W f hstable
  have hg : ∀ c : k, ∀ x : V ⧸ W, g (c • x) = c ^ p • g x := g.map_smulₛₗ
  have hginj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun z hz => by
    obtain ⟨v, rfl⟩ := W.mkQ_surjective z
    obtain ⟨w, hw⟩ := hrsurj ⟨F v, (Submodule.Quotient.mk_eq_zero W).mp hz⟩
    exact (Submodule.Quotient.mk_eq_zero W).mpr (hinj (congrArg Subtype.val hw) ▸ w.property)
  by_contra htop
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr htop)
  obtain ⟨z, hz, hgz⟩ := exists_nonzero_fixedVector p hp g.toAddMonoidHom hg hginj
    (W.mkQ x) (fun h => hx ((Submodule.Quotient.mk_eq_zero W).mp h))
  obtain ⟨v, rfl⟩ := W.mkQ_surjective z
  have hdiff : F v - v ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ (F v - v) = 0
    rw [map_sub]
    change g (W.mkQ v) - W.mkQ v = 0
    exact sub_eq_zero.mpr hgz
  obtain ⟨u, hu, he⟩ := sub_id_surjective_on_fixed_span p hp F hF hdiff
  have hfix : F (v - u) = v - u := by
    rw [map_sub, sub_eq_sub_iff_sub_eq_sub, he]
  have hvW : v ∈ W := by simpa using W.add_mem (Submodule.subset_span hfix) hu
  exact hz ((Submodule.Quotient.mk_eq_zero W).mpr hvW)

/-- Each fibre of the scalar Artin–Schreier map `t ↦ t ^ p - t` over an algebraically closed
field of characteristic `p` has exactly `p` elements. -/
private lemma natCard_pow_sub_fiber {k : Type*} [Field k] [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : 1 < p) (c : k) :
    Nat.card {x : k // x ^ p - x = c} = p := by
  classical
  let P : k[X] := X ^ p - X - C c
  have hd : P.natDegree = p := natDegree_pow_sub_X_sub_C p hp c
  have hsep : P.Separable :=
    separable_of_derivative_eq_neg_one (by simp [P, derivative_pow])
  let e : {x : k // x ^ p - x = c} ≃ P.rootSet k := Equiv.subtypeEquivRight (fun x => by
    rw [mem_rootSet, and_iff_right hsep.ne_zero]
    simp only [P, map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_self_apply]
    exact sub_eq_zero.symm)
  calc
    Nat.card {x : k // x ^ p - x = c} = Nat.card (P.rootSet k) := Nat.card_congr e
    _ = P.natDegree := by
      rw [Nat.card_eq_fintype_card]
      exact card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
    _ = p := hd

/-- In a basis of `F`-fixed vectors the fibres of `F - 1` are products of fibres of the scalar
Artin–Schreier map. -/
private lemma natCard_fiber_of_fixed_basis
    {k V ι : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [Finite ι] (b : Module.Basis ι k V)
    (p : ℕ) [CharP k p] (hp : 1 < p) (F : V →+ V)
    (hF : ∀ c : k, ∀ v : V, F (c • v) = c ^ p • F v)
    (hb : ∀ i, F (b i) = b i) (y : V) :
    Nat.card {x : V // F x - x = y} = p ^ Module.finrank k V := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hbF (c : ι → k) : F (b.equivFun.symm c) = b.equivFun.symm (fun i => c i ^ p) := by
    simp only [Module.Basis.equivFun_symm_apply, map_sum, hF, hb]
  have heF (x : V) : b.equivFun (F x) = fun i => b.equivFun x i ^ p := by
    simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using
      congrArg b.equivFun (hbF (b.equivFun x))
  let e : {x : V // F x - x = y} ≃
      {c : ι → k // ∀ i, c i ^ p - c i = b.equivFun y i} :=
    b.equivFun.toEquiv.subtypeEquiv (fun x => by
      change F x - x = y ↔ ∀ i, b.equivFun x i ^ p - b.equivFun x i = b.equivFun y i
      refine ⟨fun h i => ?_, fun h => b.equivFun.injective (funext fun i => ?_)⟩
      · simpa only [map_sub, heF, Pi.sub_apply] using congrFun (congrArg b.equivFun h) i
      · simpa only [map_sub, heF, Pi.sub_apply] using h i)
  calc
    Nat.card {x : V // F x - x = y} =
        Nat.card (∀ i : ι, {c : k // c ^ p - c = b.equivFun y i}) :=
      Nat.card_congr (e.trans (Equiv.subtypePiEquivPi
        (p := fun i (c : k) => c ^ p - c = b.equivFun y i)))
    _ = ∏ i : ι, Nat.card {c : k // c ^ p - c = b.equivFun y i} := Nat.card_pi
    _ = p ^ Fintype.card ι := by
      simp only [natCard_pow_sub_fiber p hp, Finset.prod_const, Finset.card_univ]
    _ = p ^ Module.finrank k V := by rw [Module.finrank_eq_card_basis b]

/-- If `F` is an injective Frobenius-semilinear endomorphism of a finite-dimensional vector
space over an algebraically closed field of positive characteristic `p`, then every fibre of
`F - 1` has `p ^ finrank k V` elements. -/
public theorem natCard_fiber_sub_id_eq
    {k V : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (p : ℕ) [CharP k p] (hp : 0 < p) [FiniteDimensional k V]
    (F : V →+ V) (hF : ∀ (c : k) (v : V), F (c • v) = c ^ p • F v)
    (hF_injective : Function.Injective F) (y : V) :
    Nat.card {x : V // F x - x = y} = p ^ Module.finrank k V := by
  classical
  have hpprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right (by omega)
  have : Fact p.Prime := ⟨hpprime⟩
  have hs := span_fixedVectors_eq_top p F hF hF_injective
  let s := (linearIndepOn_empty k (id : V → V)).extend
    (Set.empty_subset {v : V | F v = v})
  let b : Module.Basis s k V := Module.Basis.ofSpan hs.ge
  have : Finite s := b.linearIndependent.finite
  exact natCard_fiber_of_fixed_basis b p hpprime.one_lt F hF
    (fun i => Module.Basis.ofSpan_subset hs.ge (Set.mem_range_self i)) y

end AlgebraicGeometry
