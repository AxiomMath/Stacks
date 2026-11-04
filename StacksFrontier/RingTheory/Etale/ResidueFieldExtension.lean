module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Realizing a finite separable residue field extension by an étale algebra

Let `R` be a ring, `p` a prime of `R` and `κ(p)` its residue field, and let `L/κ(p)` be a finite
separable field extension. This file proves Stacks 00UD: there are an étale ring map `R → R'` and
a prime `p'` of `R'` lying over `p` together with an isomorphism `κ(p') ≃+* L` carrying the
canonical map `κ(p) → κ(p')` to `κ(p) → L`.

The witness is the source's. By the primitive element theorem `L = κ(p)⟮α⟯`; let `f̄ = minpoly α`.
Because `κ(p)` is the fraction field of `R ⧸ p`, a single `c` clears the denominators of all the
coefficients of `f̄` at once, and rescaling the root by `c` — that is, passing from `f̄` to
`Polynomial.scaleRoots f̄ c`, whose `i`-th coefficient is `c ^ (n - i)` times that of `f̄` — makes
every coefficient come from `R`. So `f̄.scaleRoots c` lifts to a monic `f ∈ R[X]`, and `β = cα`
is a root of `f` at which `f'` is invertible, since `f̄` is separable and `c` is a unit. The pair
`(f, f')` is a `StandardEtalePair R`, whose standard étale algebra `R' = R[x, 1/f']/(f)` is étale;
`x ↦ β` is an `R`-algebra map `R' → L`, and `p'` is its kernel. Finally `κ(p') → L` is the
extension of the injection `R' ⧸ p' ↪ L` to fraction fields, and it is onto because its image is
a subfield of `L` containing `κ(p)` and `β`, hence contains `κ(p)⟮β⟯ = L`.

## Main results

* `Stacks.Etale.ResidueFieldRealization.solution`: Stacks 00UD.

## Implementation notes

The source says "after replacing `α` by `cα` for some `c ∈ R`, `c ∉ p`, we may assume all the
coefficients of `f̄` are in the image of `R → κ(p)`" and omits the verification. The verification
is `exists_isUnit_and_scaleRoots_mem_lifts` together with
`scaleRoots_aeval_derivative_mul`: the first produces the common denominator from
`IsLocalization.exist_integer_multiples` for the fraction field `κ(p)` of `R ⧸ p`, using that
`c ^ (n - i) * f̄.coeff i = c ^ (n - i - 1) * (c * f̄.coeff i)` for `i < n` while the leading
coefficient is untouched; the second is the identity
`(f̄.scaleRoots c)'(cx) = c ^ (n - 1) * f̄'(x)`, which is what turns separability of `f̄` at `α`
into invertibility of the derivative at `β`. Note that `c` is produced as a unit of `κ(p)`, not as
an element of `R ∖ p`; the two are interchangeable here (`κ(p)` is the fraction field of `R ⧸ p`),
and the unit form is what both uses need.

`scaleRoots_aeval_derivative_mul` is the derivative companion of Mathlib's
`Polynomial.scaleRoots_aeval_smul` and `Polynomial.scaleRoots_eval_mul`, and belongs beside them
in `Mathlib.RingTheory.Polynomial.ScaleRoots`; it is proved here.

## References

* [StacksProject 00UD](https://stacks.math.columbia.edu/tag/00UD), Lemma 10.143.7.
-/

namespace Stacks.Etale.ResidueFieldRealization

open Polynomial

/-- The derivative companion of `Polynomial.scaleRoots_eval_mul`: rescaling the root of
`p.scaleRoots c` back by `c` rescales the derivative by `c ^ (p.natDegree - 1)`. -/
public lemma scaleRoots_aeval_derivative_mul {K : Type*} [CommRing K] {L : Type*} [CommRing L]
    [Algebra K L] (p : K[X]) (c : K) (x : L) :
    aeval (algebraMap K L c * x) (derivative (p.scaleRoots c)) =
      algebraMap K L (c ^ (p.natDegree - 1)) * aeval x (derivative p) := by
  have hs : (p.scaleRoots c).natDegree = p.natDegree := natDegree_scaleRoots p c
  rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
  · simp [derivative_of_natDegree_zero hn, derivative_of_natDegree_zero (hs.trans hn)]
  · set n := p.natDegree with hnd
    have hd : ∀ q : K[X], q.natDegree = n → (derivative q).natDegree < n := fun q hq =>
      hq ▸ natDegree_derivative_lt (by omega)
    have hd1 := hd _ hs
    have hd2 := hd p rfl
    rw [aeval_eq_sum_range' hd1, aeval_eq_sum_range' hd2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [coeff_derivative, coeff_derivative, coeff_scaleRoots, Algebra.smul_def, Algebra.smul_def,
      mul_pow, ← map_pow]
    simp only [← mul_assoc, ← map_mul]
    congr 2
    have h : p.natDegree - (i + 1) + i = n - 1 := by omega
    rw [← h]
    ring

/-- Clearing denominators in a monic polynomial over a fraction field: for `q` monic over
`K = Frac A` there is a unit `c` of `K` such that all the coefficients of `q.scaleRoots c`,
namely `c ^ (q.natDegree - i) * q.coeff i`, come from `A`. -/
public lemma exists_isUnit_and_scaleRoots_mem_lifts {A K : Type*} [CommRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] {q : K[X]} (hq : q.Monic) :
    ∃ c : K, IsUnit c ∧ q.scaleRoots c ∈ Polynomial.lifts (algebraMap A K) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (S := K) (nonZeroDivisors A)
    (Finset.range q.natDegree) (fun i => q.coeff i)
  refine ⟨algebraMap A K b, IsLocalization.map_units K b, ?_⟩
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro i
  show _ ∈ (algebraMap A K).range
  rw [coeff_scaleRoots]
  rcases lt_trichotomy i q.natDegree with hi | hi | hi
  · obtain ⟨a, ha⟩ := hb i (Finset.mem_range.mpr hi)
    obtain ⟨m, hm⟩ : ∃ m, q.natDegree - i = m + 1 := ⟨q.natDegree - i - 1, by omega⟩
    have key : q.coeff i * algebraMap A K b ^ (q.natDegree - i)
        = algebraMap A K b ^ m * algebraMap A K a := by
      rw [ha, Algebra.smul_def, hm]; ring
    have hb' : algebraMap A K b ∈ (algebraMap A K).range := ⟨b, rfl⟩
    have ha' : algebraMap A K a ∈ (algebraMap A K).range := ⟨a, rfl⟩
    rw [key]
    exact mul_mem (pow_mem hb' _) ha'
  · subst hi
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [show q.coeff q.natDegree = 1 from hq]
    exact one_mem _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    exact zero_mem _

/-- The polynomial data the source extracts from a finite separable extension `L/κ(p)`: a monic
`f ∈ R[X]` and a primitive element `β` of `L` over `κ(p)` which is a root of `f` at which the
derivative of `f` is invertible. -/
public lemma exists_monic_aeval_eq_zero_and_adjoin_eq_top {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] [Algebra R L]
    [IsScalarTower R p.ResidueField L] :
    ∃ (f : R[X]) (β : L), f.Monic ∧ aeval β f = 0 ∧ IsUnit (aeval β (derivative f)) ∧
      IntermediateField.adjoin p.ResidueField {β} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element p.ResidueField L
  have hmon : (minpoly p.ResidueField α).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral α)
  obtain ⟨c, hc, hlifts⟩ := exists_isUnit_and_scaleRoots_mem_lifts
    (A := R ⧸ p) (K := p.ResidueField) hmon
  have hlifts' : (minpoly p.ResidueField α).scaleRoots c ∈
      Polynomial.lifts (algebraMap R p.ResidueField) := by
    rw [Polynomial.lifts_iff_coeff_lifts] at hlifts ⊢
    intro i
    obtain ⟨a, ha⟩ := hlifts i
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨r, by rw [← ha, Ideal.algebraMap_quotient_residueField_mk]⟩
  obtain ⟨f, hfmap, -, hfmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts' ((monic_scaleRoots_iff c).mpr hmon)
  refine ⟨f, algebraMap p.ResidueField L c * α, hfmonic, ?_, ?_, ?_⟩
  · rw [← Polynomial.aeval_map_algebraMap p.ResidueField, hfmap]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval p.ResidueField α)
  · rw [← Polynomial.aeval_map_algebraMap p.ResidueField, ← Polynomial.derivative_map, hfmap,
      scaleRoots_aeval_derivative_mul]
    refine IsUnit.mul ((hc.pow _).map (algebraMap p.ResidueField L)) ?_
    obtain ⟨u, v, huv⟩ : IsCoprime (minpoly p.ResidueField α)
        (derivative (minpoly p.ResidueField α)) := Algebra.IsSeparable.isSeparable _ α
    have h1 := congrArg (Polynomial.aeval (R := p.ResidueField) α) huv
    simp only [map_add, map_mul, map_one, minpoly.aeval, mul_zero, zero_add] at h1
    exact isUnit_iff_exists_inv.mpr ⟨aeval α v, by rw [mul_comm]; exact h1⟩
  · refine top_le_iff.mp ?_
    rw [← hα, IntermediateField.adjoin_simple_le_iff]
    have hmem : algebraMap p.ResidueField L c⁻¹ * (algebraMap p.ResidueField L c * α) ∈
        IntermediateField.adjoin p.ResidueField {algebraMap p.ResidueField L c * α} :=
      mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self _ _)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc.ne_zero, map_one, one_mul] at hmem

/-- **A finite separable extension of a residue field is realized by an étale algebra.** For a
prime `p` of `R` and a finite separable extension `L` of `κ(p)`, there are an étale `R`-algebra
`R'`, a prime `p'` of `R'` lying over `p` and an isomorphism `κ(p') ≃ L` of extensions of
`κ(p)`. -/
public theorem solution {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p) (e : p'.ResidueField ≃+* L),
      (e : p'.ResidueField →+* L).comp
        (Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)) =
          algebraMap p.ResidueField L := by
  let _ : Algebra R L :=
    ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField)).toAlgebra
  have : IsScalarTower R p.ResidueField L := .of_algebraMap_eq' rfl
  obtain ⟨f, β, hfmon, hf0, hfu, hβ⟩ := exists_monic_aeval_eq_zero_and_adjoin_eq_top p L
  let P : StandardEtalePair R := ⟨f, hfmon, derivative f, ⟨1, 0, 1, by ring⟩⟩
  have hmap : P.HasMap β := ⟨hf0, hfu⟩
  let ψ : P.Ring →+* L := (P.lift β hmap : P.Ring →ₐ[R] L).toRingHom
  have hψalg : ∀ r : R, ψ (algebraMap R P.Ring r) = algebraMap R L r := (P.lift β hmap).commutes
  set p' : Ideal P.Ring := RingHom.ker ψ with hp'def
  have hp'prime : p'.IsPrime := RingHom.ker_isPrime ψ
  have hkerRL : RingHom.ker (algebraMap R L) = p := by
    ext x
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R p.ResidueField L,
      map_eq_zero_iff _ (algebraMap p.ResidueField L).injective,
      Ideal.algebraMap_residueField_eq_zero]
  have hlo : p'.LiesOver p := ⟨by
    rw [Ideal.under_def, hp'def, RingHom.comap_ker, ← hkerRL]
    congr 1
    exact (RingHom.ext hψalg).symm⟩
  let e0 : p'.ResidueField →+* L := IsFractionRing.lift (RingHom.kerLift_injective ψ)
  have he0 : ∀ y : P.Ring, e0 (algebraMap P.Ring p'.ResidueField y) = ψ y := by
    intro y
    rw [← Ideal.algebraMap_quotient_residueField_mk p' y]
    exact (IsFractionRing.lift_algebraMap _ _).trans (RingHom.kerLift_mk ψ y)
  have heq : e0.comp (Ideal.ResidueField.map p p' (algebraMap R P.Ring) (p'.over_def p)) =
      algebraMap p.ResidueField L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p)) ?_
    ext r
    simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk,
      Ideal.ResidueField.map_algebraMap, he0, hψalg]
    rw [IsScalarTower.algebraMap_apply R p.ResidueField L]
  have hsurj : Function.Surjective e0 := by
    have hmem : ∀ x : p.ResidueField, algebraMap p.ResidueField L x ∈ e0.fieldRange := fun x =>
      ⟨_, by rw [← RingHom.comp_apply, heq]⟩
    have hle : (⊤ : IntermediateField p.ResidueField L) ≤
        (e0.fieldRange).toIntermediateField hmem := by
      rw [← hβ, IntermediateField.adjoin_simple_le_iff]
      exact ⟨algebraMap P.Ring p'.ResidueField P.X, (he0 _).trans (P.lift_X β hmap)⟩
    exact fun y => RingHom.mem_fieldRange.mp (hle IntermediateField.mem_top)
  exact ⟨P.Ring, inferInstance, inferInstance, inferInstance, p', hp'prime, hlo,
    RingEquiv.ofBijective e0 ⟨e0.injective, hsurj⟩, heq⟩

/-- A root, in a field extension `M` of `L`, of a monic polynomial over `L` which splits over `L`
lies in the image of `L`. -/
public lemma mem_range_of_eval_map_eq_zero {L M : Type*} [Field L] [Field M]
    (χ : L →+* M) {h : Polynomial L} (hm : h.Monic) (hs : h.Splits) {z : M}
    (hz : (h.map χ).eval z = 0) : z ∈ Set.range χ := by
  rw [hs.eq_prod_roots_of_monic hm] at hz
  simp only [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map,
    Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hz
  obtain ⟨b, -, hb0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
  exact ⟨b, by linear_combination -hb0⟩

/-- **Every element becomes purely inseparable over a splitting field of its separable part.** Let
`E/F` be algebraic, let `L/F` be an extension in which the minimal polynomial over `F` of every
separable element of `E` splits, and let `ψ : E → M` and `χ : L → M` be maps into a field `M` which
agree on `F`. Then for every `x : E` some `e ^ n`-th power of `ψ x` lies in the image of `L`,
where `e` is the exponential characteristic of `F`.

This is the mechanism of the first étale extension in the source's proof of Stacks 00UL: an element
of `E` is an `e`-power root of a separable element, and that separable element is a root of a
polynomial which splits in `L`, hence lies in the image of `L`. -/
public lemma exists_pow_mem_range_of_splits {F E L M : Type*} [Field F] [Field E] [Field L]
    [Field M] [Algebra F E] [Algebra F L] [Algebra.IsAlgebraic F E] (e : ℕ) [ExpChar F e]
    (ψ : E →+* M) (χ : L →+* M) (hχ : χ.comp (algebraMap F L) = ψ.comp (algebraMap F E))
    (hL : ∀ z : E, IsSeparable F z → ((minpoly F z).map (algebraMap F L)).Splits) (x : E) :
    ∃ n : ℕ, ψ x ^ e ^ n ∈ Set.range χ := by
  have : ExpChar ↥(separableClosure F E) e :=
    expChar_of_injective_ringHom (algebraMap F ↥(separableClosure F E)).injective e
  obtain ⟨n, β, hβ⟩ := (isPurelyInseparable_iff_pow_mem ↥(separableClosure F E) e).mp
    (separableClosure.isPurelyInseparable F E) x
  refine ⟨n, ?_⟩
  have hmonic : ((minpoly F (β : E)).map (algebraMap F L)).Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral _)).map _
  have hroot : (((minpoly F (β : E)).map (algebraMap F L)).map χ).eval (ψ β) = 0 := by
    rw [Polynomial.map_map, hχ, Polynomial.eval_map, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  obtain ⟨y, hy⟩ :=
    mem_range_of_eval_map_eq_zero χ hmonic (hL _ (mem_separableClosure_iff.mp β.2)) hroot
  rw [← map_pow, ← hβ]
  exact ⟨y, by simpa using hy⟩

/-- **A finite separable extension splitting the separable parts of finitely many finite
extensions.** Given finitely many finite field extensions `E i` of `K`, there is a finite separable
extension `L/K` in which the minimal polynomial of every separable element of every `E i` splits.

This is the field `L` of the source's proof of Stacks 00UL: one takes the normal closure, inside
the separable closure of `K`, of the compositum of the separable closures of `K` in the `E i`. -/
public lemma exists_finite_isSeparable_splits {K : Type u} [Field K] {ι : Type*} [Finite ι]
    (E : ι → Type v) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, FiniteDimensional K (E i)] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L),
      ∀ (i : ι) (z : E i), IsSeparable K z →
        ((minpoly K z).map (algebraMap K L)).Splits := by
  set φ : ∀ i, separableClosure K (E i) →ₐ[K] SeparableClosure K :=
    fun _ => IsSepClosed.lift
  have hfr : ∀ i, FiniteDimensional K (φ i).fieldRange :=
    fun i => (φ i).toLinearMap.finiteDimensional_range
  have : FiniteDimensional K (⨆ i, (φ i).fieldRange : IntermediateField K (SeparableClosure K)) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  set N : IntermediateField K (SeparableClosure K) :=
    IntermediateField.normalClosure K
      (⨆ i, (φ i).fieldRange : IntermediateField K (SeparableClosure K)) (SeparableClosure K)
  -- `normalClosure.algebraOfTower` wins the search for `Algebra K ↥N` over
  -- `IntermediateField.algebra'`, so the three class instances below and the minimal polynomial
  -- identification are given by explicit terms rather than left to `inferInstance` and `rw`,
  -- neither of which unfolds the two `Algebra K ↥N` to each other.
  have hfd : FiniteDimensional K ↥N := normalClosure.is_finiteDimensional _ _ _
  have hnormal : Normal K ↥N := normalClosure.normal _ _ _
  have hsep : Algebra.IsSeparable K ↥N := IntermediateField.isSeparable_tower_bot K N
  refine ⟨N, inferInstance, inferInstance, hfd, hsep, ?_⟩
  intro i z hz
  set w : separableClosure K (E i) := ⟨z, mem_separableClosure_iff.mpr hz⟩
  have hzw : minpoly K z = minpoly K w :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom K _ (E i)) Subtype.val_injective w
  have hin : φ i w ∈ N :=
    IntermediateField.le_normalClosure _ (le_iSup (fun i => (φ i).fieldRange) i ⟨w, rfl⟩)
  have hsp := Normal.splits (F := K) hnormal (⟨φ i w, hin⟩ : N)
  have heq : minpoly K (⟨φ i w, hin⟩ : N) = minpoly K z :=
    (minpoly.algHom_eq N.val Subtype.val_injective (⟨φ i w, hin⟩ : N)).symm.trans
      ((minpoly.algHom_eq (φ i) (φ i).injective w).trans hzw.symm)
  rwa [heq] at hsp

end Stacks.Etale.ResidueFieldRealization

/-!
# Realizing a finite separable residue field extension by an étale algebra

Let `R` be a ring, let `p` be a prime of `R` and write `κ(p)` for its residue field. Every finite
separable field extension `L/κ(p)` is already the residue field extension of an étale `R`-algebra:
there are an étale ring map `R → R'` and a prime `p'` of `R'` lying over `p` together with an
isomorphism `κ(p') ≃ L` of extensions of `κ(p)`, that is, an isomorphism carrying the canonical
map `κ(p) → κ(p')` to the given map `κ(p) → L`.

The source produces `R'` by the theorem of the primitive element: writing `L = κ(p)[α]` with
minimal polynomial `f̄ ∈ κ(p)[x]`, one lifts `f̄` to a monic `f ∈ R[x]` (after rescaling `α` by
some `c ∉ p`, so that the coefficients of `f̄` lie in the image of `R`) and takes
`R' = R[x, 1/f'] / (f)`, a *standard* étale algebra; separability of `L/κ(p)` makes `f̄'(α)`
invertible, so `x ↦ α` defines an `R`-algebra map `R' → L`, and `p'` is its kernel.

## Main results

* `Algebra.exists_etale_liesOver_residueFieldRingEquiv`: Stacks 00UD.

## Implementation notes

*Only étaleness of `R'` is asserted, as in the source's statement.* The source's proof exhibits a
standard étale `R'` (a principal localization of `R[x]/(f)` for a monic `f`), which is strictly
more information, but the statement of the tag records only `Algebra.Etale R R'`, and that is what
its consumers (Lemmas 00UK, 04GJ, 00U2 and More on Morphisms Lemma 04D1) use. The refinement
"étale is locally standard étale" is the content of the neighbouring Proposition 00UE, so
strengthening the conclusion here would duplicate that tag rather than this one.

*The isomorphism of extensions is pinned by an equation, not by a `κ(p)`-algebra structure.* The
source writes "the field extension `κ(p')/κ(p)` is isomorphic to `κ(p) ⊂ L`". Here `κ(p')` is
canonically a `κ(p)`-algebra through `Ideal.ResidueField.map p p' (algebraMap R R')`, the map
induced on residue fields by `R → R'`, and the conclusion says that some ring isomorphism
`e : κ(p') ≃+* L` satisfies `e ∘ (κ(p) → κ(p')) = (κ(p) → L)`. This is exactly `κ(p)`-semilinearity
of `e` for the canonical structures, and it avoids assuming the `Algebra κ(p) κ(p')` instance,
which Mathlib supplies only in the presence of further localization-compatibility instances
(`Localization.AtPrime.IsLiesOverAlgebra`). It is also strictly more informative than asking for an
`R`-algebra isomorphism `κ(p') ≃ₐ[R] L`, which by itself does not name the map from `κ(p)`; the two
happen to be equivalent, because `κ(p)` is a localization of the image of `R`, so any ring map out
of `κ(p')` agreeing with the structure maps on `R` agrees with them on `κ(p)`.

*The prime is exhibited through `Ideal.LiesOver`.* "`p'` lies over `p`" is `p'.LiesOver p`, i.e.
`p = p'.comap (algebraMap R R')`, which is Mathlib's spelling and the one the sibling lemma
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` uses; `p'.over_def p` is the equation
consumed by `Ideal.ResidueField.map`.

*Universes.* `R'` is produced in the universe of `R`, as in the Mathlib sibling: the witness
`R[x, 1/f']/(f)` is built from `R`. The target `L` is left in an arbitrary universe, since a ring
isomorphism may cross universes and no smallness hypothesis on `L` is needed.

Faithfulness to [StacksProject 00UD]:

1. No hypothesis is idle. `Module.Finite κ(p) L` and `Algebra.IsSeparable κ(p) L` are both
   necessary for the conclusion, hence used: for an étale `R → R'` and a prime `p'` over `p`, the
   extension `κ(p')/κ(p)` is automatically finite (étale maps are essentially of finite type and
   quasi-finite) and separable (`Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt`), so dropping
   either hypothesis makes the statement false. `Field L` enters the conclusion through `κ(p')`
   being a field.
2. The scalars and the base are the source's. The extension is over `p.ResidueField = κ(p)` itself,
   not over `R`, `R/p` or a localization of `R`; `R'` is an algebra over `R` itself, and the map
   `κ(p) → κ(p')` is the one induced by `algebraMap R R'`.
3. Nothing that the source names is left merely to exist. The comparison map `κ(p) → κ(p')` is
   pinned as `Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)`, and the isomorphism
   is required to intertwine it with the given `algebraMap κ(p) L`; only `R'`, `p'` and `e`
   themselves, which the source also only asserts to exist, are existentially quantified.
4. The instantiation is not degenerate. For `R = ℤ`, `p = 0`, so `κ(p) = ℚ`, and `L = ℚ[i]`, the
   witness is `R' = ℤ[x, 1/2x]/(x² + 1)` with `p' = 0`: this is étale over `ℤ` and its residue
   field is `ℚ[i] = L`, a proper extension of `κ(p)`. So the statement is not the tautology
   `L = κ(p)`, `R' = R`, `p' = p`, which is all that the case `L = κ(p)` asks for.

## References

* [StacksProject 00UD](https://stacks.math.columbia.edu/tag/00UD)
* [StacksProject 00UB](https://stacks.math.columbia.edu/tag/00UB)
* [StacksProject 00UC](https://stacks.math.columbia.edu/tag/00UC)
* [StacksProject 00UE](https://stacks.math.columbia.edu/tag/00UE)

## Tags

étale ring map, standard étale, residue field, separable extension, prime lying over
-/

@[expose] public section



namespace Algebra

/-- **Stacks 00UD.** Let `R` be a ring, `p` a prime of `R` and `L/κ(p)` a finite separable field
extension. Then there are an étale ring map `R → R'` and a prime `p'` of `R'` lying over `p`
together with an isomorphism `κ(p') ≃ L` of extensions of `κ(p)`, i.e. one carrying the canonical
map `κ(p) → κ(p')` induced by `R → R'` to the structure map `κ(p) → L`. -/
@[stacks 00UD "The isomorphism of extensions `κ(p')/κ(p) ≅ κ(p) ⊂ L` is pinned as a ring
isomorphism `e : κ(p') ≃+* L` with `e ∘ Ideal.ResidueField.map p p' (algebraMap R R') = algebraMap
κ(p) L`. Only `Algebra.Etale R R'` is asserted, as in the source's statement; that `R'` may be
taken standard étale is Proposition 00UE. See the module docstring.", sga "2 XIV 3.4" "affine case"]
public theorem exists_etale_liesOver_residueFieldRingEquiv {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p) (e : p'.ResidueField ≃+* L),
      (e : p'.ResidueField →+* L).comp
        (Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)) =
          algebraMap p.ResidueField L :=
            by apply Stacks.Etale.ResidueFieldRealization.solution

end Algebra

end

/-!
# Étale at a prime: the fibre ideal is maximal and the residue field extension is finite separable

Proof of Stacks 00U4, the statement
`Algebra.IsEtaleAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField`: for a ring map
`R → S` and a prime `q` of `S` lying over `p` in `R`, étale at `q`, the ideal `p S_q` is the
maximal ideal of `S_q` and `κ(q)` is a finite separable extension of `κ(p)`.

The étale hypothesis enters only through unramifiedness at `q`, so the statement is proved in that
form — `IsUnramifiedAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField` below, which is
the content of Stacks 00UW — and Stacks 00U4 is its specialisation. Over a local base the mathematics
is Mathlib's: `S_q` formally unramified over `R` restricts along `R → R_p` to a formally
unramified `R_p`-algebra, `R_p → S_q` is a local homomorphism of local rings, and `S_q` is
essentially of finite type over `R_p` because it is so over `R`; for such an algebra
`m_{R_p} S_q = m_{S_q}` and `κ(q)/κ(p)` is finite separable. Transporting the first equality along
`R → R_p` — which is `map_algebraMap_eq_map_maximalIdeal` below, because `m_{R_p}` is generated by
`p` — gives `p S_q = m_{S_q}`.

## Main results

* `Stacks.Etale.SeparableResidueAtPrime.solution`: the statement of Stacks 00U4.

## Implementation notes

The source's route replaces `S` by an `S_g` with `R → S_g` étale and then base changes to
`κ(p)`. Passing instead to the local ring `S_q` reaches the same local statement without choosing
`g`: the hypothesis `Algebra.IsEtaleAt R q` is about `S_q` already, and it is what the
localization step of the source is for. This is also why no finiteness on `S` is needed, only
`Algebra.EssFiniteType R (Localization.AtPrime q)`; that hypothesis is spent once, in
`Algebra.EssFiniteType.of_comp`, to see that `S_q` is essentially of finite type over `R_p`.

Mathlib's `Algebra.isUnramifiedAt_iff_map_eq` is the unramified statement as an equivalence, but
under the hypothesis `Algebra.EssFiniteType R S` — essential finiteness of `S` itself — which the
source's local hypothesis does not supply. Its proof uses that hypothesis only through
`Algebra.EssFiniteType R (Localization.AtPrime q)`, so
`IsUnramifiedAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField` is one direction of it
with the finiteness weakened accordingly; the local-base lemmas it rests on
(`Algebra.FormallyUnramified.map_maximalIdeal` and the two residue field instances of
`Mathlib/RingTheory/Unramified/LocalRing.lean`) hold as stated.

`map_algebraMap_eq_map_maximalIdeal` is the ideal-theoretic bookkeeping of that comparison and
needs no unramifiedness: for any prime `q` lying over `p`, the ideal of `S_q` generated by the
image of `p` is the one generated by the image of `m_{R_p}`. It is the analogue for the prime
below of `Localization.AtPrime.map_eq_maximalIdeal`, from which it follows by transitivity of
scalars; inside Mathlib's proof of `Algebra.isUnramifiedAt_iff_map_eq` it appears only as an
unnamed goal left by `congr!`.

## References

* [StacksProject 00U4](https://stacks.math.columbia.edu/tag/00U4)
* [StacksProject 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [StacksProject 00UW](https://stacks.math.columbia.edu/tag/00UW)
-/

@[expose] public section

namespace Stacks.Etale.SeparableResidueAtPrime

open IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/-- **The ideal of `A` generated by the image of a prime `p` of `R` is the ideal generated by the
image of the maximal ideal of `R_p`,** for any `R`-algebra `A` through which `R → R_p` factors.
The analogue for the prime below of `Localization.AtPrime.map_eq_maximalIdeal`; the case
`A = S_q` for a prime `q` of `S` lying over `p` is the one used here. -/
public lemma map_algebraMap_eq_map_maximalIdeal {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] (A : Type*) [CommRing A] [Algebra R A] [Algebra (Localization.AtPrime p) A]
    [IsScalarTower R (Localization.AtPrime p) A] :
    p.map (algebraMap R A) =
      (maximalIdeal (Localization.AtPrime p)).map (algebraMap (Localization.AtPrime p) A) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The unramified form of Stacks 00U4, which is the statement of Stacks 00UW: if `R → S` is
unramified at a prime `q` lying over `p` and `S_q` is essentially of finite type over `R`, then
`p S_q` is the maximal ideal of `S_q` and `κ(q)` is a finite separable extension of `κ(p)`.

This is `Algebra.isUnramifiedAt_iff_map_eq` in the direction used here, with essential finiteness
required of `S_q` over `R` rather than of `S` over `R`. -/
@[ega "IV 18.8.6" "partial"]
private lemma IsUnramifiedAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField
    [Algebra.EssFiniteType R (Localization.AtPrime q)] [Algebra.IsUnramifiedAt R q] :
    p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) ∧
      Module.Finite p.ResidueField q.ResidueField ∧
      Algebra.IsSeparable p.ResidueField q.ResidueField :=
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  ⟨(map_algebraMap_eq_map_maximalIdeal p (Localization.AtPrime q)).trans
      Algebra.FormallyUnramified.map_maximalIdeal,
    inferInstance, inferInstance⟩

/-- If `R → S` is étale at a prime `q` lying over `p` and `S_q` is essentially of finite type
over `R`, then `p S_q` is the maximal ideal of `S_q` and `κ(q)` is a finite separable extension
of `κ(p)`. -/
public theorem solution
    [Algebra.EssFiniteType R (Localization.AtPrime q)] [Algebra.IsEtaleAt R q] :
    p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) ∧
      Module.Finite p.ResidueField q.ResidueField ∧
      Algebra.IsSeparable p.ResidueField q.ResidueField :=
  IsUnramifiedAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField p q

end Stacks.Etale.SeparableResidueAtPrime

end

/-!
# Étale at a prime: the residue field extension is finite separable

Let `R → S` be a ring map and let `q` be a prime of `S` lying over a prime `p` of `R`. If `R → S`
is étale at `q`, then the local ring `S_q` is as close to `R_p` as it can be: the ideal `p S_q`
generated by the image of `p` is already the maximal ideal of `S_q` — which is `q S_q` — so the
fibre ring `S_q / p S_q` is the residue field `κ(q)`, and that field is a *finite separable*
extension of `κ(p)`.

Both conclusions are local at `q` and both flow from unramifiedness. Being étale at `q` means
`S_q` is formally étale over `R`, hence formally unramified over `R`, hence formally unramified
over `R_p`; for a formally unramified local algebra over a local ring, essentially of finite type,
the maximal ideal of the base generates the maximal ideal and the residue field extension is
separable (`Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`), and the residue field extension
is finite because such an algebra is free (`Algebra.FormallyUnramified.finite_of_free`). Since
`m_{R_p} = p R_p` (`Localization.AtPrime.map_eq_maximalIdeal`), the first conclusion reads
`p S_q = m_{S_q}` back over `R`.

## Main results

* `Algebra.IsEtaleAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField`: if `R → S` is
  étale at a prime `q` lying over `p`, and `S_q` is essentially of finite type over `R`, then
  `p S_q` is the maximal ideal of `S_q` and `κ(q)` is a finite separable extension of `κ(p)`.

## Implementation notes

The source's hypothesis is that `R → S` be étale at `q`, that is, that there be a `g ∉ q` with
`R → S_g` étale. Assumed here instead are the two consequences the mathematics uses: `S_q` is
formally étale over `R` (`Algebra.IsEtaleAt`, Mathlib's notion of being étale at a prime) and
`S_q` is essentially of finite type over `R`. This is strictly weaker — no global finiteness on
`S` is imposed, matching the source's hypothesis being local at `q` — and it costs a caller
nothing: `Algebra.EssFiniteType R (Localization.AtPrime q)` is an instance whenever `S` is of
finite type, or merely essentially of finite type, over `R`. The two hypotheses are equivalent to
the source's when `R → S` is of finite presentation, by `Algebra.exists_etale_of_isEtaleAt` and
`Algebra.basicOpen_subset_etaleLocus_iff_etale`.

Item (1) of the source is the chain `p S_q = q S_q = m_{S_q}`; recorded here is the equality with
`m_{S_q}`, because `q S_q = m_{S_q}` holds for every prime and is
`Localization.AtPrime.map_eq_maximalIdeal`. The two forms are therefore equivalent, and the one
chosen is the one that composes.

The proof uses only that `R → S` is *unramified* at `q`, which is the strictly weaker hypothesis
of the source's Lemma 00UW — a separate tag, whose statement is otherwise word for word this one,
and whose Mathlib form is `Algebra.isUnramifiedAt_iff_map_eq` (under the stronger finiteness
hypothesis `Algebra.EssFiniteType R S`). The étale hypothesis is kept here because it is what
this tag claims; nothing is lost, since `Algebra.FormallyUnramified` is an instance consequence of
`Algebra.FormallyEtale`, so a caller holding `Algebra.IsEtaleAt R q` may use either lemma.

Residue fields are Mathlib's `Ideal.ResidueField`, the residue field of `Localization.AtPrime`;
"finite separable" is `Module.Finite` together with `Algebra.IsSeparable`. The instances
`[Algebra (Localization.AtPrime p) (Localization.AtPrime q)]` and
`[Localization.AtPrime.IsLiesOverAlgebra p q]` are Mathlib's way of naming the canonical local
homomorphism `R_p → S_q` induced by `q.LiesOver p`; they are what give `κ(p) → κ(q)`, and
`Localization.AtPrime.algebraOfLiesOver` supplies them.

Faithfulness. (1) Every hypothesis is used: `q.LiesOver p` is what makes `p` the prime under `q`,
`Algebra.IsEtaleAt R q` gives formal unramifiedness of `S_q`, and essential finiteness of `S_q` is
needed for both conclusions — over a field `k` of positive characteristic the separable closure
`k ⊂ k^{sep}` is formally étale with `p S_q = 0 = m_{S_q}` and `κ(q)/κ(p) = k^{sep}/k` separable
but infinite. (2) The scalars and base are the source's: `p S_q` is the ideal generated in `S_q`
by the image of `p` under `R → S_q`, not by the image of `m_{R_p}`, and the residue field
extension is `κ(q)` over `κ(p)`, not over `S/q` or `R/p`. (3) The source's canonical maps are
pinned, not merely asserted to exist: `p S_q` is `Ideal.map (algebraMap R (Localization.AtPrime q))
p`, and `κ(p) → κ(q)` is the algebra map coming from `Localization.AtPrime.IsLiesOverAlgebra p q`.
(4) The instantiation is not degenerate: for `R = ℤ`, `S = ℤ[i]` and `p = q = (3)` — the prime `3`
is inert in `ℤ[i]` and unramified — the hypotheses hold, `p S_q = q S_q = m_{S_q}` is a nonzero
maximal ideal, and `κ(q)/κ(p)` is `𝔽_9/𝔽_3`, separable of degree `2`.

## References

* [StacksProject 00U4](https://stacks.math.columbia.edu/tag/00U4)
* [StacksProject 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [StacksProject 00UW](https://stacks.math.columbia.edu/tag/00UW)
-/

@[expose] public section

open IsLocalRing in
/-- **Stacks 00U4.** Let `R → S` be a ring map and let `q` be a prime of `S` lying over a prime
`p` of `R`. If `R → S` is étale at `q` then (1) the ideal `p S_q` is the maximal ideal of the
local ring `S_q`, hence equals `q S_q`, and (2) the residue field extension `κ(q)/κ(p)` is finite
separable. -/
@[stacks 00U4 "The source's hypothesis that `R → S` be étale at `q` is taken in the weaker form of
its two consequences: `Algebra.IsEtaleAt R q`, and `S_q` essentially of finite type over `R`
(rather than finite presentation of `S` over `R`). Item (1) is recorded as `p S_q = m_{S_q}`; the
source's other half `q S_q = m_{S_q}` holds for any prime and is
`Localization.AtPrime.map_eq_maximalIdeal`. See the module docstring, which also records that the
unramified version of this statement is the separate tag 00UW.", sga "1 I 3.1" "(i)"]
public theorem Algebra.IsEtaleAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    [Algebra.EssFiniteType R (Localization.AtPrime q)] [Algebra.IsEtaleAt R q] :
    p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) ∧
      Module.Finite p.ResidueField q.ResidueField ∧
      Algebra.IsSeparable p.ResidueField q.ResidueField :=
        by apply Stacks.Etale.SeparableResidueAtPrime.solution

end
