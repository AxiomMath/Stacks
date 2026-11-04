module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.Koszul.Concatenation
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.Regular.Ideal

@[expose] public section

/-!
# Local complete intersection ring maps

A ring map `A → B` is a *local complete intersection* if it is of finite type and, for some
(equivalently, any) presentation `B = A[x₁, …, x_n] / I`, the ideal `I` is Koszul-regular.

## Main definitions

* `RingHom.IsLocalCompleteIntersection`: the local complete intersection property of a ring map.

## Main results

* `RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial`: Koszul-regularity of the kernel
  of a finite polynomial presentation is independent of the presentation — if the kernel of one
  surjection `A[x₁, …, x_n] → B` is Koszul-regular, then so is the kernel of every surjection
  `A[y₁, …, y_m] → B`.

## Implementation notes

A presentation `B = A[x₁, …, x_n] / I` is represented by a surjective `A`-algebra homomorphism
from `MvPolynomial (Fin n) A` to `B`, with `I` its ring-theoretic kernel. The algebra structure on
`B` is the one induced by the ring homomorphism under consideration, so the definition quantifies
over presentations of `B` as an `A`-algebra *via that map* and not via some other structure.

The source's "for some (equivalently any) presentation" is recorded as the existential over
presentations. What makes that parenthesis legitimate is
`RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial` (Stacks tag 07CZ), proved below: a
single presentation with Koszul-regular kernel forces every presentation to have Koszul-regular
kernel, so the existential above is equivalent to the corresponding universal statement. The
definition itself is stated with the existential, and the equivalence is kept separate from it.

Tag 07CZ is proved by comparing two presentations `α : A[xᵢ] → B` and `β : A[y_j] → B` through the
common presentation `A[xᵢ, y_j] → B` obtained by lifting each variable of one along the other.
Passing from `α` to that common presentation is a repeated application of
`isKoszulRegularIdeal_comap_eval_iff`, which eliminates one variable at a time: adjoining the
relation `X - C a` to an ideal preserves Koszul-regularity in either direction. The forward
direction localizes and appends the relation to the local Koszul generators
(`Koszul.koszul_regular_append`); the reverse direction first moves the relation to the front of
a local generating sequence — legitimate because it occurs there with a unit coefficient, which
`Polynomial.derivative'` detects — and then divides it out with
`Koszul.koszulRegular_quotient_of_koszulRegular_append`. Reindexing and changing generators are
absorbed by `Koszul.regularity_of_generators_of_eq_span_range`, and the variables may be indexed
by arbitrary finite types since `MvPolynomial.renameEquiv` reduces to `Fin n`. The finite-type
hypothesis on `B` plays no role once both presentations are given, so the lemma is stated without
it.

*This notion is not the root-level `IsLocalCompleteIntersection` of
`StacksFrontier.RingTheory.CompleteIntersection.Defs`,* which carries Stacks tag 00S9 (2). That
one is a property of a `k`-algebra `S` over a *field* `k` — `S` is covered by principal
localizations each of which is a global complete intersection over `k`, in the sense of Definition
00S9 (1). The notion here is a property of an arbitrary *ring map* `A →+* B` between commutative
rings, with no field, no covering condition and no Krull dimension count, and it is governed by
Koszul-regularity of a presentation ideal rather than by regularity of a sequence cutting out `S`.
The two are genuinely distinct predicates of different shapes and are deliberately kept apart:
this one lives in the `RingHom` namespace, so its full name is
`RingHom.IsLocalCompleteIntersection`, and neither declaration is renamed. Nothing in this file
depends on the 00S9 notion, and that module is not imported.

## References

* [Stacks Project, Tag 07CZ](https://stacks.math.columbia.edu/tag/07CZ)
* [Stacks Project, Tag 07D0](https://stacks.math.columbia.edu/tag/07D0)
-/

namespace RingHom

universe u v

/-! ### The definition -/

/-- A ring homomorphism is a local complete intersection if it is of finite type and some finite
polynomial presentation has Koszul-regular kernel. -/
@[stacks 07D0]
public def IsLocalCompleteIntersection {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  f.FiniteType ∧
    letI := f.toAlgebra
    ∃ (n : ℕ) (p : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective p ∧
      Ideal.IsKoszulRegular (RingHom.ker p.toRingHom)

/-! ### Independence of the chosen presentation -/


universe w x

open CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- A linear equivalence of coefficient modules preserves Koszul regularity. -/
theorem isKoszulRegularOn_linearEquiv
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {r : ℕ} (f : Fin r → R) (e : M ≃ₗ[R] N)
    (h : Koszul.IsKoszulRegularOn f M) : Koszul.IsKoszulRegularOn f N := by
  intro i hi
  obtain ⟨eH⟩ := KoszulC.homologyTransport_of_degreewiseEquiv
    (C := Koszul.seqComplexTensor f M) (D := Koszul.seqComplexTensor f N)
    (fun n => TensorProduct.congr (LinearEquiv.refl R _) e) (by
      intro n m x
      by_cases hnm : (ComplexShape.down ℕ).Rel n m
      · obtain rfl : m + 1 = n := hnm
        rw [Koszul.seqComplexTensor_d, Koszul.seqComplexTensor_d]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
            show (TensorProduct.map LinearMap.id e)
                ((LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) m)) (a ⊗ₜ[R] b)) =
              (LinearMap.rTensor N (Koszul.d (Koszul.seqDual f) m))
                ((TensorProduct.map LinearMap.id e) (a ⊗ₜ[R] b))
            simp
        | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
      · rw [HomologicalComplex.shape _ _ _ hnm, HomologicalComplex.shape _ _ _ hnm]
        simp) i
  have : Subsingleton ((Koszul.seqComplexTensor f M).homology i) :=
    ModuleCat.isZero_iff_subsingleton.mp (h i hi)
  exact ModuleCat.isZero_iff_subsingleton.mpr eH.symm.toEquiv.subsingleton

/-- Flat extension of scalars preserves Koszul regularity over the ring itself. -/
private theorem isKoszulRegular_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {r : ℕ} {f : Fin r → R} (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (fun i => algebraMap R S (f i)) := by
  have h := KoszulC.isKoszulRegular_baseChange f R
    ((Koszul.isKoszulRegularOn_self_iff f).mpr hf) (S := S)
  exact (Koszul.isKoszulRegularOn_self_iff _).mp
    (isKoszulRegularOn_linearEquiv _ (TensorProduct.AlgebraTensorModule.rid R S S) h)

/-- A ring isomorphism preserves Koszul regularity. -/
private theorem isKoszulRegular_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) {r : ℕ} {f : Fin r → R} (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (fun i => e (f i)) :=
  @isKoszulRegular_algebraMap R S _ _ e.toRingHom.toAlgebra
    (RingHom.Flat.of_bijective e.bijective) r f hf

private theorem exists_coeff_notMem_of_derivation
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    {ι : Type*} [Fintype ι] (D : Derivation A R R) (p : Ideal R) [p.IsPrime]
    {t h : R} {n : ℕ} (f a : ι → R) (hf : ∀ i, f i ∈ p)
    (ht : t ∈ p) (hD : D t = 1) (hh : h ∉ p)
    (heq : h ^ n * t = ∑ i, a i * f i) : ∃ i, a i ∉ p := by
  by_contra hn
  have ha : ∀ i, a i ∈ p := by simpa only [not_exists, not_not] using hn
  have hd : D (h ^ n * t) ∈ p := by
    rw [heq, map_sum]
    apply p.sum_mem
    intro i hi
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    exact p.add_mem (p.mul_mem_right _ (ha i)) (p.mul_mem_right _ (hf i))
  rw [D.leibniz, hD, smul_eq_mul, smul_eq_mul, mul_one] at hd
  have hpow : h ^ n ∈ p := (p.add_mem_iff_left (p.mul_mem_right _ ht)).mp hd
  exact hh (Ideal.IsPrime.mem_of_pow_mem (inferInstance : p.IsPrime) n hpow)

private theorem span_range_update_of_isUnit
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f a : ι → R) (i : ι) (ha : IsUnit (a i)) :
    Ideal.span (Set.range (Function.update f i (∑ j, a j * f j))) =
      Ideal.span (Set.range f) := by
  let t := ∑ j, a j * f j
  let J := Ideal.span (Set.range (Function.update f i t))
  have hothers : ∀ j, j ≠ i → f j ∈ J := fun j hj =>
    Ideal.subset_span ⟨j, Function.update_of_ne hj t f⟩
  have ht : t ∈ J := Ideal.subset_span ⟨i, Function.update_self i t f⟩
  have hi : a i * f i ∈ J := by
    have hs : ∑ j ∈ Finset.univ.erase i, a j * f j ∈ J :=
      J.sum_mem fun j hj => J.mul_mem_left _ (hothers j (Finset.ne_of_mem_erase hj))
    have heq : a i * f i = t - ∑ j ∈ Finset.univ.erase i, a j * f j := by
      dsimp [t]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      ring
    rw [heq]
    exact J.sub_mem ht hs
  have hfi : f i ∈ J := (Ideal.unit_mul_mem_iff_mem J ha).mp hi
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      exact Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩))
    · rw [Function.update_of_ne hj]
      exact Ideal.subset_span ⟨j, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · simpa [hj] using hfi
    · exact hothers j hj

/-- Koszul regularity of ideals is invariant under a ring isomorphism. -/
private theorem isKoszulRegularIdeal_map_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) {I : Ideal R} (hI : Ideal.IsKoszulRegular I) :
    Ideal.IsKoszulRegular (I.map e.toRingHom) := by
  intro p hp
  let q := PrimeSpectrum.comap e.toRingHom p
  obtain ⟨g, hg, r, f, hf, hs⟩ := hI q (Ideal.map_le_iff_le_comap.mp hp)
  let e' : Localization.Away g ≃+* Localization.Away (e g) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers g)
      (T := Submonoid.powers (e g)) _ _ e (by exact Submonoid.map_powers _ _)
  refine ⟨e g, hg, r, fun i => e' (f i), isKoszulRegular_ringEquiv e' hf, ?_⟩
  have he : e'.toRingHom.comp (algebraMap R (Localization.Away g)) =
      (algebraMap S (Localization.Away (e g))).comp e.toRingHom := by
    ext a
    show e' (algebraMap R (Localization.Away g) a) =
      algebraMap S (Localization.Away (e g)) (e a)
    exact IsLocalization.ringEquivOfRingEquiv_eq _ a
  rw [Ideal.map_map, ← he, ← Ideal.map_map, hs, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Koszul regularity of ideals is invariant under a ring isomorphism. -/
alias isKoszulRegularIdeal_map_ringEquiv' := isKoszulRegularIdeal_map_ringEquiv

/-- Reindexing a finite sequence does not change Koszul regularity. -/
private theorem isKoszulRegular_reindex
    {R : Type*} [CommRing R] {m n : ℕ} (e : Fin m ≃ Fin n)
    {f : Fin n → R} (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (f ∘ e) := by
  have hmn : m = n := by simpa using Fintype.card_congr e
  subst n
  refine (Koszul.regularity_of_generators_of_eq_span_range
    (Ideal.span (Set.range f)) (f ∘ e) ?_).2.2 ⟨f, rfl, hf⟩
  rw [e.surjective.range_comp]

/-- A generator occurring with an invertible coefficient can be put first in a
Koszul-regular generating sequence. -/
private theorem exists_koszulRegular_append_of_isUnit_coeff
    {R : Type*} [CommRing R] {r : ℕ} (f a : Fin r → R)
    (i : Fin r) (ha : IsUnit (a i)) (hf : Koszul.IsKoszulRegular f) :
    ∃ (n : ℕ) (g : Fin n → R),
      Koszul.IsKoszulRegular (Fin.append (fun _ : Fin 1 => ∑ j, a j * f j) g) ∧
      Ideal.span (Set.range (Fin.append (fun _ : Fin 1 => ∑ j, a j * f j) g)) =
        Ideal.span (Set.range f) := by
  classical
  obtain ⟨n, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt i.isLt)
  subst r
  let t := ∑ j, a j * f j
  let u := Function.update f i t
  have hu : Ideal.span (Set.range u) = Ideal.span (Set.range f) :=
    span_range_update_of_isUnit f a i ha
  have hureg : Koszul.IsKoszulRegular u :=
    (Koszul.regularity_of_generators_of_eq_span_range _ u hu).2.2 ⟨f, rfl, hf⟩
  let v := u ∘ Equiv.swap 0 i
  have hv0 : v 0 = t := by simp [v, u]
  let g := Fin.tail v
  have heq : Fin.append (fun _ : Fin 1 => t) g =
      v ∘ (finCongr (Nat.add_comm 1 n)) := by
    rw [Fin.append_left_eq_cons]
    congr 1
    rw [← hv0]
    exact Fin.cons_self_tail v
  refine ⟨n, g, ?_, ?_⟩
  · rw [heq]
    exact isKoszulRegular_reindex _ (isKoszulRegular_reindex _ hureg)
  · rw [heq, (finCongr (Nat.add_comm 1 n)).surjective.range_comp]
    show Ideal.span (Set.range (u ∘ Equiv.swap 0 i)) = _
    rw [(Equiv.swap 0 i).surjective.range_comp]
    exact hu

private theorem span_range_eq_of_isUnit_mul
    {R : Type*} [CommRing R] {ι : Type*} (f g a : ι → R)
    (ha : ∀ i, IsUnit (a i)) (h : ∀ i, g i = a i * f i) :
    Ideal.span (Set.range g) = Ideal.span (Set.range f) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Ideal.unit_mul_mem_iff_mem _ (ha i)).mp (h i ▸ Ideal.subset_span ⟨i, rfl⟩)

private theorem exists_numerators_span
    {R : Type*} [CommRing R] (h : R) {ι : Type*}
    (f : ι → Localization.Away h) :
    ∃ F : ι → R, Ideal.map (algebraMap R (Localization.Away h))
        (Ideal.span (Set.range F)) = Ideal.span (Set.range f) := by
  let F := fun i => (IsLocalization.Away.sec h (f i)).1
  let a := fun i => algebraMap R (Localization.Away h)
    (h ^ (IsLocalization.Away.sec h (f i)).2)
  refine ⟨F, ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  apply span_range_eq_of_isUnit_mul f (fun i => algebraMap R (Localization.Away h) (F i)) a
  · intro i
    dsimp [a]
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit h).pow _
  · intro i
    exact (IsLocalization.Away.sec_spec h (f i)).symm.trans (mul_comm _ _)

/-- A Koszul generating family in any model of a principal localization gives one in the
canonical localization. -/
private theorem exists_koszulRegular_away_of_isLocalization
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (h : R) [IsLocalization.Away h S] (I : Ideal R)
    {r : ℕ} (f : Fin r → S) (hf : Koszul.IsKoszulRegular f)
    (hs : I.map (algebraMap R S) = Ideal.span (Set.range f)) :
    ∃ g : Fin r → Localization.Away h, Koszul.IsKoszulRegular g ∧
      I.map (algebraMap R (Localization.Away h)) = Ideal.span (Set.range g) := by
  let e := IsLocalization.algEquiv (Submonoid.powers h) S (Localization.Away h)
  refine ⟨fun i => e (f i), isKoszulRegular_ringEquiv e.toRingEquiv hf, ?_⟩
  have he : e.toRingHom.comp (algebraMap R S) = algebraMap R (Localization.Away h) :=
    RingHom.ext e.commutes
  rw [← he, ← Ideal.map_map, hs, Ideal.map_span, ← Set.range_comp]
  rfl

/-- The numerator of an element of an extended prime belongs to the prime. -/
private theorem mem_prime_of_algebraMap_mem
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (h : R) (hh : h ∉ p)
    {a : R} (ha : algebraMap R (Localization.Away h) a ∈
      p.map (algebraMap R (Localization.Away h))) : a ∈ p := by
  obtain ⟨b, ⟨n, rfl⟩, hb⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers h) (Localization.Away h) p a).mp ha
  exact (Ideal.IsPrime.mul_mem_left_iff
    (fun hp => hh (Ideal.IsPrime.mem_of_pow_mem inferInstance n hp))).mp hb

/-- Around each prime containing a Koszul-regular ideal there is a principal localization in which
the ideal is generated by a Koszul-regular family of images of elements of the prime. -/
private theorem exists_koszulRegular_numerators
    {R : Type*} [CommRing R] (I : Ideal R) (hI : Ideal.IsKoszulRegular I)
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ h : R, h ∉ p.asIdeal ∧ ∃ (r : ℕ) (F : Fin r → R), (∀ i, F i ∈ p.asIdeal) ∧
      Koszul.IsKoszulRegular (fun i => algebraMap R (Localization.Away h) (F i)) ∧
      (Ideal.span (Set.range F)).map (algebraMap R (Localization.Away h)) =
        I.map (algebraMap R (Localization.Away h)) ∧
      Ideal.span (Set.range (fun i => algebraMap R (Localization.Away h) (F i))) =
        I.map (algebraMap R (Localization.Away h)) := by
  obtain ⟨h, hh, r, f, hf, hs⟩ := hI p hp
  obtain ⟨F, hF⟩ := exists_numerators_span h f
  have hFspan : Ideal.span (Set.range (fun i => algebraMap R (Localization.Away h) (F i))) =
      I.map (algebraMap R (Localization.Away h)) := by
    show Ideal.span (Set.range ((algebraMap R (Localization.Away h)) ∘ F)) = _
    rw [Set.range_comp, ← Ideal.map_span, hF, hs]
  refine ⟨h, hh, r, F, fun i => ?_,
    (Koszul.regularity_of_generators_of_eq_span_range _ _ hFspan).2.2 ⟨f, hs.symm, hf⟩,
    hF.trans hs.symm, hFspan⟩
  apply mem_prime_of_algebraMap_mem p.asIdeal h hh
  apply Ideal.map_mono hp
  rw [← hFspan]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- A Koszul generating family headed by the image of `t`, in any model of a principal
localization, gives one in the canonical localization. -/
private theorem exists_koszulRegular_append_away_of_isLocalization
    {R : Type*} [CommRing R] (T : Type*) [CommRing T] [Algebra R T]
    (d : R) [IsLocalization.Away d T] (I : Ideal R) (t : R) {n : ℕ} (g : Fin n → T)
    (hg : Koszul.IsKoszulRegular (Fin.append (fun _ : Fin 1 => algebraMap R T t) g))
    (hspan : I.map (algebraMap R T) =
      Ideal.span (Set.range (Fin.append (fun _ : Fin 1 => algebraMap R T t) g))) :
    ∃ f : Fin n → Localization.Away d,
      Koszul.IsKoszulRegular
        (Fin.append (fun _ : Fin 1 => algebraMap R (Localization.Away d) t) f) ∧
      I.map (algebraMap R (Localization.Away d)) = Ideal.span
        (Set.range (Fin.append (fun _ : Fin 1 => algebraMap R (Localization.Away d) t) f)) := by
  let e := IsLocalization.algEquiv (Submonoid.powers d) T (Localization.Away d)
  have hseq : (fun j => e ((Fin.append (fun _ : Fin 1 => algebraMap R T t) g) j)) =
      Fin.append (fun _ : Fin 1 => algebraMap R (Localization.Away d) t)
        (fun j => e (g j)) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [e.commutes]
  refine ⟨fun j => e (g j), ?_, ?_⟩
  · have hreg := isKoszulRegular_ringEquiv e.toRingEquiv hg
    change Koszul.IsKoszulRegular (fun j => e ((Fin.append _ g) j)) at hreg
    rwa [hseq] at hreg
  · have hmap := congrArg (Ideal.map e.toRingHom) hspan
    have he : e.toRingHom.comp (algebraMap R T) =
        algebraMap R (Localization.Away d) := RingHom.ext e.commutes
    rw [Ideal.map_map, he, Ideal.map_span, ← Set.range_comp] at hmap
    exact hmap.trans (congrArg Ideal.span (congrArg Set.range hseq))

/-- A relation with derivative one may be chosen as the first local Koszul generator. -/
private theorem exists_koszulRegular_append_of_derivation
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (D : Derivation A R R) (I : Ideal R) (hI : Ideal.IsKoszulRegular I)
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) (t : R) (ht : t ∈ I) (hDt : D t = 1) :
    ∃ d : R, d ∉ p.asIdeal ∧ ∃ (n : ℕ) (f : Fin n → Localization.Away d),
      Koszul.IsKoszulRegular
        (Fin.append (fun _ : Fin 1 => algebraMap R (Localization.Away d) t) f) ∧
      I.map (algebraMap R (Localization.Away d)) = Ideal.span
        (Set.range (Fin.append (fun _ : Fin 1 => algebraMap R (Localization.Away d) t) f)) := by
  classical
  obtain ⟨h, hh, r, F, hFp, hFreg, hF, hFspan'⟩ := exists_koszulRegular_numerators I hI p hp
  let L := Localization.Away h
  have hFspan : Ideal.span (Set.range (fun i => algebraMap R L (F i))) =
      I.map (algebraMap R L) := hFspan'
  have htF : algebraMap R L t ∈ (Ideal.span (Set.range F)).map (algebraMap R L) :=
    hF.ge (Ideal.mem_map_of_mem _ ht)
  obtain ⟨_, ⟨N, rfl⟩, htF⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers h) L _ t).mp htF
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp htF
  obtain ⟨i, hi⟩ := exists_coeff_notMem_of_derivation D p.asIdeal F b hFp (hp ht) hDt hh hb.symm
  let T := Localization.Away (algebraMap R L (b i))
  have : IsLocalization.Away (h * b i) T := IsLocalization.Away.mul' L T h (b i)
  have hunit : IsUnit (algebraMap R T (h ^ N)) := by
    rw [IsScalarTower.algebraMap_apply R L T, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit h).pow N).map (algebraMap L T)
  obtain ⟨u, hu⟩ := hunit
  let a := fun j => (↑u⁻¹ : T) * algebraMap R T (b j)
  let G := fun j => algebraMap R T (F j)
  have hG : Koszul.IsKoszulRegular G := by
    simpa only [G, IsScalarTower.algebraMap_apply R L T] using
      (isKoszulRegular_algebraMap (S := T) hFreg)
  have ha : IsUnit (a i) := by
    apply IsUnit.mul (Units.isUnit _)
    show IsUnit (algebraMap L T (algebraMap R L (b i)))
    exact IsLocalization.Away.algebraMap_isUnit _
  have heq : (∑ j, a j * G j) = algebraMap R T t := by
    dsimp only [a, G]
    calc
      (∑ j, (↑u⁻¹ : T) * algebraMap R T (b j) * algebraMap R T (F j)) =
          (↑u⁻¹ : T) * ∑ j, algebraMap R T (b j * F j) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
      _ = (↑u⁻¹ : T) * algebraMap R T (∑ j, b j * F j) := by rw [map_sum]
      _ = algebraMap R T t := by
        rw [hb, map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨n, g, hg, hspan⟩ := exists_koszulRegular_append_of_isUnit_coeff G a i ha hG
  rw [heq] at hg hspan
  have hspanT : I.map (algebraMap R T) = Ideal.span (Set.range
      (Fin.append (fun _ : Fin 1 => algebraMap R T t) g)) := by
    rw [hspan]
    have hFspan'' := congrArg (Ideal.map (algebraMap L T)) hFspan
    have hcomp : (algebraMap L T).comp (algebraMap R L) = algebraMap R T :=
      (IsScalarTower.algebraMap_eq R L T).symm
    simpa only [Ideal.map_map, hcomp, Ideal.map_span, ← Set.range_comp,
      Function.comp_def, ← IsScalarTower.algebraMap_apply R L T, G] using hFspan''.symm
  exact ⟨h * b i, p.isPrime.mul_notMem hh hi, n,
    exists_koszulRegular_append_away_of_isLocalization T (h * b i) I t g hg hspanT⟩

/-- Quotienting by a Koszul-regular initial family preserves regularity of the remaining
family, in any isomorphic model of the quotient. -/
private theorem isKoszulRegular_map_of_ker_eq_span
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    {m n : ℕ} (f : Fin m → R) (g : Fin n → R)
    (hker : RingHom.ker φ = Ideal.span (Set.range f))
    (hf : Koszul.IsKoszulRegular f) (hfg : Koszul.IsKoszulRegular (Fin.append f g)) :
    Koszul.IsKoszulRegular (fun i => φ (g i)) := by
  have hg := Koszul.koszulRegular_quotient_of_koszulRegular_append f g hf hfg
  let e := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have h := isKoszulRegular_ringEquiv e hg
  simpa only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk] using h

/-- Quotienting by a Koszul-regular initial family preserves regularity of the remaining
family, in any isomorphic model of the quotient. -/
alias isKoszulRegular_map_of_ker_eq_span' := isKoszulRegular_map_of_ker_eq_span

/-- A nonzerodivisor is a Koszul-regular sequence of length one. -/
private theorem isKoszulRegular_singleton_of_isRegular
    {R : Type*} [CommRing R] {t : R} (ht : IsRegular t) :
    Koszul.IsKoszulRegular (fun _ : Fin 1 => t) := by
  apply (Koszul.isKoszulRegularOn_self_iff _).mp
  apply Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
  rw [List.ofFn_const, List.replicate_one, RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact ht.left

private theorem range_append {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact Or.inl ⟨i, (Fin.append_left f g i).symm⟩
    · exact Or.inr ⟨i, (Fin.append_right f g i).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, Fin.append_left f g i⟩
    · exact ⟨Fin.natAdd m i, Fin.append_right f g i⟩

/-- Eliminating a variable whose value lies in the coefficient ring preserves Koszul
regularity of ideals containing its defining relation. -/
private theorem isKoszulRegularIdeal_map_eval
    {R : Type*} [CommRing R] (a : R) (I : Ideal (Polynomial R))
    (hI : Ideal.IsKoszulRegular I) (ht : Polynomial.X - Polynomial.C a ∈ I) :
    Ideal.IsKoszulRegular (I.map (Polynomial.evalRingHom a)) := by
  intro p hp
  let φ := Polynomial.evalRingHom a
  let q := PrimeSpectrum.comap φ p
  have hq : I ≤ q.asIdeal := Ideal.map_le_iff_le_comap.mp hp
  obtain ⟨d, hd, n, g, hreg, hspan⟩ := exists_koszulRegular_append_of_derivation
    Polynomial.derivative' I hI q hq (Polynomial.X - Polynomial.C a) ht (by simp)
  let L := Localization.Away d
  let S := Localization.Away (φ d)
  let ψ : L →+* S := IsLocalization.Away.map L S φ d
  have hψ : Function.Surjective ψ := by
    apply (IsLocalization.Away.map_surjective_iff L S φ d).mpr
    intro z
    exact ⟨Polynomial.C z, 0, by simp [φ]⟩
  have hker : RingHom.ker ψ =
      Ideal.span (Set.range (fun _ : Fin 1 => algebraMap (Polynomial R) L
        (Polynomial.X - Polynomial.C a))) := by
    show RingHom.ker (IsLocalization.map S φ _) = _
    rw [IsLocalization.ker_map S φ (Submonoid.map_powers φ d),
      Polynomial.ker_evalRingHom, Ideal.map_span, Set.image_singleton, Set.range_const]
  have hf : Koszul.IsKoszulRegular (fun _ : Fin 1 => algebraMap (Polynomial R) L
      (Polynomial.X - Polynomial.C a)) :=
    isKoszulRegular_algebraMap (isKoszulRegular_singleton_of_isRegular
      (Polynomial.monic_X_sub_C a).isRegular)
  refine ⟨φ d, hd, n, fun j => ψ (g j),
    isKoszulRegular_map_of_ker_eq_span ψ hψ _ g hker hf hreg, ?_⟩
  have he : ψ.comp (algebraMap (Polynomial R) L) = (algebraMap R S).comp φ := by
    apply RingHom.ext
    intro x
    exact IsLocalization.map_eq (M := Submonoid.powers d)
      (T := Submonoid.powers (φ d)) (S := L) (Q := S) (g := φ)
      (Submonoid.map_le_iff_le_comap.mp (le_of_eq (Submonoid.map_powers φ d))) x
  have hmap := congrArg (Ideal.map ψ) hspan
  rw [Ideal.map_map, he, ← Ideal.map_map, Ideal.map_span, ← Set.range_comp] at hmap
  rw [hmap]
  have hz : ψ (algebraMap (Polynomial R) L (Polynomial.X - Polynomial.C a)) = 0 := by
    rw [← RingHom.comp_apply, he, RingHom.comp_apply]
    simp [φ]
  have hr : Set.range (ψ ∘ Fin.append
      (fun _ : Fin 1 => algebraMap (Polynomial R) L (Polynomial.X - Polynomial.C a)) g) =
      insert 0 (Set.range (ψ ∘ g)) := by
    rw [Set.range_comp, range_append, Set.image_union, Set.range_const,
      Set.image_singleton, hz, Set.singleton_union, ← Set.range_comp]
  rw [hr, Ideal.span_insert_zero]
  rfl

private theorem comap_eval_eq_sup {R : Type*} [CommRing R] (a : R) (I : Ideal R) :
    I.comap (Polynomial.evalRingHom a) = I.map Polynomial.C ⊔
      Ideal.span {Polynomial.X - Polynomial.C a} := by
  have hm : (I.map Polynomial.C).map (Polynomial.evalRingHom a) = I := by
    rw [Ideal.map_map]
    have he : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id R := by ext; simp
    rw [he, Ideal.map_id]
  rw [← Polynomial.ker_evalRingHom, RingHom.ker_eq_comap_bot,
    ← Ideal.comap_map_of_surjective _ (Polynomial.eval_surjective a), hm]

private theorem isKoszulRegular_append_X_sub_C
    {R : Type*} [CommRing R] {r : ℕ} (a : R) (f : Fin r → R)
    (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (Fin.append (fun _ : Fin 1 => Polynomial.X - Polynomial.C a)
      (fun i => Polynomial.C (f i))) := by
  apply Koszul.koszul_regular_append
  · exact isKoszulRegular_singleton_of_isRegular (Polynomial.monic_X_sub_C a).isRegular
  · have heq : Ideal.span (Set.range (fun _ : Fin 1 => Polynomial.X - Polynomial.C a)) =
        Ideal.span {Polynomial.X - Polynomial.C a} := by rw [Set.range_const]
    let e := (Ideal.quotEquivOfEq heq).trans (Polynomial.quotientSpanXSubCAlgEquiv a).toRingEquiv
    have h := isKoszulRegular_ringEquiv e.symm hf
    convert h using 1
    funext i
    apply e.injective
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingEquiv.apply_symm_apply]
    exact Polynomial.eval_C

private theorem isKoszulRegularIdeal_comap_eval
    {R : Type*} [CommRing R] (a : R) {I : Ideal R}
    (hI : Ideal.IsKoszulRegular I) :
    Ideal.IsKoszulRegular (I.comap (Polynomial.evalRingHom a)) := by
  intro p hp
  let q := PrimeSpectrum.comap Polynomial.C p
  have hq : I ≤ q.asIdeal := by
    intro x hx
    apply hp
    show Polynomial.eval a (Polynomial.C x) ∈ I
    simpa using hx
  obtain ⟨h, hh, r, f, hf, hs⟩ := hI q hq
  let L := Localization.Away h
  let S := Polynomial L
  let : Algebra (Polynomial R) S := (Polynomial.mapRingHom (algebraMap R L)).toAlgebra
  have : IsLocalization.Away (Polynomial.C h) S := by
    simpa only [Submonoid.map_powers] using (Polynomial.isLocalization (Submonoid.powers h) L)
  let a' := algebraMap R L a
  let F := Fin.append (fun _ : Fin 1 => Polynomial.X - Polynomial.C a')
    (fun i => Polynomial.C (f i))
  have hF : Koszul.IsKoszulRegular F := isKoszulRegular_append_X_sub_C a' f hf
  have hspan : (I.comap (Polynomial.evalRingHom a)).map (algebraMap (Polynomial R) S) =
      Ideal.span (Set.range F) := by
    rw [comap_eval_eq_sup, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton]
    have hC : (algebraMap (Polynomial R) S).comp Polynomial.C =
        Polynomial.C.comp (algebraMap R L) := by
      apply RingHom.ext
      intro x
      show Polynomial.map (algebraMap R L) (Polynomial.C x) = _
      exact Polynomial.map_C _
    rw [hC, ← Ideal.map_map, hs, Ideal.map_span, ← Set.range_comp]
    rw [show algebraMap (Polynomial R) S (Polynomial.X - Polynomial.C a) =
      Polynomial.X - Polynomial.C a' by
        show (Polynomial.mapRingHom (algebraMap R L)) _ = _
        simp [a']]
    show _ = Ideal.span (Set.range (Fin.append _ _))
    rw [range_append, Ideal.span_union, Set.range_const, sup_comm]
    rfl
  obtain ⟨g, hg, hgs⟩ := exists_koszulRegular_away_of_isLocalization S (Polynomial.C h)
    (I.comap (Polynomial.evalRingHom a)) F hF hspan
  exact ⟨Polynomial.C h, hh, 1 + r, g, hg, hgs⟩

private theorem isKoszulRegularIdeal_comap_ringEquiv_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal S) :
    Ideal.IsKoszulRegular (I.comap e.toRingHom) ↔ Ideal.IsKoszulRegular I := by
  constructor
  · intro h
    have h' := isKoszulRegularIdeal_map_ringEquiv e h
    rwa [Ideal.map_comap_of_surjective e.toRingHom e.surjective I] at h'
  · intro h
    have h' := isKoszulRegularIdeal_map_ringEquiv e.symm h
    have he : I.map e.symm.toRingHom = I.comap e.toRingHom :=
      Ideal.map_comap_of_equiv e.symm
    rwa [he] at h'

private theorem isKoszulRegularIdeal_comap_eval_iff
    {R : Type*} [CommRing R] (a : R) (I : Ideal R) :
    Ideal.IsKoszulRegular (I.comap (Polynomial.evalRingHom a)) ↔
      Ideal.IsKoszulRegular I := by
  refine ⟨fun h => ?_, isKoszulRegularIdeal_comap_eval a⟩
  have h' := isKoszulRegularIdeal_map_eval a (I.comap (Polynomial.evalRingHom a)) h
    (by simp [Ideal.mem_comap])
  rwa [Ideal.map_comap_of_surjective _ (Polynomial.eval_surjective a)] at h'

private theorem isKoszulRegularIdeal_comap_mvPolynomial_eval_fin_iff
    {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) (I : Ideal R) :
    Ideal.IsKoszulRegular (I.comap (MvPolynomial.eval a)) ↔
      Ideal.IsKoszulRegular I := by
  induction n with
  | zero =>
      have he : MvPolynomial.eval a = (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          rw [MvPolynomial.eval_C]
          exact ((MvPolynomial.isEmptyAlgEquiv R (Fin 0)).commutes r).symm
        · intro i
          exact i.elim0
      rw [he]
      exact isKoszulRegularIdeal_comap_ringEquiv_iff _ _
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv R n
      let b := Fin.tail a
      let c : MvPolynomial (Fin n) R := MvPolynomial.C (a 0)
      have he : MvPolynomial.eval a = (MvPolynomial.eval b).comp
          ((Polynomial.evalRingHom c).comp e.toRingHom) := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [e, c, MvPolynomial.finSuccEquiv_apply]
        · intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [e, c, MvPolynomial.finSuccEquiv_X_zero]
          · simp [e, b, MvPolynomial.finSuccEquiv_X_succ, Fin.tail]
      rw [he, ← Ideal.comap_comap, ← Ideal.comap_comap,
        isKoszulRegularIdeal_comap_ringEquiv_iff e.toRingEquiv,
        isKoszulRegularIdeal_comap_eval_iff]
      exact ih b

private theorem isKoszulRegularIdeal_comap_mvPolynomial_eval_iff
    {R : Type u} [CommRing R] {ι : Type v} [_root_.Finite ι] (a : ι → R) (I : Ideal R) :
    Ideal.IsKoszulRegular (I.comap (MvPolynomial.eval a)) ↔
      Ideal.IsKoszulRegular I := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let E := MvPolynomial.renameEquiv R e
  have he : MvPolynomial.eval a = (MvPolynomial.eval (a ∘ e.symm)).comp E.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [E]
    · intro i
      simp [E]
  rw [he, ← Ideal.comap_comap, isKoszulRegularIdeal_comap_ringEquiv_iff E.toRingEquiv]
  exact isKoszulRegularIdeal_comap_mvPolynomial_eval_fin_iff _ _ _

/-- The kernel of every finite polynomial presentation is a Koszul-regular ideal if the kernel
of one such presentation is Koszul-regular. -/
@[stacks 07CZ]
public theorem isKoszulRegularIdeal_ker_of_surjective_mvPolynomial
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type w} [_root_.Finite ι] {κ : Type x} [_root_.Finite κ]
    (α : MvPolynomial ι A →ₐ[A] B) (hα : Function.Surjective α)
    (hI : Ideal.IsKoszulRegular (RingHom.ker α.toRingHom))
    (β : MvPolynomial κ A →ₐ[A] B) (hβ : Function.Surjective β) :
    Ideal.IsKoszulRegular (RingHom.ker β.toRingHom) := by
  classical
  choose f hf using fun j : κ => hα (β (MvPolynomial.X j))
  choose g hg using fun i : ι => hβ (α (MvPolynomial.X i))
  let E := MvPolynomial.commAlgEquiv A κ ι
  have he : α.toRingHom.comp (MvPolynomial.eval f) =
      (β.toRingHom.comp (MvPolynomial.eval g)).comp E.toRingHom := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro a
        simp [E]
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.eval_C]
        have hE : E.toRingHom (MvPolynomial.C (MvPolynomial.X i)) = MvPolynomial.X i :=
          MvPolynomial.commAlgEquiv_C_X i
        rw [hE, MvPolynomial.eval_X]
        exact (hg i).symm
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.eval_X]
      have hE : E.toRingHom (MvPolynomial.X j) = MvPolynomial.C (MvPolynomial.X j) :=
        MvPolynomial.commAlgEquiv_X j
      rw [hE, MvPolynomial.eval_C]
      exact hf j
  have hK := (isKoszulRegularIdeal_comap_mvPolynomial_eval_iff f
    (RingHom.ker α.toRingHom)).mpr hI
  have hker : (RingHom.ker α.toRingHom).comap (MvPolynomial.eval f) =
      ((RingHom.ker β.toRingHom).comap (MvPolynomial.eval g)).comap E.toRingHom :=
    congrArg RingHom.ker he
  rw [hker] at hK
  exact (isKoszulRegularIdeal_comap_mvPolynomial_eval_iff g _).mp
    ((isKoszulRegularIdeal_comap_ringEquiv_iff E.toRingEquiv _).mp hK)

end RingHom

end
