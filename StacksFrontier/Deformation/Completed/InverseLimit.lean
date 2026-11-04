module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse limits of Artinian local algebras

An object of the completed base category is the inverse limit of its
Artinian quotients. This file sets up the adic topology attached to a decreasing sequence of
ideals and identifies the limit.

## Main definitions

* `Ideal.IsAdicFiltration` says that two families consisting respectively of the
  powers of an ideal and of a given sequence of ideals are cofinal.
* `inverseLimit` is the algebra of compatible sequences in a tower of Artinian local
  algebras.
* `inverseLimitProj` is its projection to a term of the tower.

## Main results

* `quotient_filtration_isAdic` shows that the images of the ideals in the quotient by
  their intersection form an adic filtration for the image of the maximal ideal.
* `inverseLimit_isObjectOfCompleteLocalAlgCat` says that the inverse limit is a
  Noetherian complete local algebra with residue field the prescribed field.
* `kernel_projections_define_maximalIdeal_adicTopology` says that the kernels of the
  projections define its maximal-ideal-adic topology.

## Implementation notes

### Adic topology from a decreasing sequence of ideals

Saying that a sequence defines an adic topology is expressed by mutual cofinality with the
powers of the defining ideal.  In the quotient we use the image of the maximal ideal of the
original local ring.  For every proper quotient this is its maximal ideal; this formulation also
makes sense without adding a properness hypothesis absent from the source.

### Inverse limits of Artinian local algebras

The inverse limit is represented explicitly as the subalgebra of the product consisting of
compatible sequences. The assertion that the projection kernels define the adic topology uses
`Ideal.IsAdicFiltration`, which expresses their cofinality with the powers of the
maximal ideal. Cotangent-space dimensions are measured over each algebra's residue field; the
chosen residue field equivalence identifies this dimension with the dimension over `k` in the
source. Finite generation and precompleteness use stabilization of images of coefficient
solution sets in finite modules over Artinian rings. This replaces the polynomial-completion
presentation of the source and also applies without finiteness assumptions on the base ring.

## References

* [Stacks Project, Tag 06SE](https://stacks.math.columbia.edu/tag/06SE)
* [Stacks Project, Tag 06SF](https://stacks.math.columbia.edu/tag/06SF)
-/

@[expose] public section

namespace Deformation

open Stacks.RegularLocalRing.SpanFinrank

/-! ### Adic topology from a decreasing sequence of ideals -/

section
open IsLocalRing
universe u v w

namespace Ideal

/-- A sequence `K` is an `I`-adic filtration if it and the sequence of powers of `I` are
cofinal. Equivalently, the two sequences define the same linear topology. -/
@[ega "IV 11.4.7"]
def IsAdicFiltration {R : Type*} [CommRing R] (I : Ideal R) (K : ℕ → Ideal R) : Prop :=
  (∀ n, ∃ m, K m ≤ I ^ n) ∧ (∀ n, ∃ m, I ^ m ≤ K n)

end Ideal


private theorem quotient_maximalIdeal_pow_isArtinian {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ n) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (R ⧸ maximalIdeal R ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    infer_instance
  · refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ ⟨⟨?_, ?_⟩, ?_⟩
    · infer_instance
    · exact Ideal.pow_le_self hn
    · intro q hq _
      rw [← (maximalIdeal.isMaximal R).isPrime.radical, ← Ideal.radical_pow _ hn]
      exact hq.1.radical_le_iff.mpr hq.2

/-- Congruence modulo `I ^ n • ⊤` in a ring is membership of the difference in `I ^ n`. -/
private theorem smodEq_pow_smul_top_iff {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    {x y : R} : x ≡ y [SMOD I ^ n • (⊤ : Ideal R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]

private theorem antitone_ideal_eventually_le_iInf_sup_pow
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsPrecomplete (maximalIdeal R) R] (J : ℕ → Ideal R) (hJ : Antitone J)
    (hpow : ∀ n, maximalIdeal R ^ n ≤ J n) (n : ℕ) :
    ∃ N, J N ≤ (⨅ n, J n) ⊔ maximalIdeal R ^ n := by
  classical
  let m := maximalIdeal R
  have hstable (p : ℕ) : ∃ N, ∀ r ≥ N, J r ⊔ m ^ p = J N ⊔ m ^ p := by
    let q := Ideal.Quotient.mk (m ^ p)
    let F : ℕ →o (Ideal (R ⧸ m ^ p))ᵒᵈ :=
      ⟨fun r ↦ OrderDual.toDual (Ideal.map q (J r)),
        fun _ _ hab ↦ Ideal.map_mono (hJ hab)⟩
    let : IsArtinianRing (R ⧸ m ^ p) :=
      quotient_maximalIdeal_pow_isArtinian p
    obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes F
    refine ⟨N, fun r hr ↦ ?_⟩
    have heq : Ideal.map q (J r) = Ideal.map q (J N) := (hN r hr).symm
    have hc (a : ℕ) :
        Ideal.comap q (Ideal.map q (J a)) = J a ⊔ m ^ p := by
      rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, show RingHom.ker q = m ^ p from Ideal.mk_ker]
    rw [← hc r, ← hc N, heq]
  choose b hb using hstable
  let s : ℕ → ℕ := fun k ↦ Nat.rec (max n (b n))
    (fun k r ↦ max (r + 1) (b (n + k + 1))) k
  have hs_succ (k : ℕ) : s (k + 1) = max (s k + 1) (b (n + k + 1)) := by simp [s]
  have hs_ge (k : ℕ) : b (n + k) ≤ s k := by
    cases k with
    | zero => simp [s]
    | succ k =>
      rw [hs_succ]
      exact le_max_right _ _
  have hs_strict (k : ℕ) : s k < s (k + 1) := by
    rw [hs_succ]
    exact lt_max_of_lt_left (Nat.lt_succ_self _)
  have hs_id (k : ℕ) : n + k ≤ s k := by
    induction k with
    | zero => simp [s]
    | succ k ih =>
      rw [hs_succ]
      exact (Nat.add_le_add_right ih 1).trans (le_max_left _ _)
  have hsup (k : ℕ) : J (s (k + 1)) ⊔ m ^ (n + k) = J (s k) ⊔ m ^ (n + k) := by
    rw [hb (n + k) (s (k + 1)) ((hs_ge k).trans (Nat.le_of_lt (hs_strict k))),
      hb (n + k) (s k) (hs_ge k)]
  refine ⟨s 0, fun z hz => ?_⟩
  have step (k : ℕ) (y : J (s k)) :
      ∃ t : J (s (k + 1)), (y : R) - t ∈ m ^ (n + k) := by
    have hy : (y : R) ∈ J (s (k + 1)) ⊔ m ^ (n + k) := by
      rw [hsup k]
      exact (show J (s k) ≤ J (s k) ⊔ m ^ (n + k) from le_sup_left) y.property
    obtain ⟨t, ht, e, he, hye⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨t, ht⟩, ?_⟩
    simpa [← hye] using he
  let f : (k : ℕ) → J (s k) := fun k => Nat.rec (motive := fun k => J (s k))
    ⟨z, hz⟩ (fun k y => (step k y).choose) k
  have hf (k : ℕ) : (f k).val - (f (k + 1)).val ∈ m ^ (n + k) := by
    simpa only [f] using (step k (f k)).choose_spec
  have hc {a c : ℕ} (hac : a ≤ c) :
      (f a).val - (f c).val ∈ m ^ (n + a) := by
    induction c, hac using Nat.le_induction with
    | base => simp
    | succ c hac ih =>
      have hh := (m ^ (n + a)).add_mem ih
        (Ideal.pow_le_pow_right (Nat.add_le_add_left hac n) (hf c))
      simpa only [sub_add_sub_cancel] using hh
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := m) (fun k => (f k).val) (by
    intro a c hac
    rw [smodEq_pow_smul_top_iff]
    exact Ideal.pow_le_pow_right (Nat.le_add_left a n) (hc hac))
  have hLm (k : ℕ) : (f k).val - L ∈ m ^ k := by
    exact (smodEq_pow_smul_top_iff _ _).mp (hL k)
  have hLJ : L ∈ ⨅ r, J r := by
    rw [Submodule.mem_iInf]
    intro r
    have hfr : (f r).val ∈ J r :=
      hJ ((Nat.le_add_left r n).trans (hs_id r)) (f r).property
    simpa only [sub_sub_cancel] using (J r).sub_mem hfr (hpow r (hLm r))
  refine Submodule.mem_sup.mpr ⟨L, hLJ, z - L, ?_, by abel⟩
  have hh := (m ^ n).add_mem (by simpa using hc (Nat.zero_le n)) (hLm n)
  simpa only [sub_add_sub_cancel, f, Nat.rec_zero] using hh

/-- Let `A` be a Noetherian complete local algebra and let `J n` be a decreasing sequence of
ideals containing the `n`-th power of the maximal ideal.  In the quotient by `⋂ n, J n`, the
images of the `J n` form an adic filtration for the image of the maximal ideal. -/
@[stacks 06SE]
theorem quotient_filtration_isAdic
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : CompleteLocalAlgCat.{u, v, w} Λ k) (J : ℕ → Ideal A)
    (hJ : Antitone J) (hpow : ∀ n, maximalIdeal A ^ n ≤ J n) :
    Ideal.IsAdicFiltration
      (Ideal.map (Ideal.Quotient.mk (⨅ n, J n)) (maximalIdeal A))
      (fun n ↦ Ideal.map (Ideal.Quotient.mk (⨅ n, J n)) (J n)) := by
  refine ⟨fun n => ?_, fun n => ⟨n, ?_⟩⟩
  · obtain ⟨N, hN⟩ := antitone_ideal_eventually_le_iInf_sup_pow J hJ hpow n
    refine ⟨N, ?_⟩
    simpa only [← Ideal.map_pow, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] using
      (Ideal.map_mono (f := Ideal.Quotient.mk (⨅ n, J n)) hN)
  · rw [← Ideal.map_pow]
    exact Ideal.map_mono (hpow n)

end

/-! ### Inverse limits of Artinian local algebras -/

section
open CategoryTheory
open IsLocalRing
universe u v w


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]


/-- The inverse limit of a tower `⋯ → A₂ → A₁ → A₀`, realized as the subalgebra of
compatible sequences in the product. -/
def inverseLimit (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) : Subalgebra Λ (∀ n, A n) where
  carrier := {x | ∀ n, (f n).hom (x (n + 1)) = x n}
  mul_mem' hx hy n := by simp [hx n, hy n]
  add_mem' hx hy n := by simp [hx n, hy n]
  algebraMap_mem' r n := by simp

/-- The canonical algebra homomorphism from the inverse limit to one term of the tower. -/
def inverseLimitProj (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) (n : ℕ) : inverseLimit A f →ₐ[Λ] A n :=
  { (Pi.evalRingHom (fun n ↦ A n) n).comp (inverseLimit A f).val with
    commutes' := fun _ ↦ rfl }

private theorem inverseLimitProj_surjective
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ) :
    Function.Surjective (inverseLimitProj A f n) := by
  let t : ∀ n, A (n + 1) →ₗ[ℤ] A n :=
    fun n => (f n).hom.toRingHom.toAddMonoidHom.toIntLinearMap
  have ht : ∀ n, Function.Surjective (t n) := hsurj
  intro y
  obtain ⟨x, hx⟩ := invLimit.proj_surjective (fun n => A n) t ht n y
  exact ⟨⟨x.1, x.2⟩, hx⟩

private theorem cotangent_finrank_le_of_surjective
    (A B : ArtinianLocalAlgCat.{u, v, w} Λ k) (g : A ⟶ B)
    (hg : Function.Surjective g.hom) :
    Module.finrank (ResidueField B) (CotangentSpace B) ≤
      Module.finrank (ResidueField A) (CotangentSpace A) := by
  classical
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  obtain ⟨t, htcard, htspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal A).fg_of_isNoetherianRing
  have hmB : maximalIdeal B = Ideal.span (g.hom.toRingHom '' (↑t : Set A)) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective g.hom.toRingHom hg,
      ← htspan, Ideal.map_span]
  rw [hmB]
  calc
    (Ideal.span (g.hom.toRingHom '' (↑t : Set A))).spanFinrank ≤
        (g.hom.toRingHom '' (↑t : Set A)).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite (t.finite_toSet.image _)
    _ ≤ (↑t : Set A).ncard := Set.ncard_image_le t.finite_toSet
    _ = t.card := Set.ncard_coe_finset _
    _ = (maximalIdeal A).spanFinrank := htcard

private theorem cotangent_finrank_eventually_constant
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (hbounded : ∃ d : ℕ,
      ∀ n, Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) ≤ d) :
    ∃ N r : ℕ, ∀ n, N ≤ n →
      Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) = r := by
  let d : ℕ → ℕ := fun n =>
    Module.finrank (ResidueField (A n)) (CotangentSpace (A n))
  have hd : Monotone d := monotone_nat_of_le_succ fun n =>
    cotangent_finrank_le_of_surjective (A (n + 1)) (A n) (f n) (hsurj n)
  obtain ⟨b, hb⟩ := hbounded
  have hbd : BddAbove (Set.range d) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hb n
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty d) hbd
  refine ⟨N, sSup (Set.range d), fun n hn => ?_⟩
  exact le_antisymm (le_csSup hbd ⟨n, rfl⟩) (hN ▸ hd hn)

private theorem maximalIdeal_eq_span_of_equal_cotangent_finrank
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R]
    [IsLocalRing S] (π : R →+* S) (hπ : Function.Surjective π)
    (hd : (maximalIdeal R).spanFinrank = (maximalIdeal S).spanFinrank)
    (t : Finset R) (ht : ∀ x ∈ t, x ∈ maximalIdeal R)
    (hspan : maximalIdeal S = Ideal.span (π '' (↑t : Set R))) :
    maximalIdeal R = Ideal.span (↑t : Set R) := by
  let : IsLocalHom π := IsLocalHom.of_surjective π hπ
  let J : Ideal R := Ideal.span (↑t : Set R)
  have hJ : J ≤ maximalIdeal R := Ideal.span_le.mpr fun x hx => ht x (Finset.mem_coe.mp hx)
  have hmap : J.map π = maximalIdeal S := by
    simpa only [J, Ideal.map_span] using hspan.symm
  have hker := ker_le_maximalIdeal_sq_of_surjective_of_spanFinrank_eq π hπ hd
  have hle : maximalIdeal R ≤ J ⊔ maximalIdeal R ^ 2 := by
    calc
      maximalIdeal R = (maximalIdeal S).comap π :=
        (IsLocalRing.maximalIdeal_comap π).symm
      _ = (J.map π).comap π := hmap ▸ rfl
      _ = J ⊔ RingHom.ker π := by
        simpa only [RingHom.ker_eq_comap_bot] using Ideal.comap_map_of_surjective π hπ J
      _ ≤ J ⊔ maximalIdeal R ^ 2 := sup_le_sup_left hker _
  have hle' : maximalIdeal R ≤ J ⊔ maximalIdeal R • maximalIdeal R := by
    simpa only [Ideal.smul_eq_mul, pow_two] using hle
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian (maximalIdeal R))
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hle') hJ

private theorem inverseLimitProj_compatible
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) (n : ℕ) (x : inverseLimit A f) :
    (f n).hom (inverseLimitProj A f (n + 1) x) = inverseLimitProj A f n x :=
  x.property n

private def towerMap
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) {i j : ℕ} (h : i ≤ j) :
    A j →+* A i :=
  Nat.leRec (RingHom.id (A i))
    (fun n _ g => g.comp (f n).hom.toRingHom) h

private theorem towerMap_self
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) (i : ℕ) (x : A i) :
    towerMap A f (le_refl i) x = x := by
  simp [towerMap]

private theorem towerMap_succ
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) {i j : ℕ} (h : i ≤ j)
    (h' : i ≤ j + 1) (x : A (j + 1)) :
    towerMap A f h' x = towerMap A f h ((f j).hom x) := by
  simpa [towerMap] using
    congrArg (fun g : A (j + 1) →+* A i => g x)
      (Nat.leRec_succ (motive := fun j (_ : i ≤ j) => A j →+* A i)
        (RingHom.id (A i)) (fun n _ g => g.comp (f n).hom.toRingHom) h)

private theorem towerMap_comp
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : A k) :
    towerMap A f hij (towerMap A f hjk x) =
      towerMap A f (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => simp only [towerMap_self]
  | succ k hjk ih =>
    rw [towerMap_succ A f hjk (Nat.le_succ_of_le hjk), ih,
      towerMap_succ A f (hij.trans hjk) (Nat.le_succ_of_le (hij.trans hjk))]

private theorem towerMap_proj
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    {i j : ℕ} (h : i ≤ j) (x : inverseLimit A f) :
    towerMap A f h (inverseLimitProj A f j x) = inverseLimitProj A f i x := by
  induction j, h using Nat.le_induction with
  | base => exact towerMap_self A f i _
  | succ j h ih =>
    rw [towerMap_succ A f h (Nat.le_succ_of_le h), inverseLimitProj_compatible,
      ih]

private theorem towerMap_surjective
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    {i j : ℕ} (h : i ≤ j) : Function.Surjective (towerMap A f h) := by
  induction j, h using Nat.le_induction with
  | base => intro x; exact ⟨x, towerMap_self A f i x⟩
  | succ j h ih =>
    intro x
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := hsurj j y
    exact ⟨z, by rw [towerMap_succ A f h (Nat.le_succ_of_le h), hz, hy]⟩

private def coefficientTowerMap
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) {i j : ℕ} (h : i ≤ j)
    (c : t → A j) : t → A i :=
  fun a => towerMap A f h (c a)

private theorem coefficientTowerMap_self
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (i : ℕ) (c : t → A i) :
    coefficientTowerMap A f t (le_refl i) c = c := by
  funext a
  exact towerMap_self A f i (c a)

private theorem coefficientTowerMap_comp
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (c : t → A k) :
    coefficientTowerMap A f t hij (coefficientTowerMap A f t hjk c) =
      coefficientTowerMap A f t (hij.trans hjk) c := by
  funext a
  exact towerMap_comp A f hij hjk (c a)

private theorem linearCombination_towerMap
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f))
    {i j : ℕ} (h : i ≤ j) (c : t → A j) :
    towerMap A f h
      (Fintype.linearCombination (A j)
        (fun a : t => inverseLimitProj A f j a) c) =
      Fintype.linearCombination (A i)
        (fun a : t => inverseLimitProj A f i a)
        (coefficientTowerMap A f t h c) := by
  classical
  simp only [Fintype.linearCombination_apply, smul_eq_mul, map_sum, map_mul,
    coefficientTowerMap, towerMap_proj]

private def kernelImage
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (t : Finset (inverseLimit A f)) {i j : ℕ} (h : i ≤ j) :
    Submodule (A i) (t → A i) where
  carrier := {x | ∃ c : t → A j,
    Fintype.linearCombination (A j)
      (fun a : t => inverseLimitProj A f j a) c = 0 ∧
    coefficientTowerMap A f t h c = x}
  zero_mem' := by
    refine ⟨0, by simp, ?_⟩
    funext a
    simp [coefficientTowerMap]
  add_mem' := by
    intro x y hx hy
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c + d, by simp [map_add, hc, hd], ?_⟩
    rw [← hcx, ← hdy]
    funext a
    simp [coefficientTowerMap]
  smul_mem' := by
    intro r x hx
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨s, hs⟩ := towerMap_surjective A f hsurj h r
    refine ⟨s • c, by simp [map_smul, hc], ?_⟩
    rw [← hcx]
    funext a
    simp [coefficientTowerMap, Pi.smul_apply, smul_eq_mul, hs]

private theorem kernelImage_antitone
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (t : Finset (inverseLimit A f))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    kernelImage A f hsurj t (hij.trans hjk) ≤ kernelImage A f hsurj t hij := by
  intro x hx
  obtain ⟨c, hc, hcx⟩ := hx
  refine ⟨coefficientTowerMap A f t hjk c, ?_, ?_⟩
  · rw [← linearCombination_towerMap A f t hjk c, hc, map_zero]
  · rw [coefficientTowerMap_comp A f t hij hjk c, hcx]

private theorem projectionKernels_antitone
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) :
    Antitone (fun n ↦ RingHom.ker (inverseLimitProj A f n)) := by
  apply antitone_nat_of_succ_le
  intro n x hx
  apply RingHom.mem_ker.mpr
  rw [← inverseLimitProj_compatible A f n x, RingHom.mem_ker.mp hx, map_zero]

private theorem projectionKernels_iInf_eq_bot
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) :
    (⨅ n, RingHom.ker (inverseLimitProj A f n)) = ⊥ := by
  refine le_antisymm (fun x hx => (Submodule.mem_bot Λ).mpr (Subtype.ext (funext fun n =>
    RingHom.mem_ker.mp (Ideal.mem_iInf.mp hx n)))) bot_le

private theorem inverseLimitProj_zero_isLocal
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) :
    IsLocalHom (inverseLimitProj A f 0).toRingHom := by
  refine ⟨fun x hx => ?_⟩
  have hu : IsUnit (inverseLimitProj A f 0 x) := hx
  have hall : ∀ n, IsUnit (inverseLimitProj A f n x) := by
    intro n
    induction n with
    | zero => exact hu
    | succ n ih =>
      apply isUnit_of_map_unit (f n).hom.toRingHom
      show IsUnit ((f n).hom (inverseLimitProj A f (n + 1) x))
      rw [inverseLimitProj_compatible A f n x]
      exact ih
  let y : ∀ n, A n := fun n => ↑((hall n).unit⁻¹)
  have hy : ∀ n, (f n).hom (y (n + 1)) = y n := by
    intro n
    show (f n).hom (↑((hall (n + 1)).unit⁻¹)) = ↑((hall n).unit⁻¹)
    apply Units.eq_inv_of_mul_eq_one_left
    show inverseLimitProj A f n x * (f n).hom (↑((hall (n + 1)).unit⁻¹)) = 1
    rw [← inverseLimitProj_compatible A f n x, ← map_mul]
    show (f n).hom (↑((hall (n + 1)).unit) *
      ↑((hall (n + 1)).unit⁻¹)) = 1
    rw [(hall (n + 1)).unit.mul_inv, map_one]
  exact isUnit_iff_exists_inv.mpr
    ⟨⟨y, hy⟩, Subtype.ext (funext fun n => (hall n).unit.mul_inv)⟩

private theorem inverseLimit_isLocalRing
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) :
    IsLocalRing (inverseLimit A f) := by
  let : IsLocalHom (inverseLimitProj A f 0).toRingHom :=
    inverseLimitProj_zero_isLocal A f
  exact RingHom.domain_isLocalRing (inverseLimitProj A f 0).toRingHom

private theorem inverseLimit_residueEquiv
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    Nonempty (ResidueField (inverseLimit A f) ≃ₐ[Λ] k) := by
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  let : IsLocalHom (inverseLimitProj A f 0).toRingHom :=
    inverseLimitProj_zero_isLocal A f
  let : IsLocalHom (inverseLimitProj A f 0) :=
    ⟨fun x hx => (inverseLimitProj_zero_isLocal A f).map_nonunit x hx⟩
  let e := ResidueField.mapAlgHom (inverseLimitProj A f 0)
  have he : Function.Bijective e := by
    refine ⟨e.toRingHom.injective, fun y => ?_⟩
    obtain ⟨a, rfl⟩ := residue_surjective y
    obtain ⟨x, rfl⟩ := inverseLimitProj_surjective A f hsurj 0 a
    exact ⟨residue (inverseLimit A f) x, ResidueField.mapAlgHom_residue _ _⟩
  exact ⟨(AlgEquiv.ofBijective e he).trans (A 0).residueEquiv⟩

private theorem maximalIdeal_pow_le_projectionKernel
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    ∃ m, maximalIdeal (inverseLimit A f) ^ m ≤
      RingHom.ker (inverseLimitProj A f n) := by
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  obtain ⟨m, hm⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (A n)).mp inferInstance
  refine ⟨m, (Ideal.map_eq_bot_iff_le_ker _).mp ?_⟩
  rw [Ideal.map_pow]
  show ((maximalIdeal (inverseLimit A f)).map
    (inverseLimitProj A f n).toRingHom) ^ m = ⊥
  rw [
    IsLocalRing.map_maximalIdeal_of_surjective
      (inverseLimitProj A f n).toRingHom (inverseLimitProj_surjective A f hsurj n)]
  exact hm

/-- An element of the inverse limit is in the maximal ideal iff its image in a term is. -/
private theorem mem_maximalIdeal_iff_proj_mem
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ) (x : inverseLimit A f) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    x ∈ maximalIdeal (inverseLimit A f) ↔ inverseLimitProj A f n x ∈ maximalIdeal (A n) := by
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  let : IsLocalHom (inverseLimitProj A f n).toRingHom :=
    IsLocalHom.of_surjective _ (inverseLimitProj_surjective A f hsurj n)
  rw [← IsLocalRing.maximalIdeal_comap (inverseLimitProj A f n).toRingHom]
  rfl

private theorem maximalIdeal_projection_surjective
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ)
    (y : maximalIdeal (A n)) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    ∃ x : maximalIdeal (inverseLimit A f),
      inverseLimitProj A f n x = y := by
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  obtain ⟨x, hx⟩ := inverseLimitProj_surjective A f hsurj n y
  exact ⟨⟨x, (mem_maximalIdeal_iff_proj_mem A f hsurj n x).mpr (hx ▸ y.property)⟩, hx⟩

private theorem finite_maximalIdeal_generators_lift
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    ∃ t : Finset (inverseLimit A f),
      t.card ≤ Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) ∧
      (∀ x ∈ t, x ∈ maximalIdeal (inverseLimit A f)) ∧
      maximalIdeal (A n) =
        Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f))) := by
  classical
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  obtain ⟨t, htcard, htspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal (A n)).fg_of_isNoetherianRing
  have htmem (a : t) : (a : A n) ∈ maximalIdeal (A n) := by
    rw [← htspan]
    exact Ideal.subset_span a.property
  let lift (a : t) : maximalIdeal (inverseLimit A f) :=
    (maximalIdeal_projection_surjective A f hsurj n ⟨a, htmem a⟩).choose
  have hlift (a : t) : inverseLimitProj A f n (lift a) = (a : A n) :=
    (maximalIdeal_projection_surjective A f hsurj n ⟨a, htmem a⟩).choose_spec
  let s : Finset (inverseLimit A f) := t.attach.image (fun a => (lift a : inverseLimit A f))
  refine ⟨s, ?_, ?_, ?_⟩
  · calc
      s.card ≤ t.attach.card := Finset.card_image_le
      _ = t.card := Finset.card_attach
      _ = Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) := by
        rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
        exact htcard
  · intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    exact (lift a).property
  · apply le_antisymm
    · rw [← htspan]
      apply Ideal.span_le.mpr
      intro a ha
      have hat : a ∈ t := Finset.mem_coe.mp ha
      have hs : (lift ⟨a, hat⟩ : inverseLimit A f) ∈ s := Finset.mem_image.mpr ⟨⟨a, hat⟩,
        Finset.mem_attach _ _, rfl⟩
      exact Ideal.subset_span ⟨lift ⟨a, hat⟩, Finset.mem_coe.mpr hs,
        hlift ⟨a, hat⟩⟩
    · apply Ideal.span_le.mpr
      rintro a ⟨x, hx, rfl⟩
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact (mem_maximalIdeal_iff_proj_mem A f hsurj n _).mp (lift a).property

private theorem image_inverseLimitProj_succ
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n) (t : Set (inverseLimit A f)) (n : ℕ) :
    (fun x => (f n).hom.toRingHom (inverseLimitProj A f (n + 1) x)) '' t =
      inverseLimitProj A f n '' t :=
  Set.image_congr fun x _ => inverseLimitProj_compatible A f n x

private theorem maximalIdeal_generators_propagate
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ)
    (t : Finset (inverseLimit A f))
    (ht : letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
      ∀ x ∈ t, x ∈ maximalIdeal (inverseLimit A f))
    (hd : Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) =
      Module.finrank (ResidueField (A (n + 1))) (CotangentSpace (A (n + 1))))
    (hgen : maximalIdeal (A n) =
      Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f)))) :
    maximalIdeal (A (n + 1)) =
      Ideal.span ((inverseLimitProj A f (n + 1)) '' (↑t : Set (inverseLimit A f))) := by
  classical
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  let s : Finset (A (n + 1)) := t.image (inverseLimitProj A f (n + 1))
  have hs : ∀ x ∈ s, x ∈ maximalIdeal (A (n + 1)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_maximalIdeal_iff_proj_mem A f hsurj (n + 1) y).mp (ht y hy)
  have hdim : (maximalIdeal (A (n + 1))).spanFinrank =
      (maximalIdeal (A n)).spanFinrank := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact hd.symm
  have hgens : maximalIdeal (A n) =
      Ideal.span ((f n).hom.toRingHom '' (↑s : Set (A (n + 1)))) := by
    calc
      maximalIdeal (A n) =
          Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f))) := hgen
      _ = Ideal.span ((fun x : inverseLimit A f =>
            (f n).hom.toRingHom (inverseLimitProj A f (n + 1) x)) ''
              (↑t : Set (inverseLimit A f))) :=
            congrArg Ideal.span (image_inverseLimitProj_succ A f t n).symm
      _ = Ideal.span ((f n).hom.toRingHom '' (↑s : Set (A (n + 1)))) := by
        simp only [s, Finset.coe_image, Set.image_image]
  simpa only [s, Finset.coe_image, Set.image_image] using
    maximalIdeal_eq_span_of_equal_cotangent_finrank (f n).hom.toRingHom (hsurj n) hdim s hs hgens

private theorem maximalIdeal_generators_descend
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) (n : ℕ)
    (t : Finset (inverseLimit A f))
    (hgen : maximalIdeal (A (n + 1)) =
      Ideal.span ((inverseLimitProj A f (n + 1)) ''
        (↑t : Set (inverseLimit A f)))) :
    maximalIdeal (A n) =
      Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f))) := by
  calc
    maximalIdeal (A n) =
        (maximalIdeal (A (n + 1))).map (f n).hom.toRingHom :=
      (IsLocalRing.map_maximalIdeal_of_surjective (f n).hom.toRingHom (hsurj n)).symm
    _ = (Ideal.span ((inverseLimitProj A f (n + 1)) ''
          (↑t : Set (inverseLimit A f)))).map (f n).hom.toRingHom := by rw [hgen]
    _ = Ideal.span ((inverseLimitProj A f n) ''
          (↑t : Set (inverseLimit A f))) := by
      rw [Ideal.map_span, Set.image_image, image_inverseLimitProj_succ A f t n]

private theorem eventual_finite_maximalIdeal_generators
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (hbounded : ∃ d : ℕ,
      ∀ n, Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) ≤ d) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    ∃ N r : ℕ, ∃ t : Finset (inverseLimit A f),
      t.card ≤ r ∧
      (∀ x ∈ t, x ∈ maximalIdeal (inverseLimit A f)) ∧
      ∀ n, N ≤ n → maximalIdeal (A n) =
        Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f))) := by
  classical
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  obtain ⟨N, r, hstable⟩ := cotangent_finrank_eventually_constant A f hsurj hbounded
  obtain ⟨t, htcard, htmem, hgen⟩ := finite_maximalIdeal_generators_lift A f hsurj N
  refine ⟨N, r, t, ?_, htmem, ?_⟩
  · simpa only [hstable N le_rfl] using htcard
  · intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hgen
    | succ n hn ih =>
      exact maximalIdeal_generators_propagate A f hsurj n t htmem
        ((hstable n hn).trans (hstable (n + 1) (Nat.le_succ_of_le hn)).symm) ih

private theorem finite_maximalIdeal_generators_all
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (hbounded : ∃ d : ℕ,
      ∀ n, Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) ≤ d) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    ∃ t : Finset (inverseLimit A f),
      (∀ x ∈ t, x ∈ maximalIdeal (inverseLimit A f)) ∧
      ∀ n, maximalIdeal (A n) =
        Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f))) := by
  classical
  obtain ⟨N, _, t, _, htmem, hhigh⟩ :=
    eventual_finite_maximalIdeal_generators A f hsurj hbounded
  refine ⟨t, htmem, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact hhigh n hn
  · have hlow : ∀ k m : ℕ, N - m = k → m ≤ N →
        maximalIdeal (A m) =
          Ideal.span ((inverseLimitProj A f m) '' (↑t : Set (inverseLimit A f))) := by
      intro k
      induction k with
      | zero =>
        intro m hdiff hm
        obtain rfl : m = N := by omega
        exact hhigh _ le_rfl
      | succ k ih =>
        intro m hdiff hm
        exact maximalIdeal_generators_descend A f hsurj m t
          (ih (m + 1) (by omega) (by omega))
    exact hlow (N - n) n rfl (by omega)

private theorem affine_cosets_antitone_stabilize
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsArtinian R M]
    (V : ℕ → Submodule R M) (a : ℕ → M) (hV : Antitone V)
    (hC : Antitone (fun n => {x : M | x - a n ∈ V n})) :
    ∃ N, ∀ m, N ≤ m →
      {x : M | x - a N ∈ V N} = {x : M | x - a m ∈ V m} := by
  let W : ℕ →o (Submodule R M)ᵒᵈ := ⟨fun n => OrderDual.toDual (V n), hV⟩
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes W
  refine ⟨N, fun m hNm => ?_⟩
  have hVm : V N = V m := congrArg OrderDual.ofDual (hN m hNm)
  have ham : a m - a N ∈ V m := by
    rw [← hVm]
    exact hC hNm (show a m - a m ∈ V m by simp)
  ext x
  refine ⟨fun hx => ?_, fun hx => hC hNm hx⟩
  show x - a m ∈ V m
  have hx' : x - a N ∈ V m := hVm ▸ hx
  rw [show x - a m = (x - a N) - (a m - a N) by abel]
  exact sub_mem hx' ham

private abbrev coefficientFiber
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f) (n : ℕ) :=
  {c : t → A n //
    Fintype.linearCombination (A n)
      (fun a : t => inverseLimitProj A f n a) c = inverseLimitProj A f n y}

private theorem coefficientFiber_nonempty_of_projected_span
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    (hproj : ∀ n, inverseLimitProj A f n y ∈
      Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f))))
    (n : ℕ) : Nonempty (coefficientFiber A f t y n) := by
  classical
  have hrange : Set.range (fun a : t => inverseLimitProj A f n a) =
      (inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f)) :=
    (Set.image_eq_range _ _).symm
  have hy : inverseLimitProj A f n y ∈
      Ideal.span (Set.range (fun a : t => inverseLimitProj A f n a)) := by
    rw [hrange]
    exact hproj n
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (A n)).mp hy
  exact ⟨⟨c, hc⟩⟩

private def coefficientFiberMap
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    {i j : ℕ} (h : i ≤ j) :
    coefficientFiber A f t y j → coefficientFiber A f t y i := by
  intro c
  refine ⟨coefficientTowerMap A f t h c, ?_⟩
  rw [← linearCombination_towerMap A f t h c, c.property, towerMap_proj A f h y]

private theorem coefficientFiberMap_self
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    (i : ℕ) (c : coefficientFiber A f t y i) :
    coefficientFiberMap A f t y (le_refl i) c = c :=
  Subtype.ext (coefficientTowerMap_self A f t i c)

private theorem coefficientFiberMap_comp
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (c : coefficientFiber A f t y k) :
    coefficientFiberMap A f t y hij (coefficientFiberMap A f t y hjk c) =
      coefficientFiberMap A f t y (hij.trans hjk) c :=
  Subtype.ext (coefficientTowerMap_comp A f t hij hjk c)

private theorem coefficientFiber_image_eq_coset
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    {i j : ℕ} (h : i ≤ j) (c₀ : coefficientFiber A f t y j) :
    {x : t → A i | ∃ c : coefficientFiber A f t y j,
      coefficientTowerMap A f t h c = x} =
      {x : t → A i | x - coefficientTowerMap A f t h c₀ ∈
        kernelImage A f hsurj t h} := by
  classical
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(c : t → A j) - c₀, ?_, ?_⟩
    · rw [map_sub, c.property, c₀.property, sub_self]
    · funext a
      simp [coefficientTowerMap, Pi.sub_apply]
  · intro hx
    obtain ⟨d, hd, hdx⟩ := hx
    let c : coefficientFiber A f t y j := ⟨c₀ + d, by
      rw [map_add, c₀.property, hd, add_zero]⟩
    refine ⟨c, ?_⟩
    have hmap : coefficientTowerMap A f t h c =
        coefficientTowerMap A f t h c₀ + coefficientTowerMap A f t h d := by
      funext a
      simp [c, coefficientTowerMap, Pi.add_apply]
    rw [hmap, hdx]
    abel

private def coefficientFiberSystem
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f) :
    DirInvSystem (coefficientFiber A f t y) where
  φ := fun _ _ h => coefficientFiberMap A f t y h
  φ_self := coefficientFiberMap_self A f t y
  φ_comp := fun _ _ _ hij hjk x => coefficientFiberMap_comp A f t y hij hjk x

private theorem coefficientFiberSystem_isMittagLeffler
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    (hne : ∀ n, Nonempty (coefficientFiber A f t y n)) :
    (coefficientFiberSystem A f t y).IsMittagLeffler := by
  classical
  let S := coefficientFiberSystem A f t y
  intro i
  let D : ℕ → Submodule (A i) (t → A i) :=
    fun m => kernelImage A f hsurj t (Nat.le_add_right i m)
  let c₀ (m : ℕ) : coefficientFiber A f t y (i + m) :=
    Classical.choice (hne (i + m))
  let a (m : ℕ) : t → A i :=
    coefficientTowerMap A f t (Nat.le_add_right i m) (c₀ m)
  let C (m : ℕ) : Set (t → A i) :=
    {x | ∃ c : coefficientFiber A f t y (i + m),
      coefficientTowerMap A f t (Nat.le_add_right i m) c = x}
  have hCeq (m : ℕ) : C m = {x | x - a m ∈ D m} :=
    coefficientFiber_image_eq_coset A f hsurj t y (Nat.le_add_right i m) (c₀ m)
  have hD : Antitone D := fun m n hmn =>
    kernelImage_antitone A f hsurj t (Nat.le_add_right i m) (Nat.add_le_add_left hmn i)
  have hC : Antitone C := by
    rintro m n hmn x ⟨c, rfl⟩
    exact ⟨coefficientFiberMap A f t y (Nat.add_le_add_left hmn i) c,
      coefficientTowerMap_comp A f t (Nat.le_add_right i m) (Nat.add_le_add_left hmn i) c⟩
  have hcos : Antitone (fun m => {x : t → A i | x - a m ∈ D m}) := by
    intro m n hmn
    show {x : t → A i | x - a n ∈ D n} ⊆
      {x : t → A i | x - a m ∈ D m}
    rw [← hCeq m, ← hCeq n]
    exact hC hmn
  obtain ⟨N, hN⟩ := affine_cosets_antitone_stabilize D a hD hcos
  have hstable (m : ℕ) (hm : N ≤ m) : C N = C m := by
    rw [hCeq N, hCeq m]
    exact hN m hm
  refine ⟨i + N, Nat.le_add_right i N, fun k hk => ?_⟩
  apply Set.Subset.antisymm
  · exact S.range_mono (Nat.le_add_right i N) hk
  · intro z hz
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right i N).trans hk)
    obtain ⟨d, rfl⟩ := hz
    have hd : coefficientTowerMap A f t (Nat.le_add_right i N) d ∈ C N :=
      ⟨d, rfl⟩
    rw [hstable m (by omega)] at hd
    obtain ⟨c, hc⟩ := hd
    exact ⟨c, Subtype.ext hc⟩

private theorem mem_span_of_projected_span
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (t : Finset (inverseLimit A f)) (y : inverseLimit A f)
    (hproj : ∀ n, inverseLimitProj A f n y ∈
      Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f)))) :
    y ∈ Ideal.span (↑t : Set (inverseLimit A f)) := by
  classical
  let S := coefficientFiberSystem A f t y
  have hne : ∀ n, Nonempty (coefficientFiber A f t y n) :=
    coefficientFiber_nonempty_of_projected_span A f t y hproj
  have hML : S.IsMittagLeffler :=
    coefficientFiberSystem_isMittagLeffler A f hsurj t y hne
  obtain ⟨c, hc⟩ := S.nonempty_limit_of_isMittagLeffler hML hne
  let x (a : t) : inverseLimit A f := ⟨fun n => (c n).1 a, by
    intro n
    have hstep := congrArg (fun z : coefficientFiber A f t y n => (z : t → A n) a)
      (hc (Nat.le_succ n))
    change towerMap A f (Nat.le_succ n) ((c (n + 1)).1 a) = (c n).1 a at hstep
    simpa [towerMap_succ A f (le_refl n) (Nat.le_succ n), towerMap_self] using hstep⟩
  have hsum : (∑ a : t, x a * (a : inverseLimit A f)) = y := by
    apply Subtype.ext
    funext n
    show inverseLimitProj A f n (∑ a : t, x a * (a : inverseLimit A f)) =
      inverseLimitProj A f n y
    have hn := (c n).property
    change (∑ a : t, (c n).1 a * inverseLimitProj A f n a) =
      inverseLimitProj A f n y at hn
    calc
      inverseLimitProj A f n (∑ a : t, x a * (a : inverseLimit A f)) =
          ∑ a : t, inverseLimitProj A f n (x a) * inverseLimitProj A f n a := by simp
      _ = ∑ a : t, (c n).1 a * inverseLimitProj A f n a := rfl
      _ = inverseLimitProj A f n y := hn
  have hrange : Set.range (fun a : t => (a : inverseLimit A f)) =
      (↑t : Set (inverseLimit A f)) :=
    Subtype.range_coe_subtype
  rw [← hrange]
  exact (Submodule.mem_span_range_iff_exists_fun (inverseLimit A f)).mpr
    ⟨x, by simpa only [smul_eq_mul] using hsum⟩

private theorem maximalIdeal_eq_span_of_uniform_generators
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (t : Finset (inverseLimit A f))
    (ht : letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
      ∀ x ∈ t, x ∈ maximalIdeal (inverseLimit A f))
    (hgen : ∀ n, maximalIdeal (A n) =
      Ideal.span ((inverseLimitProj A f n) '' (↑t : Set (inverseLimit A f)))) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    maximalIdeal (inverseLimit A f) = Ideal.span (↑t : Set (inverseLimit A f)) := by
  classical
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  apply le_antisymm
  · intro y hy
    apply mem_span_of_projected_span A f hsurj t y
    intro n
    rw [← hgen n]
    exact (mem_maximalIdeal_iff_proj_mem A f hsurj n y).mp hy
  · exact Ideal.span_le.mpr fun x hx => ht x (Finset.mem_coe.mp hx)

private theorem inverseLimit_maximalIdeal_isHausdorff
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    IsHausdorff (maximalIdeal (inverseLimit A f)) (inverseLimit A f) := by
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  refine isHausdorff_iff.2 fun x hx => ?_
  apply (Submodule.mem_bot (inverseLimit A f)).mp
  show x ∈ (⊥ : Ideal (inverseLimit A f))
  rw [← projectionKernels_iInf_eq_bot A f]
  refine Ideal.mem_iInf.mpr fun n => ?_
  obtain ⟨m, hm⟩ := maximalIdeal_pow_le_projectionKernel A f hsurj n
  apply hm
  simpa using (smodEq_pow_smul_top_iff _ _).mp (hx m)

private theorem inverseLimit_isPrecomplete_of_fg
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (hfg : letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
      (maximalIdeal (inverseLimit A f)).FG) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    IsPrecomplete (maximalIdeal (inverseLimit A f)) (inverseLimit A f) := by
  classical
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  let I : Ideal (inverseLimit A f) := maximalIdeal (inverseLimit A f)
  refine ⟨fun v hv => ?_⟩
  let e (j : ℕ) : ℕ := (maximalIdeal_pow_le_projectionKernel A f hsurj j).choose
  have he (j : ℕ) : I ^ e j ≤ RingHom.ker (inverseLimitProj A f j) :=
    (maximalIdeal_pow_le_projectionKernel A f hsurj j).choose_spec
  have hconst (j m : ℕ) (hm : e j ≤ m) :
      inverseLimitProj A f j (v m) = inverseLimitProj A f j (v (e j)) := by
    have hmem : v (e j) - v m ∈ I ^ e j := by
      exact (smodEq_pow_smul_top_iff _ _).mp (hv hm)
    have hzero : inverseLimitProj A f j (v (e j) - v m) = 0 :=
      RingHom.mem_ker.mp (he j hmem)
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  let x : inverseLimit A f := ⟨fun j => inverseLimitProj A f j (v (e j)), by
    intro j
    let M := max (e j) (e (j + 1))
    calc
      (f j).hom (inverseLimitProj A f (j + 1) (v (e (j + 1)))) =
          (f j).hom (inverseLimitProj A f (j + 1) (v M)) := by
        rw [hconst (j + 1) M (le_max_right _ _)]
      _ = inverseLimitProj A f j (v M) := inverseLimitProj_compatible A f j (v M)
      _ = inverseLimitProj A f j (v (e j)) := hconst j M (le_max_left _ _)⟩
  refine ⟨x, fun n => ?_⟩
  rw [smodEq_pow_smul_top_iff]
  have hgoal : v n - x ∈ I ^ n := by
    obtain ⟨t, ht⟩ := Ideal.FG.pow (n := n) hfg
    rw [← ht]
    apply mem_span_of_projected_span A f hsurj t (v n - x)
    intro j
    let M := max n (e j)
    have hmem : v n - v M ∈ I ^ n := by
      exact (smodEq_pow_smul_top_iff _ _).mp (hv (le_max_left n (e j)))
    have hmap : inverseLimitProj A f j (v n - v M) ∈
        (I ^ n).map (inverseLimitProj A f j) := Ideal.mem_map_of_mem _ hmem
    rw [← ht, Ideal.map_span] at hmap
    have hxj : inverseLimitProj A f j x = inverseLimitProj A f j (v M) :=
      (hconst j M (le_max_right n (e j))).symm
    simpa only [map_sub, hxj] using hmap
  exact hgoal

private theorem inflatedProjectionKernels_iInf_eq_bot
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom) :
    letI : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
    (⨅ n, RingHom.ker (inverseLimitProj A f n) ⊔
      maximalIdeal (inverseLimit A f) ^ n) = ⊥ := by
  let : IsLocalRing (inverseLimit A f) := inverseLimit_isLocalRing A f
  apply le_antisymm _ bot_le
  intro x hx
  have hk : x ∈ (⨅ j, RingHom.ker (inverseLimitProj A f j)) := by
    apply Ideal.mem_iInf.mpr
    intro j
    obtain ⟨e, he⟩ := maximalIdeal_pow_le_projectionKernel A f hsurj j
    have hK : RingHom.ker (inverseLimitProj A f (max j e)) ≤
        RingHom.ker (inverseLimitProj A f j) :=
      projectionKernels_antitone A f (le_max_left j e)
    have hM : maximalIdeal (inverseLimit A f) ^ (max j e) ≤
        RingHom.ker (inverseLimitProj A f j) :=
      (Ideal.pow_le_pow_right (le_max_right j e)).trans he
    exact (sup_le hK hM) (Ideal.mem_iInf.mp hx (max j e))
  rwa [projectionKernels_iInf_eq_bot A f] at hk

/-- **Stacks Project, Tag 06SF (first assertion).** If the transition maps in a tower of
Artinian local `Λ`-algebras are surjective and the dimensions of the cotangent spaces are
bounded, then its inverse limit is a Noetherian complete local algebra whose residue field is
the specified field `k`. -/
@[stacks 06SF "complete local inverse limit"]
theorem inverseLimit_isObjectOfCompleteLocalAlgCat
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (hbounded : ∃ d : ℕ,
      ∀ n, Module.finrank (ResidueField (A n)) (CotangentSpace (A n)) ≤ d) :
    ∃ h : IsNoetherianCompleteLocalRing (inverseLimit A f),
      letI : IsLocalRing (inverseLimit A f) := h.isLocal
      Nonempty (ResidueField (inverseLimit A f) ≃ₐ[Λ] k) := by
  have hlocal := inverseLimit_isLocalRing A f
  have hcomplete : IsNoetherianCompleteLocalRing (inverseLimit A f) := by
    let : IsLocalRing (inverseLimit A f) := hlocal
    have hfg : (maximalIdeal (inverseLimit A f)).FG := by
      obtain ⟨t, ht, hgen⟩ := finite_maximalIdeal_generators_all A f hsurj hbounded
      rw [maximalIdeal_eq_span_of_uniform_generators A f hsurj t ht hgen]
      exact Submodule.fg_span t.finite_toSet
    have hadic : IsAdicComplete (maximalIdeal (inverseLimit A f))
        (inverseLimit A f) :=
      { toIsHausdorff := inverseLimit_maximalIdeal_isHausdorff A f hsurj
        toIsPrecomplete := inverseLimit_isPrecomplete_of_fg A f hsurj hfg }
    exact ⟨complete_local_ring_noetherian _ hadic hfg, hlocal, hadic⟩
  exact ⟨hcomplete, inverseLimit_residueEquiv A f hsurj⟩

/-- **Stacks Project, Tag 06SF (second assertion).** Under the same hypotheses, the kernels of
the projections from the inverse limit are cofinal with the powers of its maximal ideal, and
hence define its maximal-ideal-adic topology. -/
@[stacks 06SF "projection kernels define the adic topology"]
theorem kernel_projections_define_maximalIdeal_adicTopology
    (A : ℕ → ArtinianLocalAlgCat.{u, v, w} Λ k)
    (f : ∀ n, A (n + 1) ⟶ A n)
    (hsurj : ∀ n, Function.Surjective (f n).hom)
    (h : IsNoetherianCompleteLocalRing (inverseLimit A f)) :
    letI : IsLocalRing (inverseLimit A f) := h.isLocal
    Ideal.IsAdicFiltration (maximalIdeal (inverseLimit A f))
      (fun n ↦ RingHom.ker (inverseLimitProj A f n)) := by
  let : IsLocalRing (inverseLimit A f) := h.isLocal
  refine ⟨fun n => ?_, fun n => maximalIdeal_pow_le_projectionKernel A f hsurj n⟩
  let K : ℕ → Ideal (inverseLimit A f) :=
    fun j => RingHom.ker (inverseLimitProj A f j)
  let H : ℕ → Ideal (inverseLimit A f) :=
    fun j => K j ⊔ maximalIdeal (inverseLimit A f) ^ j
  have hH : Antitone H := antitone_nat_of_succ_le fun j =>
    sup_le_sup (projectionKernels_antitone A f (Nat.le_succ j))
      (Ideal.pow_le_pow_right (Nat.le_succ j))
  have hHpow : ∀ j, maximalIdeal (inverseLimit A f) ^ j ≤ H j :=
    fun _ => le_sup_right
  have hHinf : (⨅ j, H j) = ⊥ := inflatedProjectionKernels_iInf_eq_bot A f hsurj
  let B : CompleteLocalAlgCat.{u, v, w} Λ k :=
    { carrier := inverseLimit A f
      completeLocal := h
      residueEquiv := Classical.choice (inverseLimit_residueEquiv A f hsurj) }
  obtain ⟨m, hm⟩ := (quotient_filtration_isAdic B H hH hHpow).1 n
  refine ⟨m, (show K m ≤ H m from le_sup_left).trans ?_⟩
  have hmax : maximalIdeal B = maximalIdeal (inverseLimit A f) := rfl
  rw [hmax] at hm
  have hm' : (H m).map (Ideal.Quotient.mk (⨅ j, H j)) ≤
      (maximalIdeal (inverseLimit A f) ^ n).map
        (Ideal.Quotient.mk (⨅ j, H j)) := by
    rw [Ideal.map_pow]
    exact hm
  have hc := Ideal.comap_mono (f := Ideal.Quotient.mk (⨅ j, H j)) hm'
  rw [Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk] at hc
  simpa [hHinf] using hc

end

end Deformation
