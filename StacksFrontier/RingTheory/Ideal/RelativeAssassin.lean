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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparison of the candidate relative assassins of a module over a ring map

Let `R → S` be a ring map and let `N` be an `S`-module. Writing `𝔭 = R ∩ 𝔮` for the
contraction of a prime `𝔮` of `S`, there are six sets of primes of `S` attached to this data:

* `A`: the primes `𝔮` with `𝔮 ∈ Ass_S(N ⊗_R κ(𝔭))`;
* `A'`: the primes `𝔮` in the image of `Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))` under the canonical map
  `Spec(S ⊗_R κ(𝔭)) → Spec(S)`;
* `A_fin`: the primes `𝔮` with `𝔮 ∈ Ass_S(N / 𝔭N)`;
* `A'_fin`: the primes `𝔮` with `𝔮 ∈ Ass_S(N / 𝔭'N)` for *some* prime `𝔭'` of `R`;
* `B`: the primes `𝔮` with `𝔮 ∈ Ass_S(N ⊗_R M)` for some `R`-module `M`;
* `B_fin`: the same with `M` a finite `R`-module.

They are always related by `A = A'`, by `A_fin ⊆ A`, `B_fin ⊆ B`, `A_fin ⊆ A'_fin ⊆ B_fin` and
`A ⊆ B`; if `S` is Noetherian then `A = A_fin` and `B = B_fin`; if `N` is flat over `R` then
`A = A_fin = A'_fin` and `B = B_fin`; and if moreover `R` is Noetherian all six coincide.

## Main results

* `Module.relativeAssassin_comparison`: the five comparisons above, for the six sets
  described by the hypotheses `hA`, `hA'`, `hAfin`, `hA'fin`, `hB`, `hBfin`.

## Implementation notes

`Ass` is Mathlib's `associatedPrimes`: the primes equal to the *radical* of the annihilator of
an element. This agrees with the annihilator reading over a Noetherian ring
(`isAssociatedPrime_iff`).

`N / 𝔭N` is spelled `N ⧸ (Ideal.map (algebraMap R S) 𝔭 • ⊤)`, which is canonically isomorphic
to `N ⊗[R] (R ⧸ 𝔭)`. The fibre module of `A'` is spelled as the base change
`(S ⊗[R] κ(𝔭)) ⊗[S] N`, there being no `Module (S ⊗[R] κ(𝔭)) (N ⊗[R] κ(𝔭))` instance in
Mathlib; the two are the same `S`-module by
`TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N κ(𝔭)` (after `TensorProduct.comm`).

`B` and `B_fin` quantify over `R`-modules in `Type (max u v)`, where `R : Type u` and
`S : Type v`. This universe contains a copy of every residue field `κ(𝔭)` of `R`, and a witness
for every element of `B` computed in any universe.

## References

* [StacksProject 05GB](https://stacks.math.columbia.edu/tag/05GB)

## Tags

associated prime, relative assassin, fibre ring, flat module
-/

@[expose] public section

universe u v w

open Submodule TensorProduct

namespace Stacks.AssociatedPrimes.RelativeAssassin

/-! ### Associated primes under restriction of scalars -/

section RestrictScalars

variable {S : Type*} (T : Type*) [CommRing S] [CommRing T] [Algebra S T]
  {M : Type*} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower S T M]

/-- The annihilator over `S` of an element of a `T`-module is the contraction of its
annihilator over `T`. -/
private theorem colon_bot_comap (z : M) :
    (⊥ : Submodule S M).colon {z} = ((⊥ : Submodule T M).colon {z}).comap (algebraMap S T) := by
  ext s
  simp only [Ideal.mem_comap, mem_colon_singleton, mem_bot, algebraMap_smul]

private theorem radical_colon_bot_comap (z : M) :
    ((⊥ : Submodule S M).colon {z}).radical =
      (((⊥ : Submodule T M).colon {z}).radical).comap (algebraMap S T) := by
  rw [Ideal.comap_radical, colon_bot_comap T]

/-- Contraction carries associated primes over `T` to associated primes over `S`. -/
private theorem associatedPrimes_image_comap_subset :
    Ideal.comap (algebraMap S T) '' associatedPrimes T M ⊆ associatedPrimes S M := by
  rintro q ⟨Q, ⟨hQ, z, hz⟩, rfl⟩
  exact ⟨inferInstance, z, by rw [hz]; exact (radical_colon_bot_comap T z).symm⟩

/-- If contraction along `S → T` reflects primality, then it carries the associated primes over
`T` *onto* the associated primes over `S`. -/
private theorem associatedPrimes_eq_image_comap
    (h : ∀ J : Ideal T, (J.comap (algebraMap S T)).IsPrime → J.IsPrime) :
    associatedPrimes S M = Ideal.comap (algebraMap S T) '' associatedPrimes T M := by
  refine le_antisymm ?_ (associatedPrimes_image_comap_subset T)
  rintro q ⟨hq, z, hz⟩
  refine ⟨((⊥ : Submodule T M).colon {z}).radical, ⟨h _ ?_, z, rfl⟩, ?_⟩ <;>
    rw [← radical_colon_bot_comap T z]
  · exact hz ▸ hq
  · exact hz.symm

end RestrictScalars

/-- Contraction along a ring map whose target is covered by units times the image reflects
primality. -/
private theorem isPrime_of_comap_isPrime {S T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    (h : ∀ x : T, ∃ u : T, IsUnit u ∧ ∃ s : S, u * x = algebraMap S T s)
    {J : Ideal T} (hJ : (J.comap (algebraMap S T)).IsPrime) : J.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun htop => hJ.ne_top (by simp [htop]), fun {a b} hab => ?_⟩
  obtain ⟨u, hu, sa, ha⟩ := h a
  obtain ⟨v, hv, sb, hb⟩ := h b
  have key : sa * sb ∈ J.comap (algebraMap S T) := by
    have e : algebraMap S T (sa * sb) = u * v * (a * b) := by rw [map_mul, ← ha, ← hb]; ring
    rw [Ideal.mem_comap, e]
    exact J.mul_mem_left _ hab
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨w', hw'⟩ := hv.exists_right_inv
  rcases hJ.mem_or_mem key with h1 | h1
  · left
    have h2 : u * a ∈ J := ha ▸ h1
    have h3 : a = w * (u * a) := by rw [← mul_assoc, mul_comm w u, hw, one_mul]
    exact h3 ▸ J.mul_mem_left _ h2
  · right
    have h2 : v * b ∈ J := hb ▸ h1
    have h3 : b = w' * (v * b) := by rw [← mul_assoc, mul_comm w' v, hw', one_mul]
    exact h3 ▸ J.mul_mem_left _ h2

/-! ### Radicals of annihilators -/

section Radical

variable {S : Type*} [CommRing S]

/-- An ideal sandwiched between an ideal with prime radical `q` and `q` itself has radical `q`. -/
private theorem radical_eq_of_le_of_le {q I J : Ideal S} (hq : q.IsPrime) (hI : q = I.radical)
    (h1 : I ≤ J) (h2 : J ≤ q) : q = J.radical :=
  le_antisymm (hI ▸ Ideal.radical_mono h1) ((Ideal.radical_mono h2).trans_eq hq.radical)

/-- An ideal sandwiched between a power of a prime `q` and `q` itself has radical `q`. -/
private theorem radical_eq_of_pow_le_of_le {q J : Ideal S} (hq : q.IsPrime) {n : ℕ} (hn : n ≠ 0)
    (h1 : q ^ n ≤ J) (h2 : J ≤ q) : q = J.radical :=
  radical_eq_of_le_of_le hq (by rw [Ideal.radical_pow q hn, hq.radical]) h1 h2

variable {P Q : Type*} [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]

/-- The annihilator of an element is contained in the annihilator of its image under an
`S`-linear map. -/
private theorem colon_le_colon_map (f : P →ₗ[S] Q) (z : P) :
    (⊥ : Submodule S P).colon {z} ≤ (⊥ : Submodule S Q).colon {f z} := by
  intro s hs
  rw [mem_colon_singleton, mem_bot] at hs ⊢
  rw [← map_smul, hs, map_zero]

/-- An injective `S`-linear map preserves the annihilator of an element. -/
private theorem colon_map_eq (f : P →ₗ[S] Q) (hf : Function.Injective f) (z : P) :
    (⊥ : Submodule S Q).colon {f z} = (⊥ : Submodule S P).colon {z} := by
  refine le_antisymm (fun s hs => ?_) (colon_le_colon_map f z)
  rw [mem_colon_singleton, mem_bot] at hs ⊢
  exact hf (by rw [map_smul, hs, map_zero])

/-- An element killing `z` lies in any ideal equal to the radical of the annihilator of `z`. -/
private theorem mem_of_smul_eq_zero {q : Ideal S} {z : P}
    (hz : q = ((⊥ : Submodule S P).colon {z}).radical) {a : S} (h : a • z = 0) : a ∈ q := by
  rw [hz]
  exact Ideal.le_radical (by rwa [mem_colon_singleton, mem_bot])

/-- Over a Noetherian ring, a prime power `q ^ (m + 1)` with `q` the radical of the annihilator of
`z` is generated by finitely many elements, all of which kill `z`. -/
private theorem exists_finset_span_pow_smul_eq_zero [IsNoetherianRing S] {q : Ideal S} {z : P}
    (hz : q = ((⊥ : Submodule S P).colon {z}).radical) :
    ∃ (m : ℕ) (G : Finset S), Submodule.span S (G : Set S) = q ^ (m + 1) ∧
      ∀ g ∈ q ^ (m + 1), g • z = 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_radical_pow_le_of_fg ((⊥ : Submodule S P).colon {z})
    (by rw [← hz]; exact IsNoetherian.noetherian q)
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian (q ^ (m + 1))
  refine ⟨m, G, hG, fun g hg => ?_⟩
  have hg' := hm (by rw [← hz]; exact Ideal.pow_le_pow_right (Nat.le_succ m) hg)
  rwa [mem_colon_singleton, mem_bot] at hg'

end Radical

/-! ### Localization of modules and associated primes

Parts of Stacks 05BZ and 05C0, for an `S`-linear localization map along a submonoid of `R`. -/

section CompEquiv

variable {R : Type*} [CommRing R] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]

private theorem isLocalizedModule_comp_equiv (T : Submonoid R) (f : A →ₗ[R] B) (e : C ≃ₗ[R] A)
    [IsLocalizedModule T f] : IsLocalizedModule T (f ∘ₗ (e : C →ₗ[R] A)) := by
  constructor
  · exact IsLocalizedModule.map_units f
  · intro y
    obtain ⟨⟨x, t⟩, hx⟩ := IsLocalizedModule.surj T f y
    exact ⟨⟨e.symm x, t⟩, by simpa using hx⟩
  · intro x₁ x₂ h
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) (by simpa using h)
    exact ⟨t, e.injective (by simpa only [Submonoid.smul_def, map_smul] using ht)⟩

end CompEquiv

section Localized

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  {M' : Type*} [AddCommGroup M'] [Module S M'] [Module R M'] [IsScalarTower R S M']

/-- Finitely many elements each killed by an element of a submonoid are killed by a single
element of it. -/
private theorem exists_forall_smul_eq_zero {P : Type*} [AddCommGroup P] [Module R P]
    (T : Submonoid R) (s : Finset P) (h : ∀ x ∈ s, ∃ r ∈ T, r • x = 0) :
    ∃ r ∈ T, ∀ x ∈ s, r • x = 0 := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert a s ha ih =>
      obtain ⟨r, hr, hrs⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
      obtain ⟨r', hr', hr'a⟩ := h a (Finset.mem_insert_self a s)
      refine ⟨r' * r, mul_mem hr' hr, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm, mul_smul, hr'a, smul_zero]
      · rw [mul_smul, hrs x hx, smul_zero]

/-- A prime associated to a localization avoids the denominators. -/
private theorem algebraMap_notMem_of_mem_associatedPrimes (T : Submonoid R) (f : M →ₗ[S] M')
    [IsLocalizedModule T (f.restrictScalars R)] {q : Ideal S} (h : q ∈ associatedPrimes S M')
    {r : R} (hr : r ∈ T) : algebraMap R S r ∉ q := by
  obtain ⟨hq, w, hw⟩ := h
  intro hmem
  rw [hw, Ideal.mem_radical_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  rw [mem_colon_singleton, ← map_pow, algebraMap_smul, mem_bot] at hk
  have hw0 : w = 0 :=
    IsLocalizedModule.smul_injective (f.restrictScalars R) ⟨r ^ k, pow_mem hr k⟩
      (by simpa [Submonoid.smul_def] using hk)
  exact hq.ne_top (by rw [hw, hw0]; simp)

/-- An element killed by the image under a localization map is killed by a denominator. -/
private theorem exists_smul_eq_zero_of_map_eq_zero (T : Submonoid R) (f : M →ₗ[S] M')
    [IsLocalizedModule T (f.restrictScalars R)] {x : M} (h : f x = 0) : ∃ r ∈ T, r • x = 0 := by
  obtain ⟨⟨r, hr⟩, h'⟩ := (IsLocalizedModule.eq_zero_iff T (f.restrictScalars R)).mp h
  exact ⟨r, hr, h'⟩

/-- A prime associated to a localization comes from an element `w` which is the image of an
element `z` of the module up to a denominator `r`. -/
private theorem exists_smul_eq_of_mem_associatedPrimes (T : Submonoid R) (f : M →ₗ[S] M')
    [IsLocalizedModule T (f.restrictScalars R)] {q : Ideal S} (h : q ∈ associatedPrimes S M') :
    q.IsPrime ∧ ∃ (w : M') (z : M) (r : R), r ∈ T ∧
      q = ((⊥ : Submodule S M').colon {w}).radical ∧
      ∀ t : S, f (t • z) = (t * algebraMap R S r) • w := by
  obtain ⟨hq, w, hw⟩ := h
  obtain ⟨⟨z, ⟨r, hr⟩⟩, hzr⟩ := IsLocalizedModule.surj T (f.restrictScalars R) w
  refine ⟨hq, w, z, r, hr, hw, fun t => ?_⟩
  have hfz : f z = algebraMap R S r • w := by
    simpa [Submonoid.smul_def, algebraMap_smul] using hzr.symm
  rw [map_smul, hfz, smul_smul]

/-- **Stacks 05BZ (2)**: a prime avoiding the denominators and associated to a module is
associated to its localization. -/
private theorem mem_associatedPrimes_of_isLocalizedModule (T : Submonoid R) (f : M →ₗ[S] M')
    [IsLocalizedModule T (f.restrictScalars R)] {q : Ideal S}
    (hT : ∀ r ∈ T, algebraMap R S r ∉ q) (h : q ∈ associatedPrimes S M) :
    q ∈ associatedPrimes S M' := by
  obtain ⟨hq, z, hz⟩ := h
  refine ⟨hq, f z, radical_eq_of_le_of_le hq hz (colon_le_colon_map f z) fun s hs => ?_⟩
  rw [mem_colon_singleton, mem_bot] at hs
  obtain ⟨r, hr, hrz⟩ := exists_smul_eq_zero_of_map_eq_zero T f (x := s • z)
    (by rwa [map_smul])
  have key : algebraMap R S r * s ∈ q :=
    mem_of_smul_eq_zero hz (by rwa [mul_smul, algebraMap_smul])
  exact (hq.mem_or_mem key).resolve_left (hT r hr)

/-- **Stacks 05C0**: if the denominators act injectively, a prime associated to the localization
is associated to the module. -/
private theorem mem_associatedPrimes_of_isLocalizedModule_of_isSMulRegular (T : Submonoid R)
    (f : M →ₗ[S] M') [IsLocalizedModule T (f.restrictScalars R)]
    (hreg : ∀ r ∈ T, IsSMulRegular M r) {q : Ideal S} (h : q ∈ associatedPrimes S M') :
    q ∈ associatedPrimes S M := by
  have hT : ∀ r ∈ T, algebraMap R S r ∉ q :=
    fun r hr => algebraMap_notMem_of_mem_associatedPrimes T f h hr
  obtain ⟨hq, w, z, r, hr, hw, hfz⟩ := exists_smul_eq_of_mem_associatedPrimes T f h
  refine ⟨hq, z, radical_eq_of_le_of_le hq hw (fun s hs => ?_) fun s hs => ?_⟩
  · rw [mem_colon_singleton, mem_bot] at hs ⊢
    obtain ⟨r'', hr'', h'⟩ := exists_smul_eq_zero_of_map_eq_zero T f (x := s • z)
      (by rw [hfz, mul_comm, mul_smul, hs, smul_zero])
    exact hreg r'' hr'' (h'.trans (smul_zero r'').symm)
  · rw [mem_colon_singleton, mem_bot] at hs
    have h0 : (s * algebraMap R S r) • w = 0 := by rw [← hfz, hs, map_zero]
    exact (hq.mem_or_mem (mem_of_smul_eq_zero hw h0)).resolve_right (hT r hr)

/-- **Stacks 05BZ (3)**: over a Noetherian ring, a prime associated to a localization is
associated to the module. -/
private theorem mem_associatedPrimes_of_isLocalizedModule_of_isNoetherianRing [IsNoetherianRing S]
    (T : Submonoid R) (f : M →ₗ[S] M') [IsLocalizedModule T (f.restrictScalars R)] {q : Ideal S}
    (h : q ∈ associatedPrimes S M') : q ∈ associatedPrimes S M := by
  classical
  have hT : ∀ r ∈ T, algebraMap R S r ∉ q :=
    fun r hr => algebraMap_notMem_of_mem_associatedPrimes T f h hr
  obtain ⟨hq, w, z, r, hr, hw, hfz⟩ := exists_smul_eq_of_mem_associatedPrimes T f h
  obtain ⟨m, G, hG, hpow⟩ := exists_finset_span_pow_smul_eq_zero hw
  have hker : ∀ x ∈ G.image (fun g : S => g • z), ∃ r' ∈ T, r' • x = 0 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    have hgq : g ∈ q ^ (m + 1) := by rw [← hG]; exact Submodule.subset_span hg
    exact exists_smul_eq_zero_of_map_eq_zero T f
      (by rw [hfz, mul_comm, mul_smul, hpow g hgq, smul_zero])
  obtain ⟨r', hr', hr'G⟩ := exists_forall_smul_eq_zero T (G.image (fun g : S => g • z)) hker
  refine ⟨hq, algebraMap R S r' • z, radical_eq_of_pow_le_of_le hq (Nat.succ_ne_zero m) ?_ ?_⟩
  · rw [← hG, Submodule.span_le]
    intro g hg
    have h1 : algebraMap R S r' • (g • z) = 0 := by
      rw [algebraMap_smul]
      exact hr'G _ (Finset.mem_image_of_mem _ hg)
    simp only [SetLike.mem_coe, mem_colon_singleton, mem_bot]
    rw [smul_smul, mul_comm, ← smul_smul]
    exact h1
  · intro s hs
    rw [mem_colon_singleton, mem_bot, smul_smul] at hs
    have h0 : (s * algebraMap R S r' * algebraMap R S r) • w = 0 := by
      rw [← hfz, hs, map_zero]
    have h1 := (hq.mem_or_mem (mem_of_smul_eq_zero hw h0)).resolve_right (hT r hr)
    exact (hq.mem_or_mem h1).resolve_right (hT r' hr')

end Localized

/-! ### The fibre ring -/

section Fibre

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Every element of the fibre ring `S ⊗_R κ(𝔭)` becomes an element of the image of `S` after
multiplication by a unit. -/
private theorem exists_isUnit_mul_eq_algebraMap (p : Ideal R) [p.IsPrime]
    (x : S ⊗[R] p.ResidueField) :
    ∃ u : S ⊗[R] p.ResidueField, IsUnit u ∧ ∃ s : S,
      u * x = algebraMap S (S ⊗[R] p.ResidueField) s := by
  obtain ⟨r, hr, s, hs⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one p x
  refine ⟨algebraMap R _ r, ?_, s, ?_⟩
  · have hu : IsUnit (algebraMap R p.ResidueField r) :=
      isUnit_iff_ne_zero.mpr (by simpa [Ideal.algebraMap_residueField_eq_zero] using hr)
    have e : algebraMap R (S ⊗[R] p.ResidueField) r =
        Algebra.TensorProduct.includeRight (algebraMap R p.ResidueField r) := by simp
    exact e ▸ hu.map _
  · rw [← Algebra.smul_def, hs]; simp

/-- The base-change description of the fibre: `(S ⊗_R κ(𝔭)) ⊗_S N ≃ N ⊗_R κ(𝔭)` as
`S`-modules. -/
private noncomputable def fibreEquiv (p : Ideal R) [p.IsPrime] :
    (S ⊗[R] p.ResidueField) ⊗[S] N ≃ₗ[S] N ⊗[R] p.ResidueField :=
  (TensorProduct.comm S _ N).trans
    (AlgebraTensorModule.cancelBaseChange R S S N p.ResidueField)

/-- Stacks 05BY and 05BZ(1) combined for the fibre ring: the primes of `S` associated to
`N ⊗_R κ(𝔭)` are exactly the contractions of the primes of `S ⊗_R κ(𝔭)` associated to the
same module over the fibre ring. -/
private theorem associatedPrimes_fibre (p : Ideal R) [p.IsPrime] :
    associatedPrimes S (N ⊗[R] p.ResidueField) =
      Ideal.comap (algebraMap S (S ⊗[R] p.ResidueField)) ''
        associatedPrimes (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N) := by
  rw [← LinearEquiv.AssociatedPrimes.eq (fibreEquiv (N := N) p)]
  exact associatedPrimes_eq_image_comap _
    fun J hJ => isPrime_of_comap_isPrime (exists_isUnit_mul_eq_algebraMap p) hJ

/-- Associated primes are insensitive to a universe lift of the second tensor factor. -/
private theorem associatedPrimes_uLift (K : Type u) [AddCommGroup K] [Module R K] :
    associatedPrimes S (N ⊗[R] ULift.{v} K) = associatedPrimes S (N ⊗[R] K) :=
  LinearEquiv.AssociatedPrimes.eq
    (AlgebraTensorModule.congr (LinearEquiv.refl S N) ULift.moduleEquiv)

end Fibre

/-! ### The fibre as a localization of `N / 𝔭N` -/

section FibreLocalization

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The image of `R ∖ 𝔭` in `R/𝔭` consists of the nonzerodivisors. -/
private theorem algebraMapSubmonoid_primeCompl (p : Ideal R) [p.IsPrime] :
    Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl = nonZeroDivisors (R ⧸ p) := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by
      simpa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using hr)
  · intro hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨r, ?_, by simp [Ideal.Quotient.algebraMap_eq]⟩
    have hne : (Ideal.Quotient.mk p) r ≠ 0 := nonZeroDivisors.ne_zero hx
    simpa [Ideal.primeCompl, Ideal.Quotient.eq_zero_iff_mem] using hne

/-- `κ(𝔭)` is the localization of `R/𝔭` at `R ∖ 𝔭`. -/
private theorem isLocalizedModule_residueField (p : Ideal R) [p.IsPrime] :
    IsLocalizedModule p.primeCompl
      (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl) p.ResidueField := by
    rw [algebraMapSubmonoid_primeCompl]; infer_instance
  infer_instance

/-- The canonical `S`-linear map `N ⊗_R R/𝔭 → N ⊗_R κ(𝔭)`. -/
private noncomputable def fibreMk (p : Ideal R) [p.IsPrime] :
    N ⊗[R] (R ⧸ p) →ₗ[S] N ⊗[R] p.ResidueField :=
  AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N)
    (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap

/-- The fibre `N ⊗_R κ(𝔭)` is the localization of `N ⊗_R R/𝔭` at `R ∖ 𝔭`. -/
private theorem isLocalizedModule_fibreMk (p : Ideal R) [p.IsPrime] :
    IsLocalizedModule p.primeCompl ((fibreMk (S := S) N p).restrictScalars R) := by
  have hres := isLocalizedModule_residueField (R := R) p
  have key : (fibreMk (S := S) N p).restrictScalars R =
      (TensorProduct.comm R p.ResidueField N : p.ResidueField ⊗[R] N →ₗ[R] N ⊗[R] p.ResidueField)
        ∘ₗ ((AlgebraTensorModule.rTensor (A := R) R N
            (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap)
          ∘ₗ (TensorProduct.comm R N (R ⧸ p) : N ⊗[R] (R ⧸ p) →ₗ[R] (R ⧸ p) ⊗[R] N)) := by
    apply TensorProduct.ext'
    intro n x
    simp [fibreMk]
  rw [key]
  have : IsLocalizedModule p.primeCompl
      ((AlgebraTensorModule.rTensor (A := R) R N
          (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap)
        ∘ₗ (TensorProduct.comm R N (R ⧸ p) : N ⊗[R] (R ⧸ p) →ₗ[R] (R ⧸ p) ⊗[R] N)) :=
    isLocalizedModule_comp_equiv p.primeCompl (AlgebraTensorModule.rTensor (A := R) R N
      (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap)
      (TensorProduct.comm R N (R ⧸ p))
  exact IsLocalizedModule.of_linearEquiv _ _ (TensorProduct.comm R p.ResidueField N)

/-- The ideal `𝔭` annihilates `N ⊗_R R/𝔭`. -/
private theorem smul_eq_zero_of_mem (p : Ideal R) {r : R} (hr : r ∈ p) (z : N ⊗[R] (R ⧸ p)) :
    r • z = 0 := by
  induction z with
  | tmul n x =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right _ _ hr),
        TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- For a flat `N` every element of `R ∖ 𝔭` acts injectively on `N ⊗_R R/𝔭`. -/
@[ega "IV 12.1.1.1" "special case"]
private theorem isSMulRegular_tensor_quotient_of_flat [Module.Flat R N] (p : Ideal R) [p.IsPrime]
    {r : R} (hr : r ∈ p.primeCompl) : IsSMulRegular (N ⊗[R] (R ⧸ p)) r := by
  have : Module.Flat (R ⧸ p) ((R ⧸ p) ⊗[R] N) := Module.Flat.baseChange R (R ⧸ p) N
  have hreg : IsSMulRegular ((R ⧸ p) ⊗[R] N) ((Ideal.Quotient.mk p) r) := by
    refine Module.Flat.isSMulRegular_of_nonZeroDivisors ?_
    exact mem_nonZeroDivisors_of_ne_zero (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)
  intro a b hab
  have h1 : (Ideal.Quotient.mk p) r • (TensorProduct.comm R N (R ⧸ p) a)
      = (Ideal.Quotient.mk p) r • (TensorProduct.comm R N (R ⧸ p) b) := by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul]
    exact congrArg _ hab
  exact (TensorProduct.comm R N (R ⧸ p)).injective (hreg h1)

end FibreLocalization

/-! ### Realising an element of a tensor product on a finitely generated submodule

Every module is the directed colimit of its finitely generated submodules and tensor products
commute with colimits, so a relation between elements of `P ⊗ M` that holds in `P ⊗ M` already
holds in `P ⊗ M₁` for some finitely generated `M₁ ≤ M`. -/

section Colimit

variable {R : Type*} [CommRing R] (P : Type*) [AddCommGroup P] [Module R P]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The `lTensor` form of `Submodule.FG.exists_rTensor_fg_inclusion_eq`: two elements of
`P ⊗ M₀`, for `M₀` a finitely generated submodule of `M`, with the same image in `P ⊗ M` already
have the same image in `P ⊗ M₁` for some finitely generated `M₁` with `M₀ ≤ M₁ ≤ M`. -/
private theorem exists_fg_lTensor_inclusion_eq {M₀ : Submodule R M} (h₀ : M₀.FG)
    {x y : P ⊗[R] M₀} (hxy : M₀.subtype.lTensor P x = M₀.subtype.lTensor P y) :
    ∃ M₁ : Submodule R M, M₁.FG ∧ ∃ hle : M₀ ≤ M₁,
      (M₀.inclusion hle).lTensor P x = (M₀.inclusion hle).lTensor P y := by
  have key : M₀.subtype.rTensor P (TensorProduct.comm R P M₀ x)
      = M₀.subtype.rTensor P (TensorProduct.comm R P M₀ y) := by
    rw [LinearMap.rTensor_comm, LinearMap.rTensor_comm, hxy]
  obtain ⟨M₁, hfg, hle, heq⟩ := h₀.exists_rTensor_fg_inclusion_eq key
  refine ⟨M₁, hfg, hle, (TensorProduct.comm R P M₁).injective ?_⟩
  rw [← LinearMap.rTensor_comm, ← LinearMap.rTensor_comm]
  exact heq

/-- Finitely many elements of `P ⊗ M₀` vanishing in `P ⊗ M` all vanish in `P ⊗ M₁` for a single
finitely generated `M₁` with `M₀ ≤ M₁ ≤ M`. -/
private theorem exists_fg_forall_lTensor_inclusion_eq_zero {M₀ : Submodule R M} (h₀ : M₀.FG)
    (s : Finset (P ⊗[R] M₀)) (hs : ∀ x ∈ s, M₀.subtype.lTensor P x = 0) :
    ∃ M₁ : Submodule R M, M₁.FG ∧ ∃ hle : M₀ ≤ M₁,
      ∀ x ∈ s, (M₀.inclusion hle).lTensor P x = 0 := by
  classical
  revert hs
  induction s using Finset.induction with
  | empty => exact fun _ => ⟨M₀, h₀, le_rfl, by simp⟩
  | insert a s ha ih =>
      intro hs
      obtain ⟨M₁, hfg₁, hle₁, h₁⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      obtain ⟨M₂, hfg₂, hle₂, h₂⟩ := exists_fg_lTensor_inclusion_eq P h₀ (x := a) (y := 0)
        (by rw [hs a (Finset.mem_insert_self a s), map_zero])
      have hcomp : ∀ (M' : Submodule R M) (h1 : M₀ ≤ M') (h2 : M' ≤ M₁ ⊔ M₂) (w : P ⊗[R] M₀),
          (M₀.inclusion (hle₁.trans le_sup_left)).lTensor P w
            = (M'.inclusion h2).lTensor P ((M₀.inclusion h1).lTensor P w) := fun M' h1 h2 w => by
        rw [← LinearMap.lTensor_comp_apply]
        rfl
      refine ⟨M₁ ⊔ M₂, hfg₁.sup hfg₂, hle₁.trans le_sup_left, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [hcomp M₂ hle₂ le_sup_right, h₂]; simp
      · rw [hcomp M₁ hle₁ le_sup_left, h₁ x hx, map_zero]

end Colimit

/-! ### Comparisons of the sets of associated primes -/

section Steps

open _root_.Stacks.AssociatedPrimes.FlatBaseChange (quotSMulEquivTensorQuot)

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Tensoring an `R`-linear map with the `S`-module `N` on the left is `S`-linear. -/
private theorem lTensor_smul {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] (f : P →ₗ[R] Q) (s : S) (w : N ⊗[R] P) :
    f.lTensor N (s • w) = s • f.lTensor N w :=
  (AlgebraTensorModule.lTensor S N f).map_smul s w

/-- A prime associated to `N / 𝔭N` is associated to `N ⊗_R M` for some finite `R`-module `M`. -/
private theorem exists_finite_of_mem_quot (p : Ideal R) (q : Ideal S)
    (h : q ∈ associatedPrimes S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M) (_ : Module.Finite R M),
      q ∈ associatedPrimes S (N ⊗[R] M) := by
  have : Module.Finite R (R ⧸ p) := Module.Finite.of_surjective p.mkQ p.mkQ_surjective
  have : Module.Finite R (ULift.{v} (R ⧸ p)) := Module.Finite.equiv ULift.moduleEquiv.symm
  refine ⟨ULift.{v} (R ⧸ p), inferInstance, inferInstance, inferInstance, ?_⟩
  rw [associatedPrimes_uLift]
  rw [← LinearEquiv.AssociatedPrimes.eq (quotSMulEquivTensorQuot (N := N) p)]
  exact h

/-- Stacks 05BZ(2): with `𝔭 = R ∩ 𝔮`, a prime associated to `N / 𝔭N` is associated to the
fibre `N ⊗_R κ(𝔭)`. -/
private theorem mem_fibre_of_mem_quot (q : PrimeSpectrum S)
    (h : q.asIdeal ∈ associatedPrimes S (N ⧸
      ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
        (⊤ : Submodule S N)))) :
    q.asIdeal ∈ associatedPrimes S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) := by
  have hloc := isLocalizedModule_fibreMk (S := S) N
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
  refine mem_associatedPrimes_of_isLocalizedModule
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.primeCompl
    (fibreMk N (PrimeSpectrum.comap (algebraMap R S) q).asIdeal) (fun r hr hmem => hr hmem) ?_
  rw [← LinearEquiv.AssociatedPrimes.eq
    (quotSMulEquivTensorQuot (N := N) (PrimeSpectrum.comap (algebraMap R S) q).asIdeal)]
  exact h

/-- Stacks 05BZ(3): over a Noetherian `S` the inclusion of `mem_fibre_of_mem_quot` is an
equality. -/
private theorem mem_quot_of_mem_fibre_of_noetherian [IsNoetherianRing S] (q : PrimeSpectrum S)
    (h : q.asIdeal ∈ associatedPrimes S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) :
    q.asIdeal ∈ associatedPrimes S (N ⧸
      ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
        (⊤ : Submodule S N))) := by
  have hloc := isLocalizedModule_fibreMk (S := S) N
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
  rw [LinearEquiv.AssociatedPrimes.eq
    (quotSMulEquivTensorQuot (N := N) (PrimeSpectrum.comap (algebraMap R S) q).asIdeal)]
  exact mem_associatedPrimes_of_isLocalizedModule_of_isNoetherianRing
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.primeCompl
    (fibreMk N (PrimeSpectrum.comap (algebraMap R S) q).asIdeal) h

/-- Over a Noetherian `S` an element of `N ⊗_R M` whose annihilator has prime radical `𝔮` can be
replaced by an element of `N ⊗_R M'` with `M'` finite: `B = B_fin`. -/
private theorem exists_finite_of_mem_tensor_of_noetherian [IsNoetherianRing S] (q : Ideal S)
    (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (h : q ∈ associatedPrimes S (N ⊗[R] M)) :
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.Finite R M'),
      q ∈ associatedPrimes S (N ⊗[R] M') := by
  classical
  obtain ⟨hq, z, hz⟩ := h
  obtain ⟨m, G, hG, hpow⟩ := exists_finset_span_pow_smul_eq_zero hz
  obtain ⟨M₀, hfin₀, hsub⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    (M := N) {z} (Set.finite_singleton z)
  obtain ⟨z₀, hz₀⟩ := hsub rfl
  have hker : ∀ x ∈ G.image (fun g : S => g • z₀), M₀.subtype.lTensor N x = 0 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    rw [lTensor_smul, hz₀, hpow g (by rw [← hG]; exact Submodule.subset_span hg)]
  obtain ⟨M₁, hfg₁, hle, hzero⟩ := exists_fg_forall_lTensor_inclusion_eq_zero N
    (Module.Finite.iff_fg.mp hfin₀) _ hker
  have himg : M₁.subtype.lTensor N ((M₀.inclusion hle).lTensor N z₀) = z := by
    rw [← LinearMap.lTensor_comp_apply]
    exact hz₀
  refine ⟨M₁, inferInstance, inferInstance, Module.Finite.iff_fg.mpr hfg₁, hq,
    (M₀.inclusion hle).lTensor N z₀, radical_eq_of_pow_le_of_le hq (Nat.succ_ne_zero m) ?_ ?_⟩
  · rw [← hG, Submodule.span_le]
    intro g hg
    simp only [SetLike.mem_coe, mem_colon_singleton, mem_bot]
    rw [← lTensor_smul]
    exact hzero _ (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hg))
  · intro s hs
    rw [mem_colon_singleton, mem_bot] at hs
    have hsz : s • z = 0 := by rw [← himg, ← lTensor_smul, hs, map_zero]
    exact mem_of_smul_eq_zero hz hsz

/-- Stacks 05C0 for a flat `N`: with `𝔭 = R ∩ 𝔮`, a prime associated to the fibre
`N ⊗_R κ(𝔭)` is associated to `N / 𝔭N`. -/
private theorem mem_quot_of_mem_fibre_of_flat [Module.Flat R N] (q : PrimeSpectrum S)
    (h : q.asIdeal ∈ associatedPrimes S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) :
    q.asIdeal ∈ associatedPrimes S (N ⧸
      ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
        (⊤ : Submodule S N))) := by
  have hloc := isLocalizedModule_fibreMk (S := S) N
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
  rw [LinearEquiv.AssociatedPrimes.eq
    (quotSMulEquivTensorQuot (N := N) (PrimeSpectrum.comap (algebraMap R S) q).asIdeal)]
  exact mem_associatedPrimes_of_isLocalizedModule_of_isSMulRegular
    (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.primeCompl
    (fibreMk N (PrimeSpectrum.comap (algebraMap R S) q).asIdeal)
    (fun r hr => isSMulRegular_tensor_quotient_of_flat N _ hr) h

/-- For a flat `N` the prime `𝔭'` in the description of `A'_fin` is forced: it is `R ∩ 𝔮`. -/
private theorem comap_eq_of_mem_quot_of_flat [Module.Flat R N] (q : PrimeSpectrum S)
    (p : PrimeSpectrum R)
    (h : q.asIdeal ∈ associatedPrimes S
      (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))) :
    PrimeSpectrum.comap (algebraMap R S) q = p := by
  rw [LinearEquiv.AssociatedPrimes.eq (quotSMulEquivTensorQuot (N := N) p.asIdeal)] at h
  obtain ⟨hq, z, hz⟩ := h
  refine PrimeSpectrum.ext (le_antisymm ?_ ?_)
  · intro r hr
    by_contra hnp
    have hr' : algebraMap R S r ∈ q.asIdeal := hr
    rw [hz, Ideal.mem_radical_iff] at hr'
    obtain ⟨k, hk⟩ := hr'
    rw [mem_colon_singleton, ← map_pow, algebraMap_smul, mem_bot] at hk
    have hz0 : z = 0 :=
      isSMulRegular_tensor_quotient_of_flat N p.asIdeal (pow_mem hnp k)
        (by simpa using hk)
    exact hq.ne_top (by rw [hz, hz0]; simp)
  · intro r hr
    show algebraMap R S r ∈ q.asIdeal
    refine mem_of_smul_eq_zero hz ?_
    rw [algebraMap_smul]
    exact smul_eq_zero_of_mem N p.asIdeal hr z

/-- For a flat `N`, a prime associated to `N ⊗_R M` is associated to `N ⊗_R M'` for a finite
`M' ⊆ M`: `B = B_fin`. -/
private theorem exists_finite_of_mem_tensor_of_flat [Module.Flat R N] (q : Ideal S)
    (M : Type (max u v)) [AddCommGroup M] [Module R M]
    (h : q ∈ associatedPrimes S (N ⊗[R] M)) :
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.Finite R M'),
      q ∈ associatedPrimes S (N ⊗[R] M') := by
  obtain ⟨hq, z, hz⟩ := h
  obtain ⟨M₀, hfin₀, hsub⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    (M := N) {z} (Set.finite_singleton z)
  obtain ⟨z₀, hz₀⟩ := hsub rfl
  refine ⟨M₀, inferInstance, inferInstance, hfin₀, hq, z₀, ?_⟩
  rw [hz, ← hz₀]
  exact congrArg Ideal.radical (colon_map_eq (AlgebraTensorModule.lTensor S N M₀.subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (M := N) M₀.subtype
      (Submodule.injective_subtype M₀)) z₀)

/-- For a flat `N` over a Noetherian `R`, a prime associated to `N ⊗_R M` with `M` a finite
`R`-module is associated to `N ⊗_R R/𝔭` for some prime `𝔭` of `R`. -/
private theorem exists_prime_mem_tensor_quot_of_mem_tensor_finite [IsNoetherianRing R]
    [Module.Flat R N] (q : Ideal S) (M : Type (max u v)) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (h : q ∈ associatedPrimes S (N ⊗[R] M)) :
    ∃ p : PrimeSpectrum R, q ∈ associatedPrimes S (N ⊗[R] (R ⧸ p.asIdeal)) := by
  revert h
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := R) (M := M)
    ‹Module.Finite R M›
    (motive := fun P _ _ _ => q ∈ associatedPrimes S (N ⊗[R] P) →
      ∃ p : PrimeSpectrum R, q ∈ associatedPrimes S (N ⊗[R] (R ⧸ p.asIdeal)))
    (fun P _ _ _ _ hq => absurd hq (by
      rw [associatedPrimes.eq_empty_of_subsingleton]; exact Set.notMem_empty _))
    (fun P _ _ _ p e hq => ⟨p, by
      rwa [← LinearEquiv.AssociatedPrimes.eq
        (AlgebraTensorModule.congr (LinearEquiv.refl S N) e)]⟩)
    (fun P₁ _ _ _ P₂ _ _ _ P₃ _ _ _ f g hf _ hfg ih₁ ih₃ hq => ?_)
  rcases associatedPrimes.subset_union_of_exact
    (M := N ⊗[R] P₁) (M' := N ⊗[R] P₂) (M'' := N ⊗[R] P₃)
    (f := AlgebraTensorModule.lTensor S N f) (g := AlgebraTensorModule.lTensor S N g)
    (Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf)
    (Module.Flat.lTensor_exact N hfg) hq with h1 | h3
  · exact ih₁ h1
  · exact ih₃ h3

/-- `B_fin ⊆ A'_fin` for a flat `N` over a Noetherian `R`, in terms of the modules `N / 𝔭N`. -/
private theorem exists_mem_quot_of_mem_tensor_finite [IsNoetherianRing R] [Module.Flat R N]
    (q : Ideal S) (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : q ∈ associatedPrimes S (N ⊗[R] M)) :
    ∃ p : PrimeSpectrum R, q ∈ associatedPrimes S
      (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  obtain ⟨p, hp⟩ := exists_prime_mem_tensor_quot_of_mem_tensor_finite N q M h
  refine ⟨p, ?_⟩
  rw [LinearEquiv.AssociatedPrimes.eq (quotSMulEquivTensorQuot (N := N) p.asIdeal)]
  exact hp

end Steps

/-- The comparisons of Stacks 05GB between the six sets of primes `A`, `A'`, `A_fin`, `A'_fin`,
`B` and `B_fin`; this is the statement of `Module.relativeAssassin_comparison`. -/
public theorem solution (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {A A' Afin A'fin B Bfin : Set (PrimeSpectrum S)}
    (hA : A = {q | q.asIdeal ∈
      associatedPrimes S (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)})
    (hA' : A' = {q | ∃ Q : PrimeSpectrum
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
        Q.asIdeal ∈ associatedPrimes
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
          ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
        PrimeSpectrum.comap (algebraMap S
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q})
    (hAfin : Afin = {q | q.asIdeal ∈ associatedPrimes S
      (N ⧸ ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
        (⊤ : Submodule S N)))})
    (hA'fin : A'fin = {q | ∃ p : PrimeSpectrum R, q.asIdeal ∈ associatedPrimes S
      (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))})
    (hB : B = {q | ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M),
      q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)})
    (hBfin : Bfin = {q | ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.Finite R M), q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)}) :
    A = A' ∧
    (Afin ⊆ A ∧ Bfin ⊆ B ∧ Afin ⊆ A'fin ∧ A'fin ⊆ Bfin ∧ A ⊆ B) ∧
    (IsNoetherianRing S → A = Afin ∧ B = Bfin) ∧
    (Module.Flat R N → A = Afin ∧ Afin = A'fin ∧ B = Bfin) ∧
    (IsNoetherianRing R → Module.Flat R N →
      A = A' ∧ A' = Afin ∧ Afin = A'fin ∧ A'fin = Bfin ∧ Bfin = B) := by
  have h1 : A = A' := by
    subst hA hA'
    ext q
    simp only [Set.mem_ofPred_eq,
      associatedPrimes_fibre (N := N) (PrimeSpectrum.comap (algebraMap R S) q).asIdeal,
      Set.mem_image]
    refine ⟨fun ⟨J, hJ, hJq⟩ => ⟨⟨J, hJ.1⟩, hJ, PrimeSpectrum.ext hJq⟩,
      fun ⟨Q, hQ, hQq⟩ => ⟨Q.asIdeal, hQ, congrArg PrimeSpectrum.asIdeal hQq⟩⟩
  have h2A : Afin ⊆ A := by
    subst hA hAfin
    exact fun q h => mem_fibre_of_mem_quot N q h
  have h2AB : A ⊆ B := by
    subst hA hB
    intro q hq
    exact ⟨ULift.{v} (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField,
      inferInstance, inferInstance, by rw [associatedPrimes_uLift]; exact hq⟩
  have hBB : Bfin ⊆ B := by
    subst hB hBfin
    rintro q ⟨M, i1, i2, _, h⟩
    exact ⟨M, i1, i2, h⟩
  have hAA'fin : Afin ⊆ A'fin := by
    subst hAfin hA'fin
    exact fun q hq => ⟨PrimeSpectrum.comap (algebraMap R S) q, hq⟩
  have hA'finB : A'fin ⊆ Bfin := by
    subst hA'fin hBfin
    rintro q ⟨p, hp⟩
    exact exists_finite_of_mem_quot N p.asIdeal q.asIdeal hp
  have hAfl : Module.Flat R N → A = Afin := by
    intro _
    subst hA hAfin
    exact Set.Subset.antisymm (fun q hq => mem_quot_of_mem_fibre_of_flat N q hq) h2A
  have hfl : Module.Flat R N → Afin = A'fin := by
    intro _
    subst hAfin hA'fin
    refine Set.Subset.antisymm hAA'fin ?_
    rintro q ⟨p, hp⟩
    rwa [← comap_eq_of_mem_quot_of_flat N q p hp] at hp
  have hBfl : Module.Flat R N → B = Bfin := by
    intro _
    subst hB hBfin
    refine Set.Subset.antisymm ?_ hBB
    rintro q ⟨M, i1, i2, h⟩
    exact exists_finite_of_mem_tensor_of_flat N q.asIdeal M h
  refine ⟨h1, ⟨h2A, hBB, hAA'fin, hA'finB, h2AB⟩, ?_, fun hN => ⟨hAfl hN, hfl hN, hBfl hN⟩, ?_⟩
  · intro _
    subst hA hAfin hB hBfin
    refine ⟨Set.Subset.antisymm (fun q hq => mem_quot_of_mem_fibre_of_noetherian N q hq) h2A,
      Set.Subset.antisymm ?_ hBB⟩
    rintro q ⟨M, i1, i2, h⟩
    exact exists_finite_of_mem_tensor_of_noetherian N q.asIdeal M h
  · intro _ hN
    refine ⟨h1, h1.symm.trans (hAfl hN), hfl hN, Set.Subset.antisymm hA'finB ?_, (hBfl hN).symm⟩
    subst hA'fin hBfin
    rintro q ⟨M, i1, i2, i3, h⟩
    exact exists_mem_quot_of_mem_tensor_finite N q.asIdeal M h

end Stacks.AssociatedPrimes.RelativeAssassin

open TensorProduct

namespace Module

/-- Let `R → S` be a ring map, let `N` be an `S`-module, and let `A`, `A'`, `A_fin`, `A'_fin`, `B`,
`B_fin` be the six sets of primes of `S` attached to this data: with `𝔭 = R ∩ 𝔮`, the primes `𝔮`
associated to `N ⊗_R κ(𝔭)` over `S`, those in the image of the primes associated to `N ⊗_R κ(𝔭)`
over the fibre ring `S ⊗_R κ(𝔭)`, those associated to `N / 𝔭N`, those associated to `N / 𝔭'N` for
some prime `𝔭'` of `R`, those associated to `N ⊗_R M` for some `R`-module `M`, and those associated
to `N ⊗_R M` for some finite `R`-module `M`. Then (1) `A = A'`; (2) `A_fin ⊆ A`, `B_fin ⊆ B`,
`A_fin ⊆ A'_fin ⊆ B_fin` and `A ⊆ B`; (3) if `S` is Noetherian then `A = A_fin` and `B = B_fin`;
(4) if `N` is flat over `R` then `A = A_fin = A'_fin` and `B = B_fin`; (5) if `R` is Noetherian and
`N` is flat over `R` then all six sets are equal. -/
@[stacks 05GB]
public theorem relativeAssassin_comparison (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {A A' Afin A'fin B Bfin : Set (PrimeSpectrum S)}
    (hA : A = {q | q.asIdeal ∈
      associatedPrimes S (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)})
    (hA' : A' = {q | ∃ Q : PrimeSpectrum
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
        Q.asIdeal ∈ associatedPrimes
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
          ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
        PrimeSpectrum.comap (algebraMap S
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q})
    (hAfin : Afin = {q | q.asIdeal ∈ associatedPrimes S
      (N ⧸ ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
        (⊤ : Submodule S N)))})
    (hA'fin : A'fin = {q | ∃ p : PrimeSpectrum R, q.asIdeal ∈ associatedPrimes S
      (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))})
    (hB : B = {q | ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M),
      q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)})
    (hBfin : Bfin = {q | ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.Finite R M), q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)}) :
    A = A' ∧
    (Afin ⊆ A ∧ Bfin ⊆ B ∧ Afin ⊆ A'fin ∧ A'fin ⊆ Bfin ∧ A ⊆ B) ∧
    (IsNoetherianRing S → A = Afin ∧ B = Bfin) ∧
    (Module.Flat R N → A = Afin ∧ Afin = A'fin ∧ B = Bfin) ∧
    (IsNoetherianRing R → Module.Flat R N →
      A = A' ∧ A' = Afin ∧ Afin = A'fin ∧ A'fin = Bfin ∧ Bfin = B) :=
  Stacks.AssociatedPrimes.RelativeAssassin.solution R S N hA hA' hAfin hA'fin hB hBfin

end Module
