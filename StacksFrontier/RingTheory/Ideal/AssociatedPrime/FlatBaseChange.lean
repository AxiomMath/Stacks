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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Associated primes of a tensor product with a flat module

Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an `S`-module which is flat as
an `R`-module. Write `Ass` for the set of primes that are the annihilator of an element. Then every
prime of `S` associated to `N / 𝔭N`, for `𝔭` an associated prime of `M` over `R`, is associated to
`N ⊗_R M` over `S`, and if `R` is Noetherian, then
`Ass_S(N ⊗_R M) = ⋃_{𝔭 ∈ Ass_R(M)} Ass_S(N / 𝔭N)`.

## Main definitions

* `Stacks.AssociatedPrimes.FlatBaseChange.quotSMulEquivTensorQuot`: the `S`-linear isomorphism
  `N / IN ≃ N ⊗_R R/I`.

## Main results

* `Stacks.AssociatedPrimes.FlatBaseChange.associatedPrimes_tensorProduct_subset_of_flat`: for `P`
  flat over a Noetherian ring `R` and `M` a finite `R`-module, `Ass_R(P ⊗_R M) ⊆ Ass_R(M)`.
* `Stacks.AssociatedPrimes.FlatBaseChange.solution` and `associatedPrimes.tensorProduct_of_flat`:
  the inclusion and, over a Noetherian ring, the equality above.

## References

* [StacksProject 0312](https://stacks.math.columbia.edu/tag/0312)

## Tags

associated prime, flat module, tensor product, base change
-/

@[expose] public section

open TensorProduct

namespace Stacks.AssociatedPrimes.FlatBaseChange

section AssStacks

variable {S : Type*} [CommRing S] {X Y Z : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y]
  [Module S Y] [AddCommGroup Z] [Module S Z]

/-- The set of associated primes of an `S`-module: the primes of `S` that *are* the annihilator of
an element, with no radical taken. -/
private def assStacks (S : Type*) [CommRing S] (X : Type*) [AddCommGroup X] [Module S X] :
    Set (Ideal S) :=
  {q : Ideal S | q.IsPrime ∧ ∃ w : X, (⊥ : Submodule S X).colon {w} = q}

/-- The annihilator of an element, spelled as a colon ideal. -/
private theorem mem_colon_bot_singleton {w : X} {s : S} :
    s ∈ (⊥ : Submodule S X).colon {w} ↔ s • w = 0 := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]

/-- An injective linear map does not change the annihilator of an element. -/
theorem colon_singleton_apply {f : X →ₗ[S] Y} (hf : Function.Injective f) (w : X) :
    (⊥ : Submodule S Y).colon {f w} = (⊥ : Submodule S X).colon {w} := by
  ext s
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_smul,
    map_eq_zero_iff f hf]

/-- Scaling by an element outside a prime annihilator does not change it. -/
private theorem colon_singleton_smul {q : Ideal S} (hq : q.IsPrime) {w : Y}
    (hw : (⊥ : Submodule S Y).colon {w} = q) {s : S} (hs : s ∉ q) :
    (⊥ : Submodule S Y).colon {s • w} = q := by
  ext t
  rw [mem_colon_bot_singleton, smul_smul, ← mem_colon_bot_singleton, hw]
  exact ⟨fun h => (hq.mem_or_mem h).resolve_right hs, fun h => Ideal.mul_mem_right _ _ h⟩

private theorem assStacks_subset_of_injective {f : X →ₗ[S] Y} (hf : Function.Injective f) :
    assStacks S X ⊆ assStacks S Y := by
  rintro q ⟨hq, w, hw⟩
  exact ⟨hq, f w, (colon_singleton_apply hf w).trans hw⟩

private theorem assStacks_congr (e : X ≃ₗ[S] Y) : assStacks S X = assStacks S Y :=
  (assStacks_subset_of_injective e.injective).antisymm
    (assStacks_subset_of_injective e.symm.injective)

private theorem assStacks_eq_empty [Subsingleton X] : assStacks S X = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨hq, w, hw⟩ => hq.ne_top (hw.symm.trans (eq_top_iff.mpr
    fun _ _ => mem_colon_bot_singleton.mpr (by rw [Subsingleton.elim w 0, smul_zero])))

/-- Associated primes of the middle term of a left exact sequence are associated primes of one of
the ends. -/
private theorem assStacks_subset_union_of_exact {f : X →ₗ[S] Y} {g : Y →ₗ[S] Z}
    (hf : Function.Injective f) (h : Function.Exact f g) :
    assStacks S Y ⊆ assStacks S X ∪ assStacks S Z := by
  rintro q ⟨hq, w, hw⟩
  by_cases hcase : ∃ s : S, s • w ∈ Set.range f ∧ s • w ≠ 0
  · obtain ⟨s, ⟨y, hy⟩, hne⟩ := hcase
    have hs : s ∉ q := fun hsq =>
      hne (mem_colon_bot_singleton.mp (by rw [hw]; exact hsq))
    exact Or.inl ⟨hq, y, by
      rw [← colon_singleton_apply hf y, hy, colon_singleton_smul hq hw hs]⟩
  · push Not at hcase
    refine Or.inr ⟨hq, g w, ?_⟩
    ext t
    rw [mem_colon_bot_singleton, ← map_smul]
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    · rw [← hw]
      exact mem_colon_bot_singleton.mpr (hcase t ((h (t • w)).mp ht))
    · rw [show t • w = 0 from mem_colon_bot_singleton.mp (by rw [hw]; exact ht), map_zero]

end AssStacks

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

section BaseChange

variable {M' M'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

/-- The `S`-linear base change of an `R`-linear map along `N` is the `R`-linear one. -/
theorem map_id_apply (f : M →ₗ[R] M') (z : N ⊗[R] M) :
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) f z
      = LinearMap.lTensor N f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem injective_map_id [Module.Flat R N] {f : M →ₗ[R] M'} (hf : Function.Injective f) :
    Function.Injective
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) f) := by
  intro a b hab
  refine Module.Flat.lTensor_preserves_injective_linearMap f hf ?_
  rw [← map_id_apply (S := S) f a, ← map_id_apply (S := S) f b, hab]

private theorem exact_map_id [Module.Flat R N] {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (h : Function.Exact f g) :
    Function.Exact (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) f)
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) g) := by
  intro y
  rw [map_id_apply (S := S) g y]
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact N h y).mp hy
    exact ⟨w, by rw [map_id_apply (S := S) f w, hw]⟩
  · rintro ⟨w, rfl⟩
    rw [map_id_apply (S := S) f w]
    exact (Module.Flat.lTensor_exact N h _).mpr ⟨w, rfl⟩

/-- The image of `N ⊗ A` in `N ⊗ M` grows with the submodule `A`. -/
theorem mem_range_map_subtype_of_le {A B : Submodule R M} (h : A ≤ B) {z : N ⊗[R] M}
    (hz : z ∈ LinearMap.range
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) A.subtype)) :
    z ∈ LinearMap.range
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) B.subtype) := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n a => exact ⟨n ⊗ₜ ⟨(a : M), h a.2⟩, rfl⟩
  | add u v hu hv =>
      obtain ⟨u', hu'⟩ := hu
      obtain ⟨v', hv'⟩ := hv
      exact ⟨u' + v', by rw [map_add, hu', hv', ← map_add]⟩

/-- Every element of `N ⊗_R M` comes from `N ⊗_R M₀` for some finitely generated submodule
`M₀ ⊆ M`. -/
theorem exists_fg_mem_range (z : N ⊗[R] M) :
    ∃ M₀ : Submodule R M, M₀.FG ∧ z ∈ LinearMap.range
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N) M₀.subtype) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, zero_mem _⟩
  | tmul n m => exact ⟨Submodule.span R {m}, Submodule.fg_span_singleton m,
      ⟨n ⊗ₜ ⟨m, Submodule.mem_span_singleton_self m⟩, rfl⟩⟩
  | add a b ha hb =>
      obtain ⟨A, hA, ha⟩ := ha
      obtain ⟨B, hB, hb⟩ := hb
      exact ⟨A ⊔ B, hA.sup hB, add_mem (mem_range_map_subtype_of_le le_sup_left ha)
        (mem_range_map_subtype_of_le le_sup_right hb)⟩

/-- For `N` flat over `R`, a prime of `S` associated to `N ⊗_R M` is already associated to
`N ⊗_R M₀` for some finite submodule `M₀ ⊆ M`. -/
private theorem exists_finite_submodule_mem_assStacks [Module.Flat R N] {q : Ideal S}
    (hq : q ∈ assStacks S (N ⊗[R] M)) :
    ∃ M₀ : Submodule R M, Module.Finite R ↥M₀ ∧ q ∈ assStacks S (N ⊗[R] ↥M₀) := by
  obtain ⟨hqp, z, hz⟩ := hq
  obtain ⟨M₀, hM₀, w, hw⟩ := exists_fg_mem_range (S := S) z
  refine ⟨M₀, Module.Finite.iff_fg.mpr hM₀, hqp, w, ?_⟩
  rw [← hz, ← hw]
  exact (colon_singleton_apply (injective_map_id (S := S) (Submodule.injective_subtype M₀)) w).symm

end BaseChange

section QuotSMul

/-- `IN` is stable under the `S`-action on `N`. -/
private theorem smul_mem_smul_top (I : Ideal R) (a : S) {n : N}
    (hn : n ∈ I • (⊤ : Submodule R N)) : a • n ∈ I • (⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on hn ?_ fun x y hx hy => by rw [smul_add]; exact add_mem hx hy
  intro r hr n' _
  rw [smul_comm]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- `𝔭N` read as the `S`-submodule generated by the image ideal and as the `R`-submodule `𝔭 • N`
are the same subgroup of `N`. -/
private theorem mem_smul_top_map_iff (I : Ideal R) (n : N) :
    n ∈ I.map (algebraMap R S) • (⊤ : Submodule S N) ↔ n ∈ I • (⊤ : Submodule R N) := by
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · refine Submodule.smul_induction_on hn ?_ fun a b ha hb => add_mem ha hb
    intro s hs n' _
    rw [Ideal.map, Ideal.span] at hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
        obtain ⟨r, hr, rfl⟩ := hs
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_smul]; exact smul_mem_smul_top I a hx
  · refine Submodule.smul_induction_on hn ?_ fun a b ha hb => add_mem ha hb
    intro r hr n' _
    rw [← algebraMap_smul S r n']
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top

/-- An element of `N` dies in `N ⊗_R R/I` exactly when it lies in `IN`. -/
private theorem tmul_one_eq_zero_iff (I : Ideal R) (n : N) :
    n ⊗ₜ[R] (1 : R ⧸ I) = 0 ↔ n ∈ I • (⊤ : Submodule R N) := by
  rw [← TensorProduct.tensorQuotEquivQuotSMul_symm_mk I n, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero]

/-- The `S`-linear map `n ↦ n ⊗ 1` from `N` to `N ⊗_R R/I` has kernel `IN`. -/
theorem ker_mk_flip_one (I : Ideal R) :
    LinearMap.ker ((TensorProduct.AlgebraTensorModule.mk R S N (R ⧸ I)).flip 1)
      = I.map (algebraMap R S) • (⊤ : Submodule S N) :=
  Submodule.ext fun n => (tmul_one_eq_zero_iff I n).trans (mem_smul_top_map_iff I n).symm

/-- The `S`-linear map `n ↦ n ⊗ 1` from `N` to `N ⊗_R R/I` is surjective. -/
private theorem surjective_mk_flip_one (I : Ideal R) :
    Function.Surjective ((TensorProduct.AlgebraTensorModule.mk R S N (R ⧸ I)).flip 1) := fun z => by
  obtain ⟨n, hn⟩ := ((TensorProduct.tensorQuotEquivQuotSMul N I).symm.surjective.comp
    (Submodule.mkQ_surjective (I • (⊤ : Submodule R N)))) z
  exact ⟨n, by simpa [TensorProduct.tensorQuotEquivQuotSMul_symm_mk] using hn⟩

/-- The `S`-linear isomorphism `N / IN ≃ N ⊗_R R/I` sending the class of `n` to `n ⊗ 1`. -/
noncomputable def quotSMulEquivTensorQuot (I : Ideal R) :
    (N ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S N))) ≃ₗ[S] N ⊗[R] (R ⧸ I) :=
  LinearEquiv.ofBijective
    (Submodule.liftQ _ ((TensorProduct.AlgebraTensorModule.mk R S N (R ⧸ I)).flip 1)
      (ker_mk_flip_one I).ge)
    ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (ker_mk_flip_one I).symm),
      by
        rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
        exact surjective_mk_flip_one I⟩

/-- `N / IN` and `N ⊗_R R/I` have the same associated primes. -/
private theorem assStacks_quotSMul_eq (I : Ideal R) :
    assStacks S (N ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S N))) =
      assStacks S (N ⊗[R] (R ⧸ I)) :=
  assStacks_congr (quotSMulEquivTensorQuot I)

/-- If `N` is flat over `R` and `R ⧸ I` embeds into `M`, then every prime of `S` associated to
`N / IN` is associated to `N ⊗_R M`. -/
private theorem assStacks_quotSMul_subset_of_injective [Module.Flat R N] (I : Ideal R)
    {φ : (R ⧸ I) →ₗ[R] M} (hφ : Function.Injective φ) :
    assStacks S (N ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S N))) ⊆
      assStacks S (N ⊗[R] M) := by
  rw [assStacks_quotSMul_eq]
  exact assStacks_subset_of_injective (injective_map_id (S := S) hφ)

end QuotSMul

/-- An element of `M` whose annihilator is `p` gives an injection `R ⧸ p → M`. -/
private theorem exists_injective_of_colon_eq {p : Ideal R} {m : M}
    (hm : (⊥ : Submodule R M).colon {m} = p) :
    ∃ φ : (R ⧸ p) →ₗ[R] M, Function.Injective φ :=
  have h : p = LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    rw [← hm]; ext r; simp [LinearMap.toSpanSingleton, Submodule.mem_colon_singleton]
  ⟨p.liftQ _ h.le, LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ h)⟩

/-- For `N` flat over `R`, every prime of `S` associated to `N / 𝔭N`, for `𝔭` a prime that is the
annihilator of an element of `M`, is associated to `N ⊗_R M`. -/
private theorem iUnion_assStacks_subset [Module.Flat R N] :
    (⋃ p ∈ {p : Ideal R | p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon {m} = p},
      assStacks S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) ⊆
      assStacks S (N ⊗[R] M) := by
  refine Set.iUnion₂_subset fun p hp => ?_
  obtain ⟨-, m, hm⟩ := hp
  obtain ⟨φ, hφ⟩ := exists_injective_of_colon_eq hm
  exact assStacks_quotSMul_subset_of_injective p hφ

/-- For `N` flat over a Noetherian ring `R`, every prime of `S` associated to `N / 𝔭N`, for
`𝔭 ∈ associatedPrimes R M`, is associated to `N ⊗_R M`. -/
private theorem iUnion_subset_of_isNoetherianRing [Module.Flat R N] (h : IsNoetherianRing R) :
    (⋃ p ∈ associatedPrimes R M,
        assStacks S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) ⊆
      assStacks S (N ⊗[R] M) := by
  refine Set.iUnion₂_subset fun p hp => ?_
  obtain ⟨φ, hφ⟩ := ((isAssociatedPrime_iff_exists_injective_linearMap p M).mp hp).2
  exact assStacks_quotSMul_subset_of_injective p hφ

/-- Restriction of scalars along `R → S` contracts an associated prime of an `S`-module to an
associated prime of the same module over `R`. -/
@[ega "IV 3.1.10.1" "Contraction inclusion"]
private theorem comap_mem_associatedPrimes {X : Type*} [AddCommGroup X] [Module S X] [Module R X]
    [IsScalarTower R S X] {q : Ideal S} (hq : q ∈ assStacks S X) :
    q.comap (algebraMap R S) ∈ associatedPrimes R X := by
  obtain ⟨hqp, z, hz⟩ := hq
  refine ⟨hqp.comap _, z, ?_⟩
  rw [← hz]
  have hcolon : (⊥ : Submodule R X).colon {z} = ((⊥ : Submodule S X).colon {z}).comap
      (algebraMap R S) := by
    ext r
    simp [Ideal.mem_comap, Submodule.mem_colon_singleton, algebraMap_smul]
  rw [hcolon, ← Ideal.comap_radical, hz, hqp.radical]

section FlatDescent

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- Over a Noetherian ring, an ideal that is not an associated prime of a finite module `M`
contains an element lying in no associated prime of `M` below it. -/
private theorem exists_mem_notMem_of_notMem_associatedPrimes [IsNoetherianRing R]
    [Module.Finite R M] {q : Ideal R} (hqM : q ∉ associatedPrimes R M) :
    ∃ x ∈ q, ∀ p ∈ associatedPrimes R M, p ≤ q → x ∉ p := by
  have hfin : {p ∈ associatedPrimes R M | p ≤ q}.Finite :=
    (associatedPrimes.finite R M).subset fun p hp => hp.1
  have hnot : ¬ ((q : Set R) ⊆ ⋃ p ∈ {p ∈ associatedPrimes R M | p ≤ q}, (p : Set R)) := by
    rw [Ideal.subset_union_prime_finite hfin ⊥ ⊥ fun p hp _ _ => hp.1.1]
    rintro ⟨p, hp, hle⟩
    exact hqM (le_antisymm hp.2 hle ▸ hp.1)
  obtain ⟨x, hxq, hx⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and] at hx
  exact ⟨x, hxq, fun p hp hpq => hx p ⟨hp, hpq⟩⟩

/-- If no associated prime of a finite module `M` below `q` contains `y`, then the kernel of
multiplication by `y` on `M` is killed by an element outside `q`. -/
private theorem exists_notMem_mem_annihilator_ker [IsNoetherianRing R] [Module.Finite R M]
    {q : Ideal R} [q.IsPrime] {y : R} (hy : ∀ p ∈ associatedPrimes R M, p ≤ q → y ∉ p) :
    ∃ t ∉ q, t ∈ Module.annihilator R
      ↥(LinearMap.ker (y • LinearMap.id : M →ₗ[R] M)) := by
  have hyK : y ∈ Module.annihilator R ↥(LinearMap.ker (y • LinearMap.id : M →ₗ[R] M)) :=
    Module.mem_annihilator.mpr fun k =>
      Subtype.ext (k.2 : (y • LinearMap.id : M →ₗ[R] M) (k : M) = 0)
  have hann : ¬ Module.annihilator R
      ↥(LinearMap.ker (y • LinearMap.id : M →ₗ[R] M)) ≤ q := fun hle => by
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hle
    exact hy p (associatedPrimes.subset_of_injective (f := (LinearMap.ker
        (y • LinearMap.id : M →ₗ[R] M)).subtype) (Submodule.injective_subtype _)
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ hp))
      hpq (hp.1.2 hyK)
  obtain ⟨t, ht, htq⟩ := Set.not_subset.mp hann
  exact ⟨t, htq, ht⟩

/-- If `P` is flat over `R`, then anything killing `ker(y : M → M)` kills every element of
`P ⊗_R M` that `y` kills. -/
theorem smul_eq_zero_of_mem_annihilator_ker [Module.Flat R P] {y t : R}
    (ht : t ∈ Module.annihilator R ↥(LinearMap.ker (y • LinearMap.id : M →ₗ[R] M)))
    {z : P ⊗[R] M} (hz : y • z = 0) : t • z = 0 := by
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact P
    (LinearMap.exact_subtype_ker_map (y • LinearMap.id : M →ₗ[R] M)) z).mp (by
      rw [LinearMap.lTensor_smul, LinearMap.lTensor_id]; simpa using hz)
  have htw : t • w = 0 := by
    have hzero : (t • LinearMap.id : ↥(LinearMap.ker
        (y • LinearMap.id : M →ₗ[R] M)) →ₗ[R] _) = 0 :=
      LinearMap.ext fun k => Module.mem_annihilator.mp ht k
    rw [show t • w = LinearMap.lTensor P (t • LinearMap.id) w by
      rw [LinearMap.lTensor_smul, LinearMap.lTensor_id]; rfl, hzero]
    simp
  rw [← hw, ← map_smul, htw, map_zero]

/-- Associated primes descend along a flat base change: if `P` is a flat `R`-module and `M` a
finite module over a Noetherian ring `R`, then every associated prime of `P ⊗_R M` is an
associated prime of `M`. -/
@[ega "IV 3.3.8" "special case"]
theorem associatedPrimes_tensorProduct_subset_of_flat [IsNoetherianRing R]
    [Module.Flat R P] [Module.Finite R M] :
    associatedPrimes R (P ⊗[R] M) ⊆ associatedPrimes R M := by
  rintro q ⟨hqp, z, hz⟩
  by_contra hqM
  obtain ⟨x, hxq, hx⟩ := exists_mem_notMem_of_notMem_associatedPrimes (M := M) hqM
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x ^ (n + 1) • z = 0 := by
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hz ▸ hxq)
    exact ⟨n, by
      rw [pow_succ, mul_comm, mul_smul,
        show x ^ n • z = 0 from by simpa using Submodule.mem_colon_singleton.mp hn, smul_zero]⟩
  obtain ⟨t, htq, ht⟩ := exists_notMem_mem_annihilator_ker (M := M) (q := q)
    fun p hp hpq hmem => hx p hp hpq (hp.1.mem_of_pow_mem _ hmem)
  exact htq (hz ▸ Ideal.le_radical (Submodule.mem_colon_singleton.mpr (by
    simpa using smul_eq_zero_of_mem_annihilator_ker ht hn)))

end FlatDescent

/-- If `N` is flat over a Noetherian ring `R` and `X` is a finite `R`-module, then every prime of
`S` associated to `N ⊗_R X` is associated to `N ⊗_R R/𝔭` for some prime `𝔭` of `R`. -/
private theorem assStacks_subset_iUnion_quotient [Module.Flat R N] [IsNoetherianRing R]
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] :
    assStacks S (N ⊗[R] X) ⊆
      ⋃ p ∈ {p : Ideal R | p.IsPrime}, assStacks S (N ⊗[R] (R ⧸ p)) := by
  induction ‹Module.Finite R X› using
    IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton Y =>
      have : Unique (N ⊗[R] Y) := TensorProduct.uniqueRight
      exact assStacks_eq_empty.subset.trans (Set.empty_subset _)
  | quotient Y p e =>
      rw [assStacks_congr (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) e)]
      exact Set.subset_biUnion_of_mem
        (u := fun p : Ideal R => assStacks S (N ⊗[R] (R ⧸ p))) p.2
  | exact Y₁ Y₂ Y₃ f g hf _ hfg h₁ h₃ =>
      exact (assStacks_subset_union_of_exact (injective_map_id (S := S) hf)
        (exact_map_id (S := S) hfg)).trans (Set.union_subset h₁ h₃)

/-- For `N` flat over a Noetherian ring `R`, every prime of `S` associated to `N ⊗_R M` is
associated to `N / 𝔭N` for some `𝔭` associated to `M`. -/
private theorem subset_iUnion_of_isNoetherianRing [Module.Flat R N] (h : IsNoetherianRing R) :
    assStacks S (N ⊗[R] M) ⊆
      ⋃ p ∈ associatedPrimes R M,
        assStacks S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) := by
  intro q hq
  obtain ⟨M₀, _, hq₀⟩ := exists_finite_submodule_mem_assStacks (S := S) hq
  obtain ⟨p, hp, hqp'⟩ := Set.mem_iUnion₂.mp
    (assStacks_subset_iUnion_quotient (S := S) ↥M₀ hq₀)
  have hcp : q.comap (algebraMap R S) = p := by
    have h1 := associatedPrimes_tensorProduct_subset_of_flat (P := N) (M := R ⧸ p)
      (comap_mem_associatedPrimes (R := R) hqp')
    rwa [associatedPrimes.eq_singleton_of_isPrimary hp.isPrimary, hp.radical,
      Set.mem_singleton_iff] at h1
  refine Set.mem_biUnion (associatedPrimes.subset_of_injective (f := M₀.subtype)
    (Submodule.injective_subtype _) (associatedPrimes_tensorProduct_subset_of_flat (P := N)
      (M := ↥M₀) (comap_mem_associatedPrimes (R := R) hq₀))) ?_
  rw [assStacks_quotSMul_eq (S := S) (N := N), hcp]
  exact hqp'

/-- Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an `S`-module which is flat
as an `R`-module. Every prime of `S` associated to `N / 𝔭N`, for `𝔭` a prime that is the
annihilator of an element of `M`, is associated to `N ⊗_R M`, and if `R` is Noetherian the primes
of `S` associated to `N ⊗_R M` are exactly those associated to `N / 𝔭N` for some
`𝔭 ∈ associatedPrimes R M`. Associated primes are the primes that are the annihilator of an
element. -/
public theorem solution {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [Module.Flat R N] :
    (⋃ p ∈ {p : Ideal R | p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon {m} = p},
        {q : Ideal S | q.IsPrime ∧
          ∃ w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)),
            (⊥ : Submodule S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))).colon {w} =
              q}) ⊆
      {q : Ideal S | q.IsPrime ∧ ∃ w : N ⊗[R] M, (⊥ : Submodule S (N ⊗[R] M)).colon {w} = q} ∧
    (IsNoetherianRing R →
      {q : Ideal S | q.IsPrime ∧ ∃ w : N ⊗[R] M, (⊥ : Submodule S (N ⊗[R] M)).colon {w} = q} =
        ⋃ p ∈ associatedPrimes R M,
          {q : Ideal S | q.IsPrime ∧
            ∃ w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)),
              (⊥ : Submodule S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))).colon {w} =
                q}) :=
  ⟨iUnion_assStacks_subset, fun h => (subset_iUnion_of_isNoetherianRing h).antisymm
    (iUnion_subset_of_isNoetherianRing h)⟩

end Stacks.AssociatedPrimes.FlatBaseChange

open TensorProduct

/-- Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an `S`-module which is flat
as an `R`-module. Then `Ass_S(N ⊗_R M) ⊇ ⋃_{𝔭 ∈ Ass_R(M)} Ass_S(N / 𝔭N)`, and if `R` is
Noetherian this inclusion is an equality. Here `Ass` is the set of primes that *are* the
annihilator of an element, written out as such, and the index set of the equality is
`associatedPrimes R M`. -/
@[stacks 0312]
public theorem associatedPrimes.tensorProduct_of_flat {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [Module.Flat R N] :
    (⋃ p ∈ {p : Ideal R | p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon {m} = p},
        {q : Ideal S | q.IsPrime ∧
          ∃ w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)),
            (⊥ : Submodule S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))).colon {w} =
              q}) ⊆
      {q : Ideal S | q.IsPrime ∧ ∃ w : N ⊗[R] M, (⊥ : Submodule S (N ⊗[R] M)).colon {w} = q} ∧
    (IsNoetherianRing R →
      {q : Ideal S | q.IsPrime ∧ ∃ w : N ⊗[R] M, (⊥ : Submodule S (N ⊗[R] M)).colon {w} = q} =
        ⋃ p ∈ associatedPrimes R M,
          {q : Ideal S | q.IsPrime ∧
            ∃ w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)),
              (⊥ : Submodule S (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))).colon {w} =
                q}) :=
  Stacks.AssociatedPrimes.FlatBaseChange.solution
