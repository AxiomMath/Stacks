module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
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
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# Minimal primes and multiplicities in a prime filtration

Proof of Stacks Tag 00L7. Let `R` be a ring, `M` an `R`-module, and
`0 = N₀ ⊆ N₁ ⊆ ⋯ ⊆ Nₙ = M` a filtration whose successive quotients are `Nᵢ₊₁ ⧸ Nᵢ ≅ R ⧸ 𝔭ᵢ`
for primes `𝔭ᵢ`. Then the minimal elements of `{𝔭ᵢ}` are the minimal elements of `Supp(M)`, and
a minimal `𝔭 ∈ Supp(M)` occurs `length_{R_𝔭} M_𝔭` times among the `𝔭ᵢ`.

Both conclusions come from the same bookkeeping. An invariant of modules that is additive along
a short exact sequence — the support, for the union; the length of a localization, for the sum —
telescopes along a filtration, so its value on `M` is the combination of its values on the
subquotients `Nᵢ₊₁ ⧸ Nᵢ ≅ R ⧸ 𝔭ᵢ`. For the support this gives `Supp(M) = ⋃ V(𝔭ᵢ)`
(Stacks 00L4), and the first conclusion is then the order-theoretic fact that a subset and a
superset all of whose elements lie above the subset have the same minimal elements. For the
length it gives `length_{R_𝔭} M_𝔭 = ∑ᵢ length_{R_𝔭} (R ⧸ 𝔭ᵢ)_𝔭`, and each summand is `1` if
`𝔭ᵢ = 𝔭` and `0` otherwise: the localization `(R ⧸ 𝔭ᵢ)_𝔭 = R_𝔭 ⧸ 𝔭ᵢ R_𝔭` vanishes unless
`𝔭ᵢ ⊆ 𝔭`, hence — `𝔭` being minimal and `𝔭ᵢ ∈ Supp(M)` — unless `𝔭ᵢ = 𝔭`, in which case it is
the residue field `κ(𝔭)`.

## Main results

* `Stacks.Length.PrimeFiltration.solution`: the statement of Tag 00L7.

## Implementation notes

Neither Noetherian nor finiteness hypotheses are used anywhere: the filtration is the
hypothesis, and both `Module.support_of_exact` and `Module.length_eq_add_of_exact` hold for
arbitrary modules over a commutative ring.

The bookkeeping is separated from the mathematics: `eq_add_sum_of_forall_succ_eq_add` and
`eq_union_iUnion_of_forall_succ_eq_union` telescope a family indexed by `Fin (n + 1)` in a
commutative monoid and in a power set, with no modules in sight, and the two additivity steps
`support_eq_union_support_quotient` and `length_localizedModule_eq_add_of_le` are stated for an
arbitrary pair `N₁ ≤ N₂` of submodules rather than for consecutive steps of the filtration.

Four of the auxiliary results are general and none is in Mathlib:
`support_eq_iUnion_support_subquotient` is Stacks 00L4 for an arbitrary filtration;
`length_localizedModule_eq_add_of_exact` is the additivity of length over `S⁻¹R` along the
localization of a short exact sequence of `R`-modules — the composite of
`Module.length_eq_add_of_exact` with the exactness of localization, and note that
`LocalizedModule.map` is already `S⁻¹R`-linear, so no scalar extension is needed;
`length_localizedModule_eq_sum_subquotient` is its telescoped form; and
`isSimpleModule_localizedModule_quotient` identifies `(R ⧸ 𝔭)_𝔭` with the residue field of
`R_𝔭`, through `Submodule.toLocalizedQuotient'` and `IsLocalization.AtPrime.map_eq_maximalIdeal`.

## References

* [StacksProject 00L7](https://stacks.math.columbia.edu/tag/00L7)

-/

namespace Stacks.Length.PrimeFiltration

/-- If `s ⊆ t` and every element of `t` lies above an element of `s`, then `s` and `t` have the
same minimal elements. -/
private theorem setOf_minimal_eq_setOf_minimal_of_forall_exists_le {α : Type*} [PartialOrder α]
    {s t : Set α} (hst : s ⊆ t) (hex : ∀ x ∈ t, ∃ y ∈ s, y ≤ x) :
    {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ t) x} := by
  ext x
  refine ⟨fun hx => ⟨hst hx.1, fun y hy hyx => ?_⟩, fun hx => ?_⟩
  · obtain ⟨z, hz, hzy⟩ := hex y hy
    exact (hx.2 hz (hzy.trans hyx)).trans hzy
  · obtain ⟨z, hz, hzx⟩ := hex x hx.1
    exact ⟨le_antisymm hzx (hx.2 (hst hz) hzx) ▸ hz, fun y hy hyx => hx.2 (hst hy) hyx⟩

section Telescope

/-- Telescoping a filtration in a commutative monoid: if `w` increases from `w i.castSucc` to
`w i.succ` by `c i` at every step, then `w (Fin.last n)` is `w 0` plus the sum of the `c i`. -/
private theorem eq_add_sum_of_forall_succ_eq_add {α : Type*} [AddCommMonoid α] {n : ℕ}
    (w : Fin (n + 1) → α) (c : Fin n → α)
    (hstep : ∀ i : Fin n, w i.succ = w i.castSucc + c i) :
    w (Fin.last n) = w 0 + ∑ i, c i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.succ_last, hstep (Fin.last n), ih (fun j => w j.castSucc) (fun i => c i.castSucc)
      fun i => by rw [← Fin.succ_castSucc]; exact hstep i.castSucc, Fin.castSucc_zero,
      Fin.sum_univ_castSucc, add_assoc]

/-- Telescoping a filtration of sets: if `w` grows from `w i.castSucc` to `w i.succ` by `c i` at
every step, then `w (Fin.last n)` is `w 0` together with the union of the `c i`. -/
private theorem eq_union_iUnion_of_forall_succ_eq_union {α : Type*} {n : ℕ}
    (w : Fin (n + 1) → Set α) (c : Fin n → Set α)
    (hstep : ∀ i : Fin n, w i.succ = w i.castSucc ∪ c i) :
    w (Fin.last n) = w 0 ∪ ⋃ i, c i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.succ_last, hstep (Fin.last n), ih (fun j => w j.castSucc) (fun i => c i.castSucc)
      fun i => by rw [← Fin.succ_castSucc]; exact hstep i.castSucc, Fin.castSucc_zero,
      Set.iUnion_fin_add_one_eq_iUnion_castSucc c, Set.union_assoc]
    rfl

end Telescope

section Support

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The support of `R ⧸ I` is the closed set `V(I)`. -/
private theorem support_quotient (I : Ideal R) :
    Module.support R (R ⧸ I) = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

/-- The support is additive along one step `N₁ ≤ N₂` of a filtration. -/
private theorem support_eq_union_support_quotient {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) :
    Module.support R ↥N₂ =
      Module.support R ↥N₁ ∪ Module.support R (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [← LinearEquiv.support_eq (Submodule.comapSubtypeEquivOfLe h)]
  exact Module.support_of_exact (LinearMap.exact_subtype_mkQ _)
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)

/-- **Stacks 00L4** for an arbitrary filtration: the support of `M` is the union of the supports
of the subquotients of a filtration `0 = N₀ ⊆ ⋯ ⊆ Nₙ = M`. -/
private theorem support_eq_iUnion_support_subquotient {n : ℕ} (N : Fin (n + 1) → Submodule R M)
    (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ) (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) :
    Module.support R M =
      ⋃ i : Fin n, Module.support R (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) := by
  have hbot' : Module.support R ↥(N 0) = ∅ := by
    rw [hbot, Module.support_eq_empty_iff]
    infer_instance
  have htop' : Module.support R ↥(N (Fin.last n)) = Module.support R M := by
    rw [htop]
    exact LinearEquiv.support_eq Submodule.topEquiv
  have key := eq_union_iUnion_of_forall_succ_eq_union (fun j => Module.support R ↥(N j))
    (fun i : Fin n => Module.support R (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)))
    fun i => support_eq_union_support_quotient (hle i)
  rw [← htop', key, hbot', Set.empty_union]

end Support

section Localization

variable {R : Type*} [CommRing R]

/-- Length over `S⁻¹R` is additive along the localization at `S` of a short exact sequence of
`R`-modules: localization is exact, and `LocalizedModule.map` is already `S⁻¹R`-linear. -/
private theorem length_localizedModule_eq_add_of_exact (S : Submonoid R) {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) :
    Module.length (Localization S) (LocalizedModule S B) =
      Module.length (Localization S) (LocalizedModule S A) +
        Module.length (Localization S) (LocalizedModule S C) :=
  Module.length_eq_add_of_exact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (LocalizedModule.map_injective S _ hf) (LocalizedModule.map_surjective S _ hg)
    (LocalizedModule.map_exact S _ _ H)

/-- Isomorphic `R`-modules have localizations of the same length over `S⁻¹R`. -/
private theorem length_localizedModule_congr (S : Submonoid R) {A B : Type*} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    Module.length (Localization S) (LocalizedModule S A) =
      Module.length (Localization S) (LocalizedModule S B) :=
  (LinearEquiv.ofBijective (LocalizedModule.map S e.toLinearMap)
    ⟨LocalizedModule.map_injective S _ e.injective,
      LocalizedModule.map_surjective S _ e.surjective⟩).length_eq

section Filtration

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The length of the localization is additive along one step `N₁ ≤ N₂` of a filtration. -/
private theorem length_localizedModule_eq_add_of_le (S : Submonoid R) {N₁ N₂ : Submodule R M}
    (h : N₁ ≤ N₂) :
    Module.length (Localization S) (LocalizedModule S ↥N₂) =
      Module.length (Localization S) (LocalizedModule S ↥N₁) +
        Module.length (Localization S) (LocalizedModule S (↥N₂ ⧸ N₁.submoduleOf N₂)) := by
  rw [← length_localizedModule_congr S (Submodule.comapSubtypeEquivOfLe h)]
  exact length_localizedModule_eq_add_of_exact S _ _ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)

/-- The length over `S⁻¹R` of `S⁻¹M` is the sum of the lengths of the localized subquotients of a
filtration `0 = N₀ ⊆ ⋯ ⊆ Nₙ = M`. -/
private theorem length_localizedModule_eq_sum_subquotient (S : Submonoid R) {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) :
    Module.length (Localization S) (LocalizedModule S M) =
      ∑ i : Fin n, Module.length (Localization S)
        (LocalizedModule S (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ))) := by
  have hbot' : Module.length (Localization S) (LocalizedModule S ↥(N 0)) = 0 := by
    rw [hbot]
    exact Module.length_eq_zero
  have htop' : Module.length (Localization S) (LocalizedModule S ↥(N (Fin.last n)))
      = Module.length (Localization S) (LocalizedModule S M) := by
    rw [htop]
    exact length_localizedModule_congr S Submodule.topEquiv
  have key := eq_add_sum_of_forall_succ_eq_add
    (fun j => Module.length (Localization S) (LocalizedModule S ↥(N j)))
    (fun i : Fin n => Module.length (Localization S)
      (LocalizedModule S (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ))))
    fun i => length_localizedModule_eq_add_of_le S (hle i)
  rw [← htop', key, hbot', zero_add]

end Filtration

end Localization

section AtPrime

variable {R : Type*} [CommRing R]

/-- The localization of `R ⧸ 𝔭` at `𝔭` is the residue field of `R_𝔭`, in particular a simple
`R_𝔭`-module. -/
private theorem isSimpleModule_localizedModule_quotient (q : Ideal R) [q.IsPrime] :
    IsSimpleModule (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ q)) := by
  have e := IsLocalizedModule.linearEquiv q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl (R ⧸ q))
    (Submodule.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)) q)
  have hmax : Submodule.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)) q
      = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.localized'_eq_map, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have hsimple : IsSimpleModule (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  exact IsSimpleModule.congr
    ((LinearEquiv.extendScalarsOfIsLocalization q.primeCompl (Localization.AtPrime q) e).trans
      (Submodule.quotEquivOfEq _ _ hmax))

/-- The localization `(R ⧸ 𝔭)_𝔮 = R_𝔮 ⧸ 𝔭 R_𝔮` at a prime `𝔮` minimal over `𝔭`, in the sense
that `𝔭 ⊆ 𝔮` forces `𝔭 = 𝔮`: it is the residue field `κ(𝔮)`, of length one, when `𝔭 = 𝔮`, and
zero otherwise. -/
private theorem length_localizedModule_quotient_atPrime (p q : PrimeSpectrum R)
    [Decidable (p = q)] (hmin : p ≤ q → p = q) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (R ⧸ p.asIdeal)) = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst h
    have := isSimpleModule_localizedModule_quotient p.asIdeal
    rw [ite_eq_left rfl]
    exact Module.length_eq_one _ _
  · have : Subsingleton (LocalizedModule q.asIdeal.primeCompl (R ⧸ p.asIdeal)) :=
      Module.notMem_support_iff.mp <| by
        rw [support_quotient]
        simpa [PrimeSpectrum.mem_zeroLocus] using fun hsub => h (hmin hsub)
    rw [ite_eq_right h]
    exact Module.length_eq_zero

end AtPrime

/-- The size of a fibre of `f`, counted by summing indicators in `ℕ∞`. -/
private theorem ncard_setOf_eq_sum_ite {ι κ : Type*} [Fintype ι] (f : ι → κ) (b : κ)
    [DecidablePred fun i => f i = b] :
    ({i | f i = b}.ncard : ℕ∞) = ∑ i, if f i = b then 1 else 0 := by
  rw [Finset.sum_boole, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- **Stacks 00L7**. -/
public theorem solution {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ} (N : Fin (n + 1) → Submodule R M)
    (p : Fin n → PrimeSpectrum R) (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hquot : ∀ i : Fin n,
      Nonempty ((↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) :
    {q | Minimal (· ∈ Set.range p) q} = {q | Minimal (· ∈ Module.support R M) q} ∧
      ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q →
        ({i | p i = q}.ncard : ℕ∞) =
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
  classical
  -- `Supp(M) = ⋃ V(𝔭ᵢ)`, since the `i`-th subquotient of the filtration has support `V(𝔭ᵢ)`.
  have hsupp : Module.support R M = ⋃ i, PrimeSpectrum.zeroLocus ((p i).asIdeal : Set R) := by
    rw [support_eq_iUnion_support_subquotient N hle hbot htop]
    exact Set.iUnion_congr fun i => by
      rw [LinearEquiv.support_eq (hquot i).some, support_quotient]
  have hmem : ∀ i : Fin n, p i ∈ Module.support R M := fun i =>
    hsupp ▸ Set.mem_iUnion.mpr ⟨i, (PrimeSpectrum.mem_zeroLocus _ _).mpr subset_rfl⟩
  refine ⟨setOf_minimal_eq_setOf_minimal_of_forall_exists_le (Set.range_subset_iff.mpr hmem) ?_,
    fun q hq => ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsupp ▸ hx)
    exact ⟨p i, Set.mem_range_self i, (PrimeSpectrum.mem_zeroLocus _ _).mp hi⟩
  -- The localized subquotient at `i` has length `1` if `𝔭ᵢ = 𝔮` and `0` otherwise, so the
  -- localized filtration counts the indices with `𝔭ᵢ = 𝔮`.
  · have hone : ∀ i : Fin n, Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ))) = if p i = q then 1 else 0 :=
      fun i => by
        rw [length_localizedModule_congr _ (hquot i).some]
        exact length_localizedModule_quotient_atPrime (p i) q
          fun hsub => le_antisymm hsub (hq.2 (hmem i) hsub)
    change ({i | p i = q}.ncard : ℕ∞) = Module.length (Localization q.asIdeal.primeCompl)
      (LocalizedModule q.asIdeal.primeCompl M)
    rw [length_localizedModule_eq_sum_subquotient q.asIdeal.primeCompl N hle hbot htop,
      Finset.sum_congr rfl fun i _ => hone i, ncard_setOf_eq_sum_ite]

end Stacks.Length.PrimeFiltration

/-!
# Minimal primes and multiplicities in a prime filtration

Let `R` be a ring, `M` an `R`-module and
`0 = M₀ ⊆ M₁ ⊆ ⋯ ⊆ Mₙ = M` a filtration whose successive quotients are `Mᵢ₊₁ ⧸ Mᵢ ≅ R ⧸ 𝔭ᵢ`
for primes `𝔭ᵢ` of `R` (Stacks 00L0 produces such a filtration when `R` is Noetherian and `M`
is finite). Two things are then true of the family `(𝔭ᵢ)`, and this is the content of Tag 00L7.

First, the minimal elements of `{𝔭ᵢ}` are exactly the minimal elements of `Supp(M)`. This is
read off `Supp(M) = ⋃ V(𝔭ᵢ)` (Stacks 00L4): a prime minimal in `Supp(M)` contains some `𝔭ᵢ`,
which itself lies in `Supp(M)`, hence equals it; conversely a prime minimal among the `𝔭ᵢ`
cannot strictly contain any point of `⋃ V(𝔭ᵢ)`.

Second, while the family `(𝔭ᵢ)` depends on the filtration, its multiplicities at the *minimal*
primes do not: for `𝔭` minimal in `Supp(M)` the number of indices `i` with `𝔭ᵢ = 𝔭` equals the
length of `M_𝔭` over `R_𝔭`. Indeed localizing the filtration at `𝔭` gives a filtration of `M_𝔭`
with subquotients `R_𝔭 ⧸ 𝔭ᵢ R_𝔭`, which vanish unless `𝔭ᵢ ⊆ 𝔭`, i.e. unless `𝔭ᵢ = 𝔭` by
minimality, and which equal the residue field `κ(𝔭)`, of length `1`, in that case.

## Main results

* `Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length`: for a filtration
  with subquotients `R ⧸ 𝔭ᵢ`, the minimal elements of `{𝔭ᵢ}` are the minimal elements of
  `Supp(M)`, and a minimal `𝔭` occurs `length_{R_𝔭} M_𝔭` times among the `𝔭ᵢ`.

## Implementation notes

The primes are carried as data, `p : Fin n → PrimeSpectrum R`, rather than existentially bound
as in `Submodule.IsQuotientEquivQuotientPrime`: the source counts the indices `i` with
`𝔭ᵢ = 𝔭`, so the family and not merely its existence is the hypothesis. A filtration produced
by `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` (Stacks 00L0) instantiates
this with `N := X.toFun`, `n := X.length`, `hle := fun i => (X.step i).1` and `p` chosen from
`fun i => (X.step i).2`.

Neither `IsNoetherianRing R` nor `Module.Finite R M` is assumed, although the source inherits
both from Stacks 00L0. The filtration is the hypothesis here, and it already forces `M` to be
finite; nothing in either conclusion uses more. Stating the lemma this way also lets it be
applied to a filtration obtained by other means, for instance the localization or the base
change of a given one.

The count `#{i | 𝔭ᵢ = 𝔭}` is `Set.ncard` of a subset of `Fin n`, and the equality is in `ℕ∞`
after coercion, so it also records that `M_𝔭` has finite length; no separate finiteness
statement is needed. `M_𝔭` and `R_𝔭` are the concrete models `LocalizedModule 𝔭.primeCompl M`
and `Localization.AtPrime 𝔭`, the spelling of Mathlib's own invariants at a prime
(`Module.mem_support_iff`, `Module.mem_freeLocus`, `Ideal.ramificationIdx`); any other
localization of `M` at `𝔭` is isomorphic to this one over an isomorphic ring, so the length is
unchanged. Sets of minimal elements are written `{q | Minimal (· ∈ s) q}`, following
`minimalPrimes_eq_minimals`.

Faithfulness. (1) Every hypothesis is used: `hquot` names the primes counted in both
conclusions, `hle` is what makes the localized lengths add up along the filtration, and
`hbot`, `htop` pin the filtration to run from `0` to `M` — with `htop` dropped, `n = 0` and
`N 0 = ⊥` for `M = ℤ ⧸ 4` would give an empty left-hand side against `Supp(M) = {(2)}`.
(2) The scalars are the source's: `Supp(M)` and the filtration are over `R`, while the length
is taken over `R_𝔭` and not over `R` (over `R`, the length of `M_𝔭` is generally larger — it is
`⊤` for `R = ℤ`, `M = ℤ`, `𝔭 = (0)`). (3) The invariants are pinned, not merely asserted to
exist: the right-hand side is the length of the canonical localization `M_𝔭` over
`Localization.AtPrime 𝔭`, and the left-hand side is an equality of the two sets of minimal
elements, not an inclusion. (4) The instantiation is not degenerate: for `R = ℤ`,
`M = ℤ ⧸ 4` and the filtration `0 ⊂ 2ℤ ⧸ 4 ⊂ ℤ ⧸ 4` with `p = ((2), (2))`, both conclusions
say something — `{(2)}` on both sides of the first, and `2 = length_{ℤ_{(2)}} ℤ ⧸ 4` in the
second, a multiplicity greater than `1`. Taking instead `M = ℤ ⊕ ℤ ⧸ 2` with the filtration
`0 ⊂ 0 ⊕ ℤ ⧸ 2 ⊂ M` and `p = ((2), (0))` exhibits a `𝔭ᵢ` that is *not* minimal, which the
first conclusion discards.

## References

* [StacksProject 00L7](https://stacks.math.columbia.edu/tag/00L7)

## Tags

support, minimal prime, length, localization, filtration

-/

namespace Module

/-- **Stacks 00L7**.
Let `R` be a ring, `M` an `R`-module, and let `0 = N₀ ⊆ N₁ ⊆ ⋯ ⊆ Nₙ = M` be a filtration whose
successive quotients are `Nᵢ₊₁ ⧸ Nᵢ ≅ R ⧸ 𝔭ᵢ` for primes `𝔭ᵢ = p i` of `R`, as produced by
Stacks 00L0. Then the minimal elements of the set `{𝔭ᵢ}` are exactly the minimal elements of
`Supp(M)`, and each minimal `𝔭 ∈ Supp(M)` occurs among the `𝔭ᵢ` exactly
`length_{R_𝔭} M_𝔭` times. -/
@[stacks 00L7]
public theorem setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ} (N : Fin (n + 1) → Submodule R M)
    (p : Fin n → PrimeSpectrum R) (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hquot : ∀ i : Fin n,
      Nonempty ((↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) :
    {q | Minimal (· ∈ Set.range p) q} = {q | Minimal (· ∈ Module.support R M) q} ∧
      ∀ q : PrimeSpectrum R, Minimal (· ∈ Module.support R M) q →
        ({i | p i = q}.ncard : ℕ∞) =
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) :=
  Stacks.Length.PrimeFiltration.solution N p hle hquot hbot htop

end Module
