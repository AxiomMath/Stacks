module

public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# The graded Nakayama lemma

Let `A = ⨁ᵢ 𝒜ᵢ` be a graded ring, graded by degrees in a canonically ordered additive monoid, and
let `M = ⨁_d ℳ_d` be a graded `A`-module. Write `𝒜₊ = ⨁_{i > 0} 𝒜ᵢ` for the irrelevant ideal. If
`N, N' ⊆ M` are graded submodules, `N'` is finitely generated and `N' ⊆ N + I N'` for some ideal
`I ⊆ 𝒜₊`, then `N' ⊆ N`.

The mechanism is that a scalar of positive degree strictly raises degrees: choosing a finite
homogeneous generating set of `N'` and a generator `y` whose degree is minimal, the degree of `y`
receives no contribution from `I N'`, so `y` is the degree-`deg y` component of an element of `N`
and hence lies in `N` because `N` is graded; induction on the number of generators finishes the
argument.

Gradedness of `N` cannot be dropped: take `A = k[x]` with its standard grading, `M = A`,
`N = A · (1 + x)` and `N' = ⊤`. Then `N'` is graded and finitely generated and `N' ≤ N + 𝒜₊ N'`,
since `1 = (1 + x) - x · 1`, yet `N' ≰ N`. Gradedness of `N'` enters differently, and this example
says nothing about whether it too is necessary: it supplies the finite homogeneous generating set
the induction runs on, obtained in `Submodule.IsHomogeneous.exists_finset_homogeneous_span_eq` by
decomposing an arbitrary finite generating set into its homogeneous components.

## Main results

* `Submodule.IsHomogeneous.exists_finset_homogeneous_span_eq`: a finitely generated homogeneous
  submodule is spanned by finitely many homogeneous elements, given with their degrees.
* `Module.Finite.exists_finset_homogeneous_span_eq_top`: the same for a finite graded module.
* `Submodule.IsHomogeneous.le_of_le_smul_of_le_irrelevant`: the graded Nakayama lemma in the form
  above.

## Implementation notes

The four assertions of the source are specializations of this one statement, in the order in which
the source deduces them from one another:

* (1) `𝒜₊M = M` and `M` finite imply `M = 0`: take `N = ⊥`, `N' = ⊤` and `I = 𝒜₊`, so that `N'.FG`
  is `Module.Finite A M` and the hypothesis reads `⊤ ≤ ⊥ ⊔ 𝒜₊ • ⊤`.
* (2) `M = N + 𝒜₊N'` with `N'` finite implies `M = N`: from `N' ≤ ⊤ = N ⊔ 𝒜₊ • N'` the statement
  gives `N' ≤ N`, whence `⊤ = N ⊔ 𝒜₊ • N' ≤ N`.
* (3) a map of graded modules `f : P → M` with `P/𝒜₊P → M/𝒜₊M` surjective and `M` finite is
  surjective: take `N = LinearMap.range f`, graded because `f` preserves degrees, and `N' = ⊤`.
* (4) homogeneous `x₁, …, x_n ∈ M` generating `M/𝒜₊M` generate `M` when `M` is finite: take
  `N = Submodule.span A {x₁, …, x_n}`, graded because the `xᵢ` are homogeneous, and `N' = ⊤`.

Finiteness is asked of `N'` alone and the conclusion is the inclusion `N' ≤ N` rather than an
equality of `M` with `N`; the ideal is an arbitrary `I ≤ 𝒜₊` rather than `𝒜₊` itself. This is the
shape of the ungraded sibling `Submodule.le_of_le_smul_of_le_jacobson_bot`, which hypothesizes
`I ≤ Ideal.jacobson ⊥` rather than fixing the Jacobson radical. It contains the source's parts
(1), (3) and (4) — where the finite module is the ambient one — at `N' = ⊤`, and an arbitrary `I`
is what the application to a homogeneous ideal `I ⊆ 𝒜₊` and the modules `M/IᵏM` needs.

Extracting a homogeneous generating set uses neither the grading of `A` nor the order on the
degrees, only the decomposition of `M`, and is stated at that generality: a finite set of
homogeneous generators together with their degrees is the datum any construction over a graded
module starts from, and `Module.Finite.exists_finset_homogeneous_span_eq_top` is that datum for a
finite graded module.

The degrees of the ring and of the module are separate index types `ιA` and `ιM`, with the degree
shift given by an `AddAction ιA ιM`; the source's `ιA = ℕ` acting on `ιM = ℤ` is one instance and
`ιA = ιM = ℕ` (Mathlib's `AddMonoid.toAddAction`) another. The order hypotheses `PartialOrder ιM`
and `IsOrderedCancelVAdd ιA ιM` say precisely what the proof uses of the degrees: `d < i +ᵥ d`
whenever `0 < i`, i.e. a scalar of positive degree strictly raises the degree of a homogeneous
element. Mathlib supplies `AddAction ι ι` but no action of `ℕ` on `ℤ`, so the source's `ℤ`-graded
modules over an `ℕ`-graded ring need that degree shift declared at the point of use.

## References

* [StacksProject 0EKB](https://stacks.math.columbia.edu/tag/0EKB)
-/

open scoped HomogeneousIdeal
open DirectSum Submodule

section General

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]

/-- Discarding from a generating set an element that already lies in `N` preserves the Nakayama
hypothesis: `span T ≤ N ⊔ I • span T` as soon as `span (insert y T) ≤ N ⊔ I • span (insert y T)`
and `y ∈ N`. -/
private theorem span_le_sup_smul_of_insert {I : Ideal A} {N : Submodule A M} {T : Set M} {y : M}
    (hy : y ∈ N) (h : span A (insert y T) ≤ N ⊔ I • span A (insert y T)) :
    span A T ≤ N ⊔ I • span A T := by
  rw [span_insert, smul_sup] at h
  refine (le_sup_right.trans h).trans (sup_le le_sup_left (sup_le ?_ le_sup_right))
  exact le_sup_of_le_left (smul_le_right.trans ((span_singleton_le_iff_mem _ _).mpr hy))

end General

section Graded

variable {ιA ιM σA σM A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
  [DecidableEq ιA] [AddCommMonoid ιA] [PartialOrder ιA] [CanonicallyOrderedAdd ιA]
  [SetLike σA A] [AddSubmonoidClass σA A] {𝒜 : ιA → σA} [GradedRing 𝒜]
  [DecidableEq ιM] [PartialOrder ιM] [SetLike σM M] [AddSubmonoidClass σM M]
  {ℳ : ιM → σM} [Decomposition ℳ]
  [AddAction ιA ιM] [IsOrderedCancelVAdd ιA ιM] [SetLike.GradedSMul 𝒜 ℳ]

omit [CanonicallyOrderedAdd ιA] [DecidableEq ιA] [DecidableEq ιM] in
/-- A degree shift by a positive element of `ιA` strictly raises a degree in `ιM`. -/
private theorem lt_vadd_of_pos {i : ιA} (hi : 0 < i) (d : ιM) : d < i +ᵥ d := by
  simpa using VAdd.vadd_lt_vadd_of_lt_of_le hi (le_refl d)

/-- A scalar in the irrelevant ideal sends a homogeneous element of degree `i` into the degrees
strictly above `i`: the degree-`j` component of `a • x` vanishes unless `i < j`. -/
private theorem decompose_smul_eq_zero_of_not_lt {a : A} (ha : a ∈ 𝒜₊.toIdeal)
    {i j : ιM} {x : M} (hx : x ∈ ℳ i) (hij : ¬ i < j) :
    (decompose ℳ (a • x) j : M) = 0 := by
  replace ha : a ∈ AddSubmonoid.closure (⋃ k > 0, (𝒜 k : Set A)) :=
    (HomogeneousIdeal.irrelevant_eq_closure 𝒜).le ha
  induction ha using AddSubmonoid.closure_induction with
  | mem b hb =>
    obtain ⟨k, hk, hbk⟩ : ∃ k > 0, b ∈ 𝒜 k := by simpa using hb
    exact decompose_of_mem_ne ℳ (SetLike.GradedSMul.smul_mem hbk hx)
      fun h => hij (h ▸ lt_vadd_of_pos hk i)
  | zero => simp
  | add b c _ _ ihb ihc => simp [add_smul, ihb, ihc]

/-- If `I ≤ 𝒜₊` and every element of `T` is homogeneous of a degree not below `e`, then the
degree-`e` component of `a • x` vanishes for `a ∈ I` and `x` in the span of `T`. -/
private theorem decompose_smul_eq_zero_of_mem_span {I : Ideal A} (hI : I ≤ 𝒜₊.toIdeal)
    {T : Set M} {e : ιM} (hT : ∀ y ∈ T, ∃ i, ¬ i < e ∧ y ∈ ℳ i)
    {x : M} (hx : x ∈ span A T) {a : A} (ha : a ∈ I) : (decompose ℳ (a • x) e : M) = 0 := by
  induction hx using span_induction generalizing a with
  | mem y hy =>
    obtain ⟨i, hie, hyi⟩ := hT y hy
    exact decompose_smul_eq_zero_of_not_lt (hI ha) hyi hie
  | zero => simp
  | add y z _ _ ihy ihz => simp [smul_add, ihy ha, ihz ha]
  | smul c y _ ih => rw [smul_smul]; exact ih (Ideal.mul_mem_right _ _ ha)

/-- If `I ≤ 𝒜₊` and every element of `T` is homogeneous of a degree not below `e`, then the
degree-`e` component of every element of `I • span T` vanishes. -/
private theorem decompose_eq_zero_of_mem_smul_span {I : Ideal A} (hI : I ≤ 𝒜₊.toIdeal)
    {T : Set M} {e : ιM} (hT : ∀ y ∈ T, ∃ i, ¬ i < e ∧ y ∈ ℳ i)
    {m : M} (hm : m ∈ I • span A T) : (decompose ℳ m e : M) = 0 :=
  smul_induction_on hm (fun _ ha _ hx => decompose_smul_eq_zero_of_mem_span hI hT hx ha)
    fun y z hy hz => by simp [hy, hz]

/-- Let `N` be a graded submodule, `I ≤ 𝒜₊`, and `T` a set of homogeneous elements none of whose
degrees lies below `e`. Then a homogeneous element of degree `e` of `N + I • span T` already lies
in `N`. -/
private theorem mem_of_mem_sup_smul_span {I : Ideal A} (hI : I ≤ 𝒜₊.toIdeal)
    {N : Submodule A M} (hN : N.IsHomogeneous ℳ) {T : Set M} {e : ιM}
    (hT : ∀ y ∈ T, ∃ i, ¬ i < e ∧ y ∈ ℳ i) {y : M} (hy : y ∈ ℳ e)
    (hmem : y ∈ N ⊔ I • span A T) : y ∈ N := by
  obtain ⟨n, hn, m, hm, rfl⟩ := mem_sup.mp hmem
  have h : n + m = (decompose ℳ n e : M) := by
    rw [← decompose_of_mem_same ℳ hy]
    simp [decompose_eq_zero_of_mem_smul_span hI hT hm]
  exact h ▸ hN e hn

/-- The graded Nakayama lemma for a submodule spanned by finitely many homogeneous elements. -/
private theorem span_image_le_of_le_sup_smul {I : Ideal A} (hI : I ≤ 𝒜₊.toIdeal)
    {N : Submodule A M} (hN : N.IsHomogeneous ℳ) {P : Finset (ιM × M)}
    (hP : ∀ p ∈ P, p.2 ∈ ℳ p.1)
    (hle : span A (Prod.snd '' (P : Set (ιM × M))) ≤
      N ⊔ I • span A (Prod.snd '' (P : Set (ιM × M)))) :
    span A (Prod.snd '' (P : Set (ιM × M))) ≤ N := by
  classical
  induction P using Finset.strongInduction with
  | _ P ih =>
    rcases P.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨e, heP, hemin⟩ := (P.image Prod.fst).exists_minimal (hne.image _)
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heP
    have hdeg : ∀ y ∈ Prod.snd '' (P : Set (ιM × M)), ∃ i, ¬ i < p.1 ∧ y ∈ ℳ i := by
      rintro y ⟨q, hq, rfl⟩
      exact ⟨q.1, fun h => absurd (hemin (Finset.mem_image_of_mem _ hq) h.le) h.not_ge, hP q hq⟩
    have hpN : p.2 ∈ N :=
      mem_of_mem_sup_smul_span hI hN hdeg (hP p hp) (hle (subset_span ⟨p, hp, rfl⟩))
    have hsplit : Prod.snd '' (P : Set (ιM × M)) =
        insert p.2 (Prod.snd '' ((P.erase p : Finset (ιM × M)) : Set (ιM × M))) := by
      rw [← Set.image_insert_eq, ← Finset.coe_insert, Finset.insert_erase hp]
    rw [hsplit] at hle ⊢
    rw [span_insert]
    exact sup_le ((span_singleton_le_iff_mem _ _).mpr hpN)
      (ih _ (Finset.erase_ssubset hp) (fun q hq => hP q (Finset.mem_of_mem_erase hq))
        (span_le_sup_smul_of_insert hpN hle))

end Graded

@[expose] public section

section Homogeneous

variable {ιM σM A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
  [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] {ℳ : ιM → σM}
  [DirectSum.Decomposition ℳ]

/-- A finitely generated homogeneous submodule of a graded module is spanned by finitely many
homogeneous elements, presented as a finite set of pairs `(i, y)` with `y ∈ ℳ i`: decomposing a
finite generating set into its homogeneous components gives such a family, and homogeneity of `N`
keeps the components inside `N`.

The degrees travel alongside the elements because a homogeneous element does not determine its
degree, `0` lying in every `ℳ i`. -/
public theorem Submodule.IsHomogeneous.exists_finset_homogeneous_span_eq {N : Submodule A M}
    (hN : N.IsHomogeneous ℳ) (hfg : N.FG) :
    ∃ P : Finset (ιM × M), (∀ p ∈ P, p.2 ∈ ℳ p.1) ∧
      span A (Prod.snd '' (P : Set (ιM × M))) = N := by
  classical
  obtain ⟨s, hs⟩ := hfg
  refine ⟨s.biUnion fun x => (decompose ℳ x).support.image fun i => (i, (decompose ℳ x i : M)),
    ?_, le_antisymm (span_le.mpr ?_) ?_⟩
  · simp only [Finset.mem_biUnion, Finset.mem_image]
    rintro p ⟨x, -, i, -, rfl⟩
    exact (decompose ℳ x i).2
  · rintro y ⟨p, hp, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨x, hxs, i, -, rfl⟩ := hp
    exact hN i (hs ▸ subset_span hxs)
  · rw [← hs, span_le]
    intro x hx
    rw [← sum_support_decompose ℳ x]
    refine Submodule.sum_mem _ fun i hi => subset_span ⟨(i, _), ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

variable (ℳ) in
/-- A finite graded module is spanned by finitely many homogeneous elements, presented as a finite
set of pairs `(i, y)` with `y ∈ ℳ i`. This is the graded form of `Module.Finite.exists_fin`, and
the form in which a finite graded module is used: homogeneous generators together with their
degrees. -/
public theorem Module.Finite.exists_finset_homogeneous_span_eq_top [Module.Finite A M] :
    ∃ P : Finset (ιM × M), (∀ p ∈ P, p.2 ∈ ℳ p.1) ∧
      span A (Prod.snd '' (P : Set (ιM × M))) = ⊤ :=
  Submodule.IsHomogeneous.exists_finset_homogeneous_span_eq (fun _ _ _ => Submodule.mem_top)
    Module.Finite.fg_top

end Homogeneous

/-- **Stacks 0EKB** (graded Nakayama). Let `A = ⨁ᵢ 𝒜ᵢ` be a graded ring and `M = ⨁_d ℳ_d` a
graded `A`-module. Let `N, N' ⊆ M` be graded submodules with `N'` finitely generated, and let
`I ⊆ 𝒜₊ = ⨁_{i > 0} 𝒜ᵢ` be an ideal. If `N' ⊆ N + I N'`, then `N' ⊆ N`. -/
@[stacks 0EKB]
public theorem Submodule.IsHomogeneous.le_of_le_smul_of_le_irrelevant
    {ιA ιM σA σM A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
    [DecidableEq ιA] [AddCommMonoid ιA] [PartialOrder ιA] [CanonicallyOrderedAdd ιA]
    [SetLike σA A] [AddSubmonoidClass σA A] {𝒜 : ιA → σA} [GradedRing 𝒜]
    [DecidableEq ιM] [PartialOrder ιM] [SetLike σM M] [AddSubmonoidClass σM M]
    {ℳ : ιM → σM} [DirectSum.Decomposition ℳ]
    [AddAction ιA ιM] [IsOrderedCancelVAdd ιA ιM] [SetLike.GradedSMul 𝒜 ℳ]
    {I : Ideal A} {N N' : Submodule A M}
    (hN : N.IsHomogeneous ℳ) (hN' : N'.IsHomogeneous ℳ) (hfg : N'.FG)
    (hI : I ≤ 𝒜₊.toIdeal) (hle : N' ≤ N ⊔ I • N') :
    N' ≤ N := by
  obtain ⟨P, hP, hspan⟩ := hN'.exists_finset_homogeneous_span_eq hfg
  rw [← hspan] at hle ⊢
  exact span_image_le_of_le_sup_smul hI hN hP hle

end
