module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.Tactic.ENatToNat
public import StacksFrontier.Algebra.Module.Projective.CountablyGenerated

/-!
# Kaplansky's theorem: projective modules over a local ring are free

Let `R` be a commutative local ring. Then every projective `R`-module is free, with no finiteness
hypothesis on the module (Stacks 0593). The proof is the source's (Stacks, Section 10.85):

* **Stacks 0591.** A countably generated module `M` with property (P) is free. Property (P) says:
  for every decomposition `M = N ⊕ N'` with `N'` finite free, every element of `N` lies in a free
  direct summand of `N`. One builds an increasing chain of finite free direct summands whose
  increments are an independent family of free submodules spanning `M`.
* **Stacks 0592.** Every element of a projective module over a local ring lies in a free direct
  summand. Realize the module as a direct summand of a free module in such a way that the given
  element `x` has as few nonzero coordinates as possible; minimality forces no coordinate of `x` to
  be a combination of the others, and this makes the matrix expressing the projections of the
  corresponding basis vectors invertible, because over a local ring a matrix fixing such a vector
  has unit determinant.
* **Stacks 0593.** Freeness of all projective modules is a question about the countably generated
  ones (Stacks 0590, imported). A direct summand of a projective module is projective, so 0592
  gives property (P) for a projective module over a local ring, and 0591 makes it free.

## Main results

* `countablyGenerated_propertyP_free`: a countably generated module with property (P) is free
  (Stacks 0591).
* `projective_local_free_summand`: every element of a projective module over a local ring lies in
  a free direct summand (Stacks 0592).
* `Module.free_of_projective_of_isLocalRing`: a projective module over a commutative local ring is
  free (Stacks 0593).

## Implementation notes

For 0592 the module is realized as a direct summand of the free module `P →₀ R` rather than of an
abstract free module; this fixes a basis (`Finsupp.single j 1`) indexed by `P` itself, so the
"minimal number of basis elements needed to express `x`" of the source is the cardinality of
`(i x).support` for a section `i`, and the source's change of basis is replaced by a change of
section: the pair `(i, π)` is replaced by `((1 - f) ∘ i, π ∘ (1 + f))` for a square-zero `f`.

Kaplansky's theorem is deliberately *not* an instance: `Module.Free R P` implies
`Module.Projective R P` by `Module.Projective.of_free`, so registering the converse would make
instance search for freeness loop back on itself. The ring is commutative, as in the source, whose
proof of 0592 shows a matrix is invertible *because its determinant is a unit*.

## References

* [StacksProject 0591](https://stacks.math.columbia.edu/tag/0591)
* [StacksProject 0592](https://stacks.math.columbia.edu/tag/0592)
* [StacksProject 0593](https://stacks.math.columbia.edu/tag/0593)
-/

@[expose] public section

universe u v

/-! ## Stacks 0591: a countably generated module with property (P) is free -/

section PropertyP

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An `R`-module `M` is *countably generated* if there is a countable subset of
`M` whose `R`-span is all of `M`. -/
def CountablyGenerated (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤

/-- A submodule `F` is a *direct summand* of the submodule `N` if there is a
submodule `G` with `N = F ⊕ G` inside the submodule lattice, i.e. `F` and `G`
are disjoint and their join is `N`. Note that this forces `F ≤ N`. -/
def IsDirectSummandOf (F N : Submodule R M) : Prop :=
  ∃ G : Submodule R M, Disjoint F G ∧ F ⊔ G = N

/-- A submodule `F` is a *free direct summand* of the submodule `N` if `F` is a
direct summand of `N` and `F` is free as an `R`-module. -/
def IsFreeDirectSummandOf (F N : Submodule R M) : Prop :=
  IsDirectSummandOf F N ∧ Module.Free R F

/-- Property (P) for `M`: for every direct sum decomposition `M = N ⊕ N'` in
which `N'` is finite free, every element `x ∈ N` is contained in a free direct
summand of `N`. -/
def PropertyP (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ N N' : Submodule R M, IsCompl N N' →
    Module.Free R N' → Module.Finite R N' →
      ∀ x ∈ N, ∃ F : Submodule R M, IsFreeDirectSummandOf F N ∧ x ∈ F

/-- **Enumeration of a countable generating set.**
A countably generated module admits a generating *sequence* `x : ℕ → M`, i.e. a
function from `ℕ` whose range spans `M`.

Argument: by `CountablyGenerated` there is a countable `s` with `span R s = ⊤`.
If `s = ∅` then `span R ∅ = ⊥ = ⊤`, so `M` is the zero module; take `x := fun _ => 0`,
whose range is `{0}` and still spans `⊤`. Otherwise `s` is a nonempty countable set,
so there is a surjection `ℕ → s` (Mathlib: `Set.Countable.exists_surjective` /
`Set.Countable` ↔ `∃ f : ℕ → M, s ⊆ range f` for nonempty `s`); compose with the
inclusion to get `x : ℕ → M` with `s ⊆ range x ⊆ M`, hence
`span R (range x) ≥ span R s = ⊤`. -/
theorem exists_generating_seq (hcg : CountablyGenerated R M) :
    ∃ x : ℕ → M, Submodule.span R (Set.range x) = ⊤ := by
  obtain ⟨s, hsc, hspan⟩ := hcg
  rcases s.eq_empty_or_nonempty with he | hne
  · -- empty case: span is ⊥ = ⊤, so M is subsingleton
    subst he
    rw [Submodule.span_empty] at hspan
    refine ⟨fun _ => 0, le_antisymm le_top ?_⟩
    rw [← hspan]
    exact bot_le
  · -- nonempty case: surjection ℕ → s
    obtain ⟨f, hf⟩ := hsc.exists_surjective hne
    refine ⟨fun n => (f n : M), le_antisymm le_top ?_⟩
    rw [← hspan]
    exact Submodule.span_mono fun y hy => (hf ⟨y, hy⟩).imp fun _ hn => congrArg Subtype.val hn

/-- **Free assembly from an independent spanning family of free submodules.**
If `A : ℕ → Submodule R M` is an independent family (`iSupIndep A`) whose supremum
is everything (`⨆ n, A n = ⊤`) and each `A n` is a free `R`-module, then `M` is free.

Argument: `iSupIndep A` together with `⨆ A = ⊤` gives
`DirectSum.IsInternal A` (Mathlib: `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`).
Choosing a basis `v n : Basis (κ n) R (A n)` of each free summand
(`Module.Free.chooseBasis`), the collected basis
`DirectSum.IsInternal.collectedBasis` is a basis of `M` indexed by `Σ n, κ n`;
hence `Module.Free.of_basis` gives `Module.Free R M`. -/
theorem free_of_iSupIndep_iSup_eq_top_free
    (A : ℕ → Submodule R M)
    (hindep : iSupIndep A) (hsup : ⨆ n, A n = ⊤)
    (hfree : ∀ n, Module.Free R (A n)) :
    Module.Free R M := by
  classical
  exact Module.Free.of_basis
    ((DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hsup).collectedBasis
      fun n => Module.Free.chooseBasis R (A n))

/-- **Shrinking a free direct summand to a *finite* free direct summand around a point.**
Inside `N`, if `F` is a free direct summand of `N` and `x ∈ F`, then there is a
*finite* free direct summand `F₀` of `N` with `x ∈ F₀` and `F₀ ≤ F`.

Argument: let `b : Basis κ R F` be a basis of the free module `F`. The element
`x ∈ F` has finite support in this basis: `x = Σ_{i ∈ t} c i • b i` for a finite
`t ⊆ κ`. Let `F₀ := span R (b '' t)`, spanned by finitely many basis vectors; it is
finite free (`Module.Finite.span_of_finite`, `Basis.span`) and contains `x`. Within
`F`, `F₀` is complemented by `span R (b '' tᶜ)` (a subset of a basis splits off a
complementary span: `LinearIndependent.disjoint_span_image` for disjointness, and the
two spans join to `F` because together the index sets cover `κ`); so `F₀` is a direct
summand of `F`. Since `F` is a direct summand of `N` and direct-summand-ness is
transitive, `F₀` is a direct summand of `N`. -/
theorem exists_finFree_directSummand_mem
    (N F : Submodule R M) (hF : IsFreeDirectSummandOf F N) {x : M} (hxF : x ∈ F) :
    ∃ F₀ : Submodule R M, IsDirectSummandOf F₀ N ∧ Module.Free R F₀ ∧
      Module.Finite R F₀ ∧ x ∈ F₀ := by
  classical
  obtain ⟨hFds, hFfree⟩ := hF
  have htrans : ∀ F₀ C : Submodule R M, Disjoint F₀ C → F₀ ⊔ C = F → IsDirectSummandOf F₀ N := by
    intro F₀ C hdisj hsup
    obtain ⟨G, hFG, hFGsup⟩ := hFds
    refine ⟨C ⊔ G, hdisj.disjoint_sup_right_of_disjoint_sup_left (hsup ▸ hFG), ?_⟩
    rw [← sup_assoc, hsup, hFGsup]
  set b := Module.Free.chooseBasis R F with hb
  set x' : F := ⟨x, hxF⟩ with hx'
  set t := (b.repr x').support with ht
  set s : Set (Module.Free.ChooseBasisIndex R F) := (↑t : Set (Module.Free.ChooseBasisIndex R F))
      with hs
  set S : Submodule R F := Submodule.span R (b '' s) with hS
  set C : Submodule R F := Submodule.span R (b '' sᶜ) with hC
  have hdSC : Disjoint S C := (b.linearIndependent).disjoint_span_image disjoint_compl_right
  have hsupSC : S ⊔ C = ⊤ := by
    rw [hS, hC, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self,
      Set.image_univ, b.span_eq]
  have hx'S : x' ∈ S := by
    rw [hS, hs, ht]
    exact Module.Basis.mem_span_repr_support b x'
  set F₀ : Submodule R M := S.map F.subtype with hF₀
  set Cm : Submodule R M := C.map F.subtype with hCm
  have hdisj₀ : Disjoint F₀ Cm := Submodule.disjoint_map F.injective_subtype hdSC
  have hsup₀ : F₀ ⊔ Cm = F := by
    rw [hF₀, hCm, ← Submodule.map_sup, hsupSC, Submodule.map_subtype_top]
  set w' : s → M := fun i => F.subtype (b i) with hw'
  have hwli : LinearIndependent R w' :=
    ((b.linearIndependent).comp (Subtype.val : s → _) Subtype.val_injective).map' F.subtype
      (by simp)
  have hspaneq : Submodule.span R (Set.range w') = F₀ := by
    rw [hF₀, hS, ← Submodule.span_image]
    congr 1
    have hcomp : w' = (F.subtype ∘ b) ∘ (Subtype.val) := rfl
    rw [hcomp, Set.range_comp, Subtype.range_coe, Set.image_comp]
  exact ⟨F₀, htrans F₀ Cm hdisj₀ hsup₀, hspaneq ▸ Module.Free.of_basis (Module.Basis.span hwli),
    hspaneq ▸ Module.Finite.span_of_finite R (Set.finite_range w'),
    Submodule.mem_map.2 ⟨x', hx'S, rfl⟩⟩

/-- Independence of a `ℕ`-indexed family of submodules from prefix-disjointness of
its partial sums. -/
theorem aux_iSupIndep_of_chain (F : ℕ → Submodule R M)
    (hchain : ∀ n, Disjoint (⨆ i ∈ Finset.range n, F i) (F n)) :
    iSupIndep F := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro v hv hsum i hi
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp at hi
    set m := s.max' hne with hm
    have hmem : m ∈ s := s.max'_mem hne
    have hsplit : v m + ∑ j ∈ s.erase m, v j = 0 := by
      rwa [← Finset.sum_erase_add s v hmem, add_comm] at hsum
    have hin : ∑ j ∈ s.erase m, v j ∈ (⨆ i ∈ Finset.range m, F i) := by
      refine Submodule.sum_mem _ fun j hj => ?_
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      exact le_biSup (f := F)
        (Finset.mem_range.2 ((s.le_max' j hjs).lt_of_ne (Finset.ne_of_mem_erase hj))) (hv j hjs)
    have hvm_in : v m ∈ (⨆ i ∈ Finset.range m, F i) := by
      rw [eq_neg_of_add_eq_zero_left hsplit]
      exact Submodule.neg_mem _ hin
    have hvm0 : v m = 0 := Submodule.disjoint_def.1 (hchain m) _ hvm_in (hv m hmem)
    have hsum' : ∑ j ∈ s.erase m, v j = 0 := by simpa [hvm0] using hsplit
    by_cases heq : i = m
    · exact heq ▸ hvm0
    · exact ih (s.erase m) (Finset.erase_ssubset hmem) v
        (fun j hj => hv j (Finset.mem_of_mem_erase hj)) hsum' i (Finset.mem_erase.2 ⟨heq, hi⟩)

/-- The internal direct sum of two disjoint free submodules is free. -/
theorem aux_free_sup (A B : Submodule R M) (hd : Disjoint A B)
    (hAf : Module.Free R A) (hBf : Module.Free R B) :
    Module.Free R ↥(A ⊔ B) := by
  set N := A ⊔ B
  have hAle : A ≤ N := le_sup_left
  have hBle : B ≤ N := le_sup_right
  set A' := Submodule.comap N.subtype A with hA'
  set B' := Submodule.comap N.subtype B with hB'
  have hcompl : IsCompl A' B' := by
    constructor
    · rw [disjoint_iff] at hd ⊢
      rw [hA', hB', ← Submodule.comap_inf, hd]
      simp
    · rw [codisjoint_iff, eq_top_iff]
      rintro y -
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 y.property
      rw [show y = (⟨a, hAle ha⟩ : N) + ⟨b, hBle hb⟩ from Subtype.ext (by simp [hab])]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb)
  have hA'f : Module.Free R A' := Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe hAle).symm
  have hB'f : Module.Free R B' := Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe hBle).symm
  exact Module.Free.of_equiv (Submodule.prodEquivOfIsCompl A' B' hcompl)

/-- Assembling a complement: if `IsCompl P Q`, `Q = F₀ ⊕ G₀`, then `IsCompl (P ⊔ F₀) G₀`. -/
theorem aux_compl_sup (P Q F₀ G₀ : Submodule R M)
    (hPQ : IsCompl P Q) (hsup : F₀ ⊔ G₀ = Q) (hdFG : Disjoint F₀ G₀) :
    IsCompl (P ⊔ F₀) G₀ := by
  refine ⟨hdFG.disjoint_sup_left_of_disjoint_sup_right (hsup ▸ hPQ.disjoint), ?_⟩
  rw [codisjoint_iff, sup_assoc, hsup, hPQ.sup_eq_top]

/-- One inductive step, retaining freeness of the increment.  From a finite free
direct summand `P` (with complement in `M`) and a target `y`, produce a larger such
`P'` together with a *free finite* increment `F` with `P' = P ⊕ F` and `y ∈ P'`. -/
theorem aux_step (hP : PropertyP R M)
    (P : Submodule R M) (hPc : ∃ Q, IsCompl P Q)
    (hPfree : Module.Free R P) (hPfin : Module.Finite R P) (y : M) :
    ∃ P' F : Submodule R M,
      (∃ Q', IsCompl P' Q') ∧ Module.Free R P' ∧ Module.Finite R P' ∧
      Disjoint P F ∧ P ⊔ F = P' ∧ y ∈ P' ∧ Module.Free R F ∧ Module.Finite R F := by
  obtain ⟨Q, hPQ⟩ := hPc
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hPQ.sup_eq_top ▸ Submodule.mem_top (x := y))
  obtain ⟨F, hFfree, hqF⟩ := hP Q P hPQ.symm hPfree hPfin q hq
  obtain ⟨F₀, hF₀ds, hF₀free, hF₀fin, hqF₀⟩ := exists_finFree_directSummand_mem Q F hFfree hqF
  obtain ⟨G₀, hdF₀G₀, hsupF₀G₀⟩ := hF₀ds
  have hdisj : Disjoint P F₀ := hPQ.disjoint.mono_right (hsupF₀G₀ ▸ le_sup_left)
  refine ⟨P ⊔ F₀, F₀, ⟨G₀, aux_compl_sup P Q F₀ G₀ hPQ hsupF₀G₀ hdF₀G₀⟩,
    aux_free_sup P F₀ hdisj hPfree hF₀free, inferInstance, hdisj, rfl, ?_, hF₀free, hF₀fin⟩
  rw [← hpq]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hqF₀)

/-- A finite free submodule of `M` together with the existence of a complement. -/
structure GState (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- The underlying submodule. -/
  P : Submodule R M
  /-- The submodule `P` has a complement in `M`. -/
  hc : ∃ Q, IsCompl P Q
  /-- The submodule `P` is free. -/
  hfree : Module.Free R P
  /-- The submodule `P` is finitely generated. -/
  hfin : Module.Finite R P

/-- The recursively-built chain of finite free direct summands. -/
noncomputable def buildSeq (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (hP : PropertyP R M) (x : ℕ → M) : ℕ → GState R M
  | 0 => ⟨⊥, ⟨⊤, isCompl_bot_top⟩, inferInstance, inferInstance⟩
  | (n+1) =>
      let s := buildSeq R M hP x n
      let h := aux_step hP s.P s.hc s.hfree s.hfin (x n)
      ⟨h.choose, h.choose_spec.choose_spec.left, h.choose_spec.choose_spec.right.left,
        h.choose_spec.choose_spec.right.right.left⟩

/-- The increment submodule at level `n`. -/
noncomputable def incrF (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (hP : PropertyP R M) (x : ℕ → M) (n : ℕ) : Submodule R M :=
  let s := buildSeq R M hP x n
  let h := aux_step hP s.P s.hc s.hfree s.hfin (x n)
  h.choose_spec.choose

/-- The properties of the increment at level `n`. -/
theorem step_spec (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (hP : PropertyP R M) (x : ℕ → M) (n : ℕ) :
    Disjoint (buildSeq R M hP x n).P (incrF R M hP x n) ∧
    (buildSeq R M hP x n).P ⊔ (incrF R M hP x n) = (buildSeq R M hP x (n+1)).P ∧
    x n ∈ (buildSeq R M hP x (n+1)).P ∧
    Module.Free R (incrF R M hP x n) := by
  set s := buildSeq R M hP x n
  set h := aux_step hP s.P s.hc s.hfree s.hfin (x n)
  obtain ⟨-, -, -, hdisj, hsup, hmem, hFfree, -⟩ := h.choose_spec.choose_spec
  exact ⟨hdisj, hsup, hmem, hFfree⟩

/-- The partial sum of the increments equals the chain element `P n`. -/
theorem partial_sum (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (hP : PropertyP R M) (x : ℕ → M) (n : ℕ) :
    (buildSeq R M hP x n).P = ⨆ i ∈ Finset.range n, incrF R M hP x i := by
  induction n with
  | zero => simp [buildSeq]
  | succ k ih =>
    rw [Finset.range_add_one, Finset.iSup_insert, ← (step_spec R M hP x k).right.left, ih,
      sup_comm]

/-- **The inductive construction of the increment family.**
Given a generating sequence `x : ℕ → M`, there is a family `F : ℕ → Submodule R M`
of finite free submodules such that:
  * `F` is independent (`iSupIndep F`);
  * for every `n`, the partial sum `⨆ i ∈ Finset.range n, F i` is a direct summand of
    `M` containing `x j` for all `j < n`;
  * consequently `⨆ n, F n = ⊤` (the supremum contains every generator `x n`).

Argument: build by recursion on `n` a chain of finite free direct summands
`P n` of `M` with `P 0 = ⊥`, `P n ≤ P (n+1)`, `x n ∈ P (n+1)`, and `P n` a direct
summand of `P (n+1)` (via `aux_step` applied to `P n` and `y := x n`). Take
`F n` to be the increment summand with `P (n+1) = P n ⊕ F n` (each finite free). Then
`P n = ⨆ i ∈ range n, F i`; independence of the `F i` follows from each `P n ⊕ F n`
being an internal direct sum; and since `P n` contains `x 0,…,x (n-1)`, the total
supremum `⨆ F` contains every `x n`, hence equals `span R (range x) = ⊤`. -/
theorem exists_increment_family
    (hP : PropertyP R M) (x : ℕ → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ F : ℕ → Submodule R M,
      iSupIndep F ∧ (⨆ n, F n = ⊤) ∧ (∀ n, Module.Free R (F n)) := by
  refine ⟨incrF R M hP x, ?_, ?_, ?_⟩
  · apply aux_iSupIndep_of_chain
    intro n
    rw [← partial_sum R M hP x n]
    exact (step_spec R M hP x n).left
  · rw [← top_le_iff, ← hx, Submodule.span_le]
    rintro y ⟨i, rfl⟩
    have hmem : x i ∈ (buildSeq R M hP x (i+1)).P := (step_spec R M hP x i).right.right.left
    rw [partial_sum R M hP x (i+1)] at hmem
    exact iSup₂_le (fun j _ => le_iSup (incrF R M hP x) j) hmem
  · exact fun n => (step_spec R M hP x n).right.right.right

/-- Stacks Tag 0591 / Lemma 10.85.2: a countably generated module satisfying
property (P) is free. -/
@[stacks 0591]
theorem countablyGenerated_propertyP_free
    (hcg : CountablyGenerated R M) (hP : PropertyP R M) :
    Module.Free R M := by
  obtain ⟨x, hx⟩ := exists_generating_seq hcg
  obtain ⟨F, hindep, hsup, hfree⟩ := exists_increment_family hP x hx
  exact free_of_iSupIndep_iSup_eq_top_free F hindep hsup hfree

end PropertyP

/-! ## Stacks 0592: elements of projective modules over local rings lie in free summands -/

section FreeSummand

variable {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]

/-- Among all realizations of `P` as a direct summand of the free module `P →₀ R`, one may
choose one for which a given element `x` has as few nonzero coordinates as possible. -/
private theorem exists_minimal_splitting [Module.Projective R P] (x : P) :
    ∃ (i : P →ₗ[R] (P →₀ R)) (π : (P →₀ R) →ₗ[R] P),
      (∀ w, π (i w) = w) ∧
        ∀ (i' : P →ₗ[R] (P →₀ R)) (π' : (P →₀ R) →ₗ[R] P),
          (∀ w, π' (i' w) = w) → (i x).support.card ≤ (i' x).support.card := by
  have hne :
    {n |
        ∃ (i : P →ₗ[R] (P →₀ R)) (π : (P →₀ R) →ₗ[R] P),
          (∀ w, π (i w) = w) ∧ (i x).support.card = n}.Nonempty := by
    obtain ⟨s, hs⟩ := Module.projective_def.mp ‹Module.Projective R P›
    exact ⟨_, s, Finsupp.linearCombination R id, hs, rfl⟩
  obtain ⟨i, π, hπ, hcard⟩ := Nat.sInf_mem hne
  refine ⟨i, π, hπ, fun i' π' h => ?_⟩
  rw [hcard]
  exact Nat.sInf_le ⟨i', π', h, rfl⟩

/-- If a section makes the number of nonzero coordinates of `x` minimal, then no coordinate of
`x` is a linear combination of the other coordinates: otherwise the section can be modified by a
square-zero endomorphism of `P →₀ R` so as to kill that coordinate. -/
private theorem not_eq_sum_erase_of_minimal [DecidableEq P] (i : P →ₗ[R] (P →₀ R))
    (π : (P →₀ R) →ₗ[R] P) (hπ : ∀ w, π (i w) = w) (x : P)
    (hmin :
      ∀ (i' : P →ₗ[R] (P →₀ R)) (π' : (P →₀ R) →ₗ[R] P),
        (∀ w, π' (i' w) = w) → (i x).support.card ≤ (i' x).support.card)
    (j : P) (hj : j ∈ (i x).support) (c : P → R) :
    (i x) j ≠ ∑ k ∈ (i x).support.erase j, (i x) k * c k := by
  intro heq
  set φ : (P →₀ R) →ₗ[R] R := ∑ k ∈ (i x).support.erase j, c k • Finsupp.lapply k with hφ
  set f : (P →₀ R) →ₗ[R] (P →₀ R) :=
    (LinearMap.toSpanSingleton R (P →₀ R) (Finsupp.single j (1 : R))) ∘ₗ φ with hf
  have hfapply :
    ∀ w, f w = (∑ k ∈ (i x).support.erase j, c k * w k) • Finsupp.single j (1 : R) := by
    intro w
    rw [hf, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
    congr 1
    rw [hφ, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by simp
  have hfsingle : f (Finsupp.single j (1 : R)) = 0 := by
    rw [hfapply, Finset.sum_eq_zero fun k hk => by simp [(Finset.ne_of_mem_erase hk).symm],
      zero_smul]
  have hff : ∀ w, f (f w) = 0 := fun w => by rw [hfapply w, map_smul, hfsingle, smul_zero]
  set g : (P →₀ R) →ₗ[R] (P →₀ R) := LinearMap.id - f with hg
  set g' : (P →₀ R) →ₗ[R] (P →₀ R) := LinearMap.id + f with hg'
  have hgg' : ∀ w, g' (g w) = w := by
    intro w
    simp only [hg, hg', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hff]
    abel
  have hfx : f (i x) = Finsupp.single j ((i x) j) := by
    rw [hfapply]
    have hsum : (∑ k ∈ (i x).support.erase j, c k * (i x) k) = (i x) j := by
      rw [heq]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hsum, Finsupp.smul_single', mul_one]
  have hix : (g ∘ₗ i) x = Finsupp.erase j (i x) := by
    rw [LinearMap.comp_apply, hg, LinearMap.sub_apply, LinearMap.id_apply, hfx,
      Finsupp.erase_eq_sub_single]
  have hle :=
    hmin (g ∘ₗ i) (π ∘ₗ g') (fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hgg', hπ])
  rw [hix, Finsupp.support_erase] at hle
  exact (Finset.card_erase_lt_of_mem hj).not_ge hle

/-- Over a local ring, a square matrix fixing a vector no entry of which is an `R`-combination
of the other entries has unit determinant: the off-diagonal entries and `1 - Bᵢᵢ` are non-units,
so modulo the maximal ideal the matrix is diagonal with nonzero diagonal. -/
private theorem isUnit_det_of_vecMul_eq_self [IsLocalRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (a : n → R) (B : Matrix n n R) (hrel : ∀ k, ∑ j, a j * B j k = a k)
    (hA : ∀ (j : n) (c : n → R), a j ≠ ∑ k ∈ Finset.univ.erase j, a k * c k) : IsUnit B.det := by
  have hnu : ∀ j k, ¬IsUnit ((if j = k then (1 : R) else 0) - B j k) := by
    intro j k hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    refine hA j (fun l => (B l k - if l = k then 1 else 0) * w) ?_
    have h1 : ∑ l ∈ Finset.univ.erase j, a l * B l k = a k - a j * B j k := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), hrel k]
    have h2 : ∑ l ∈ Finset.univ.erase j, a l * (if l = k then 1 else 0) =
        a k - a j * (if j = k then 1 else 0) := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      simp [mul_ite]
    calc
      a j = a j * (((if j = k then (1 : R) else 0) - B j k) * w) := by rw [hw, mul_one]
      _ = ((∑ l ∈ Finset.univ.erase j, a l * B l k) -
            ∑ l ∈ Finset.univ.erase j, a l * (if l = k then 1 else 0)) * w := by
        rw [h1, h2]; ring
      _ = ∑ l ∈ Finset.univ.erase j, a l * ((B l k - if l = k then 1 else 0) * w) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
  have hoff : ∀ j k, j ≠ k → ¬IsUnit (B j k) := fun j k h => by
    simpa [h] using hnu j k
  have hdiag : ∀ j, IsUnit (B j j) := by
    intro j
    have h1 : ¬IsUnit (1 - B j j) := by simpa using hnu j j
    by_contra hbj
    refine (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    rw [show (1 : R) = B j j + (1 - B j j) by ring]
    exact
      Ideal.add_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hbj)
        ((IsLocalRing.mem_maximalIdeal _).mpr h1)
  have hmap :
    (IsLocalRing.residue R).mapMatrix B =
      Matrix.diagonal (fun j => IsLocalRing.residue R (B j j)) := by
    ext j k
    rcases eq_or_ne j k with rfl | h
    · simp
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ h]
      exact
        (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (hoff j k h))
  by_contra hdet
  have h0 : IsLocalRing.residue R B.det = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hdet)
  rw [RingHom.map_det, hmap, Matrix.det_diagonal] at h0
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ((hdiag j).map (IsLocalRing.residue R)).ne_zero hj

end FreeSummand

/-- **Stacks Tag 0592, Lemma 10.85.3.** Any element of a projective module over a
(commutative) local ring is contained in a free direct summand. Concretely, for
every `x` in a projective module `P` over a local ring `R`, there is a submodule
`N` of `P` with `x ∈ N`, with `N` free as an `R`-module, and with `N` a direct
summand of `P` (witnessed by a complementary submodule `N'`, `IsCompl N N'`). -/
@[stacks 0592]
theorem projective_local_free_summand {R : Type*} [CommRing R] [IsLocalRing R]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P] (x : P) :
    ∃ N : Submodule R P, x ∈ N ∧ Module.Free R N ∧ ∃ N' : Submodule R P, IsCompl N N' := by
  classical
  obtain ⟨i, π, hπ, hmin⟩ := exists_minimal_splitting (R := R) x
  set T : Finset P := (i x).support with hT
  set y : ↥T → P := fun j => π (Finsupp.single (j : P) (1 : R)) with hy
  set B : Matrix ↥T ↥T R := Matrix.of fun j k => (i (y j)) (k : P) with hB
  have hvm :
    ∀ (v : ↥T → R) (M : Matrix ↥T ↥T R) (l : ↥T), Matrix.vecMul v M l = ∑ k, v k * M k l :=
    fun _ _ _ => rfl
  have hxsum : x = ∑ j : ↥T, ((i x) (j : P)) • y j := by
    have h1 : (i x) = ∑ j ∈ T, ((i x) j) • (Finsupp.single j (1 : R)) := by
      conv_lhs => rw [← Finsupp.sum_single (i x)]
      exact Finset.sum_congr rfl fun j _ => by rw [Finsupp.smul_single', mul_one]
    calc
      x = π (i x) := (hπ x).symm
      _ = π (∑ j ∈ T, ((i x) j) • (Finsupp.single j (1 : R))) := congrArg π h1
      _ = _ := by
        rw [map_sum, ← Finset.sum_coe_sort T]
        exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  have hBc : ∀ (c : ↥T → R) (l : ↥T),
      ∑ j : ↥T, c j * B j l = (i (∑ j : ↥T, c j • y j)) (l : P) := fun c l => by
    simp [hB, map_sum, Finsupp.finsetSum_apply]
  have hrel : ∀ k : ↥T, ∑ j : ↥T, ((i x) (j : P)) * B j k = (i x) (k : P) := fun k => by
    rw [hBc (fun j => (i x) (j : P)), ← hxsum]
  have hA :
    ∀ (j : ↥T) (c : ↥T → R), (i x) (j : P) ≠ ∑ k ∈ Finset.univ.erase j, (i x) (k : P) * c k := by
    intro j c heq
    refine
      not_eq_sum_erase_of_minimal i π hπ x hmin (j : P) j.2
        (fun k => if h : k ∈ T then c ⟨k, h⟩ else 0) ?_
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)] at heq
    rw [Finset.sum_erase_eq_sub j.2]
    have e3 :
      ∑ k ∈ T, (i x) k * (if h : k ∈ T then c ⟨k, h⟩ else 0) = ∑ k : ↥T, (i x) (k : P) * c k := by
      rw [← Finset.sum_coe_sort T fun k => (i x) k * (if h : k ∈ T then c ⟨k, h⟩ else 0)]
      exact Finset.sum_congr rfl fun k _ => by simp
    rw [e3]
    simpa using heq
  have hdet : IsUnit B.det :=
    isUnit_det_of_vecMul_eq_self (n := ↥T) (fun j => (i x) (j : P)) B hrel hA
  have hli : LinearIndependent R y := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h0 : ∀ l : ↥T, ∑ j : ↥T, c j * B j l = 0 := fun l => by
      rw [hBc, hc, map_zero]
      rfl
    calc
      c k = Matrix.vecMul c (B * B⁻¹) k := by rw [Matrix.mul_nonsing_inv B hdet, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, show Matrix.vecMul c B = 0 from funext h0]; simp
  refine ⟨Submodule.span R (Set.range y), ?_, Module.Free.of_basis (Module.Basis.span hli), ?_⟩
  · rw [hxsum]
    exact
      Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · set bN := Module.Basis.span hli with hbN
    set ρ : P →ₗ[R] ↥(Submodule.span R (Set.range y)) :=
      bN.equivFun.symm.toLinearMap ∘ₗ
        (Matrix.vecMulLinear B⁻¹) ∘ₗ
        LinearMap.pi (fun j : ↥T => (Finsupp.lapply (j : P)).comp i) with
      hρdef
    have hρy : ∀ j : ↥T, ρ (y j) = bN j := by
      intro j
      have h1 :
        (LinearMap.pi (fun k : ↥T => (Finsupp.lapply (k : P)).comp i)) (y j) = fun k : ↥T =>
          B j k := by
        funext k
        simp [hB]
      have h2 :
        Matrix.vecMul (fun k : ↥T => B j k) B⁻¹ = fun l : ↥T => (1 : Matrix ↥T ↥T R) j l := by
        funext l
        rw [hvm, ← Matrix.mul_nonsing_inv B hdet, Matrix.mul_apply]
      rw [hρdef]
      simp only [LinearMap.coe_comp, Function.comp_apply, h1, Matrix.vecMulLinear_apply, h2,
        LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]
      simp [Matrix.one_apply]
    have hρ : ∀ z : ↥(Submodule.span R (Set.range y)), ρ ↑z = z := by
      have hcomp : ρ ∘ₗ (Submodule.span R (Set.range y)).subtype = LinearMap.id := by
        refine bN.ext fun j => ?_
        rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply,
          show ((bN j : ↥(Submodule.span R (Set.range y))) : P) = y j by
            rw [hbN, Module.Basis.span_apply]]
        exact hρy j
      intro z
      simpa using LinearMap.congr_fun hcomp z
    exact ⟨_, LinearMap.isCompl_of_proj hρ⟩

/-! ## Stacks 0593: Kaplansky's theorem -/

/-- A projective module over a local ring has property (P): if `M = N ⊕ N'`, then `N` is
projective, so by Stacks 0592 every element of `N` lies in a free direct summand of `N`. -/
theorem propertyP_of_projective {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Projective R M] : PropertyP R M := by
  intro N N' h _ _ x hx
  have : Module.Projective R N :=
    Module.Projective.of_split N.subtype (N.projectionOnto N' h)
      (N.projectionOnto_comp_subtype h)
  obtain ⟨F₀, hmem, hfree, F₀', hcompl⟩ := projective_local_free_summand (R := R) (⟨x, hx⟩ : N)
  refine ⟨F₀.map N.subtype, ⟨⟨F₀'.map N.subtype,
    Submodule.disjoint_map N.injective_subtype hcompl.disjoint, ?_⟩,
    Module.Free.of_equiv (Submodule.equivMapOfInjective N.subtype N.injective_subtype F₀)⟩,
    ⟨⟨x, hx⟩, hmem, rfl⟩⟩
  rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_subtype_top]

/-- **Stacks 0593** (Kaplansky). If `P` is a projective module over a commutative local ring `R`,
then `P` is free. No finiteness hypothesis on `P` is needed. -/
@[stacks 0593 "Projective modules over local rings are free, with no finiteness hypothesis.",
  sga "3 VIA 2.1.3"]
public theorem Module.free_of_projective_of_isLocalRing {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [IsLocalRing R] [Module.Projective R P] : Module.Free R P :=
  (Module.forall_free_of_projective_iff_forall_free_of_projective_of_countable_span R).mpr
    (fun _ _ _ _ hcg => countablyGenerated_propertyP_free hcg propertyP_of_projective) P
    ‹Module.Projective R P›
