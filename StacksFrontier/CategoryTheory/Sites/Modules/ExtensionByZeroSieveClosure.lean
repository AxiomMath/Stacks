module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroMarkedSpan
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Closing a finite set of marked generators under the differential, on a site

Let `(C, O)` be a ringed site and let `P` be a cochain complex of sheaves of `O`-modules each of
whose terms is presented as a sum of extensions by zero of structure sheaves of slices,
`P^n = ⊕_α j_{U_{n,α}!}O_{U_{n,α}}`. Given finitely many sections of the terms of `P` over an
object `V`, all in degrees `≥ L`, and a degree `b` above which `P` vanishes, this file produces
a **covering sieve of `V` along whose arrows there is a finite set `S` of marked generators**
such that

* every generator in `S` has degree `≥ L`;
* the restrictions of the given sections lie in the span of the generators of `S` of their
  degree;
* the differential of each generator of `S` of degree `n` lies in the span of the generators of
  `S` of degree `n + 1`.

That last clause is what makes the generators of `S` span a *subcomplex*, and it is the reason
for the construction: closing a finite set of generators under the differential.

## Main definitions

* `Stacks.Sites.ExtensionByZeroSpan.cofanTerm`: the cofan presenting `P^n` as a sum of extensions
  by zero.
* `Stacks.Sites.ExtensionByZeroSpan.MarkedT`: a marked generator of some degree.
* `Stacks.Sites.ExtensionByZeroSpan.fibT`: the marked generators of a given degree in a finite
  set of marked generators of all degrees.
* `Stacks.Sites.ExtensionByZeroSpan.ClosedSpanUpTo`: the invariant of the construction, read as
  a property of an *arrow* — closure under the differential is only required in degrees
  `L ≤ n ≤ m`.
* `Stacks.Sites.ExtensionByZeroSpan.closureSieve`: the sieve of arrows at which that invariant
  holds. That it *is* a sieve is `ClosedSpanUpTo.comp`.

## Main results

* `Stacks.Sites.ExtensionByZeroSpan.ClosedSpanUpTo.comp`: the invariant is stable under
  precomposition — restricting a finite set of marked generators along an arrow gives a finite
  set of marked generators again, by `markedResT`, and all three clauses restrict.
* `Stacks.Sites.ExtensionByZeroSpan.closureSieve_base_mem`: the invariant with an empty range of
  degrees holds on a covering sieve. This is local generation,
  `Stacks.Sites.ExtensionByZeroSpan.spanSieve_mem`, intersected over the finitely many given
  sections.
* `Stacks.Sites.ExtensionByZeroSpan.closureSieve_succ_mem`: one more degree of closure costs one
  more refinement, by transitivity of the topology.
* `Stacks.Sites.ExtensionByZeroSpan.exists_sieve_closedSpan`: **the differential closure**, the
  statement displayed above.

## Implementation notes

**Why this is not a transcription of the ringed-space argument.** Over a space
(`Stacks.Cohomology.LeftDualPerfect.exists_closed_span`) each step of the induction on the
degree shrinks an open neighbourhood of a point, and the lattice of opens lets the finitely many
shrinkings be taken simultaneously by an infimum; the invariant is a statement about an *open*.
On a site there is no such lattice: a refinement is a covering sieve of an object reached by the
previous refinement, and the data attached to its arrows cannot be read off a single object. So
the invariant here is a property of an **arrow into `V`**, and the two facts that drive the
induction are
*  that the property is stable under precomposition, so that it defines a sieve, and
*  `CategoryTheory.GrothendieckTopology.transitive`, which turns "covering, and covering again
   past each arrow" into "covering",
in place of "shrink the open and intersect". Only the base case is an intersection, and it is a
finite intersection of sieves on the *same* object, `Finset.inf`, which is where the finitely
many given sections are handled at once.

**Why `Finset.image` and not a hypothesis.** A marked generator restricts to a marked generator
with no side condition, so the finite set travels along an arrow as a `Finset.image` and
`fibT_image` identifies the degree-`n` part of the image with the image of the degree-`n` part.
The ringed-space argument instead carries the hypothesis `∀ α ∈ S, Z ≤ U α` through every step,
because there a generator is named by its index alone.

Nothing below is a clause of a tag; these are steps of the proof of [Stacks, Tag 0FPV], so no
`@[stacks …]` attribute is attached.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ExtensionByZeroSpan

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u}) (P : CochainComplex (SheafOfModules.{u} O) ℤ)
  {I : ℤ → Type u} (U : ∀ n, I n → C) (ιP : ∀ n α, extUnit O (U n α) ⟶ P.X n)

/-- The cofan presenting the term `P^n` as a sum of extensions by zero. -/
abbrev cofanTerm (n : ℤ) : Cofan fun α : I n => extUnit O (U n α) :=
  Cofan.mk (P.X n) (ιP n)

/-- A marked generator of some degree: a degree `n` together with a marked generator of the
family presenting `P^n`. -/
abbrev MarkedT (U : ∀ n, I n → C) (W : C) : Type u := Σ n : ℤ, Marked (U n) W

/-- Restriction of a marked generator of some degree along an arrow. -/
def markedResT {W' W : C} (f : W' ⟶ W) (m : MarkedT U W) : MarkedT U W' :=
  ⟨m.1, markedRes (U m.1) f m.2⟩

/-- The marked generators of degree `n` in a finite set of marked generators of all degrees. -/
def fibT {W : C} (S : Finset (MarkedT U W)) (n : ℤ) : Finset (Marked (U n) W) :=
  S.preimage (fun m : Marked (U n) W => (⟨n, m⟩ : MarkedT U W))
    fun _ _ _ _ h => by simpa using h

/-- A marked generator `m` of degree `n` lies in the degree-`n` part of `S` if and only if
`⟨n, m⟩` lies in `S`. -/
theorem mem_fibT {V : ∀ n, I n → C} {W : C} {S : Finset (MarkedT V W)} {n : ℤ}
    {m : Marked (V n) W} : m ∈ fibT V S n ↔ (⟨n, m⟩ : MarkedT V W) ∈ S :=
  Finset.mem_preimage

open Classical in
/-- The degree-`n` part of a restricted finite set of marked generators is the restriction of
its degree-`n` part. -/
theorem fibT_image {W' W : C} (f : W' ⟶ W) (S : Finset (MarkedT U W)) (n : ℤ) :
    fibT U (S.image (markedResT U f)) n = (fibT U S n).image (markedRes (U n) f) := by
  ext m'
  rw [mem_fibT, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxe⟩
    obtain ⟨k, mk⟩ := x
    cases congrArg Sigma.fst hxe
    exact ⟨mk, mem_fibT.2 hx, by simpa [markedResT] using hxe⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨n, m⟩, mem_fibT.1 hm, rfl⟩

/-- The differential commutes with restricting a marked generator. -/
theorem d_app_elemSec_markedRes (n n' : ℤ) {W' W : C} (g : W' ⟶ W) (mm : Marked (U n) W) :
    (P.d n n').val.app (op W') (elemSec O (U n) (cofanTerm O P U ιP n) (markedRes (U n) g mm)) =
      (P.X n').val.map g.op
        ((P.d n n').val.app (op W) (elemSec O (U n) (cofanTerm O P U ιP n) mm)) :=
  (congrArg ((P.d n n').val.app (op W'))
    (map_elemSec O (U n) (cofanTerm O P U ιP n) g mm).symm).trans
    (PresheafOfModules.naturality_apply (P.d n n').val g.op _)

/-- **The invariant of the differential-closure construction**, as a property of an arrow
`f : W ⟶ V`: over `W` there is a finite set of marked generators, all of degree `≥ L`, whose
span contains the restrictions of the given sections and which is closed under the differential
in the degrees `L ≤ n ≤ m`. -/
def ClosedSpanUpTo (L m : ℤ) {V : C} {κ : Type*} (deg : κ → ℤ)
    (s : ∀ i, (P.X (deg i)).val.obj (op V)) {W : C} (f : W ⟶ V) : Prop :=
  ∃ S : Finset (MarkedT U W), (∀ x ∈ S, L ≤ x.1) ∧
    (∀ i, InSpan O (U (deg i)) (cofanTerm O P U ιP (deg i)) (fibT U S (deg i))
      ((P.X (deg i)).val.map f.op (s i))) ∧
    ∀ n, L ≤ n → n ≤ m → ∀ g ∈ fibT U S n,
      InSpan O (U (n + 1)) (cofanTerm O P U ιP (n + 1)) (fibT U S (n + 1))
        ((P.d n (n + 1)).val.app (op W) (elemSec O (U n) (cofanTerm O P U ιP n) g))

/-- A generator of `S` of degree `n` restricts to a generator of degree `n` of any finite set
containing the restriction of `S`. -/
private theorem markedRes_mem_fibT {W' W : C} [DecidableEq (MarkedT U W')] (g : W' ⟶ W)
    {S : Finset (MarkedT U W)} {T : Finset (MarkedT U W')} (hST : S.image (markedResT U g) ⊆ T)
    {n : ℤ} {mm : Marked (U n) W} (hmm : mm ∈ fibT U S n) : markedRes (U n) g mm ∈ fibT U T n :=
  mem_fibT.2 (hST (Finset.mem_image_of_mem _ (mem_fibT.1 hmm)))

/-- **The invariant is stable under precomposition**, so it defines a sieve. -/
theorem ClosedSpanUpTo.comp {L m : ℤ} {V : C} {κ : Type*} {deg : κ → ℤ}
    {s : ∀ i, (P.X (deg i)).val.obj (op V)} {W W' : C} {f : W ⟶ V}
    (h : ClosedSpanUpTo O P U ιP L m deg s f) (g : W' ⟶ W) :
    ClosedSpanUpTo O P U ιP L m deg s (g ≫ f) := by
  classical
  obtain ⟨S, hSL, hsec, hd⟩ := h
  refine ⟨S.image (markedResT U g), ?_, fun i => ?_, fun n hn hnm m' hm' => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact hSL y hy
  · rw [op_comp, (P.X (deg i)).val.map_comp_apply f.op g.op]
    exact (hsec i).res O _ _ g fun mm hmm => markedRes_mem_fibT U g subset_rfl hmm
  · rw [fibT_image] at hm'
    obtain ⟨mm, hmm, rfl⟩ := Finset.mem_image.1 hm'
    rw [d_app_elemSec_markedRes O P U ιP]
    exact (hd n hn hnm mm hmm).res O _ _ g fun mm' hmm' =>
      markedRes_mem_fibT U g subset_rfl hmm'

/-- The sieve of arrows at which the invariant of the differential-closure construction
holds. -/
def closureSieve (L m : ℤ) {V : C} {κ : Type*} (deg : κ → ℤ)
    (s : ∀ i, (P.X (deg i)).val.obj (op V)) : Sieve V where
  arrows _ f := ClosedSpanUpTo O P U ιP L m deg s f
  downward_closed h g := h.comp O P U ιP g

/-- **The base of the induction**: with an empty range of degrees to close, the invariant holds
along a covering sieve. This is local generation of each term of `P` by its marked generators,
intersected over the finitely many given sections. -/
theorem closureSieve_base_mem (hc : ∀ n, IsColimit (cofanTerm O P U ιP n)) (L : ℤ) {V : C}
    {κ : Type*} [Fintype κ] (deg : κ → ℤ) (s : ∀ i, (P.X (deg i)).val.obj (op V))
    (hL : ∀ i, L ≤ deg i) : closureSieve O P U ιP L (L - 1) deg s ∈ J V := by
  classical
  refine J.superset_covering ?_ (finset_inf_mem (J := J) (Finset.univ : Finset κ)
    (fun i => Stacks.SheafOfModules.spanSieve (cofanTerm O P U ιP (deg i)).pt
      (genSections O (U (deg i)) (cofanTerm O P U ιP (deg i))) (s i))
    fun i _ => spanSieve_mem O (U (deg i)) (cofanTerm O P U ιP (deg i)) (hc _) (s i))
  intro W f hf
  change ClosedSpanUpTo O P U ιP L (L - 1) deg s f
  have key : ∀ i : κ, ∃ S : Finset (Marked (U (deg i)) W),
      InSpan O (U (deg i)) (cofanTerm O P U ιP (deg i)) S
        ((P.X (deg i)).val.map f.op (s i)) := by
    intro i
    have hle : (Finset.univ.inf fun j => Stacks.SheafOfModules.spanSieve
          (cofanTerm O P U ιP (deg j)).pt
          (genSections O (U (deg j)) (cofanTerm O P U ιP (deg j))) (s j)) ≤
        Stacks.SheafOfModules.spanSieve (cofanTerm O P U ιP (deg i)).pt
          (genSections O (U (deg i)) (cofanTerm O P U ιP (deg i))) (s i) :=
      Finset.inf_le (Finset.mem_univ i)
    exact exists_inSpan_of_mem_spanSubmodule O _ _ (hle f hf)
  choose Sfun hSfun using key
  refine ⟨Finset.univ.biUnion fun i => (Sfun i).image (Sigma.mk (deg i)), ?_, fun i => ?_,
    fun n hn hn' => absurd (hn.trans hn') (by omega)⟩
  · intro x hx
    obtain ⟨i, -, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨mm, -, rfl⟩ := Finset.mem_image.1 hx
    exact hL i
  · exact (hSfun i).mono O _ _ fun mm hmm =>
      mem_fibT.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hmm⟩)

/-- **One more degree of closure costs one more refinement.** The generators of degree `m + 1`
of a finite set satisfying the invariant are finitely many, so their differentials lie in the
span of finitely many generators of degree `m + 2` along a covering sieve of the object the
previous refinement reached; transitivity of the topology assembles the two. -/
theorem closureSieve_succ_mem (hc : ∀ n, IsColimit (cofanTerm O P U ιP n)) (L m : ℤ)
    (hm : L - 1 ≤ m) {V : C} {κ : Type*} {deg : κ → ℤ}
    {s : ∀ i, (P.X (deg i)).val.obj (op V)}
    (h : closureSieve O P U ιP L m deg s ∈ J V) :
    closureSieve O P U ιP L (m + 1) deg s ∈ J V := by
  classical
  refine J.transitive h _ fun W f hf => ?_
  obtain ⟨S, hSL, hsec, hd⟩ := hf
  obtain ⟨R', hR', hR'spec⟩ := exists_sieve_inSpan_finset O (U (m + 1 + 1))
    (cofanTerm O P U ιP (m + 1 + 1)) (hc _) (fibT U S (m + 1))
    fun mm => (P.d (m + 1) (m + 1 + 1)).val.app (op W)
      (elemSec O (U (m + 1)) (cofanTerm O P U ιP (m + 1)) mm)
  refine J.superset_covering ?_ hR'
  intro W' g hg
  change ClosedSpanUpTo O P U ιP L (m + 1) deg s (g ≫ f)
  obtain ⟨S', hS'⟩ := hR'spec g hg
  refine ⟨S.image (markedResT U g) ∪ S'.image (Sigma.mk (m + 1 + 1)), ?_, fun i => ?_,
    fun n hn hnm m' hm' => ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with h1 | h1
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h1
      exact hSL y hy
    · obtain ⟨β, -, rfl⟩ := Finset.mem_image.1 h1
      change L ≤ m + 1 + 1
      omega
  · rw [op_comp, (P.X (deg i)).val.map_comp_apply f.op g.op]
    exact (hsec i).res O _ _ g fun mm hmm =>
      markedRes_mem_fibT U g Finset.subset_union_left hmm
  · have hsplit : m' ∈ fibT U (S.image (markedResT U g)) n := by
      rcases Finset.mem_union.1 (mem_fibT.1 hm') with h1 | h1
      · exact mem_fibT.2 h1
      · obtain ⟨β, -, hβ⟩ := Finset.mem_image.1 h1
        have hdeg : m + 1 + 1 = n := congrArg Sigma.fst hβ
        exact absurd hdeg (by omega)
    rw [fibT_image] at hsplit
    obtain ⟨mm, hmm, rfl⟩ := Finset.mem_image.1 hsplit
    rw [d_app_elemSec_markedRes O P U ιP]
    by_cases hn' : n ≤ m
    · exact (hd n hn hn' mm hmm).res O _ _ g fun mm' hmm' =>
        markedRes_mem_fibT U g Finset.subset_union_left hmm'
    · obtain rfl : n = m + 1 := by omega
      refine (hS' mm hmm).mono O _ _ fun mm' hmm' => mem_fibT.2 ?_
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hmm')

/-- **The differential closure of a finite family of sections, on a site.** Let `P` be a complex
of sheaves of `O`-modules whose terms are presented as sums of extensions by zero of structure
sheaves of slices, with `P^n = 0` for `n > b`, and let finitely many sections of the terms of
`P`, in degrees `≥ L`, over an object `V` be given. Then along the arrows of a covering sieve of
`V` there is a finite set `S` of marked generators, all of degree `≥ L`, spanning the
restrictions of the given sections and such that the differential of each generator of `S` lies
in the span of the generators of `S` of the next degree. -/
theorem exists_sieve_closedSpan (hc : ∀ n, IsColimit (cofanTerm O P U ιP n)) (b L : ℤ)
    (hb : ∀ n, b < n → IsZero (P.X n)) {V : C} {κ : Type*} [Fintype κ] (deg : κ → ℤ)
    (s : ∀ i, (P.X (deg i)).val.obj (op V)) (hL : ∀ i, L ≤ deg i) :
    ∃ R : Sieve V, R ∈ J V ∧ ∀ ⦃W : C⦄ (f : W ⟶ V), R.arrows f →
      ∃ S : Finset (MarkedT U W), (∀ x ∈ S, L ≤ x.1) ∧
        (∀ i, InSpan O (U (deg i)) (cofanTerm O P U ιP (deg i)) (fibT U S (deg i))
          ((P.X (deg i)).val.map f.op (s i))) ∧
        ∀ n, ∀ g ∈ fibT U S n,
          InSpan O (U (n + 1)) (cofanTerm O P U ιP (n + 1)) (fibT U S (n + 1))
            ((P.d n (n + 1)).val.app (op W) (elemSec O (U n) (cofanTerm O P U ιP n) g)) := by
  refine ⟨closureSieve O P U ιP L (max b (L - 1)) deg s, ?_, fun W f hf => ?_⟩
  · exact Int.leInduction (closureSieve_base_mem O P U ιP hc L deg s hL)
      (fun k hk ih => closureSieve_succ_mem O P U ιP hc L k hk ih) (max b (L - 1))
      (le_max_right _ _)
  · obtain ⟨S, hSL, hsec, hd⟩ := hf
    refine ⟨S, hSL, hsec, fun n g hg => ?_⟩
    by_cases hn : n ≤ max b (L - 1)
    · exact hd n (hSL ⟨n, g⟩ (mem_fibT.1 hg)) hn g hg
    · have h0 : (P.d n (n + 1)).val.app (op W) (elemSec O (U n) (cofanTerm O P U ιP n) g) = 0 :=
        congrArg (fun φ : P.X n ⟶ P.X (n + 1) =>
            φ.val.app (op W) (elemSec O (U n) (cofanTerm O P U ιP n) g))
          ((hb (n + 1) (by omega)).eq_of_tgt (P.d n (n + 1)) 0)
      rw [h0]
      exact inSpan_zero O _ _ _

end Stacks.Sites.ExtensionByZeroSpan

end
