module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SieveIndexedSpan
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# A finite set of arrow generators closed under the differential

Let `(C, J)` be a small site, `O` a sheaf of rings on it, and `P` a cochain complex of sheaves
of `O`-modules each of whose terms is presented as a direct sum of extensions by zero of the
structure sheaves of slices, `P^n = ⊕_{α ∈ I n} j_{U n α !} O_{U n α}`, with `P^n = 0` for
`n > b`. Given finitely many sections of terms of `P` over an object `V`, in degrees `≥ L`,
there is a covering sieve of `V` over each member of which one can choose a *finite* graded set
`S` of arrow generators, concentrated in degrees `≥ L`, such that

* the restrictions of the given sections lie in the span of the generators of `S` of their own
  degree, and
* the differential of each generator of `S` of degree `n` lies in the span of the generators of
  `S` of degree `n + 1`.

That is the data from which a finitely generated subcomplex of `P` is built, and this file is
the sieve-indexed replacement for the ringed-space construction
`Stacks.Cohomology.LeftDualPerfect.exists_closed_span` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroClosure`.

## Main definitions

* `Stacks.Sites.ExtensionByZero.cofanP`: the cofan presenting the degree-`n` term of `P`.
* `Stacks.Sites.ExtensionByZero.closureSieve`: the sieve of arrows along which such a finite
  graded set of generators exists, with the differential condition imposed in degrees `≤ m`.

## Main results

* `Stacks.Sites.ExtensionByZero.d_genSec_res`: the differential commutes with restriction on
  arrow generators.
* `Stacks.Sites.ExtensionByZero.closureSieve_zero_mem`: the sieve is covering when no
  differential condition is imposed.
* `Stacks.Sites.ExtensionByZero.closureSieve_mem`: it stays covering as the differential
  condition is imposed one degree at a time.
* `Stacks.Sites.ExtensionByZero.exists_sieve_closed_span`: **the finite graded set of
  generators closed under the differential in every degree**, over a covering sieve.

## Implementation notes

Over a space the corresponding construction shrinks one open repeatedly, once per degree
between `L` and `b`, and the invariant carries that open. Here the invariant is a *sieve* —
"over this arrow such a finite set exists" is stable under further precomposition, by
`Stacks.Sites.ExtensionByZero.InSpan.res` — and the induction on the degree refines it by
`GrothendieckTopology.transitive`. The induction is `Int.le_induction` from `L - 1`, and it
stops at `max b (L - 1)`: above `b` the target of the differential is a zero module, so the
condition there is automatic.

The graded set of generators is a family `S : ∀ n, Finset (GenIdx (U n) W)` together with a
`Finset ℤ` outside of which it is empty, rather than a single `Finset (Σ n, GenIdx (U n) W)` as
on the space side. The two carry the same information; the graded form avoids destructuring a
dependent `Sigma` equality every time the family is restricted along an arrow, which is what
the degree induction does at every step.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ExtensionByZero

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u}) (P : CochainComplex (SheafOfModules.{u} O) ℤ)
  {I : ℤ → Type u} (U : ∀ n, I n → C)
  (ιP : ∀ (n : ℤ) (α : I n), (SheafOfModules.extensionByZero.{u, u, u, u} O (U n α)).obj
    (SheafOfModules.unit (O.over (U n α))) ⟶ P.X n)

/-- **The cofan presenting the degree-`n` term of `P` as a sum of extensions by zero.** -/
abbrev cofanP (n : ℤ) : Cofan fun α : I n =>
    (SheafOfModules.extensionByZero.{u, u, u, u} O (U n α)).obj
      (SheafOfModules.unit (O.over (U n α))) :=
  Cofan.mk (P.X n) (ιP n)

/-- **The differential commutes with restriction on arrow generators.** -/
theorem d_genSec_res {W' W : C} (m : W' ⟶ W) (n : ℤ) (y : GenIdx (U n) W) :
    (P.d n (n + 1)).val.app (op W')
        (genSec O (U n) (cofanP O P U ιP n) W' (resGenIdx (U n) m y)) =
      (P.X (n + 1)).val.restrictₛₗ m.op
        ((P.d n (n + 1)).val.app (op W) (genSec O (U n) (cofanP O P U ιP n) W y)) :=
  (congrArg ((P.d n (n + 1)).val.app (op W'))
      (restrictₛₗ_genSec O (U n) (cofanP O P U ιP n) m y).symm).trans
    (PresheafOfModules.naturality_apply (P.d n (n + 1)).val m.op
      (genSec O (U n) (cofanP O P U ιP n) W y))

/-- **Adjoining generators of one degree to a graded set of generators.** -/
def addAtDeg {W : C} (S : ∀ n : ℤ, Set (GenIdx (U n) W)) (d : ℤ)
    (S' : Set (GenIdx (U d) W)) (n : ℤ) : Set (GenIdx (U n) W) :=
  if h : d = n then S n ∪ h ▸ S' else S n

/-- Away from degree `d`, adjoining `S'` in degree `d` leaves `S n` unchanged. -/
theorem addAtDeg_of_ne {W : C} (S : ∀ n : ℤ, Set (GenIdx (U n) W)) {d : ℤ}
    (S' : Set (GenIdx (U d) W)) {n : ℤ} (h : d ≠ n) : addAtDeg U S d S' n = S n :=
  dite_eq_right h

/-- In degree `d`, adjoining `S'` in degree `d` gives `S d ∪ S'`. -/
theorem addAtDeg_self {W : C} (S : ∀ n : ℤ, Set (GenIdx (U n) W)) (d : ℤ)
    (S' : Set (GenIdx (U d) W)) : addAtDeg U S d S' d = S d ∪ S' :=
  dite_eq_left rfl

/-- Each `S n` is contained in the degree-`n` part of `addAtDeg U S d S'`. -/
theorem subset_addAtDeg {W : C} (S : ∀ n : ℤ, Set (GenIdx (U n) W)) (d : ℤ)
    (S' : Set (GenIdx (U d) W)) (n : ℤ) : S n ⊆ addAtDeg U S d S' n := by
  rw [addAtDeg]
  split
  · exact Set.subset_union_left
  · exact subset_rfl

/-- The set `S'` is contained in the degree-`d` part of `addAtDeg U S d S'`. -/
theorem subset_addAtDeg_self {W : C} (S : ∀ n : ℤ, Set (GenIdx (U n) W)) (d : ℤ)
    (S' : Set (GenIdx (U d) W)) : S' ⊆ addAtDeg U S d S' d := by
  rw [addAtDeg_self]
  exact Set.subset_union_right

/-- Adjoining a finite set to a degreewise finite graded set gives a degreewise finite graded
set. -/
theorem finite_addAtDeg {W : C} {S : ∀ n : ℤ, Set (GenIdx (U n) W)} (hS : ∀ n, (S n).Finite)
    {d : ℤ} {S' : Set (GenIdx (U d) W)} (hS' : S'.Finite) (n : ℤ) :
    (addAtDeg U S d S' n).Finite := by
  by_cases h : d = n
  · subst h
    rw [addAtDeg_self]
    exact (hS d).union hS'
  · rw [addAtDeg_of_ne U S S' h]
    exact hS n

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A section of a zero sheaf of modules vanishes. -/
theorem eq_zero_of_isZero {M : SheafOfModules.{u} O} (hM : IsZero M) {W : C}
    (x : M.val.obj (op W)) : x = 0 :=
  congrArg (fun φ : M ⟶ M => φ.val.app (op W) x) (hM.eq_of_src (𝟙 M) 0)

/-- **The sieve of arrows along which a finite graded set of arrow generators spans the given
sections and is closed under the differential in degrees `≤ m`.** -/
def closureSieve (L m : ℤ) {V : C} {ι : Type*} (A : Finset ι) (deg : ι → ℤ)
    (s : ∀ i, (P.X (deg i)).val.obj (op V)) : Sieve V where
  arrows W k := ∃ S : ∀ n : ℤ, Set (GenIdx (U n) W),
    (∀ n : ℤ, (S n).Finite) ∧ (∀ n : ℤ, n < L → S n = ∅) ∧
    (∀ i ∈ A, InSpan O (U (deg i)) (cofanP O P U ιP (deg i)) W (S (deg i))
      ((P.X (deg i)).val.restrictₛₗ k.op (s i))) ∧
    (∀ n : ℤ, n ≤ m → ∀ y ∈ S n,
      InSpan O (U (n + 1)) (cofanP O P U ιP (n + 1)) W (S (n + 1))
        ((P.d n (n + 1)).val.app (op W) (genSec O (U n) (cofanP O P U ιP n) W y)))
  downward_closed := by
    rintro W W'' k ⟨S, hfin, hlow, hspan, hd⟩ m'
    refine ⟨fun n => resGenIdx (U n) m' '' S n, fun n => (hfin n).image _, fun n hn => ?_,
      fun i hi => ?_, fun n hnm y hy => ?_⟩
    · change resGenIdx (U n) m' '' S n = ∅
      rw [hlow n hn, Set.image_empty]
    · rw [restrictₛₗ_op_comp_apply O m' k (s i)]
      exact (hspan i hi).res O _ _ m' fun z hz => Set.mem_image_of_mem _ hz
    · obtain ⟨y₀, hy₀, rfl⟩ := hy
      rw [d_genSec_res O P U ιP m' n y₀]
      exact (hd n hnm y₀ hy₀).res O _ _ m' fun z hz => Set.mem_image_of_mem _ hz

/-- Restricting a section in the span of `S` gives a section in the span of the restricted `S`. -/
private theorem inSpan_image_res {W' W : C} (m : W' ⟶ W) {n : ℤ} {S : Set (GenIdx (U n) W)}
    {x : (P.X n).val.obj (op W)} (hx : InSpan O (U n) (cofanP O P U ιP n) W S x) :
    InSpan O (U n) (cofanP O P U ιP n) W' (resGenIdx (U n) m '' S)
      ((P.X n).val.restrictₛₗ m.op x) :=
  hx.res O _ _ m fun _ hz => Set.mem_image_of_mem _ hz

/-- Restricting a finite graded set vanishing below `L` gives one with the same properties. -/
private theorem finite_low_image_res {W' W : C} (m : W' ⟶ W) (L : ℤ)
    {S : ∀ n : ℤ, Set (GenIdx (U n) W)} (hfin : ∀ n : ℤ, (S n).Finite)
    (hlow : ∀ n : ℤ, n < L → S n = ∅) {Sm : ∀ n : ℤ, Set (GenIdx (U n) W')}
    (hSm : Sm = fun n => resGenIdx (U n) m '' S n) :
    (∀ n : ℤ, (Sm n).Finite) ∧ ∀ n : ℤ, n < L → Sm n = ∅ := by
  subst hSm
  exact ⟨fun n => (hfin n).image _, fun n hn => by simp [hlow n hn]⟩

variable [∀ n : ℤ, HasCoproduct fun α : I n =>
  (SheafOfModules.extensionByZero.{u, u, u, u} O (U n α)).obj
    (SheafOfModules.unit (O.over (U n α)))]

/-- **Finitely many sections of the terms of `P`, in degrees `≥ L`, lie on a covering sieve in
the span of a finite graded set of arrow generators vanishing in degrees `< L`.** No condition
on the differential is imposed yet. -/
theorem closureSieve_bot_mem (hc : ∀ n : ℤ, IsColimit (cofanP O P U ιP n)) (L : ℤ) {V : C}
    {ι : Type*} (A : Finset ι) (deg : ι → ℤ) (hL : ∀ i ∈ A, L ≤ deg i)
    (s : ∀ i, (P.X (deg i)).val.obj (op V)) :
    closureSieve O P U ιP L (L - 1) A deg s ∈ J V := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    refine J.superset_covering (fun W k _ => ⟨fun _ => ∅, fun _ => Set.finite_empty,
      fun _ _ => rfl, by simp, fun n _ y hy => absurd hy (Set.notMem_empty y)⟩) (J.top_mem V)
  | insert i A hi ih =>
    have hLi : L ≤ deg i := hL i (Finset.mem_insert_self i A)
    have hLA : ∀ j ∈ A, L ≤ deg j := fun j hj => hL j (Finset.mem_insert_of_mem hj)
    refine J.transitive (ih hLA) _ fun {W} k hk => ?_
    obtain ⟨S, hfin, hlow, hspan, -⟩ := hk
    refine J.superset_covering ?_ (spanSieve_mem O (U (deg i)) (cofanP O P U ιP (deg i))
      (hc (deg i)) ((P.X (deg i)).val.restrictₛₗ k.op (s i)))
    intro W' m hm
    obtain ⟨S', hS'fin, hS'⟩ := hm
    set Sm : ∀ n : ℤ, Set (GenIdx (U n) W') := fun n => resGenIdx (U n) m '' S n with hSmdef
    obtain ⟨hSmfin, hSmlow⟩ := finite_low_image_res U m L hfin hlow hSmdef
    refine ⟨addAtDeg U Sm (deg i) S', finite_addAtDeg U hSmfin hS'fin, fun n hn => ?_,
      fun j hj => ?_, fun n hnm y hy => ?_⟩
    · rw [addAtDeg_of_ne U Sm S' (by omega : deg i ≠ n), hSmlow n hn]
    · rw [restrictₛₗ_op_comp_apply O m k (s j)]
      rcases Finset.mem_insert.1 hj with rfl | hjA
      · exact hS'.mono O _ _ (subset_addAtDeg_self U Sm _ S')
      · exact (inSpan_image_res O P U ιP m (hspan j hjA)).mono O _ _
          (subset_addAtDeg U Sm (deg i) S' (deg j))
    · exfalso
      rw [addAtDeg_of_ne U Sm S' (by omega : deg i ≠ n), hSmlow n (by omega)] at hy
      exact Set.notMem_empty y hy

/-- **The differential condition can be imposed one degree at a time.** -/
theorem closureSieve_succ_mem (hc : ∀ n : ℤ, IsColimit (cofanP O P U ιP n)) (L m : ℤ)
    (hm : L - 1 ≤ m) {V : C} {ι : Type*} (A : Finset ι) (deg : ι → ℤ)
    (s : ∀ i, (P.X (deg i)).val.obj (op V))
    (h : closureSieve O P U ιP L m A deg s ∈ J V) :
    closureSieve O P U ιP L (m + 1) A deg s ∈ J V := by
  classical
  refine J.transitive h _ fun {W} k hk => ?_
  obtain ⟨S, hfin, hlow, hspan, hd⟩ := hk
  refine J.superset_covering ?_ (spanSieveFinset_mem O (U (m + 1 + 1))
    (cofanP O P U ιP (m + 1 + 1)) (hc (m + 1 + 1)) (hfin (m + 1)).toFinset
    (fun y => (P.d (m + 1) (m + 1 + 1)).val.app (op W)
      (genSec O (U (m + 1)) (cofanP O P U ιP (m + 1)) W y)))
  intro W' m' hm'
  obtain ⟨S', hS'fin, hS'⟩ := hm'
  set Sm : ∀ n : ℤ, Set (GenIdx (U n) W') := fun n => resGenIdx (U n) m' '' S n with hSmdef
  obtain ⟨hSmfin, hSmlow⟩ := finite_low_image_res U m' L hfin hlow hSmdef
  refine ⟨addAtDeg U Sm (m + 1 + 1) S', finite_addAtDeg U hSmfin hS'fin, fun n hn => ?_,
    fun j hj => ?_, fun n hnm y hy => ?_⟩
  · rw [addAtDeg_of_ne U Sm S' (by omega : m + 1 + 1 ≠ n), hSmlow n hn]
  · rw [restrictₛₗ_op_comp_apply O m' k (s j)]
    exact (inSpan_image_res O P U ιP m' (hspan j hj)).mono O _ _
      (subset_addAtDeg U Sm (m + 1 + 1) S' (deg j))
  · rw [addAtDeg_of_ne U Sm S' (by omega : m + 1 + 1 ≠ n)] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [d_genSec_res O P U ιP m' n y₀]
    by_cases hnm2 : n ≤ m
    · exact (inSpan_image_res O P U ιP m' (hd n hnm2 y₀ hy₀)).mono O _ _
        (subset_addAtDeg U Sm (m + 1 + 1) S' (n + 1))
    · obtain rfl : n = m + 1 := by omega
      exact (hS' y₀ ((hfin (m + 1)).mem_toFinset.2 hy₀)).mono O _ _
        (subset_addAtDeg_self U Sm (m + 1 + 1) S')

/-- **The finite graded set of arrow generators closed under the differential.** Over a
covering sieve of `V` there is a finite graded set of arrow generators, vanishing in degrees
`< L`, spanning the restrictions of the given sections and closed under the differential in
every degree.

This is the sieve-indexed replacement for the ringed-space statement
`Stacks.Cohomology.LeftDualPerfect.exists_closed_span`, whose conclusion holds over a single
open shrunk around a point. -/
theorem exists_sieve_closed_span (hc : ∀ n : ℤ, IsColimit (cofanP O P U ιP n)) (b L : ℤ)
    (hb : ∀ n : ℤ, b < n → IsZero (P.X n)) {V : C} {ι : Type*} (A : Finset ι) (deg : ι → ℤ)
    (hL : ∀ i ∈ A, L ≤ deg i) (s : ∀ i, (P.X (deg i)).val.obj (op V)) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (k : W ⟶ V), T k →
      ∃ S : ∀ n : ℤ, Set (GenIdx (U n) W),
        (∀ n : ℤ, (S n).Finite) ∧ (∀ n : ℤ, n < L → S n = ∅) ∧
        (∀ i ∈ A, InSpan O (U (deg i)) (cofanP O P U ιP (deg i)) W (S (deg i))
          ((P.X (deg i)).val.restrictₛₗ k.op (s i))) ∧
        (∀ n : ℤ, ∀ y ∈ S n,
          InSpan O (U (n + 1)) (cofanP O P U ιP (n + 1)) W (S (n + 1))
            ((P.d n (n + 1)).val.app (op W) (genSec O (U n) (cofanP O P U ιP n) W y))) := by
  have hstage : ∀ m : ℤ, L - 1 ≤ m → closureSieve O P U ιP L m A deg s ∈ J V := fun m hmL =>
    Int.leInduction (closureSieve_bot_mem O P U ιP hc L A deg hL s)
      (fun j hj ih => closureSieve_succ_mem O P U ιP hc L j hj A deg s ih) m hmL
  refine ⟨_, hstage (max b (L - 1)) (le_max_right _ _), fun {W} k hk => ?_⟩
  obtain ⟨S, hfin, hlow, hspan, hd⟩ := hk
  refine ⟨S, hfin, hlow, hspan, fun n y hy => ?_⟩
  by_cases hnm : n ≤ max b (L - 1)
  · exact hd n hnm y hy
  · have h0 : (P.d n (n + 1)).val.app (op W)
        (genSec O (U n) (cofanP O P U ιP n) W y) = 0 :=
      eq_zero_of_isZero O (hb (n + 1) (by omega)) _
    rw [h0]
    exact inSpan_zero O (U (n + 1)) (cofanP O P U ιP (n + 1)) W (S (n + 1))

end Stacks.Sites.ExtensionByZero

end
