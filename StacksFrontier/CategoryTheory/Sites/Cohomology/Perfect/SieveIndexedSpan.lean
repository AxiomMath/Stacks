module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.ExtensionByZeroArrowSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoproductLocalFiniteSumLarge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sieve-indexed span of arrow generators in a sum of extensions by zero

Let `(C, J)` be a small site, `O` a sheaf of rings on it, and let a sheaf of modules be
presented as a direct sum `⊕_{α ∈ I} j_{U_α!} O_{U_α}` of extensions by zero of the structure
sheaves of slices, by a colimiting cofan `c`. Over an object `W` the module `c.pt(W)` has a
distinguished family of sections indexed by the pairs `(α, g)` with `g : W ⟶ U_α`: push the
generator `Stacks.Sites.ExtensionByZero.genAt O (U α) g` into the sum along the `α`-th
injection.

This file introduces the span of a finite set of such indices and proves that every section of
the sum over an object lies, on a covering sieve of that object, in the span of finitely many of
them — and that finitely many sections can be made to share one such finite set.

The index set is the point of the construction. On the site of opens of a space, the
corresponding ringed-space development
(`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ExtensionByZeroSums`) indexes the
span by the summands `α` alone, because an open `Z` has at most one inclusion into `U_α`, and it
*shrinks an open around a point* to make the terms with `y ∉ U_α` vanish. Neither step is
available on a site: there are arbitrarily many arrows `W ⟶ U_α`, and there is no point outside
`U_α` whose neighbourhood kills a term. Both are replaced by refinement along a covering sieve,
and the index becomes the pair.

## Main definitions

* `Stacks.Sites.ExtensionByZero.GenIdx`: the index type `Σ α, (W ⟶ U α)` of arrow generators
  over `W`.
* `Stacks.Sites.ExtensionByZero.resGenIdx`: restriction of a generator index along an arrow.
* `Stacks.Sites.ExtensionByZero.genSec`: the section of the sum attached to a generator index.
* `Stacks.Sites.ExtensionByZero.InSpan`: membership in the `O(W)`-span of the generators of a
  finite set of indices.
* `Stacks.Sites.ExtensionByZero.spanSieve` and
  `Stacks.Sites.ExtensionByZero.spanSieveFinset`: the sieve of arrows along which a given
  section — respectively each of finitely many given sections — falls into the span of finitely
  many generators.

## Main results

* `Stacks.Sites.ExtensionByZero.map_genSec`: restricting the generator at an index gives the
  generator at the restricted index, so the family is stable under refinement.
* `Stacks.Sites.ExtensionByZero.InSpan.res`: the span is stable under restriction, provided the
  target set of indices contains the restrictions of the source ones.
* `Stacks.Sites.ExtensionByZero.spanSieve_mem`: **every section of a sum of extensions by zero
  lies, on a covering sieve, in the span of finitely many arrow generators.**
* `Stacks.Sites.ExtensionByZero.spanSieveFinset_mem`: the same for finitely many sections at
  once, with one finite set of generators serving all of them.

## Implementation notes

`InSpan` is `Submodule.span` membership rather than an explicit finite sum with a coefficient
function. That choice is what makes `InSpan.res` short: restriction along an arrow is only
*semilinear* — `PresheafOfModules.restrictₛₗ` — and `Submodule.image_span_subset_span` holds for
semilinear maps with no surjectivity hypothesis, whereas an explicit-coefficient formulation
would have to regroup the coefficients of indices that the restriction identifies.

Restriction of sections is written with `PresheafOfModules.restrictₛₗ` rather than with
`PresheafOfModules.map`, because the latter lands in a `ModuleCat.restrictScalars` of the module
of sections: the same carrier, but not the same expression, so a rewrite under
`InSpan` would not typecheck. `restrictₛₗ` has the module of sections itself as its codomain.

`spanSieve` is a sieve on the nose, not merely a set of arrows that happens to be covering: the
property "the restriction of `s` lies in the span of finitely many generators" is stable under
further precomposition, by `InSpan.res`. That is the structural simplification over the
ringed-space development, where the corresponding statement carries a shrunken open and has to
be re-shrunk at every step.

Covering-ness is `GrothendieckTopology.transitive` over the sieve supplied by
`Stacks.SheafOfModules.CoproductSheafificationLarge.exists_sieve_sum_inj_of_isColimit`, followed
by a finite intersection — one covering sieve for each summand that occurs in the local finite
sum, from `Stacks.Sites.ExtensionByZero.exists_sieve_eq_sum_smul_genAt`. The finite intersection
is `Stacks.Sites.ExtensionByZero.finset_inf_mem`.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ExtensionByZero

section Sieves

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)

/-- **A finite intersection of covering sieves is covering.** -/
@[sga "4 II 1.1.1" "special case"]
theorem finset_inf_mem {V : C} {ι : Type*} (s : Finset ι) (T : ι → Sieve V)
    (hT : ∀ i ∈ s, T i ∈ J V) : s.inf T ∈ J V := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    exact J.top_mem V
  | insert i s hi ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (hT i (Finset.mem_insert_self i s))
      (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

end Sieves

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u})

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restricting a section along a composite of arrows of the site is restricting twice.**
Stated for `PresheafOfModules.restrictₛₗ`, whose codomain is the module of sections itself. -/
theorem restrictₛₗ_op_comp_apply {M : PresheafOfModules.{u} O.obj} {W'' W' W : C}
    (m : W'' ⟶ W') (k : W' ⟶ W) (x : M.obj (op W)) :
    M.restrictₛₗ (m ≫ k).op x = M.restrictₛₗ m.op (M.restrictₛₗ k.op x) :=
  M.map_comp_apply k.op m.op x

variable {I : Type u} (U : I → C)

/-- **The index type of the arrow generators over `W`** of a sum of extensions by zero
`⊕_α j_{U_α!} O_{U_α}`: a summand together with an arrow to the object it extends from. -/
abbrev GenIdx (W : C) : Type u := Σ α : I, (W ⟶ U α)

/-- **Restriction of a generator index along an arrow**: compose. -/
def resGenIdx {W' W : C} (k : W' ⟶ W) (y : GenIdx U W) : GenIdx U W' := ⟨y.1, k ≫ y.2⟩

/-- Restricting a generator index along an arrow keeps its summand. -/
@[simp]
theorem resGenIdx_fst {W' W : C} (k : W' ⟶ W) (y : GenIdx U W) :
    (resGenIdx U k y).1 = y.1 := rfl

/-- The arrow of the restriction of a generator index along `k` is `k` composed with its
arrow. -/
@[simp]
theorem resGenIdx_snd {W' W : C} (k : W' ⟶ W) (y : GenIdx U W) :
    (resGenIdx U k y).2 = k ≫ y.2 := rfl

variable (c : Cofan fun α : I => (SheafOfModules.extensionByZero.{u, u, u, u} O (U α)).obj
  (SheafOfModules.unit (O.over (U α))))

/-- **The section of the sum attached to a generator index**: the image under the `α`-th
injection of the generator at the arrow. -/
def genSec (W : C) (y : GenIdx U W) : c.pt.val.obj (op W) :=
  (c.inj y.1).val.app (op W) (genAt O (U y.1) y.2)

/-- **The arrow generators of a sum of extensions by zero are stable under refinement.** -/
theorem restrictₛₗ_genSec {W' W : C} (k : W' ⟶ W) (y : GenIdx U W) :
    c.pt.val.restrictₛₗ k.op (genSec O U c W y) = genSec O U c W' (resGenIdx U k y) :=
  (PresheafOfModules.naturality_apply (c.inj y.1).val k.op (genAt O (U y.1) y.2)).symm.trans
    (congrArg ((c.inj y.1).val.app (op W')) (map_genAt O (U y.1) k y.2))

/-- **A section of `⊕_α j_{U_α!} O_{U_α}` over `W` lies in the span of the generators indexed
by `S`.** -/
def InSpan (W : C) (S : Set (GenIdx U W)) (x : c.pt.val.obj (op W)) : Prop :=
  x ∈ Submodule.span ((O.obj.obj (op W) : RingCat.{u}) : Type u) (genSec O U c W '' S)

/-- Zero lies in every span. -/
theorem inSpan_zero (W : C) (S : Set (GenIdx U W)) : InSpan O U c W S 0 :=
  Submodule.zero_mem _

/-- A generator of `S` lies in the span of `S`. -/
theorem inSpan_genSec (W : C) (S : Set (GenIdx U W)) {y : GenIdx U W} (hy : y ∈ S) :
    InSpan O U c W S (genSec O U c W y) :=
  Submodule.subset_span ⟨y, hy, rfl⟩

/-- The span grows with the set of indices. -/
theorem InSpan.mono {W : C} {S S' : Set (GenIdx U W)} (hSS : S ⊆ S')
    {x : c.pt.val.obj (op W)} (hx : InSpan O U c W S x) : InSpan O U c W S' x :=
  Submodule.span_mono (Set.image_mono hSS) hx

/-- Sums stay in the span. -/
theorem InSpan.add {W : C} {S : Set (GenIdx U W)} {x y : c.pt.val.obj (op W)}
    (hx : InSpan O U c W S x) (hy : InSpan O U c W S y) : InSpan O U c W S (x + y) :=
  Submodule.add_mem _ hx hy

/-- Multiples stay in the span. -/
theorem InSpan.smul {W : C} {S : Set (GenIdx U W)} {x : c.pt.val.obj (op W)}
    (r : ((O.obj.obj (op W) : RingCat.{u}) : Type u)) (hx : InSpan O U c W S x) :
    InSpan O U c W S (r • x) :=
  Submodule.smul_mem _ r hx

/-- A finite sum of multiples of generators of `S` lies in the span of `S`. -/
theorem inSpan_sum_smul {W : C} {S : Set (GenIdx U W)} {ι : Type*} (A : Finset ι)
    (f : ι → GenIdx U W) (hf : ∀ i ∈ A, f i ∈ S)
    (r : ι → ((O.obj.obj (op W) : RingCat.{u}) : Type u)) :
    InSpan O U c W S (∑ i ∈ A, r i • genSec O U c W (f i)) :=
  Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f i, hf i hi, rfl⟩)

/-- **The span is stable under restriction.** If every restriction of an index of `S` lies in
`S'`, a section in the span of `S` restricts into the span of `S'`. -/
theorem InSpan.res {W' W : C} (k : W' ⟶ W) {S : Set (GenIdx U W)} {S' : Set (GenIdx U W')}
    (hSS : ∀ y ∈ S, resGenIdx U k y ∈ S') {x : c.pt.val.obj (op W)}
    (hx : InSpan O U c W S x) : InSpan O U c W' S' (c.pt.val.restrictₛₗ k.op x) := by
  have himg : (c.pt.val.restrictₛₗ k.op) '' (genSec O U c W '' S) ⊆ genSec O U c W' '' S' := by
    rintro - ⟨-, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨resGenIdx U k y, hSS y hy, (restrictₛₗ_genSec O U c k y).symm⟩
  refine Submodule.span_mono himg ?_
  exact Submodule.image_span_subset_span (c.pt.val.restrictₛₗ k.op) _ ⟨x, hx, rfl⟩

/-- **The sieve of arrows along which a section falls into the span of finitely many arrow
generators.** It is a sieve because the span is stable under restriction. -/
def spanSieve {V : C} (s : c.pt.val.obj (op V)) : Sieve V where
  arrows W k := ∃ S : Set (GenIdx U W), S.Finite ∧
    InSpan O U c W S (c.pt.val.restrictₛₗ k.op s)
  downward_closed := by
    rintro W W'' k ⟨S, hSfin, hS⟩ m
    refine ⟨resGenIdx U m '' S, hSfin.image _, ?_⟩
    rw [restrictₛₗ_op_comp_apply O m k s]
    exact hS.res O U c m fun y hy => Set.mem_image_of_mem _ hy

/-- **The sieve of arrows along which each of finitely many sections falls into the span of one
finite set of arrow generators.** -/
def spanSieveFinset {V : C} {ι : Type*} (A : Finset ι) (s : ι → c.pt.val.obj (op V)) :
    Sieve V where
  arrows W k := ∃ S : Set (GenIdx U W), S.Finite ∧
    ∀ i ∈ A, InSpan O U c W S (c.pt.val.restrictₛₗ k.op (s i))
  downward_closed := by
    rintro W W'' k ⟨S, hSfin, hS⟩ m
    refine ⟨resGenIdx U m '' S, hSfin.image _, fun i hi => ?_⟩
    rw [restrictₛₗ_op_comp_apply O m k (s i)]
    exact (hS i hi).res O U c m fun y hy => Set.mem_image_of_mem _ hy

variable [HasCoproduct fun α : I => (SheafOfModules.extensionByZero.{u, u, u, u} O (U α)).obj
  (SheafOfModules.unit (O.over (U α)))]

/-- **Every section of a sum of extensions by zero lies, on a covering sieve, in the span of
finitely many arrow generators.**

This is the sieve-indexed replacement for the ringed-space statement
`Stacks.Cohomology.LeftDualPerfect.exists_nhd_inSpan`, where the span is indexed by the
summands alone and the open is shrunk around a point. -/
theorem spanSieve_mem (hc : IsColimit c) {V : C} (s : c.pt.val.obj (op V)) :
    spanSieve O U c s ∈ J V := by
  classical
  obtain ⟨T₀, hT₀, hsum⟩ :=
    Stacks.SheafOfModules.CoproductSheafificationLarge.exists_sieve_sum_inj_of_isColimit O
      (fun α : I => (SheafOfModules.extensionByZero.{u, u, u, u} O (U α)).obj
        (SheafOfModules.unit (O.over (U α)))) hc s
  refine J.transitive hT₀ _ fun {W} k hk => ?_
  obtain ⟨S₀, y, hy⟩ := hsum k hk
  have hsummand : ∀ α : I, ∃ T : Sieve W, T ∈ J W ∧ ∀ ⦃W' : C⦄ (m : W' ⟶ W), T m →
      ∃ (A : Finset (W' ⟶ U α)) (cf : (W' ⟶ U α) → O.obj.obj (op W')),
        ((SheafOfModules.extensionByZero.{u, u, u, u} O (U α)).obj
            (SheafOfModules.unit (O.over (U α)))).val.restrictₛₗ m.op (y α) =
          ∑ g ∈ A, cf g • genAt O (U α) g :=
    fun α => exists_sieve_eq_sum_smul_genAt O (U α) (y α)
  choose T hT hTspec using hsummand
  refine J.superset_covering ?_ (finset_inf_mem J S₀ T fun α _ => hT α)
  intro W' m hm
  have hle : ∀ α ∈ S₀, S₀.inf T ≤ T α := fun α hα => Finset.inf_le hα
  have hmem : ∀ α ∈ S₀, T α m := fun α hα => hle α hα m hm
  have key : ∀ α : I, ∃ (A : Finset (W' ⟶ U α)) (cf : (W' ⟶ U α) → O.obj.obj (op W')),
      α ∈ S₀ → ((SheafOfModules.extensionByZero.{u, u, u, u} O (U α)).obj
          (SheafOfModules.unit (O.over (U α)))).val.restrictₛₗ m.op (y α) =
        ∑ g ∈ A, cf g • genAt O (U α) g := by
    intro α
    by_cases hα : α ∈ S₀
    · obtain ⟨A, cf, h⟩ := hTspec α m (hmem α hα)
      exact ⟨A, cf, fun _ => h⟩
    · exact ⟨∅, fun _ => 0, fun h => absurd h hα⟩
  choose A cf hAcf using key
  refine ⟨↑(S₀.sigma A), (S₀.sigma A).finite_toSet, ?_⟩
  have hsk : c.pt.val.restrictₛₗ k.op s =
      ∑ α ∈ S₀, (c.inj α).val.app (op W) (y α) := hy
  have e : c.pt.val.restrictₛₗ (m ≫ k).op s =
      ∑ α ∈ S₀, ∑ g ∈ A α, cf α g • genSec O U c W' ⟨α, g⟩ := by
    rw [restrictₛₗ_op_comp_apply O m k s, hsk, map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    refine ((PresheafOfModules.naturality_apply (c.inj α).val m.op (y α)).symm.trans
      (congrArg (fun t => (c.inj α).val.app (op W') t) (hAcf α hα))).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun g hg =>
    Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨α, g⟩, Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨hα, hg⟩), rfl⟩)

/-- **Finitely many sections of a sum of extensions by zero lie, on a covering sieve, in the
span of one finite set of arrow generators.**

This is the sieve-indexed replacement for the ringed-space statement
`Stacks.Cohomology.LeftDualPerfect.exists_nhd_inSpan_finset`. -/
theorem spanSieveFinset_mem (hc : IsColimit c) {V : C} {ι : Type*} (A : Finset ι)
    (s : ι → c.pt.val.obj (op V)) : spanSieveFinset O U c A s ∈ J V := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    exact J.superset_covering (fun W k _ => ⟨∅, Set.finite_empty, by simp⟩) (J.top_mem V)
  | insert i A hi ih =>
    refine J.transitive ih _ fun {W} k hk => ?_
    obtain ⟨S, hSfin, hS⟩ := hk
    refine J.superset_covering ?_ (spanSieve_mem O U c hc (c.pt.val.restrictₛₗ k.op (s i)))
    intro W' m hm
    obtain ⟨S', hS'fin, hS'⟩ := hm
    refine ⟨resGenIdx U m '' S ∪ S', (hSfin.image _).union hS'fin, fun j hj => ?_⟩
    rw [restrictₛₗ_op_comp_apply O m k (s j)]
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hS'.mono O U c Set.subset_union_right
    · exact ((hS j hj).res O U c m fun z hz => Set.mem_image_of_mem _ hz).mono O U c
        Set.subset_union_left

end Stacks.Sites.ExtensionByZero

end
