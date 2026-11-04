module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Local generation of a sum of extensions by zero by its marked generators

Let `(C, O)` be a ringed site, let `U : I → C` be a family of objects and let

`c : ⊕_α j_{U_α!} O_{U_α}`

be a colimiting cofan of the extensions by zero of the structure sheaves of their slices. A
**marked generator over an object `W`** is an index `α` together with an arrow `a : W ⟶ U α`;
the section it names is the tautological generator of the summand `α`, restricted along `a`.
This file proves that every section of the vertex of the cofan is, along the arrows of a
covering sieve, an `O`-linear combination of finitely many marked generators.

Over a topological space the same statement is
`Stacks.Cohomology.LeftDualPerfect.exists_nhd_inSpan`; there an open `Z` either is contained in
`U_α` or is not, so a generator over `Z` is named by its index alone and the argument can run
through the stalks of `j_{U_α!}O_{U_α}` outside `U_α`. On a site there can be many arrows
`W ⟶ U α`, each naming a different section, so the *arrow is part of the index*: that is what
`Marked` records, and it is what makes the restriction of a marked generator along `g` be
again a marked generator — of the composed arrow — with no side condition, so that the
`Finset`s of this file need no "defined over `Z`" hypothesis travelling with them.

## Main definitions

* `Stacks.Sites.ExtensionByZeroSpan.extUnit`: the extension by zero `j_{U!}O_U` of the
  structure sheaf of the slice over `U`.
* `Stacks.Sites.ExtensionByZeroSpan.Marked`: a marked generator over `W` — an index of the
  family together with an arrow from `W` to the corresponding object.
* `Stacks.Sites.ExtensionByZeroSpan.markedRes`: restriction of a marked generator along an
  arrow, by composition.
* `Stacks.Sites.ExtensionByZeroSpan.elemSec`: the section of the vertex named by a marked
  generator.
* `Stacks.Sites.ExtensionByZeroSpan.genSections`: the family of all marked generator sections,
  in the form `Stacks.SheafOfModules.spanSubmodule` takes.
* `Stacks.Sites.ExtensionByZeroSpan.InSpan`: a section is an `O(W)`-combination of the marked
  generators in a given finite set.

## Main results

* `Stacks.Sites.ExtensionByZeroSpan.epi_localSpan_ι`: the inclusion of the subsheaf of sections
  locally in the span of the marked generators is an epimorphism.
* `Stacks.Sites.ExtensionByZeroSpan.spanSieve_mem`: **every section of the vertex restricts into
  the span of the marked generators along a covering sieve.**
* `Stacks.Sites.ExtensionByZeroSpan.exists_sieve_inSpan_finset`: for *finitely many* sections at
  once there is a single covering sieve along whose arrows all of them lie in the span of one
  finite set of marked generators.

## Implementation notes

The local-span machinery is `Stacks.SheafOfModules.spanSubmodule`, `spanSieve`, `localSpan` and
`mem_localSpan_of_epi_ι` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators`, which is family-indexed
and is applied here to the family of marked generators. Membership in the objectwise span gives
`InSpan` for some finite set of marked generators, by `Submodule.span_induction`
(`exists_inSpan_of_mem_spanSubmodule`).

`InSpan` is stated as the existence of a coefficient *function* on all marked generators rather
than on the members of the given finite set, which is what makes `InSpan.mono` hold with no
hypothesis beyond the inclusion of the finite sets.

Everything is at a single universe `u` for the site, its rings and its modules, as forced by
`StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators`.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW) — the extensions by
  zero of the structure sheaves generate.
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.ExtensionByZeroSpan

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J RingCat.{u})

/-- The extension by zero `j_{U!}O_U` of the structure sheaf of the slice site over `U`. -/
abbrev extUnit (U : C) : SheafOfModules.{u} O :=
  (SheafOfModules.extensionByZero.{u, u, u, u} O U).obj (SheafOfModules.unit (O.over U))

variable {I : Type u} (U : I → C) (c : Cofan fun α => extUnit O (U α))

/-- **A marked generator over `W`**: an index `α` of the family together with an arrow
`W ⟶ U α` along which the tautological generator of `j_{U_α!}O_{U_α}` is restricted. -/
abbrev Marked (U : I → C) (W : C) : Type u := Σ α : I, (W ⟶ U α)

/-- Restriction of a marked generator along an arrow: compose the arrows. -/
def markedRes {W' W : C} (f : W' ⟶ W) (m : Marked U W) : Marked U W' := ⟨m.1, f ≫ m.2⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Restricting a marked generator along `f` and then along `g` is restricting it along `g ≫ f`. -/
theorem markedRes_markedRes {W'' W' W : C} (g : W'' ⟶ W') (f : W' ⟶ W) (m : Marked U W) :
    markedRes U g (markedRes U f m) = markedRes U (g ≫ f) m := by
  simp [markedRes]

/-- **The section named by a marked generator**: the tautological generator of the summand `α`,
restricted along the arrow and pushed into the vertex of the cofan. -/
def elemSec {W : C} (m : Marked U W) : c.pt.val.obj (op W) :=
  (c.inj m.1).val.app (op W)
    ((extUnit O (U m.1)).val.map m.2.op (SheafOfModules.extensionByZeroGen O (U m.1)))

/-- Restricting the section named by a marked generator gives the section named by the
restricted marked generator. -/
theorem map_elemSec {W' W : C} (f : W' ⟶ W) (m : Marked U W) :
    c.pt.val.map f.op (elemSec O U c m) = elemSec O U c (markedRes U f m) :=
  (PresheafOfModules.naturality_apply (c.inj m.1).val f.op _).symm.trans
    (congrArg ((c.inj m.1).val.app (op W'))
      ((extUnit O (U m.1)).val.map_comp_apply m.2.op f.op
        (SheafOfModules.extensionByZeroGen O (U m.1))).symm)

/-- The section named by a marked generator with the identity arrow is the tautological
generator itself. -/
theorem elemSec_id (α : I) :
    elemSec O U c ⟨α, 𝟙 (U α)⟩ =
      (c.inj α).val.app (op (U α)) (SheafOfModules.extensionByZeroGen O (U α)) := by
  rw [elemSec]
  refine congrArg ((c.inj α).val.app (op (U α))) ?_
  rw [show (𝟙 (U α)).op = 𝟙 (op (U α)) from rfl, PresheafOfModules.map_id]
  rfl

/-- The family of all sections named by marked generators, in the form that
`Stacks.SheafOfModules.spanSubmodule` takes. -/
def genSections (X : Cᵒᵖ) : Set (c.pt.val.obj X) :=
  {x | ∃ m : Marked U X.unop, elemSec O U c m = x}

/-- The section named by a marked generator belongs to `genSections`. -/
theorem elemSec_mem_genSections {W : C} (m : Marked U W) :
    elemSec O U c m ∈ genSections O U c (op W) :=
  ⟨m, rfl⟩

/-- **A section over `W` is an `O(W)`-combination of the marked generators in a finite set.** -/
def InSpan {W : C} (S : Finset (Marked U W)) (x : c.pt.val.obj (op W)) : Prop :=
  ∃ coef : Marked U W → O.obj.obj (op W), x = ∑ m ∈ S, coef m • elemSec O U c m

/-- A section in the span of a finite set of marked generators is in the span of any larger finite
set. -/
theorem InSpan.mono {W : C} {S S' : Finset (Marked U W)} {x : c.pt.val.obj (op W)}
    (hx : InSpan O U c S x) (hSS : S ⊆ S') : InSpan O U c S' x := by
  classical
  obtain ⟨coef, hcoef⟩ := hx
  refine ⟨fun m => if m ∈ S then coef m else 0, ?_⟩
  rw [hcoef, ← Finset.sum_subset hSS fun m _ hm => by simp [hm]]
  exact Finset.sum_congr rfl fun m hm => by simp [hm]

/-- The zero section is in the span of any finite set of marked generators. -/
theorem inSpan_zero {W : C} (S : Finset (Marked U W)) : InSpan O U c S 0 :=
  ⟨0, by simp⟩

/-- The span of a finite set of marked generators is closed under addition. -/
theorem InSpan.add {W : C} {S : Finset (Marked U W)} {x y : c.pt.val.obj (op W)}
    (hx : InSpan O U c S x) (hy : InSpan O U c S y) : InSpan O U c S (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [ha, hb, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => (add_smul (a m) (b m) (elemSec O U c m)).symm

/-- The span of a finite set of marked generators is closed under multiplication by sections of
`O`. -/
theorem InSpan.smul {W : C} {S : Finset (Marked U W)} (r : O.obj.obj (op W))
    {x : c.pt.val.obj (op W)} (hx : InSpan O U c S x) : InSpan O U c S (r • x) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun m => r * a m, ?_⟩
  rw [ha, Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => (mul_smul r (a m) _).symm

/-- The section named by a member of a finite set of marked generators is in its span. -/
theorem inSpan_elemSec {W : C} {S : Finset (Marked U W)} {m : Marked U W} (hm : m ∈ S) :
    InSpan O U c S (elemSec O U c m) := by
  classical
  refine ⟨fun m' => if m' = m then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hm' => by simp [hm']]
  simp

/-- Restriction of a section in the span of a finite set of marked generators lies in the span
of any finite set containing the restrictions of its members. -/
theorem InSpan.res {W' W : C} (f : W' ⟶ W) {S : Finset (Marked U W)}
    {S' : Finset (Marked U W')} (hSS : ∀ m ∈ S, markedRes U f m ∈ S')
    {x : c.pt.val.obj (op W)} (hx : InSpan O U c S x) :
    InSpan O U c S' (c.pt.val.map f.op x) := by
  obtain ⟨coef, rfl⟩ := hx
  rw [map_sum]
  refine Finset.sum_induction _ (InSpan O U c S') (fun _ _ => InSpan.add O U c)
    (inSpan_zero O U c S') fun m hm => ?_
  rw [PresheafOfModules.map_smul, map_elemSec]
  exact (inSpan_elemSec O U c (hSS m hm)).smul O U c _

/-- A section in the objectwise span of the marked generators lies in the span of a *finite*
set of them. -/
theorem exists_inSpan_of_mem_spanSubmodule {W : C} {x : c.pt.val.obj (op W)}
    (hx : x ∈ (Stacks.SheafOfModules.spanSubmodule c.pt (genSections O U c)).obj (op W)) :
    ∃ S : Finset (Marked U W), InSpan O U c S x := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨Z, g, z, ⟨m, rfl⟩, rfl⟩ := hy
    exact ⟨{markedRes U g.unop m}, (map_elemSec O U c g.unop m) ▸
      inSpan_elemSec O U c (Finset.mem_singleton_self _)⟩
  | zero => exact ⟨∅, inSpan_zero O U c ∅⟩
  | add y z _ _ hy hz =>
    obtain ⟨S₁, h₁⟩ := hy
    obtain ⟨S₂, h₂⟩ := hz
    exact ⟨S₁ ∪ S₂, (h₁.mono O U c Finset.subset_union_left).add O U c
      (h₂.mono O U c Finset.subset_union_right)⟩
  | smul r y _ hy =>
    obtain ⟨S, h⟩ := hy
    exact ⟨S, h.smul O U c r⟩

/-- **A morphism out of the vertex that kills the local span of the marked generators is
zero**, and so the inclusion of that local span is an epimorphism: the morphism kills each
tautological generator, and a morphism out of `j_{U!}O_U` is determined by the image of the
tautological generator. -/
theorem epi_localSpan_ι (hc : IsColimit c) :
    Epi (Stacks.SheafOfModules.localSpan c.pt (genSections O U c)).ι := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z g hg
  refine Cofan.IsColimit.hom_ext hc _ 0 fun α => ?_
  refine (SheafOfModules.bijective_val_app_gen O Z (U α)).1 ?_
  have h0 : g.val.app (op (U α)) (elemSec O U c ⟨α, 𝟙 (U α)⟩) = 0 :=
    Stacks.SheafOfModules.apply_eq_zero_of_mem_localSpan g hg
      (Stacks.SheafOfModules.mem_localSpan (elemSec_mem_genSections O U c ⟨α, 𝟙 (U α)⟩))
  rw [elemSec_id] at h0
  exact h0

/-- **Every section of `⊕_α j_{U_α!}O_{U_α}` restricts into the span of the marked generators
along the arrows of a covering sieve.** -/
theorem spanSieve_mem (hc : IsColimit c) {X : Cᵒᵖ} (x : c.pt.val.obj X) :
    Stacks.SheafOfModules.spanSieve c.pt (genSections O U c) x ∈ J X.unop :=
  have := epi_localSpan_ι O U c hc
  Stacks.SheafOfModules.spanSieve_mem_of_epi_ι x

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A finite intersection of covering sieves is covering. -/
theorem finset_inf_mem {V : C} {ι : Type*} (A : Finset ι) (R : ι → Sieve V)
    (hR : ∀ i ∈ A, R i ∈ J V) : A.inf R ∈ J V := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert i A hi ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (hR i (Finset.mem_insert_self i A))
      (ih fun j hj => hR j (Finset.mem_insert_of_mem hj))

/-- **Finitely many sections of `⊕_α j_{U_α!}O_{U_α}` lie, along the arrows of one covering
sieve, in the span of one finite set of marked generators.** -/
theorem exists_sieve_inSpan_finset (hc : IsColimit c) {W : C} {ι : Type*} (A : Finset ι)
    (s : ι → c.pt.val.obj (op W)) :
    ∃ R : Sieve W, R ∈ J W ∧ ∀ ⦃W' : C⦄ (f : W' ⟶ W), R.arrows f →
      ∃ S : Finset (Marked U W'), ∀ i ∈ A, InSpan O U c S (c.pt.val.map f.op (s i)) := by
  classical
  refine ⟨A.inf fun i => Stacks.SheafOfModules.spanSieve c.pt (genSections O U c) (s i),
    finset_inf_mem A _ fun i _ => spanSieve_mem O U c hc (s i), fun W' f hf => ?_⟩
  have key : ∀ i ∈ A, ∃ S : Finset (Marked U W'),
      InSpan O U c S (c.pt.val.map f.op (s i)) := fun i hi => by
    have hle : (A.inf fun j => Stacks.SheafOfModules.spanSieve c.pt (genSections O U c) (s j)) ≤
        Stacks.SheafOfModules.spanSieve c.pt (genSections O U c) (s i) := Finset.inf_le hi
    exact exists_inSpan_of_mem_spanSubmodule O U c (hle f hf)
  choose! Sfun hSfun using key
  exact ⟨A.biUnion Sfun, fun i hi =>
    (hSfun i hi).mono O U c (Finset.subset_biUnion_of_mem Sfun hi)⟩

end Stacks.Sites.ExtensionByZeroSpan

end
