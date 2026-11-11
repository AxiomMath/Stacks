module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSpanSubcomplex

/-!
# Enlarging a set of generators so that boundaries in the span have primitives in it

Let `K` be a cochain complex of sheaves of modules on a site and `c : ι → C` a family of
objects. This file bounds the sizes of the spans `Stacks.SheafOfModules.DenseSpan.span`, and
enlarges a set of generators, by countably many steps, to one which is stable under the
differential and contains a primitive of every section of its span, over an object of the family,
which is a boundary in `K`. If the family, its arrows and the rings of sections over it are
bounded by an infinite cardinal `ν` and so are the starting generators, so is the enlargement.

This is the half of the closure argument which makes the inclusion of the locally spanned
subcomplex injective on cohomology; see `Stacks.SheafOfModules.DenseSpan.quasiIso_incl`.

## Main definitions

* `Stacks.SheafOfModules.DenseSpan.dClosure`: the generators together with their differentials
  and the zero sections.
* `Stacks.SheafOfModules.DenseSpan.witnesses`: a chosen primitive of every section of the span
  over an object of the family which is a boundary.
* `Stacks.SheafOfModules.DenseSpan.enlargement`: the union of the countably many enlargement
  steps.

## Main results

* `Stacks.SheafOfModules.DenseSpan.mk_span_obj_le`: the span over an object of the family is
  bounded by `ν`.
* `Stacks.SheafOfModules.DenseSpan.isDClosed_enlargement`,
  `Stacks.SheafOfModules.DenseSpan.subset_enlargement`,
  `Stacks.SheafOfModules.DenseSpan.exists_mem_closure_d_eq_of_enlargement` and
  `Stacks.SheafOfModules.DenseSpan.mk_enlargement_le`: the enlargement contains the starting
  generators, is stable under the differential, has the primitives, and is bounded by `ν`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe t u'

namespace Stacks.SheafOfModules.DenseSpan

/-- The type of all candidate generators: sections of the terms of `K` over the objects of the
family, in all degrees. -/
abbrev GenType {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
    {ι : Type*} (c : ι → C) (K : CochainComplex (_root_.SheafOfModules.{t} R) ℤ) :=
  Σ n : ℤ, Σ i : ι, (K.X n).val.obj (op (c i))

/-- A set contained in the range of a map from a type bounded by `ν` is bounded by `ν`. -/
private theorem mk_le_of_subset_range {α β : Type t} {s : Set β} {F : α → β} {ν : Cardinal.{t}}
    (h : s ⊆ Set.range F) (hα : #α ≤ ν) : #s ≤ ν :=
  (Cardinal.mk_le_mk_of_subset h).trans (Cardinal.mk_range_le.trans hα)

/-- A product of types bounded by an infinite cardinal is bounded by it. -/
private theorem mk_prod_le_of_le {α β : Type t} {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hα : #α ≤ ν)
    (hβ : #β ≤ ν) : #(α × β) ≤ ν := by
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (mul_le_mul' hα hβ).trans (Cardinal.mul_eq_self hν).le

/-- The lifted integers are bounded by any infinite cardinal. -/
private theorem mk_uLift_int_le {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) : #(ULift.{t} ℤ) ≤ ν := by
  rwa [Cardinal.mk_uLift, Cardinal.mk_int, Cardinal.lift_aleph0]

/-- **A span is bounded by the number of finite lists of scalars and generators.** -/
theorem mk_span_le {A M : Type t} [Semiring A] [AddCommMonoid M] [Module A M] (s : Set M)
    {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hA : #A ≤ ν) (hs : #s ≤ ν) :
    #(Submodule.span A s) ≤ ν := by
  let F : List (A × s) → M := fun l => (l.map (fun p => p.1 • (p.2 : M))).sum
  have hsub : (Submodule.span A s : Set M) ⊆ Set.range F := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨[(1, ⟨x, hx⟩)], by simp [F]⟩
    | zero => exact ⟨[], by simp [F]⟩
    | add x y _ _ hx hy =>
      obtain ⟨l₁, rfl⟩ := hx
      obtain ⟨l₂, rfl⟩ := hy
      exact ⟨l₁ ++ l₂, by simp [F]⟩
    | smul a x _ hx =>
      obtain ⟨l, rfl⟩ := hx
      refine ⟨l.map (fun p => (a * p.1, p.2)), ?_⟩
      simp only [F, List.map_map, List.smul_sum]
      simp [Function.comp_def, mul_smul]
  exact mk_le_of_subset_range hsub
    ((Cardinal.mk_list_le_max _).trans (max_le hν (mk_prod_le_of_le hν hA hs)))

/-- A dependent sum of types bounded by an infinite cardinal, over an index type bounded by it,
is bounded by it. -/
theorem mk_sigma_le_of_le {α : Type t} {β : α → Type t} {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν)
    (hα : #α ≤ ν) (hβ : ∀ a, #(β a) ≤ ν) : #(Σ a, β a) ≤ ν := by
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_mk_mul_iSup _).trans ?_
  by_cases hne : Nonempty α
  · exact (mul_le_mul' hα (ciSup_le' hβ)).trans (Cardinal.mul_eq_self hν).le
  · have : IsEmpty α := not_nonempty_iff.mp hne
    simp

/-- A dependent sum over the integers of types bounded by an infinite cardinal is bounded by
it. -/
theorem mk_sigma_int_le {β : ℤ → Type t} {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν)
    (hβ : ∀ n, #(β n) ≤ ν) : #(Σ n, β n) ≤ ν := by
  rw [← Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := β) Equiv.ulift)]
  exact mk_sigma_le_of_le hν (mk_uLift_int_le hν) (fun n => hβ n.down)

variable {C : Type u'} [Category.{t} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {ι : Type t} {c : ι → C} {K : CochainComplex (_root_.SheafOfModules.{t} R) ℤ}

/-- **The span over an object of the family is bounded by `ν`** when the generators, the
family, its arrows and its rings of sections are. -/
theorem mk_span_obj_le (A : Gens c K) {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hA : #A ≤ ν)
    (hι : #ι ≤ ν) (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν)
    (hR : ∀ i : ι, #(R.obj.obj (op (c i))) ≤ ν) (n : ℤ) (i : ι) :
    #((span A n).obj (op (c i))) ≤ ν := by
  rw [span_obj]
  refine mk_span_le _ hν (hR i) ?_
  let D := Σ (i' : ι), Σ (_ : {s : (K.X n).val.obj (op (c i')) // ⟨n, i', s⟩ ∈ A}),
    (c i ⟶ c i')
  let F : D → (K.X n).val.obj (op (c i)) := fun d => (K.X n).val.map d.2.2.op d.2.1.1
  have hsub : genSet A n (op (c i)) ⊆ Set.range F := by
    intro x hx
    obtain ⟨i', s, f, hs, rfl⟩ := mem_genSet_iff.1 hx
    exact ⟨⟨i', ⟨s, hs⟩, f⟩, rfl⟩
  refine mk_le_of_subset_range hsub ?_
  refine mk_sigma_le_of_le hν hι (fun i' => mk_sigma_le_of_le hν ?_ (fun _ => hHom i i'))
  refine (Cardinal.mk_le_of_injective (f := fun s : {s : (K.X n).val.obj (op (c i')) //
    ⟨n, i', s⟩ ∈ A} => (⟨⟨n, i', s.1⟩, s.2⟩ : A)) ?_).trans hA
  intro s s' h
  apply Subtype.ext
  simpa using congrArg (fun g : A => g.1) h

/-- The generators together with all their differentials and all the zero sections. -/
def dClosure (A : Gens c K) : Gens c K :=
  A ∪ {g | ∃ (m : ℤ) (s : (K.X m).val.obj (op (c g.2.1))), ⟨m, g.2.1, s⟩ ∈ A ∧
      g.2.2 = (K.d m g.1).val.app _ s} ∪ {g | g.2.2 = 0}

/-- A section over an object of the family lies in the differential closure iff it is a
generator, the differential of a generator over the same object, or zero. -/
theorem mk_mem_dClosure_iff {A : Gens c K} {n : ℤ} {i : ι} {x : (K.X n).val.obj (op (c i))} :
    ⟨n, i, x⟩ ∈ dClosure A ↔ (⟨n, i, x⟩ ∈ A ∨ ∃ (m : ℤ) (s : (K.X m).val.obj (op (c i))),
      ⟨m, i, s⟩ ∈ A ∧ x = (K.d m n).val.app (op (c i)) s) ∨ x = 0 :=
  Iff.rfl

/-- A set of generators is contained in its differential closure. -/
theorem subset_dClosure (A : Gens c K) : A ⊆ dClosure A :=
  fun _ h => Or.inl (Or.inl h)

/-- The generators together with their differentials and the zero sections are stable under
the differential. -/
theorem isDClosed_dClosure (A : Gens c K) : IsDClosed (dClosure A) := by
  intro m n i s hs
  rw [mk_mem_dClosure_iff] at hs ⊢
  rcases hs with (hA | ⟨m', s', -, rfl⟩) | rfl
  · exact Or.inl (Or.inr ⟨m, s, hA, rfl⟩)
  · refine Or.inr ?_
    rw [← _root_.SheafOfModules.comp_val_app_apply, K.d_comp_d,
      _root_.SheafOfModules.zero_val_app_apply]
  · exact Or.inr (map_zero _)

/-- The differential closure of a set of generators bounded by an infinite cardinal `ν` is bounded
by `ν` when the family is. -/
theorem mk_dClosure_le (A : Gens c K) {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hA : #A ≤ ν)
    (hι : #ι ≤ ν) : #(dClosure A) ≤ ν := by
  let D : A × ULift.{t} ℤ → GenType c K := fun p =>
    ⟨p.2.down, p.1.1.2.1, (K.d p.1.1.1 p.2.down).val.app _ p.1.1.2.2⟩
  let Z : ULift.{t} ℤ × ι → GenType c K := fun p => ⟨p.1.down, p.2, 0⟩
  have hsub : dClosure A ⊆ A ∪ Set.range D ∪ Set.range Z := by
    rintro ⟨n, i, x⟩ hx
    obtain (hA | ⟨m, s, hs, rfl⟩) | rfl := mk_mem_dClosure_iff.1 hx
    · exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr ⟨(⟨⟨m, i, s⟩, hs⟩, ⟨n⟩), rfl⟩)
    · exact Or.inr ⟨(⟨n⟩, i), rfl⟩
  refine (Cardinal.mk_le_mk_of_subset hsub).trans ((Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hν ((Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le hν hA ?_)) ?_))
  · exact Cardinal.mk_range_le.trans (mk_prod_le_of_le hν hA (mk_uLift_int_le hν))
  · exact Cardinal.mk_range_le.trans (mk_prod_le_of_le hν (mk_uLift_int_le hν) hι)

/-- A section of the span, over an object of the family, which is a boundary in `K`. -/
structure BoundaryIndex (A : Gens c K) where
  /-- The degree of the primitive. -/
  deg : ℤ
  /-- The index of the object of the family. -/
  idx : ι
  /-- The section of the span, in degree `deg + 1`. -/
  sec : (span A (deg + 1)).obj (op (c idx))
  /-- The section is a boundary. -/
  exists_d_eq : ∃ t : (K.X deg).val.obj (op (c idx)),
    (K.d deg (deg + 1)).val.app (op (c idx)) t = sec.1

/-- **A chosen primitive of every section of the span, over an object of the family, which is a
boundary in `K`.** -/
def witnesses (A : Gens c K) : Gens c K :=
  Set.range (fun x : BoundaryIndex A => (⟨x.deg, x.idx, x.exists_d_eq.choose⟩ : GenType c K))

/-- A section of the span which is a boundary has a primitive among the witnesses. -/
theorem exists_mem_witnesses (A : Gens c K) (j : ℤ) (i : ι) (s : (K.X (j + 1)).val.obj (op (c i)))
    (hs : s ∈ (span A (j + 1)).obj (op (c i)))
    (hb : ∃ t, (K.d j (j + 1)).val.app (op (c i)) t = s) :
    ∃ t, (⟨j, i, t⟩ : GenType c K) ∈ witnesses A ∧ (K.d j (j + 1)).val.app (op (c i)) t = s :=
  ⟨hb.choose, ⟨⟨j, i, ⟨s, hs⟩, hb⟩, rfl⟩, hb.choose_spec⟩

/-- One enlargement step: add the primitives, then the differentials and the zero sections. -/
def step (A : Gens c K) : Gens c K := dClosure (A ∪ witnesses A)

/-- The enlargement steps, starting from the differential closure of `A₀`. -/
def seq (A₀ : Gens c K) : ℕ → Gens c K
  | 0 => dClosure A₀
  | k + 1 => step (seq A₀ k)

/-- **The enlargement of a set of generators**: the union of the enlargement steps. -/
def enlargement (A₀ : Gens c K) : Gens c K := ⋃ k, seq A₀ k

/-- A generator lies in the enlargement iff it lies in one of the enlargement steps. -/
theorem mem_enlargement_iff {A₀ : Gens c K} {g : GenType c K} :
    g ∈ enlargement A₀ ↔ ∃ k, g ∈ seq A₀ k :=
  Set.mem_iUnion

/-- Each enlargement step after the first is one step applied to the previous one. -/
theorem seq_succ (A₀ : Gens c K) (k : ℕ) : seq A₀ (k + 1) = step (seq A₀ k) := rfl

/-- A set of generators is contained in its enlargement step. -/
theorem subset_step (A : Gens c K) : A ⊆ step A :=
  fun _ h => subset_dClosure _ (Or.inl h)

/-- The witnesses of a set of generators are contained in its enlargement step. -/
theorem witnesses_subset_step (A : Gens c K) : witnesses A ⊆ step A :=
  fun _ h => subset_dClosure _ (Or.inr h)

/-- Each enlargement step is contained in the next one. -/
theorem seq_subset_seq_succ (A₀ : Gens c K) (k : ℕ) : seq A₀ k ⊆ seq A₀ (k + 1) := by
  rw [seq_succ]
  exact subset_step _

/-- The enlargement steps form an increasing sequence. -/
theorem monotone_seq (A₀ : Gens c K) : Monotone (seq A₀) :=
  monotone_nat_of_le_succ (seq_subset_seq_succ A₀)

/-- The starting generators are contained in their enlargement. -/
theorem subset_enlargement (A₀ : Gens c K) : A₀ ⊆ enlargement A₀ :=
  fun _ h => mem_enlargement_iff.2 ⟨0, subset_dClosure _ h⟩

/-- Every enlargement step is stable under the differential. -/
theorem isDClosed_seq (A₀ : Gens c K) : ∀ k, IsDClosed (seq A₀ k)
  | 0 => isDClosed_dClosure _
  | _ + 1 => isDClosed_dClosure _

/-- **The enlargement is stable under the differential.** -/
theorem isDClosed_enlargement (A₀ : Gens c K) : IsDClosed (enlargement A₀) := by
  intro m n i s hs
  obtain ⟨k, hk⟩ := mem_enlargement_iff.1 hs
  exact mem_enlargement_iff.2 ⟨k, isDClosed_seq A₀ k m n i s hk⟩

/-- The generating sections of the enlargement are the union of those of the steps. -/
theorem genSet_enlargement (A₀ : Gens c K) (n : ℤ) (V : Cᵒᵖ) :
    genSet (enlargement A₀) n V = ⋃ k, genSet (seq A₀ k) n V := by
  ext x
  simp only [mem_genSet_iff, mem_enlargement_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨i, s, f, ⟨k, hk⟩, rfl⟩
    exact ⟨k, i, s, f, hk, rfl⟩
  · rintro ⟨k, i, s, f, hk, rfl⟩
    exact ⟨i, s, f, ⟨k, hk⟩, rfl⟩

/-- The generating sections are monotone in the set of generators. -/
theorem genSet_mono {A B : Gens c K} (h : A ⊆ B) (n : ℤ) (V : Cᵒᵖ) :
    genSet A n V ⊆ genSet B n V := by
  intro x hx
  obtain ⟨i, s, f, hs, rfl⟩ := mem_genSet_iff.1 hx
  exact mem_genSet_iff.2 ⟨i, s, f, h hs, rfl⟩

/-- A section of the span of the enlargement lies in the span of one of the steps. -/
theorem exists_mem_span_seq (A₀ : Gens c K) {n : ℤ} {V : Cᵒᵖ} {x : (K.X n).val.obj V}
    (hx : x ∈ (span (enlargement A₀) n).obj V) : ∃ k, x ∈ (span (seq A₀ k) n).obj V := by
  have hmono : Monotone (fun k => Submodule.span (R.obj.obj V) (genSet (seq A₀ k) n V)) :=
    fun a b hab => Submodule.span_mono (genSet_mono (monotone_seq A₀ hab) n V)
  simp only [span_obj] at hx ⊢
  rwa [genSet_enlargement, Submodule.span_iUnion,
    Submodule.mem_iSup_of_directed _ hmono.directed_le] at hx

/-- **Every section of the span of the enlargement over an object of the family which is a
boundary in `K` is the boundary of a section of the local closure.** -/
theorem exists_mem_closure_d_eq_of_enlargement (A₀ : Gens c K) (j n : ℤ) (hjn : j + 1 = n)
    (i : ι) (s : (K.X n).val.obj (op (c i))) (hs : s ∈ (span (enlargement A₀) n).obj (op (c i)))
    (hb : ∃ t, (K.d j n).val.app (op (c i)) t = s) :
    ∃ t, t ∈ (closure (enlargement A₀) j).obj (op (c i)) ∧ (K.d j n).val.app (op (c i)) t = s := by
  subst hjn
  obtain ⟨k, hk⟩ := exists_mem_span_seq A₀ hs
  obtain ⟨t, ht, hdt⟩ := exists_mem_witnesses (seq A₀ k) j i s hk hb
  refine ⟨t, mem_closure_of_mem _ (mem_enlargement_iff.2 ⟨k + 1, ?_⟩), hdt⟩
  rw [seq_succ]
  exact witnesses_subset_step _ ht

section Bounds

variable {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hι : #ι ≤ ν) (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν)
  (hR : ∀ i : ι, #(R.obj.obj (op (c i))) ≤ ν)

include hν hι hHom hR in
/-- The witnesses of a set of generators bounded by `ν` are bounded by `ν`. -/
theorem mk_witnesses_le (A : Gens c K) (hA : #A ≤ ν) : #(witnesses A) ≤ ν := by
  refine Cardinal.mk_range_le.trans ((Cardinal.mk_le_of_injective (f := fun x : BoundaryIndex A =>
    (⟨x.deg, x.idx, x.sec⟩ : Σ n : ℤ, Σ i : ι, (span A (n + 1)).obj (op (c i)))) ?_).trans ?_)
  · rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ ⟨⟩
    rfl
  · exact mk_sigma_int_le hν (fun n => mk_sigma_le_of_le hν hι
      (fun i => mk_span_obj_le A hν hA hι hHom hR (n + 1) i))

include hν hι hHom hR in
/-- Every enlargement step of a set of generators bounded by `ν` is bounded by `ν`. -/
theorem mk_seq_le (A₀ : Gens c K) (hA₀ : #A₀ ≤ ν) : ∀ k, #(seq A₀ k) ≤ ν
  | 0 => mk_dClosure_le A₀ hν hA₀ hι
  | k + 1 => by
    rw [seq_succ]
    exact mk_dClosure_le _ hν ((Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hν
      (mk_seq_le A₀ hA₀ k) (mk_witnesses_le hν hι hHom hR _ (mk_seq_le A₀ hA₀ k)))) hι

include hν hι hHom hR in
/-- **The enlargement is bounded by `ν`.** -/
theorem mk_enlargement_le (A₀ : Gens c K) (hA₀ : #A₀ ≤ ν) : #(enlargement A₀) ≤ ν := by
  let F : (Σ k : ULift.{t} ℕ, seq A₀ k.down) → GenType c K := fun p => p.2.1
  refine mk_le_of_subset_range (F := F) ?_ (mk_sigma_le_of_le hν ?_ fun k =>
    mk_seq_le hν hι hHom hR A₀ hA₀ _)
  · intro g hg
    obtain ⟨k, hk⟩ := mem_enlargement_iff.1 hg
    exact ⟨⟨⟨k⟩, ⟨g, hk⟩⟩, rfl⟩
  · rwa [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]

end Bounds

end Stacks.SheafOfModules.DenseSpan
