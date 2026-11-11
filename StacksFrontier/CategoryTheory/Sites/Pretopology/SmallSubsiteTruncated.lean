module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsiteIndexUniverse
import all StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
import all StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsiteIndexUniverse

/-!
# Set-sized sub-sites, with the `V_α` truncation (Stacks 000X)

Stacks 000X (Sets, Section 000W) cuts a possibly proper class `Cov(C)` of coverings down to the
*set* `Cov(C)_{κ, α}` of those coverings that lie in the stage `V_α` of the von Neumann hierarchy
and whose index set has cardinality at most `κ`. This file states and proves it with that
truncation in place: the truncated class is set-sized, contains a prescribed set of coverings,
is again a site, and represents every covering up to combinatorial equivalence.

## Main definitions

* `CovTrunc IsCov κ 𝒯`: the coverings in `IsCov` with index set of cardinality at most `κ` whose
  index type belongs to the collection of types `𝒯`. For a small `𝒯` this is the class
  `Cov(C)_{κ, α}` of Stacks 000X, with `𝒯` in the role of `V_α`.

## Main results

* `small_covTrunc`: for a small `𝒯`, the class `CovTrunc IsCov κ 𝒯` is set-sized.
* `exists_covTrunc_isSite`: Stacks 000X.

## Implementation notes

A Lean type has no von Neumann rank, so `V_α` cannot be intersected with the coverings directly.
What membership in `V_α` does in the source is to make the coverings form a set, by drawing their
index sets from the set `V_α`, while a limit ordinal `α` chosen large enough makes this set of
index sets closed under the operations the site axioms perform on index sets (the one-point set,
the dependent sums `∐_{i ∈ I} J_i` of the composition axiom; base change keeps the index set).
Here a small collection `𝒯 : Set (Type _)` of index types plays this role, and the theorem asserts
the two things `V_α` provides: `Cov(C)_{κ, 𝒯}` is `Small`, and it satisfies the site axioms. The
second is where the work lies: `𝒯` is the range of the decoding `IdxCode.El` of a small inductive
type of codes, built from the index types of `Cov₀` and of a system of combinatorial
representatives by the one-point type and by `Σ`-types over families indexed by a fixed type `K`
with `#K = κ`, which is the transfinite closure the source obtains by choosing `α`. The objects and
morphisms of `C` need no truncation, `C` being a small category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

/-! ### The truncated class of coverings -/

section Trunc

variable {C : Type u} [Category.{v} C]

/-- `CovTrunc IsCov κ 𝒯 𝒰` says that `𝒰` is a covering in `IsCov` whose index set has cardinality
at most `κ` and is one of the types in `𝒯`. For a small collection `𝒯`, standing for the stage
`V_α` of the von Neumann hierarchy, this is the set `Cov(C)_{κ, α}` of Stacks 000X. -/
def CovTrunc (IsCov : Covering.{u, v, w} C → Prop) (κ : Cardinal.{w}) (𝒯 : Set (Type w))
    (𝒰 : Covering C) : Prop :=
  CovBounded IsCov κ 𝒰 ∧ 𝒰.2.I₀ ∈ 𝒯

/-- For a small collection `𝒯` of index types, the coverings of `C` whose index type lies in `𝒯`
form a small type: such a covering is a target, an index type in `𝒯`, and a family of sources and
morphisms over it. -/
lemma small_covering_index_mem (𝒯 : Set (Type (max u v w))) [Small.{max u v w} 𝒯] :
    Small.{max u v w} {𝒰 : Covering.{u, v, max u v w} C // 𝒰.2.I₀ ∈ 𝒯} := by
  let F : (Σ (U : C) (t : 𝒯) (X : t.1 → C), ∀ i, X i ⟶ U) →
      {𝒰 : Covering.{u, v, max u v w} C // 𝒰.2.I₀ ∈ 𝒯} :=
    fun p => ⟨⟨p.1, ⟨p.2.1.1, p.2.2.1, p.2.2.2⟩⟩, p.2.1.2⟩
  refine small_of_surjective (f := F) ?_
  rintro ⟨⟨U, ⟨I, X, g⟩⟩, h⟩
  exact ⟨⟨U, ⟨I, h⟩, X, g⟩, rfl⟩

/-- For a small collection `𝒯` of index types, the truncated class `CovTrunc IsCov κ 𝒯` is a
set. -/
theorem small_covTrunc (IsCov : Covering.{u, v, max u v w} C → Prop)
    (κ : Cardinal.{max u v w}) (𝒯 : Set (Type (max u v w))) [Small.{max u v w} 𝒯] :
    Small.{max u v w} {𝒰 // CovTrunc IsCov κ 𝒯 𝒰} := by
  have := small_covering_index_mem (C := C) 𝒯
  exact small_of_injective (f := fun 𝒰 : {𝒰 // CovTrunc IsCov κ 𝒯 𝒰} =>
    (⟨𝒰.1, 𝒰.2.2⟩ : {𝒰 : Covering C // 𝒰.2.I₀ ∈ 𝒯})) fun a b h => Subtype.ext (by
      simpa using congrArg Subtype.val h)

end Trunc

/-! ### A small collection of index types closed under `PUnit` and `Σ` -/

/-- Codes for index types: base types indexed by `ι`, the one-point type, and `Σ`-types over a
coded type of families indexed through a fixed type `K`. -/
inductive IdxCode (K ι : Type w) : Type w
  | base : ι → IdxCode K ι
  | unit : IdxCode K ι
  | sigma : IdxCode K ι → (K → IdxCode K ι) → IdxCode K ι

namespace IdxCode

variable {K ι : Type w} (T : ι → Type w)

/-- For an infinite cardinal `#K`, a `Σ`-type whose base and fibres all have cardinality at most
`#K` again has cardinality at most `#K`. -/
lemma mk_sigma_le_of_le (hK : ℵ₀ ≤ #K) {A : Type w} (hA : #A ≤ #K) {B : A → Type w}
    (hB : ∀ x, #(B x) ≤ #K) : #(Σ x, B x) ≤ #K :=
  calc #(Σ x, B x) = sum fun x => #(B x) := mk_sigma B
    _ ≤ #A * #K := (sum_le_sum _ _ hB).trans (by simp [sum_const])
    _ ≤ #K * #K := mul_le_mul' hA le_rfl
    _ = #K := mul_eq_self hK

/-- A chosen embedding into `K` of a type of cardinality at most `#K`. -/
noncomputable def embK (A : {X : Type w // #X ≤ #K}) : A.1 ↪ K :=
  Classical.choice (Cardinal.le_def _ _ |>.mp A.2)

/-- The type decoded from a code, with its cardinality bound `#K`. A `Σ`-code `sigma a b` decodes
to `Σ x : El a, El (b (embK (El a) x))`. -/
noncomputable def El (hK : ℵ₀ ≤ #K) (hT : ∀ j, #(T j) ≤ #K) :
    IdxCode K ι → {X : Type w // #X ≤ #K}
  | base j => ⟨T j, hT j⟩
  | unit => ⟨PUnit, mk_punit.trans_le (one_le_aleph0.trans hK)⟩
  | sigma a b =>
    ⟨Σ x : (El hK hT a).1, (El hK hT (b (embK (El hK hT a) x))).1,
      mk_sigma_le_of_le hK (El hK hT a).2 fun x => (El hK hT (b (embK (El hK hT a) x))).2⟩

variable {T}

/-- The collection of decoded types is closed under `Σ`-types: a family of decoded types over a
decoded type has a decoded `Σ`-type. -/
lemma sigma_mem_range (hK : ℵ₀ ≤ #K) (hT : ∀ j, #(T j) ≤ #K) {A : Type w}
    (hA : A ∈ Set.range fun c => (El T hK hT c).1) {B : A → Type w}
    (hB : ∀ x, B x ∈ Set.range fun c => (El T hK hT c).1) :
    (Σ x, B x) ∈ Set.range fun c => (El T hK hT c).1 := by
  classical
  obtain ⟨a, rfl⟩ := hA
  choose c hc using hB
  obtain rfl : B = fun x => (El T hK hT (c x)).1 := funext fun x => (hc x).symm
  let e := embK (El T hK hT a)
  let b : K → IdxCode K ι := fun k => if h : ∃ x, e x = k then c h.choose else unit
  have hb : ∀ x, b (e x) = c x := fun x => by
    have h : ∃ y, e y = e x := ⟨x, rfl⟩
    simp only [b, dite_eq_left h, e.injective h.choose_spec]
  refine ⟨sigma a b, ?_⟩
  change (Σ x : (El T hK hT a).1, (El T hK hT (b (e x))).1) = _
  simp only [hb]

end IdxCode

/-! ### The main theorem -/

/-- **Stacks 000X**. Let `IsCov` be a site on `C` and let `Cov₀` be a set of coverings in it.
Then there are an (infinite) cardinal `κ` and a small collection `𝒯` of index types, standing for
the stage `V_α` of the von Neumann hierarchy, such that the class `Cov(C)_{κ, 𝒯}` of coverings in
`IsCov` with index set in `𝒯` of cardinality at most `κ` is a *set*, contains `Cov₀`, satisfies
the site axioms, and contains a combinatorially equivalent copy of every covering in `IsCov`.

The collection `𝒯` does the work of the limit ordinal `α`: it is closed under the one-point type
and under `Σ`-types of families of its members, which is what the composition and isomorphism
axioms need. The index sets live in a universe `Type (max u v w)` at least as large as that of the
objects and morphisms of `C`; `w = 0` is the case `Type (max u v)` of `exists_covBounded_isSite`. -/
@[stacks 000X "The stage `V_α` of the von Neumann hierarchy is modelled by a small collection `𝒯`
of index types closed under the one-point type and `Σ`-types, as a Lean type has no rank; the
truncated class is proved `Small`."]
theorem exists_covTrunc_isSite
    {C : Type u} [Category.{v} C]
    (IsCov : Covering.{u, v, max u v w} C → Prop)
    (hSite : IsSite IsCov)
    (Cov₀ : Set (Covering.{u, v, max u v w} C))
    [Small.{max u v w} Cov₀]
    (hCov₀ : ∀ 𝒰 ∈ Cov₀, IsCov 𝒰) :
    ∃ (κ : Cardinal.{max u v w}) (𝒯 : Set (Type (max u v w))),
      ℵ₀ ≤ κ ∧ Small.{max u v w} 𝒯 ∧
      Small.{max u v w} {𝒰 // CovTrunc IsCov κ 𝒯 𝒰} ∧
      (∀ 𝒰 ∈ Cov₀, CovTrunc IsCov κ 𝒯 𝒰) ∧
      IsSite (CovTrunc IsCov κ 𝒯) ∧
      (∀ 𝒰 : Covering C, IsCov 𝒰 →
        ∃ 𝒰' : Covering C, CovTrunc IsCov κ 𝒯 𝒰' ∧ Covering.CombEquiv 𝒰 𝒰') := by
  classical
  obtain ⟨hIso, hComp, hBC⟩ := hSite
  -- One representative per value of the combinatorial invariant `arrowSet`.
  let Cls := {c : Σ U : C, Set (Σ V : C, V ⟶ U) // ∃ 𝒰 : Covering C, IsCov 𝒰 ∧ arrowSet 𝒰 = c}
  let rep : Cls → Covering C := fun c => c.2.choose
  -- The coverings whose index types seed `𝒯`.
  let 𝒮 : Set (Covering C) := Cov₀ ∪ Set.range rep
  have : Small.{max u v w} 𝒮 := small_union _ _
  let T : Shrink.{max u v w} 𝒮 → Type (max u v w) := fun j => ((equivShrink 𝒮).symm j).1.2.I₀
  have hT𝒮 : ∀ 𝒰 (h : 𝒰 ∈ 𝒮), T (equivShrink 𝒮 ⟨𝒰, h⟩) = 𝒰.2.I₀ := fun 𝒰 h =>
    congrArg (fun x : 𝒮 => x.1.2.I₀) ((equivShrink 𝒮).symm_apply_apply ⟨𝒰, h⟩)
  let κ : Cardinal.{max u v w} := ℵ₀ ⊔ sum fun j => #(T j)
  let K : Type (max u v w) := κ.out
  have hKκ : #K = κ := mk_out κ
  have hK : ℵ₀ ≤ #K := by rw [hKκ]; exact le_sup_left
  have hT : ∀ j, #(T j) ≤ #K := fun j => by rw [hKκ]; exact (le_sum _ j).trans le_sup_right
  let 𝒯 : Set (Type (max u v w)) := Set.range fun c => (IdxCode.El T hK hT c).1
  have h𝒯 : Small.{max u v w} 𝒯 := small_range _
  have h𝒮 : ∀ 𝒰 ∈ 𝒮, IsCov 𝒰 → CovTrunc IsCov κ 𝒯 𝒰 := fun 𝒰 h hcov =>
    ⟨⟨hcov, by rw [← hT𝒮 𝒰 h, ← hKκ]; exact hT _⟩, ⟨.base (equivShrink 𝒮 ⟨𝒰, h⟩), hT𝒮 𝒰 h⟩⟩
  have hκ : ℵ₀ ≤ κ := le_sup_left
  refine ⟨κ, 𝒯, hκ, h𝒯, small_covTrunc IsCov κ 𝒯,
    fun 𝒰 h => h𝒮 𝒰 (Or.inl h) (hCov₀ 𝒰 h), ⟨?_, ?_, ?_⟩, fun 𝒰 h𝒰 => ?_⟩
  · intro U V f _
    exact ⟨covBounded_isoCond_univ hIso hκ f, ⟨.unit, rfl⟩⟩
  · intro 𝒰 h𝒰 𝒱 h𝒱 htargets
    refine ⟨covBounded_compositionCond_univ hComp hκ 𝒰 h𝒰.1 𝒱 (fun i => (h𝒱 i).1) htargets, ?_⟩
    exact IdxCode.sigma_mem_range hK hT h𝒰.2 fun i => (h𝒱 i).2
  · intro 𝒰 h𝒰 V g
    obtain ⟨P, π₁, π₂, hpb, hcov⟩ := covBounded_baseChangeCond_univ hBC 𝒰 h𝒰.1 V g
    exact ⟨P, π₁, π₂, hpb, hcov, h𝒰.2⟩
  · let c : Cls := ⟨arrowSet 𝒰, 𝒰, h𝒰, rfl⟩
    obtain ⟨hcov, heq⟩ := c.2.choose_spec
    exact ⟨rep c, h𝒮 _ (Or.inr ⟨c, rfl⟩) hcov,
      (combEquiv_of_arrowSet_eq (rep c) 𝒰 heq).symm⟩
