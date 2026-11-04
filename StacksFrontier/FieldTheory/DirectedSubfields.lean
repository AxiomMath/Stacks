module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Directed families of intermediate fields and coordinate subspaces

Let `K/k` be a field extension and let `{K_α}_{α ∈ A}` be a nonempty family of intermediate
fields of `K/k` which is directed downwards (for all `α, α'` there is `α''` with
`K_{α''} ⊆ K_α ∩ K_{α'}`) and whose intersection is `k`. We show that for every `n` and every
`K`-subspace `V ⊆ K^{⊕n}`, the subspace `V` contains a nonzero vector with all coordinates in
`k` if and only if it contains, for every `α`, a nonzero vector with all coordinates in `K_α`.

## Main definitions

* `coordSubset`: the set of vectors of `K^{⊕n}` all of whose coordinates lie in a given
  intermediate field; with `F = ⊥` this is `k^{⊕ι}`.

## Main results

* `intersection_subfields_07P3`: for a nonempty directed family of intermediate fields with
  intersection `k`, a subspace `V ⊆ K^{⊕n}` meets `k^{⊕n}` nontrivially if and only if it meets
  every `K_α^{⊕n}` nontrivially.
* `exists_ne_zero_mem_coordSubset_bot`: the substantive direction of the above.

## Implementation notes

A field extension `K/k` is modelled by `[Field k] [Field K] [Algebra k K]`, and a subfield of `K`
containing `k` by an `IntermediateField k K`; the condition `k ⊆ K_α` is then automatic from the
type. The copy of `k` inside `K` is the bottom intermediate field `(⊥ : IntermediateField k K)`,
whose underlying set is `Set.range (algebraMap k K)`, so the hypothesis `k = ⋂_α K_α` is stated as
`⨅ α, Kα α = ⊥`. The coordinate space `K^{⊕n}` is `Fin n → K`, with `K`-subspaces being
`Submodule K (Fin n → K)`. Downward directedness of the family is `Directed (· ≥ ·) Kα`. Since
all the sets involved contain the zero vector, "meets nontrivially" is spelled as the existence
of a nonzero element of the intersection.

## References

* [Stacks: Tag 07P3](https://stacks.math.columbia.edu/tag/07P3)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Coordinate subsets -/

/-- For an intermediate field `F` of `K/k`, the subset `F^{⊕n}` of `K^{⊕n}` of vectors all of
whose coordinates lie in `F`. With `F = ⊥` this is `k^{⊕n}`. -/
def coordSubset (n : ℕ) (F : IntermediateField k K) : Set (Fin n → K) :=
  {x | ∀ i, x i ∈ F}

/-- A subset `S ⊆ K^{⊕n}` is nonzero if it contains a nonzero vector. -/
def NonzeroSubset {n : ℕ} (S : Set (Fin n → K)) : Prop :=
  ∃ v ∈ S, v ≠ 0

/-- `coordSubset n F` is the set of vectors all of whose coordinates lie in `F`. -/
theorem coordSubset_def {n : ℕ} (F : IntermediateField k K) :
    coordSubset n F = {x | ∀ i, x i ∈ F} := rfl

/-- A vector lies in `coordSubset n F` if and only if each of its coordinates lies in `F`. -/
@[simp]
theorem mem_coordSubset_iff {n : ℕ} {F : IntermediateField k K} {x : Fin n → K} :
    x ∈ coordSubset n F ↔ ∀ i, x i ∈ F := Iff.rfl

/-- The zero vector lies in `coordSubset n F`. -/
theorem zero_mem_coordSubset {n : ℕ} (F : IntermediateField k K) :
    (0 : Fin n → K) ∈ coordSubset n F := fun _ => zero_mem F

/-- `coordSubset n` is monotone in the intermediate field. -/
theorem coordSubset_mono {n : ℕ} {F F' : IntermediateField k K} (hF : F ≤ F') :
    coordSubset n F ⊆ coordSubset n F' := fun _ hx i => hF (hx i)

/-! ### Auxiliary lemmas -/

namespace IntermediateField

/-- An element belongs to an infimum of a family of intermediate fields if and only if it
belongs to every member of the family. -/
theorem mem_iInf {ι : Sort*} {S : ι → IntermediateField k K} {x : K} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  rw [← SetLike.mem_coe, IntermediateField.coe_iInf]
  simp only [Set.mem_iInter, SetLike.mem_coe]

end IntermediateField

/-- A vector on `Fin (n + 1)` whose last coordinate vanishes and whose restriction to the
first `n` coordinates vanishes is zero. -/
theorem eq_zero_of_last_eq_zero_of_comp_castSucc_eq_zero {M : Type*} [Zero M] {n : ℕ}
    {x : Fin (n + 1) → M} (hl : x (Fin.last n) = 0) (hp : x ∘ Fin.castSucc = 0) : x = 0 := by
  funext i
  rcases eq_or_ne i (Fin.last n) with rfl | hi
  · simpa using hl
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simpa using congrFun hp j

/-! ### The backward direction -/

/-- If a `K`-subspace `V ⊆ K^{⊕n}` contains, for every member `Kα α` of a nonempty directed family
of intermediate fields with intersection `⊥`, a nonzero vector with all coordinates in `Kα α`,
then it contains a nonzero vector with all coordinates in `⊥`. -/
theorem exists_ne_zero_mem_coordSubset_bot {A : Type*} [Nonempty A]
    (Kα : A → IntermediateField k K) (hinf : ⨅ α, Kα α = ⊥) (hdir : Directed (· ≥ ·) Kα)
    {n : ℕ} (V : Submodule K (Fin n → K))
    (h : ∀ α, ∃ v ∈ (V : Set (Fin n → K)) ∩ coordSubset _ (Kα α), v ≠ 0) :
    ∃ v ∈ (V : Set (Fin n → K)) ∩ coordSubset _ (⊥ : IntermediateField k K), v ≠ 0 := by
  induction n with
  | zero =>
    obtain ⟨v, _, hv0⟩ := h (Classical.arbitrary A)
    exact absurd (Subsingleton.elim v 0) hv0
  | succ n ih =>
    set last : Fin (n+1) := Fin.last n
    set proj : (Fin (n+1) → K) →ₗ[K] (Fin n → K) := LinearMap.funLeft K K Fin.castSucc
    set L : Submodule K (Fin (n+1) → K) :=
      V ⊓ LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ => K) last)
    set L' : Submodule K (Fin n → K) := L.map proj
    by_cases hcase : ∀ α, ∃ v ∈ (L' : Set (Fin n → K)) ∩ coordSubset _ (Kα α), v ≠ 0
    · obtain ⟨y', ⟨⟨y, ⟨hyV, hylast⟩, hyproj⟩, hy'k⟩, hy'0⟩ := ih L' hcase
      refine ⟨y, ⟨hyV, fun i => ?_⟩, fun hy => hy'0 (by rw [← hyproj, hy, map_zero])⟩
      rcases eq_or_ne i last with rfl | hi
      · exact (show y last = 0 from hylast) ▸ zero_mem _
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
        exact (show y' j = y j.castSucc by rw [← hyproj]; rfl) ▸ hy'k j
    · rw [not_forall] at hcase
      obtain ⟨αs, hαs⟩ := hcase
      have hkey : ∀ w ∈ V, (∀ i, w i ∈ Kα αs) → w last = 0 → w = 0 := by
        intro w hwV hwc hwl
        by_contra hne
        exact hαs ⟨proj w, ⟨Submodule.mem_map_of_mem (⟨hwV, hwl⟩ : w ∈ L), fun j => hwc _⟩,
          fun hpw => hne (eq_zero_of_last_eq_zero_of_comp_castSucc_eq_zero hwl hpw)⟩
      have hnorm : ∀ (γ : A), Kα γ ≤ Kα αs →
          ∃ w : Fin (n+1) → K, w ∈ V ∧ (∀ i, w i ∈ Kα γ) ∧ w last = 1 := by
        intro γ hγ
        obtain ⟨w, ⟨hwV, hwc⟩, hw0⟩ := h γ
        have hwlast : w last ≠ 0 := fun hwl => hw0 (hkey w hwV (fun i => hγ (hwc i)) hwl)
        exact ⟨(w last)⁻¹ • w, V.smul_mem _ hwV,
          fun i => mul_mem (inv_mem (hwc last)) (hwc i), by simp [hwlast]⟩
      obtain ⟨w0, hw0V, hw0c, hw0last⟩ := hnorm αs le_rfl
      have hw0bot : ∀ i, w0 i ∈ (⊥ : IntermediateField k K) := by
        intro i
        rw [← hinf, IntermediateField.mem_iInf]
        intro β
        obtain ⟨γ, hγαs, hγβ⟩ := hdir αs β
        obtain ⟨w, hwV, hwc, hwlast⟩ := hnorm γ hγαs.le
        have hw : w = w0 := sub_eq_zero.mp (hkey _ (V.sub_mem hwV hw0V)
          (fun j => sub_mem (hγαs.le (hwc j)) (hw0c j)) (by simp [hwlast, hw0last]))
        exact hw ▸ hγβ.le (hwc i)
      exact ⟨w0, ⟨hw0V, hw0bot⟩, fun hw0 => by simp [hw0] at hw0last⟩

/-! ### Main statement -/

/-- Let `K/k` be a field extension and `{K_α}_{α ∈ A}` a nonempty directed family of
intermediate fields with intersection `k`. Then for every `n` and every `K`-subspace
`V ⊆ K^{⊕n}`, `V` meets `k^{⊕n}` nontrivially iff `V` meets every `K_α^{⊕n}` nontrivially.

Here:
* `hinf : ⨅ α, Kα α = ⊥` encodes the condition `k = ⋂_α K_α` (the intermediate
  field `⊥` is the copy of `k` in `K`);
* `hdir : ∀ α α', ∃ α'', Kα α'' ≤ Kα α ⊓ Kα α'` encodes downward directedness of the family;
* the condition `k ⊆ K_α` is automatic from `Kα α : IntermediateField k K`. -/
@[stacks 07P3, ega "0 21.8.1"]
theorem intersection_subfields_07P3 {A : Type*} [Nonempty A]
    (Kα : A → IntermediateField k K)
    (hinf : ⨅ α, Kα α = ⊥)
    (hdir : ∀ α α', ∃ α'', Kα α'' ≤ Kα α ⊓ Kα α')
    (n : ℕ) (V : Submodule K (Fin n → K)) :
    NonzeroSubset ((V : Set (Fin n → K)) ∩ coordSubset n (⊥ : IntermediateField k K)) ↔
    ∀ α, NonzeroSubset ((V : Set (Fin n → K)) ∩ coordSubset n (Kα α)) :=
  by
  have hdir' : Directed (· ≥ ·) Kα := fun a b => by
    obtain ⟨c, hc⟩ := hdir a b
    exact ⟨c, (le_inf_iff.mp hc).1, (le_inf_iff.mp hc).2⟩
  unfold NonzeroSubset
  exact ⟨fun ⟨v, hv, hv0⟩ _ =>
      ⟨v, Set.inter_subset_inter subset_rfl (coordSubset_mono bot_le) hv, hv0⟩,
    exists_ne_zero_mem_coordSubset_bot Kα hinf hdir' V⟩
