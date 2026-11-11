module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Split
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Split

/-!
# Split simplicial semi-representable objects, by subobjects

Tag 0DAU of the Stacks Project characterises the simplicial and the `r`-truncated simplicial
objects `K` of `SR(C)` that are split in the sense of Tag 017P: with `K_n = {U_{n, i}}_{i ∈ I_n}`,
`K` is split exactly when every surjection `φ : [m] → [n]` acts by isomorphisms
`f_{φ, i} : U_{n, i} → U_{m, α(φ)(i)}`, and exactly when the elementary degeneracies do.

## Main results

* `tfae_nonempty_subobjectSplitting`: Tag 0DAU for simplicial objects, with
  `SimplicialObject.SubobjectSplitting`, the splitting of Tag 017P.
* `tfae_nonempty_truncated_subobjectSplitting`: Tag 0DAU for `r`-truncated simplicial objects, with
  `SimplicialObject.Truncated.SubobjectSplitting`, the truncated splitting of Tag 017P.
* `isTruncatedSplit_iff_nonempty_subobjectSplitting`: a truncated simplicial semi-representable
  object extends to a split simplicial object exactly when it is split in the sense of Tag 017P.

## References

* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
* [Stacks Project, Tag 017P](https://stacks.math.columbia.edu/tag/017P)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

/-- **Stacks Project, Tag 0DAU**, for simplicial objects. For a simplicial object `K` of `SR(C)`,
written `K_n = {U_{n, i}}_{i ∈ I_n}`, the following are equivalent:
1. `K` is split, in the sense of Tag 017P (a splitting by subobjects);
2. for every surjection `φ : [m] → [n]` and every `i ∈ I_n`, the component
  `f_{φ, i} : U_{n, i} → U_{m, α(φ)(i)}` is an isomorphism;
3. for all `n`, `0 ≤ j ≤ n` and `i ∈ I_n`, the component of the degeneracy `σ^n_j` at `i` is an
  isomorphism. -/
@[stacks 0DAU "simplicial objects (`r = ∞`): (1), (2) and (3) are equivalent, with (1) the \
  splitting by subobjects of Tag 017P"]
theorem tfae_nonempty_subobjectSplitting
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    List.TFAE
      [Nonempty K.SubobjectSplitting,
        ∀ {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ] (i : (K.obj (op n)).I),
          IsIso ((K.map φ.op).φ i),
        ∀ (n : ℕ) (j : Fin (n + 1)) (i : (K.obj (op (SimplexCategory.mk n))).I),
          IsIso ((K.map (SimplexCategory.σ j).op).φ i)] := by
  tfae_have 1 ↔ 2 := by
    rw [components_of_epi_iff_exists_splitting_mono]
    exact ⟨fun ⟨s⟩ => ⟨s.toSplitting, s.mono_ι⟩, fun ⟨s, hs⟩ => ⟨⟨s, hs⟩⟩⟩
  tfae_have 2 ↔ 3 := components_of_epi_iff_components_of_degeneracy K
  tfae_finish

/-- **Stacks Project, Tag 0DAU**, for `r`-truncated simplicial objects. For an `r`-truncated
simplicial object `K` of `SR(C)`, written `K_n = {U_{n, i}}_{i ∈ I_n}`, the following are
equivalent:
1. `K` is split, in the sense of Tag 017P for truncated simplicial objects;
2. for every surjection `φ : [m] → [n]` with `m ≤ r` and every `i ∈ I_n`, the component
  `f_{φ, i} : U_{n, i} → U_{m, α(φ)(i)}` is an isomorphism;
3. for all `0 ≤ j ≤ n < r` and `i ∈ I_n`, the component of the degeneracy `σ^n_j` at `i` is an
  isomorphism. -/
@[stacks 0DAU "`r`-truncated simplicial objects: (1), (2) and (3) are equivalent, with (1) the \
  truncated splitting by subobjects of Tag 017P"]
theorem tfae_nonempty_truncated_subobjectSplitting (r : ℕ)
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) :
    List.TFAE
      [Nonempty (SimplicialObject.Truncated.SubobjectSplitting K),
        ∀ {m n : SimplexCategory.Truncated r} (φ : m ⟶ n) [Epi φ] (i : (K.obj (op n)).I),
          IsIso ((K.map φ.op).φ i),
        ∀ (n : ℕ) (hn : n + 1 ≤ r) (j : Fin (n + 1))
          (i : (K.obj (op (⟨SimplexCategory.mk n, Nat.le_of_succ_le hn⟩ :
            SimplexCategory.Truncated r))).I),
          IsIso ((K.map (ObjectProperty.homMk (SimplexCategory.σ j) :
            (⟨SimplexCategory.mk (n + 1), hn⟩ : SimplexCategory.Truncated r) ⟶
            (⟨SimplexCategory.mk n, Nat.le_of_succ_le hn⟩ :
              SimplexCategory.Truncated r)).op).φ i)] := by
  tfae_have 1 ↔ 2 := by
    rw [truncated_components_of_epi_iff_exists_isColimit]
    exact ⟨fun ⟨s⟩ => ⟨s.N, s.ι, s.mono_ι, fun a => ⟨s.isColimit' (op a)⟩⟩,
      fun ⟨N, ι, hι, hc⟩ => ⟨⟨N, ι, hι, fun Δ => (hc Δ.unop).some⟩⟩⟩
  tfae_have 2 ↔ 3 := truncated_components_of_epi_iff_components_of_degeneracy r K
  tfae_finish

/-- A truncated simplicial formal coproduct admits a split simplicial extension exactly when it is
split in the sense of Tag 017P for truncated simplicial objects. -/
theorem isTruncatedSplit_iff_nonempty_subobjectSplitting (r : ℕ)
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) :
    IsTruncatedSplit r K ↔ Nonempty (SimplicialObject.Truncated.SubobjectSplitting K) :=
  (truncated_split_iff_components_of_epi r K).trans
    ((tfae_nonempty_truncated_subobjectSplitting r K).out 1 2).symm

end Stacks.CategoryTheory.Hypercovering
