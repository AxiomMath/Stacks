module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
import StacksCore.Tactic.StacksAttribute

/-!
# A non-quasi-compact inverse limit of quasi-compact spaces

Quasi-compactness is not stable under inverse limits: there is an inverse system of
quasi-compact topological spaces indexed by the natural numbers whose limit is not
quasi-compact.

The system is the source's. Each stage is the set `ℕ` with the topology whose open sets are
the sets that, as soon as they contain one point `≥ n`, contain every point `≥ n`; the `n`-th
stage is quasi-compact because a cover can be refined to the finitely many sets covering
`0, …, n - 1` together with one set covering the whole tail. The transition maps are the
identity, which is continuous because the topologies decrease as `n` grows. A point of the
limit is a constant sequence, so the limit is `ℕ` with the discrete topology, which the
singletons `{k}` cover with no finite subcover.

## Main results

* `Stacks.Examples.exists_inverse_system_isCompact_not_isCompact_limit`: there is an inverse
  system over `ℕᵒᵖ` of quasi-compact spaces whose limit is not quasi-compact.

## Implementation notes

An inverse system indexed by the natural numbers is a functor from `ℕᵒᵖ` to `TopCat`.
Quasi-compactness is expressed as compactness of the whole underlying space, so that no
separation hypothesis is involved. The existential is stated in `TopCat.{0}`, the universe
containing the source's explicit topologies on `ℕ`.

## References

* [Stacks Project, Tag 09ZK](https://stacks.math.columbia.edu/tag/09ZK)
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.Examples

/-- The `n`-th stage topology on `ℕ`: a set is open when, if it meets the tail `[n, ∞)`, it
contains all of it. -/
@[instance_reducible] private def tailTopology (n : ℕ) : TopologicalSpace ℕ where
  IsOpen s := ∀ ⦃x⦄, x ∈ s → n ≤ x → ∀ y, n ≤ y → y ∈ s
  isOpen_univ := by simp
  isOpen_inter _ _ hs ht _ hx hn y hy := ⟨hs hx.1 hn y hy, ht hx.2 hn y hy⟩
  isOpen_sUnion := by
    intro S hS x hx hn y hy
    obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨s, hs, hS s hs hxs hn y hy⟩

private theorem tailTopology_mono {m n : ℕ} (hmn : m ≤ n) :
    tailTopology n ≤ tailTopology m :=
  fun _ hs _ hx hm y hy => hs hx (hmn.trans hm) y (hmn.trans hy)

private theorem tailTopology_isCompact (n : ℕ) :
    @IsCompact ℕ (tailTopology n) Set.univ := by
  let := tailTopology n
  apply isCompact_of_finite_subcover
  intro ι U hUo hcover
  classical
  choose pick hpick using fun k => Set.mem_iUnion.mp (hcover (Set.mem_univ k))
  refine ⟨(Finset.range n).image pick ∪ {pick n}, fun x _ => Set.mem_iUnion₂.mpr ?_⟩
  rcases Nat.lt_or_ge x n with hxn | hnx
  · exact ⟨pick x, Finset.mem_union_left _
      (Finset.mem_image_of_mem pick (Finset.mem_range.mpr hxn)), hpick x⟩
  · exact ⟨pick n, Finset.mem_union_right _ (Finset.mem_singleton_self _),
      hUo (pick n) (hpick n) le_rfl x hnx⟩

/-- The `n`-th stage of the system, as a topological space. -/
private def tailStage (n : ℕ) : TopCat := @TopCat.of ℕ (tailTopology n)

/-- The inverse system: the identity maps between the decreasing tail topologies on `ℕ`. -/
private def tailSystem : ℕᵒᵖ ⥤ TopCat.{0} where
  obj n := tailStage n.unop
  map {i j} f := by
    let g : @ContinuousMap ℕ ℕ (tailTopology i.unop) (tailTopology j.unop) :=
      @ContinuousMap.mk ℕ ℕ (tailTopology i.unop) (tailTopology j.unop) id <| by
        rw [@continuous_def ℕ ℕ (tailTopology i.unop) (tailTopology j.unop) id]
        intro s hs
        change @IsOpen ℕ (tailTopology i.unop) s
        exact tailTopology_mono (leOfHom f.unop) s hs
    exact @TopCat.ofHom ℕ ℕ (tailTopology i.unop) (tailTopology j.unop) g
  map_id _ := TopCat.hom_ext rfl
  map_comp _ _ := TopCat.hom_ext rfl

/-- **Stacks 09ZK.** There is an inverse system of quasi-compact topological spaces over the
natural numbers whose limit is not quasi-compact. -/
@[stacks 09ZK]
theorem exists_inverse_system_isCompact_not_isCompact_limit :
    ∃ F : ℕᵒᵖ ⥤ TopCat.{0},
      (∀ n, IsCompact (Set.univ : Set (F.obj n))) ∧
        ¬ IsCompact (Set.univ : Set ↑(limit F : TopCat.{0})) := by
  refine ⟨tailSystem, ?_, ?_⟩
  · intro n
    change @IsCompact ℕ (tailTopology n.unop) Set.univ
    exact tailTopology_isCompact n.unop
  · intro hcompact
    let c := TopCat.limitCone tailSystem
    let e : (limit tailSystem : TopCat.{0}) ≃ₜ c.pt :=
      TopCat.homeoOfIso ((limit.isLimit tailSystem).conePointUniqueUpToIso
        (TopCat.limitConeIsLimit tailSystem))
    have hc : IsCompact (Set.univ : Set c.pt) := by
      simpa using e.symm.isCompact_preimage.mpr hcompact
    obtain ⟨t, ht⟩ := hc.elim_finite_subcover
      (fun k : ℕ => {x : c.pt | x.val (Opposite.op (k + 1)) = k})
      (by
        intro k
        change IsOpen ((c.π.app (Opposite.op (k + 1))).hom ⁻¹' ({k} : Set ℕ))
        apply IsOpen.preimage ((c.π.app (Opposite.op (k + 1))).hom.continuous)
        change @IsOpen ℕ (tailTopology (k + 1)) ({k} : Set ℕ)
        rintro x rfl htail y hy
        omega)
      (by
        intro x hx
        let k : ℕ := x.1 (Opposite.op 0)
        have hcoord : x.1 (Opposite.op (k + 1)) = k := by
          have hcompat := x.2 (show Opposite.op (k + 1) ⟶ Opposite.op 0 from
            Opposite.op (homOfLE (Nat.zero_le (k + 1))))
          change x.1 (Opposite.op (k + 1)) = x.1 (Opposite.op 0) at hcompat
          simpa [k] using hcompat
        exact Set.mem_iUnion.mpr ⟨k, hcoord⟩)
    obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset t
    let x : c.pt := ⟨fun _ => m, fun _ => rfl⟩
    obtain ⟨k, hx⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hkt, hxk⟩ := Set.mem_iUnion.mp hx
    have hmk : m = k := by
      change x.1 (Opposite.op (k + 1)) = k at hxk
      simpa [x, tailSystem, tailStage] using hxk
    exact hm (hmk ▸ hkt)

end Stacks.Examples

end
