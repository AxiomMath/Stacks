module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Images of generic points, and dense open subsets

Let `q : X ⟶ Y` be a continuous map with dense image, and let `E ⊆ X` be a finite set whose
closure is `X`, for instance the generic points of the irreducible components of a sober
Noetherian space. If no point of `q(E)` specializes to the image of another point of `E`, then
every dense open subset of `Y` contains `q(E)`, so its inverse image is dense in `X`.

For the inverse-limit topology on a space `X`, the infimum of the topologies induced by maps
`p_i : X ⟶ X_i`, a point `y` specializes to `x` as soon as every `p_i y` specializes to
`p_i x`.

## Main results

* `C1573.eq_of_mem_genericPoints_of_mem_closure`: two generic points of irreducible components of a
  `T₀` space, one in the closure of the other, are equal.
* `C1573.dense_preimage_of_finite_of_closure_eq_univ`: the statement of the first paragraph.
* `C1573.specializes_of_forall_specializes_of_eq_iInf_induced`: the statement of the second
  paragraph.
-/

namespace C1573
end C1573

@[expose] public section

open Topology

section

open _root_.C1573
variable {X : Type*} [TopologicalSpace X]

/-- **Generic points of irreducible components are incomparable.** In a `T₀` space, a generic
point of an irreducible component lying in the closure of another one is that one. -/
theorem C1573.eq_of_mem_genericPoints_of_mem_closure [T0Space X] {a b : X}
    (ha : a ∈ genericPoints X) (hb : b ∈ genericPoints X) (h : a ∈ closure {b}) : a = b := by
  have hsub : closure {a} ⊆ closure {b} := closure_minimal (Set.singleton_subset_iff.2 h)
    isClosed_closure
  have heq : closure ({a} : Set X) = closure {b} :=
    le_antisymm hsub (ha.2 hb.1 hsub)
  exact congrArg Subtype.val (genericPoints.component_injective (α := X)
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext heq))

/-- **Dense open subsets contain incomparable images of a dense finite set.** Let `q : X ⟶ Y` be
continuous with dense image and let `E ⊆ X` be finite and dense, no point of `q(E)` lying in the
closure of the image of another point of `E`. Then the inverse image of every dense open subset of
`Y` is dense in `X`. -/
theorem C1573.dense_preimage_of_finite_of_closure_eq_univ {Y : Type*} [TopologicalSpace Y]
    {q : X → Y} (hq : Continuous q) (hqd : DenseRange q) {E : Set X} (hEf : E.Finite)
    (hE : closure E = Set.univ)
    (hinc : ∀ a ∈ E, ∀ b ∈ E, q a ∈ closure {q b} → a = b)
    {O : Set Y} (hO : IsOpen O) (hOd : Dense O) : Dense (q ⁻¹' O) := by
  have hcl : ∀ S : Set X, S.Finite → IsClosed (⋃ b ∈ S, closure ({q b} : Set Y)) :=
    fun _ hS => hS.isClosed_biUnion fun _ _ => isClosed_closure
  have hcover : (Set.univ : Set Y) ⊆ ⋃ b ∈ E, closure {q b} := by
    have himg : q '' E ⊆ ⋃ b ∈ E, closure ({q b} : Set Y) := by
      rintro _ ⟨b, hb, rfl⟩
      exact Set.mem_biUnion hb (subset_closure rfl)
    rw [← hqd.closure_range]
    refine closure_minimal ?_ (hcl E hEf)
    rintro _ ⟨x, rfl⟩
    exact closure_minimal himg (hcl E hEf)
      (map_mem_closure hq (hE ▸ Set.mem_univ x) fun a ha => ⟨a, ha, rfl⟩)
  have hmem : ∀ a ∈ E, q a ∈ O := by
    intro a ha
    set U := (⋃ b ∈ E \ {a}, closure ({q b} : Set Y))ᶜ with hU
    have hUo : IsOpen U := (hcl _ hEf.sdiff).isOpen_compl
    have haU : q a ∈ U := by
      simp only [hU, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      intro b hb hab
      exact hb.2 (hinc a ha b hb.1 hab).symm
    obtain ⟨z, hzU, hzO⟩ := hOd.inter_open_nonempty U hUo ⟨q a, haU⟩
    obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcover (Set.mem_univ z))
    have hba : b = a := by
      by_contra hne
      exact hzU (Set.mem_biUnion ⟨hb, hne⟩ hzb)
    subst hba
    exact (specializes_iff_mem_closure.2 hzb).mem_open hO hzO
  exact (dense_iff_closure_eq.2 hE).mono hmem

end

open _root_.C1573
/-- **Specialization in an inverse-limit topology.** If the topology of `X` is the infimum of the
topologies induced by maps `p i : X ⟶ Y i`, then `y` specializes to `x` as soon as every `p i y`
specializes to `p i x`. -/
theorem C1573.specializes_of_forall_specializes_of_eq_iInf_induced {X : Type*} {ι : Type*}
    {Y : ι → Type*} [τ : ∀ i, TopologicalSpace (Y i)] [t : TopologicalSpace X]
    (p : ∀ i, X → Y i) (ht : t = ⨅ i, TopologicalSpace.induced (p i) (τ i)) {x y : X}
    (h : ∀ i, p i y ⤳ p i x) : y ⤳ x := by
  subst ht
  change @nhds X (⨅ i, TopologicalSpace.induced (p i) (τ i)) y ≤
    @nhds X (⨅ i, TopologicalSpace.induced (p i) (τ i)) x
  rw [nhds_iInf, nhds_iInf]
  refine le_iInf fun i => (iInf_le _ i).trans ?_
  rw [nhds_induced, nhds_induced]
  exact Filter.comap_mono (h i)
