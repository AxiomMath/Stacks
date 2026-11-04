module

public import Mathlib.Topology.Irreducible
public import StacksFrontier.Topology.Noetherian.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Irreducible components of a closed subspace of a locally Noetherian space

A locally Noetherian space has, around every point, a Noetherian open neighbourhood, and a
Noetherian space has only finitely many irreducible components. So the irreducible components
of a subspace closed-embedded in a locally Noetherian space form a locally finite collection
of subsets of the ambient space.

## Main results

* `TopologicalSpace.IsLocallyNoetherianSpace.locallyFinite_image_irreducibleComponents`: the
  images of the irreducible components of a closed subspace are locally finite.

## Implementation notes

Around a point of the image the witness is a Noetherian open neighbourhood `U`: intersecting
with `U` is injective on the components meeting `U`, because such a component is the closure of
the image of the irreducible component of `f ⁻¹' U` it cuts out, and `f ⁻¹' U` is Noetherian,
being induced from `U`. Away from the image the complement of the image is a neighbourhood
meeting no member of the collection.
-/

@[expose] public section

namespace TopologicalSpace

/-- The images of the irreducible components of a space closed-embedded in a locally Noetherian
space form a locally finite collection of subsets of the ambient space. -/
@[ega "I 7.3.3" "more general", ega "IV 2.3.6" "more general"]
theorem IsLocallyNoetherianSpace.locallyFinite_image_irreducibleComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hY : IsLocallyNoetherianSpace Y)
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) :
    LocallyFinite fun C : irreducibleComponents X ↦ f '' (C : Set X) := by
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨U, hUopen, hxU, hUnoeth⟩ := hY (f x)
    let V : Set X := f ⁻¹' U
    let j : V → X := fun z ↦ z.1
    have hj : Topology.IsOpenEmbedding j :=
      (hUopen.preimage hf.continuous).isOpenEmbedding_subtypeVal
    let k : V → U := fun z ↦ ⟨f z.1, z.2⟩
    have hk : Topology.IsInducing k :=
      .of_comp (g := fun z : U ↦ (z : Y)) (by fun_prop) continuous_subtype_val
        (by simpa [k, j, Function.comp_def] using hf.isInducing.comp hj.isInducing)
    have : NoetherianSpace V := hk.noetherianSpace
    let g : {C : irreducibleComponents X // (f '' (C : Set X) ∩ U).Nonempty} →
        irreducibleComponents V := fun C ↦
      ⟨j ⁻¹' (C : Set X), preimage_mem_irreducibleComponents C.1.2 hj (by
        obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := C.2
        exact ⟨x, hx, ⟨⟨x, hz⟩, rfl⟩⟩)⟩
    have hclosure (E : {C : irreducibleComponents X // (f '' (C : Set X) ∩ U).Nonempty}) :
        closure (j '' ((g E : irreducibleComponents V) : Set V)) = (E.1 : Set X) := by
      apply closure_image_preimage_of_isPreirreducible j hj.isOpenMap
      · obtain ⟨_, ⟨x, hx, rfl⟩, hxU⟩ := E.2
        exact ⟨⟨x, hxU⟩, hx⟩
      · exact E.1.2.1.2
      · exact isClosed_of_mem_irreducibleComponents _ E.1.2
    have hginj : Function.Injective g := fun C D hCD ↦ Subtype.ext <| Subtype.ext <|
      (hclosure C).symm.trans ((congrArg
        (fun E : irreducibleComponents V ↦ closure (j '' (E : Set V))) hCD).trans (hclosure D))
    refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
    have : Finite (irreducibleComponents V) :=
      NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_injective g hginj)
  · refine ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl.mem_nhds hy, ?_⟩
    exact Set.finite_empty.subset fun _ ⟨_, ⟨x, _, rfl⟩, hx⟩ ↦ hx ⟨x, rfl⟩

end TopologicalSpace

end
