module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# Irreducible components of a closed subscheme are locally finite

If `X` is a locally Noetherian scheme and `Z ⟶ X` is a closed immersion, then the images in
`X` of the irreducible components of `Z` form a locally finite family. This is the finiteness
statement that makes the Weil divisor associated to a closed subscheme well defined.

## Main results

* `AlgebraicGeometry.locallyFinite_irreducibleComponents_image`: the irreducible components of
  a closed subscheme of a locally Noetherian scheme are locally finite in the ambient scheme.

## Implementation notes

A closed subscheme is represented by a closed immersion `i : Z ⟶ X`. Its irreducible
components are indexed by the subtype `irreducibleComponents Z`, and each component is regarded
as a subset of `X` by taking its image under `i`. The topological content is isolated as
`AlgebraicGeometry.locallyFinite_image_irreducibleComponents_of_isLocallyNoetherianSpace`:
over a locally Noetherian space, the images of the irreducible components of a closed subspace
are locally finite.

## References

* [Stacks Project, Tag 0BE1](https://stacks.math.columbia.edu/tag/0BE1)
-/

@[expose] public section

open TopologicalSpace

namespace AlgebraicGeometry

/-- Over a locally Noetherian space, the images of the irreducible components of a closed
subspace form a locally finite family. -/
@[ega "I 7.3.3" "more general", ega "IV 2.3.6" "more general"]
theorem locallyFinite_image_irreducibleComponents_of_isLocallyNoetherianSpace
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hY : IsLocallyNoetherianSpace Y) (f : X → Y) (hf : Topology.IsClosedEmbedding f) :
    LocallyFinite (fun C : irreducibleComponents X ↦ f '' (C : Set X)) := by
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨U, hUopen, hxU, hUnoeth⟩ := hY (f x)
    let V : Set X := f ⁻¹' U
    let j : V → X := fun z => z.1
    have hj : Topology.IsOpenEmbedding j :=
      (hUopen.preimage hf.continuous).isOpenEmbedding_subtypeVal
    let k : V → U := fun z => ⟨f z.1, z.2⟩
    have hk : Topology.IsInducing k :=
      .of_comp (f := k) (g := fun z : U => (z : Y)) (by fun_prop) continuous_subtype_val
        (by simpa [k, j, Function.comp_def] using hf.isInducing.comp hj.isInducing)
    have : NoetherianSpace V := hk.noetherianSpace
    let g : {C : irreducibleComponents X // (f '' (C : Set X) ∩ U).Nonempty} →
        irreducibleComponents V := fun C =>
      ⟨j ⁻¹' (C : Set X), preimage_mem_irreducibleComponents C.1.2 hj (by
        obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := C.2
        exact ⟨x, hx, ⟨⟨x, hz⟩, rfl⟩⟩)⟩
    have hclosure (E : {C : irreducibleComponents X // (f '' (C : Set X) ∩ U).Nonempty}) :
        closure (j '' ((g E : irreducibleComponents V) : Set V)) = (E.1 : Set X) := by
      refine closure_image_preimage_of_isPreirreducible j hj.isOpenMap _ ?_ E.1.2.1.2
        (isClosed_of_mem_irreducibleComponents _ E.1.2)
      obtain ⟨_, ⟨x, hx, rfl⟩, hxU⟩ := E.2
      exact ⟨⟨x, hxU⟩, hx⟩
    have hg_inj : Function.Injective g := fun C D hCD =>
      Subtype.ext (Subtype.ext (by rw [← hclosure C, ← hclosure D, hCD]))
    refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
    have : Finite (irreducibleComponents V) :=
      NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_injective g hg_inj)
  · refine ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl.mem_nhds hy,
      Set.finite_empty.subset ?_⟩
    rintro C ⟨_, ⟨x, _, rfl⟩, hx⟩
    exact hx ⟨x, rfl⟩

/-- **Stacks 0BE1.** The images of the irreducible components of a closed subscheme of a locally
Noetherian scheme form a locally finite family in the ambient scheme. -/
@[stacks 0BE1]
theorem locallyFinite_irreducibleComponents_image
    {X Z : Scheme} [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    LocallyFinite (fun C : irreducibleComponents Z ↦ i '' (C : Set Z)) :=
  locallyFinite_image_irreducibleComponents_of_isLocallyNoetherianSpace
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) _ i.isClosedEmbedding

end AlgebraicGeometry
