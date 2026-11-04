module

public import StacksFrontier.Topology.Noetherian.Defs

/-!
# Images of (locally) Noetherian spaces (Stacks 04Z8)

Stacks 04Z8 has two parts. Part (1), that the continuous image of a Noetherian topological
space is Noetherian, is `TopologicalSpace.NoetherianSpace.range` in Mathlib and is therefore
not restated here.

Part (2), that the image of a locally Noetherian space under a continuous *open* map is
locally Noetherian, is genuinely new: Mathlib has no notion of a locally Noetherian
topological space at all, so the statement is made against the predicate
`TopologicalSpace.IsLocallyNoetherianSpace`, which unfolds to "every point has a Noetherian
open neighbourhood". Openness of `f` is needed, not merely continuity: the image of a
Noetherian open neighbourhood `U` of `x` has to be an open neighbourhood of `f x` inside
`Set.range f`.
-/

@[expose] public section

namespace TopologicalSpace

/-- **Stacks 04Z8 (2).** The image of a locally Noetherian space under a continuous open map
is locally Noetherian. -/
@[stacks 04Z8 "(2)"]
theorem IsLocallyNoetherianSpace.range_of_isOpenMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (hX : IsLocallyNoetherianSpace X)
    (f : X → Y) (hf : Continuous f) (hopen : IsOpenMap f) :
    IsLocallyNoetherianSpace (Set.range f) := by
  intro y
  obtain ⟨x, hx⟩ := y.2
  obtain ⟨U, hU_open, hx_U, hU_noeth⟩ := hX x
  -- The restricted map `g : ↥U → ↥(Set.range f)` sending `z ↦ ⟨f z.val, z.val, rfl⟩`.
  set g : ↥U → ↥(Set.range f) := fun z => ⟨f z.val, z.val, rfl⟩
  have hg_cont : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  -- `Set.range g` corresponds (via `Subtype.val`) to the open set `f '' U`.
  have hg_range : Set.range g = Subtype.val ⁻¹' (f '' U) := by
    ext w
    refine ⟨fun ⟨z, hz⟩ => ⟨z.val, z.property, by rw [← hz]⟩, ?_⟩
    rintro ⟨x, hxU, hfx⟩
    exact ⟨⟨x, hxU⟩, Subtype.ext hfx⟩
  refine ⟨Set.range g, ?_, ⟨⟨x, hx_U⟩, Subtype.ext hx⟩, NoetherianSpace.range _ hg_cont⟩
  rw [hg_range]
  exact (hopen U hU_open).preimage continuous_subtype_val

/-- Local Noetherianity transfers along a homeomorphism: the image of a Noetherian open
neighbourhood is one. -/
theorem IsLocallyNoetherianSpace.of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (hX : IsLocallyNoetherianSpace X) (e : X ≃ₜ Y) :
    IsLocallyNoetherianSpace Y := fun y ↦
  have h := hX (e.symm y)
  ⟨e '' h.choose, e.isOpenMap _ h.choose_spec.1,
    ⟨e.symm y, h.choose_spec.2.1, e.apply_symm_apply y⟩,
    (noetherianSpace_iff_of_homeomorph (e.image h.choose)).mp h.choose_spec.2.2⟩

/-- A continuous open surjection from a locally Noetherian space has locally Noetherian
target: the target is the range of the map, which is locally Noetherian by Stacks 04Z8 (2). -/
theorem IsLocallyNoetherianSpace.of_isOpenMap_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (hX : IsLocallyNoetherianSpace X) (f : X → Y)
    (hf : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    IsLocallyNoetherianSpace Y :=
  (hX.range_of_isOpenMap f hf hopen).of_homeomorph
    ((Homeomorph.setCongr hsurj.range_eq).trans (Homeomorph.Set.univ Y))

end TopologicalSpace
