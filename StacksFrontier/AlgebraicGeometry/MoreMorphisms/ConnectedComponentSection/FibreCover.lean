module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.CardComponents
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.CoveringFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.Topology.Noetherian.LocallyConnected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separating the generic fibre into two closed pieces over an open neighbourhood

Let `f : X ⟶ Y` be a finite type morphism of schemes and let `η : Y` be a generic point of `Y`.
If the generic fibre is partitioned into two closed subsets `A` and `B`, then over an open
neighbourhood of `η` the closures of `A` and `B` in `X` still cover and still separate every
fibre. This is the geometric input for Tag 055N.

## Main results

* `AlgebraicGeometry.exists_open_fibers_disjoint_of_generic_disjoint`: two closed subsets of
  `X` whose traces on the generic fibre are disjoint have disjoint traces on all fibres over
  an open neighbourhood of `η`.
* `AlgebraicGeometry.exists_open_fibers_covered_and_disjoint_by_closures`: a partition of the
  generic fibre into two closed pieces spreads out to a partition of every nearby fibre.
* `AlgebraicGeometry.ConnectedAlongSection.isClopen_fiberComponent`: for a finite type
  morphism the selected connected component of a fibre is open and closed.

## Implementation notes

Disjointness is spread out by applying Tag 02NE to the reduced induced closed subscheme on
`A ∩ B`: the generic point is not in its image, so an open neighbourhood of it has empty
inverse image. Covering is spread out by Tag 054Y. The component of a fibre is open because a
fibre of a finite type morphism is a Noetherian, hence locally connected, space.

## References

* [Stacks Project, Tag 055N](https://stacks.math.columbia.edu/tag/055N)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A generic point of the whole space lies in every nonempty open subset. -/
@[ega "0 2.1.4" "partial"]
theorem IsGenericPoint.mem_of_isOpen_of_nonempty
    {Y : Type u} [TopologicalSpace Y] {η : Y} (hη : IsGenericPoint η Set.univ) {V : Set Y}
    (hV : IsOpen V) (hne : V.Nonempty) : η ∈ V :=
  (hη.mem_open_set_iff hV).2 (by simpa using hne)

/-- A closed subset whose complement is also closed and which together with a second closed
subset covers the space and is disjoint from it is open and closed. -/
theorem isClopen_of_isClosed_of_union_univ_of_disjoint
    {α : Type*} [TopologicalSpace α] (A B : Set α)
    (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B) : IsClopen A :=
  ⟨hA, by rwa [← isClosed_compl_iff, (IsCompl.of_eq hdisj.eq_bot hcover).compl_eq]⟩

namespace ConnectedAlongSection

/-- For a finite type morphism the selected connected component of a fibre is open and closed,
because the fibre is a Noetherian and hence locally connected space. -/
theorem isClopen_fiberComponent (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] (η : D.Y) :
    IsClopen (D.fiberComponent η) := by
  have : LocallyOfFiniteType (D.f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd D.f (D.Y.fromSpecResidueField η))
    infer_instance
  have : IsLocallyNoetherian (D.f.fiber η) :=
    LocallyOfFiniteType.isLocallyNoetherian (D.f.fiberToSpecResidueField η)
  have : IsNoetherian (D.f.fiber η) := {}
  have : LocallyConnectedSpace (D.f.fiber η) :=
    IsLocallyNoetherianSpace.locallyConnectedSpace _ (isLocallyNoetherianSpace_of_noetherianSpace _)
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩

end ConnectedAlongSection

/-- Two closed subsets of the source whose traces on the generic fibre are disjoint have
disjoint traces on every fibre over some open neighbourhood of the generic point. -/
theorem exists_open_fibers_disjoint_of_generic_disjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hηdisj : Disjoint ((f.fiberι η) ⁻¹' A) ((f.fiberι η) ⁻¹' B)) :
    ∃ V : Y.Opens, η ∈ V ∧ ∀ y ∈ V,
      Disjoint ((f.fiberι y) ⁻¹' A) ((f.fiberι y) ⁻¹' B) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨A ∩ B, hA.inter hB⟩
  let g : I.subscheme ⟶ Y := I.subschemeι ≫ f
  have : QuasiCompact g := quasiCompact_comp I.subschemeι f
  have : PreirreducibleSpace Y := ⟨by simpa using hη.isIrreducible.isPreirreducible⟩
  have : IrreducibleSpace Y := ⟨⟨η⟩⟩
  have hηgp : η ∈ genericPoints Y := by
    change closure ({η} : Set Y) ∈ irreducibleComponents Y
    rw [show closure ({η} : Set Y) = Set.univ from hη.def, irreducibleComponents_eq_singleton]
    simp
  have hηg : η ∉ Set.range g := by
    rintro ⟨t, ht⟩
    have hxt : f (I.subschemeι t) = η := by simpa [g] using ht
    let z : f.fiber η := (f.fiberHomeo η).symm ⟨I.subschemeι t, hxt⟩
    have hz : f.fiberι η z = I.subschemeι t := by simp [z]
    have hrange : I.subschemeι t ∈ Set.range I.subschemeι := ⟨t, rfl⟩
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hrange
    exact Set.disjoint_left.mp hηdisj (show f.fiberι η z ∈ A from hz ▸ hrange.1)
      (show f.fiberι η z ∈ B from hz ▸ hrange.2)
  obtain ⟨V, hηV, hpre⟩ := exists_open_nhds_disjoint_range_of_quasiCompact g η hηgp hηg
  refine ⟨V, hηV, fun y hy => Set.disjoint_left.mpr fun z hzA hzB => ?_⟩
  obtain ⟨t, ht⟩ : f.fiberι y z ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact ⟨hzA, hzB⟩
  have htg : g t = y := (congrArg f ht).trans (by simpa using (f.fiberHomeo y z).2)
  have htV : t ∈ g ⁻¹ᵁ V := show g t ∈ V from htg ▸ hy
  simp [hpre] at htV

/-- A partition of the generic fibre into two closed pieces spreads out: over an open
neighbourhood of the generic point, the closures in `X` of the two pieces both cover and
separate every fibre. -/
theorem exists_open_fibers_covered_and_disjoint_by_closures
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (A B : Set (f.fiber η)) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : ∀ x, x ∈ A ∨ x ∈ B) (hdisj : Disjoint A B) :
    ∃ V : Y.Opens, η ∈ V ∧ ∀ y ∈ V,
      (∀ x : f.fiber y,
        f.fiberι y x ∈ closure (f.fiberι η '' A) ∨
          f.fiberι y x ∈ closure (f.fiberι η '' B)) ∧
      Disjoint ((f.fiberι y) ⁻¹' closure (f.fiberι η '' A))
        ((f.fiberι y) ⁻¹' closure (f.fiberι η '' B)) := by
  let Z : Bool → Set (f.fiber η) := fun b => if b then B else A
  have hZcover : ∀ x : f.fiber η, ∃ b, x ∈ Z b := fun x =>
    (hcover x).elim (⟨false, ·⟩) (⟨true, ·⟩)
  obtain ⟨Vcover, hVcoverOpen, hVcoverNe, hVcover⟩ :=
    exists_open_fiber_covered_by_closures f η hη Z hZcover
  let VcoverO : Y.Opens := ⟨Vcover, hVcoverOpen⟩
  have hpre : ∀ C : Set (f.fiber η), IsClosed C →
      (f.fiberι η) ⁻¹' closure (f.fiberι η '' C) = C := fun C hC => by
    rw [← (f.fiberι η).isEmbedding.closure_eq_preimage_closure_image, hC.closure_eq]
  obtain ⟨Vdisj, hηdisj, hVdisj⟩ :=
    exists_open_fibers_disjoint_of_generic_disjoint f η hη (closure (f.fiberι η '' A))
      (closure (f.fiberι η '' B)) isClosed_closure isClosed_closure
      (by rwa [hpre A hA, hpre B hB])
  refine ⟨VcoverO ⊓ Vdisj,
    ⟨IsGenericPoint.mem_of_isOpen_of_nonempty hη VcoverO.2 hVcoverNe, hηdisj⟩, ?_⟩
  rintro y ⟨hy₁, hy₂⟩
  refine ⟨fun x => ?_, hVdisj y hy₂⟩
  obtain ⟨b, hx⟩ := hVcover y hy₁ x
  cases b with
  | false => exact Or.inl (by simpa [Z] using hx)
  | true => exact Or.inr (by simpa [Z] using hx)

end AlgebraicGeometry

end
