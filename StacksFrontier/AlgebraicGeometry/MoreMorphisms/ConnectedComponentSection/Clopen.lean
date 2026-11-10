module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.GenericComponentClosure

/-!
# The fibrewise component locus is clopen after shrinking

Let `f : X ⟶ Y` be a finite type morphism of schemes with a section `s`, and let `X⁰ ⊆ X` be
the union of the connected components of the fibres meeting the section. Stacks Tag 055N says
that for every `y : Y` there is a nonempty open subset `V` of the closure of `y` such that `X⁰`
is open and closed in the inverse image of `V`.

The proof needs Stacks Tag 055G, which is not yet available in the library, so the results
below take its conclusion as a hypothesis, packaged as
`AlgebraicGeometry.GeometricallyConnectedAfterShrinking`.

## Main definitions

* `AlgebraicGeometry.GeometricallyConnectedAfterShrinking` is the conclusion of Stacks Tag
  055G, packaged as a `Prop`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.exists_open_isClopen_locus_of_geometricallyConnected`
  is Stacks Tag 055N granted that hypothesis.

## Implementation notes

The argument first replaces the target by the reduced induced closed subscheme on the closure
of `y`, which is integral with generic point `y`; the locus is carried along by Tag 055M. Over
an integral base one partitions the generic fibre into the selected component `C` and its
complement, spreads the partition out by Tag 054Y and Tag 02NE, and identifies the trace of
the closure of `C` on each nearby fibre with the selected component of that fibre, using that
the fibres of the closure of `C` stay connected by Tag 055G.

## References

* [Stacks Project, Tag 055N](https://stacks.math.columbia.edu/tag/055N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The conclusion of **Stacks Project, Tag 055G**: a finite type morphism onto an irreducible
base whose fibre over the generic point is geometrically connected has geometrically connected
fibres over a nonempty open subscheme of the base.

This is the one input of Tag 055N which is not yet available in the library, so the results
below take it as a hypothesis. -/
def GeometricallyConnectedAfterShrinking : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IrreducibleSpace Y → LocallyOfFiniteType f →
    QuasiCompact f → ∀ η : Y, IsGenericPoint η Set.univ →
      GeometricallyConnected (f.fiberToSpecResidueField η) →
      ∃ V : Y.Opens, Nonempty V ∧ GeometricallyConnected (f ∣_ V)

namespace ConnectedAlongSection

/-- Granted Tag 055G, the fibres of the closure of the selected generic component are
connected spaces over an open neighbourhood of the generic point. -/
theorem exists_open_connectedSpace_fiber_genericComponentClosure
    (H : GeometricallyConnectedAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    ∃ V : D.Y.Opens, η ∈ V ∧
      ∀ y ∈ V, ConnectedSpace ((D.genericComponentClosure η hη).f.fiber y) := by
  have : PreirreducibleSpace D.Y := ⟨by simpa using hη.isIrreducible.isPreirreducible⟩
  have hirr : IrreducibleSpace D.Y := ⟨⟨η⟩⟩
  let D' := D.genericComponentClosure η hη
  obtain ⟨V, hVne, hVgeom⟩ := H D'.f hirr inferInstance inferInstance η hη
    (D.genericComponentClosure_geometricallyConnected η hη)
  exact ⟨V, IsGenericPoint.mem_of_isOpen_of_nonempty hη V.2 (hVne.elim fun z => ⟨z.1, z.2⟩),
    connectedSpace_fiber_of_geometricallyConnected_restrict D'.f V hVgeom⟩

/-- If over `y` the closures of the selected generic component and of its complement cover and
separate the fibre, and the fibre of the closure of that component is connected, then the
trace of that closure on the fibre over `y` is exactly the selected component of the fibre. -/
theorem fiberι_preimage_closure_eq_fiberComponent
    (D : ConnectedAlongSection.{u}) [LocallyOfFiniteType D.f] [QuasiCompact D.f] [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) (y : D.Y)
    (hcover : ∀ x : D.f.fiber y,
      D.f.fiberι y x ∈ closure (D.f.fiberι η '' D.fiberComponent η) ∨
        D.f.fiberι y x ∈ closure (D.f.fiberι η '' (D.fiberComponent η)ᶜ))
    (hdisj : Disjoint ((D.f.fiberι y) ⁻¹' closure (D.f.fiberι η '' D.fiberComponent η))
      ((D.f.fiberι y) ⁻¹' closure (D.f.fiberι η '' (D.fiberComponent η)ᶜ)))
    (hconn : ConnectedSpace ((D.genericComponentClosure η hη).f.fiber y)) :
    (D.f.fiberι y) ⁻¹' closure (D.f.fiberι η '' D.fiberComponent η) = D.fiberComponent y := by
  set A : Set D.X := closure (D.f.fiberι η '' D.fiberComponent η)
  have hclopen : IsClopen ((D.f.fiberι y) ⁻¹' A) :=
    isClopen_of_isClosed_of_union_univ_of_disjoint _ _
      (isClosed_closure.preimage (D.f.fiberι y).continuous)
      (isClosed_closure.preimage (D.f.fiberι y).continuous)
      (Set.eq_univ_of_forall hcover) hdisj
  have hsection : D.sectionPoint y ∈ (D.f.fiberι y) ⁻¹' A := by
    change D.f.fiberι y (D.sectionPoint y) ∈ A
    rw [D.fiberι_sectionPoint]
    exact D.range_section_subset_closure_image_fiberComponent η hη ⟨y, rfl⟩
  have hconnSet : _root_.IsConnected ((D.f.fiberι y) ⁻¹' A) :=
    isConnected_iff_connectedSpace.mpr
      ((D.genericComponentClosureFiberHomeo η hη y).connectedSpace_iff.mp hconn)
  exact (hconnSet.subset_connectedComponent hsection).antisymm
    (hclopen.connectedComponent_subset hsection)

/-- Granted Tag 055G, over an integral base the locus `X⁰` is open and closed in the inverse
image of an open neighbourhood of the generic point. -/
theorem exists_open_isClopen_locus_of_isGenericPoint
    (H : GeometricallyConnectedAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    ∃ V : D.Y.Opens, η ∈ V ∧
      IsClopen {x : {x : D.X // D.f x ∈ V} | x.1 ∈ D.locus} := by
  have hC : IsClopen (D.fiberComponent η) := D.isClopen_fiberComponent η
  obtain ⟨Vspread, hηspread, hspread⟩ :=
    exists_open_fibers_covered_and_disjoint_by_closures D.f η hη
      (D.fiberComponent η) (D.fiberComponent η)ᶜ hC.1 hC.2.isClosed_compl
      (fun x => by by_cases hx : x ∈ D.fiberComponent η <;> simp [hx]) disjoint_compl_right
  obtain ⟨Vconn, hηconn, hconn⟩ :=
    D.exists_open_connectedSpace_fiber_genericComponentClosure H η hη
  refine ⟨Vspread ⊓ Vconn, ⟨hηspread, hηconn⟩, ?_⟩
  set A : Set D.X := closure (D.f.fiberι η '' D.fiberComponent η)
  set T : Type u := {x : D.X // D.f x ∈ Vspread ⊓ Vconn}
  have hfib (x : T) : ∃ z, ∀ S : Set D.X, z ∈ (D.f.fiberι (D.f x.1)) ⁻¹' S ↔ x.1 ∈ S := by
    obtain ⟨z, hxid⟩ := (D.f.range_fiberι (D.f x.1)).ge rfl
    exact ⟨z, fun S => by rw [Set.mem_preimage, hxid]⟩
  have hkey (x : T) : (x.1 ∈ D.locus ↔ (x.1 : D.X) ∈ A) := by
    obtain ⟨z, hz⟩ := hfib x
    rw [← hz, ← hz, D.fiberι_preimage_locus, D.fiberι_preimage_closure_eq_fiberComponent η hη _
      (hspread _ x.2.1).1 (hspread _ x.2.1).2 (hconn _ x.2.2)]
  rw [show {x : T | x.1 ∈ D.locus} = {x : T | (x.1 : D.X) ∈ A} from Set.ext hkey]
  refine isClopen_of_isClosed_of_union_univ_of_disjoint _ _
    (isClosed_closure.preimage continuous_subtype_val)
    (isClosed_closure (s := D.f.fiberι η '' (D.fiberComponent η)ᶜ).preimage
      continuous_subtype_val) ?_ ?_
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨z, hz⟩ := hfib x
    exact ((hspread _ x.2.1).1 z).imp (hz _).1 (hz _).1
  · refine Set.disjoint_left.mpr fun x hxA hxB => ?_
    obtain ⟨z, hz⟩ := hfib x
    exact Set.disjoint_left.mp (hspread _ x.2.1).2 ((hz _).2 hxA) ((hz _).2 hxB)

/-- **Stacks Project, Tag 055N**, granted the conclusion of Tag 055G. For a finite type
sectioned morphism and any point `y` of the target, there is a nonempty open subset `V` of the
closure of `y` such that the locus `X⁰` is open and closed in the inverse image of `V`. -/
theorem exists_open_isClopen_locus_of_geometricallyConnected
    (H : GeometricallyConnectedAfterShrinking.{u}) (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] (y : D.Y) :
    ∃ V : Opens (↑(closure ({y} : Set D.Y))), Nonempty V ∧
      IsClopen
        {x : {x : D.X // D.f x ∈ Set.range (fun z : V ↦ (z.1.1 : D.Y))} |
          (x.1 : D.X) ∈ D.locus} := by
  set C : Set D.Y := closure ({y} : Set D.Y)
  let I : D.Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, isClosed_closure⟩
  let e : I.subscheme ≃ₜ C :=
    (IsPreimmersion.isEmbedding I.subschemeι).toHomeomorph.trans
      (Homeomorph.setCongr (by
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl))
  have hηQ : IsGenericPoint (⟨y, subset_closure rfl⟩ : C) Set.univ :=
    isGenericPoint_iff_specializes.mpr fun z => (subtype_specializes_iff _ z).trans
      (specializes_iff_mem_closure.trans (iff_of_true z.2 trivial))
  have hη : IsGenericPoint (e.symm ⟨y, subset_closure rfl⟩) Set.univ := by
    simpa using hηQ.image e.symm.continuous
  let D' := D.baseChange I.subschemeι
  have : LocallyOfFiniteType D'.f :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd D.f I.subschemeι))
  have : QuasiCompact D'.f := inferInstanceAs (QuasiCompact (pullback.snd D.f I.subschemeι))
  have : IsReduced D'.Y :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal ⟨C, isClosed_closure⟩
  obtain ⟨W, hηW, hW⟩ := D'.exists_open_isClopen_locus_of_isGenericPoint H _ hη
  refine ⟨Opens.comap ⟨e.symm, e.symm.continuous⟩ W, ⟨⟨⟨y, subset_closure rfl⟩, hηW⟩⟩, ?_⟩
  have hR : Set.range (fun z : Opens.comap ⟨e.symm, e.symm.continuous⟩ W ↦ (z.1.1 : D.Y)) =
      I.subschemeι '' (W : Set D'.Y) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z.1, z.2, congrArg Subtype.val (e.apply_symm_apply z.1)⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨e w, by
        change e.symm (e w) ∈ W
        rwa [e.symm_apply_apply]⟩, rfl⟩
  rw [hR]
  let K : {p : ↥(pullback D.f I.subschemeι) // pullback.snd D.f I.subschemeι p ∈ (W : Set D'.Y)} ≃ₜ
      {x : D.X // D.f x ∈ I.subschemeι '' (W : Set D'.Y)} :=
    Topology.IsEmbedding.toHomeomorphOfSurjective
      (f := fun p ↦ ⟨pullback.fst D.f I.subschemeι p.1, pullback.snd D.f I.subschemeι p.1, p.2,
        by rw [← Scheme.Hom.comp_apply (pullback.snd D.f I.subschemeι) I.subschemeι,
          ← pullback.condition, Scheme.Hom.comp_apply]⟩)
      (Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
        ((IsPreimmersion.isEmbedding (pullback.fst D.f I.subschemeι)).comp .subtypeVal))
      fun x => by
        obtain ⟨w, hw, hx⟩ := x.2
        obtain ⟨p, hfst, hsnd⟩ :=
          Scheme.Pullback.exists_preimage_pullback (f := D.f) (g := I.subschemeι) x.1 w hx.symm
        exact ⟨⟨p, by rwa [hsnd]⟩, Subtype.ext hfst⟩
  have hpre : K ⁻¹' {x | (x.1 : D.X) ∈ D.locus} = {p | (p.1 : D'.X) ∈ D'.locus} := by
    ext p
    change pullback.fst D.f I.subschemeι p.1 ∈ D.locus ↔ p.1 ∈ D'.locus
    rw [D.locus_baseChange]
    rfl
  have hK : IsClopen (K ⁻¹' {x | (x.1 : D.X) ∈ D.locus}) := by rwa [hpre]
  exact ⟨K.isClosed_preimage.mp hK.1, K.isOpen_preimage.mp hK.2⟩

end ConnectedAlongSection

end AlgebraicGeometry

end
