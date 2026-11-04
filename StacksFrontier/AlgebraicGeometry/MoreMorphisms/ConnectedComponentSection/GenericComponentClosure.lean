module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closure of the generic component as a sectioned morphism

Let `D` be a morphism `f : X ⟶ Y` with a section `s`, let `η : Y` be a generic point of `Y`
and let `C = X⁰_η` be the connected component of the generic fibre selected by the section.
The closure `A` of the image of `C` in `X`, with its reduced induced closed subscheme
structure, again carries a section of its morphism to `Y`, and its fibre over `η` is `C`,
which is connected. Since that fibre has a rational point, it is even geometrically connected.

## Main definitions

* `AlgebraicGeometry.ConnectedAlongSection.baseChange` is the base change of a sectioned
  morphism along an arbitrary morphism to the target.
* `AlgebraicGeometry.ConnectedAlongSection.genericComponentClosure` is the sectioned morphism
  obtained by restricting the source to the closure of the selected component of the generic
  fibre.

## Main results

* `AlgebraicGeometry.idealSheafFiberHomeo` identifies the fibre of a closed subscheme over a
  point of `Y` with the trace of that subscheme on the fibre of `f`.
* `AlgebraicGeometry.ConnectedAlongSection.genericComponentClosure_geometricallyConnected`:
  the generic fibre of `genericComponentClosure` is geometrically connected.
* `AlgebraicGeometry.connectedSpace_fiber_of_geometricallyConnected_restrict`: if the
  restriction of a morphism over an open subscheme has geometrically connected fibres, then
  each of its fibres is a connected space.

## Implementation notes

The closed subscheme structure used throughout is the reduced induced one, obtained as
`Scheme.IdealSheafData.vanishingIdeal`. The section lifts to it by the factorization criterion
of Tag 0356, which needs the target to be reduced; this is why Tag 055N first replaces the
target by the reduced induced subscheme on the closure of the given point.

## References

* [Stacks Project, Tag 055N](https://stacks.math.columbia.edu/tag/055N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The fibre over `y` of the composite `I.subscheme ⟶ X ⟶ Y` is homeomorphic to the trace on
the fibre of `f` of the image of `I.subscheme` in `X`. -/
noncomputable def idealSheafFiberHomeo {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData)
    (y : Y) :
    (I.subschemeι ≫ f).fiber y ≃ₜ
      {z : f.fiber y // f.fiberι y z ∈ Set.range I.subschemeι} := by
  let g : I.subscheme ⟶ Y := I.subschemeι ≫ f
  let q : g.fiber y → f.fiber y := fun z =>
    (f.fiberHomeo y).symm ⟨I.subschemeι ((g.fiberHomeo y) z).1, by
      have hz := (g.fiberHomeo y z).2
      change g ((g.fiberHomeo y z).1) = y at hz
      simpa [g] using hz⟩
  let m : g.fiber y → X := fun z => I.subschemeι (g.fiberι y z)
  have hmq (z : g.fiber y) : f.fiberι y (q z) = m z := by
    simp [q, m, Scheme.Hom.fiberι_fiberHomeo_symm]
  have hpre : g ⁻¹' ({y} : Set Y) = I.subschemeι ⁻¹' Set.range (f.fiberι y) := by
    ext z
    change f (I.subschemeι z) = y ↔ I.subschemeι z ∈ Set.range (f.fiberι y)
    rw [f.range_fiberι]
    rfl
  have hRangeM : Set.range m =
      Set.range (f.fiberι y) ∩ Set.range I.subschemeι := by
    calc
      Set.range m = I.subschemeι '' (g ⁻¹' {y}) := by
        change Set.range (I.subschemeι ∘ g.fiberι y) = _
        rw [Set.range_comp, g.range_fiberι]
      _ = I.subschemeι '' (I.subschemeι ⁻¹' Set.range (f.fiberι y)) := by rw [hpre]
      _ = Set.range (f.fiberι y) ∩ Set.range I.subschemeι :=
        Set.image_preimage_eq_inter_range
  have hmEmbed : Topology.IsEmbedding m :=
    (IsPreimmersion.isEmbedding I.subschemeι).comp (g.fiberι y).isEmbedding
  have hfq : ⇑(f.fiberι y) ∘ q = m := funext hmq
  have hqEmbed : Topology.IsEmbedding q := by
    refine (f.fiberι y).isEmbedding.of_comp_iff.mp ?_
    rwa [hfq]
  have hRangeQ : Set.range q = (f.fiberι y) ⁻¹' Set.range I.subschemeι := by
    rw [← (f.fiberι y).isEmbedding.injective.preimage_image (Set.range q), ← Set.range_comp,
      hfq, hRangeM, Set.preimage_inter, Set.preimage_range, Set.univ_inter]
  exact ((Homeomorph.Set.univ (g.fiber y)).symm.trans
    (Homeomorph.setCongr (Set.preimage_range q)).symm).trans
    ((hqEmbed.homeomorphOfSubsetRange (s := Set.range q) Set.Subset.rfl).trans
      (Homeomorph.setCongr hRangeQ))

/-- If the restriction of `f` over an open subscheme `V` has geometrically connected fibres,
then the fibre of `f` over any point of `V` is a connected space. -/
theorem connectedSpace_fiber_of_geometricallyConnected_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hV : GeometricallyConnected (f ∣_ V)) (y : Y) (hy : y ∈ V) :
    ConnectedSpace (f.fiber y) := by
  let p : pullback f V.ι ⟶ V.toScheme := pullback.snd f V.ι
  have hp := isPullback_morphismRestrict f V
  let he : Arrow.mk (f ∣_ V) ≅ Arrow.mk p :=
    Arrow.isoMk hp.flip.isoPullback (Iso.refl _) hp.flip.isoPullback_hom_snd
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hpGeom : GeometricallyConnected p :=
    (MorphismProperty.arrow_mk_iso_iff
      (P := show MorphismProperty Scheme from @GeometricallyConnected) he).mp hV
  let y' : V := ⟨y, hy⟩
  have : GeometricallyConnected (f.fiberToSpecResidueField y) := by
    have hmem : y' ∈ {z | GeometricallyConnected (p.fiberToSpecResidueField z)} :=
      (GeometricallyConnected.iff_geometricallyConnected_fiber (f := p)).mp hpGeom y'
    rwa [geometricallyConnected_fiber_locus_pullback] at hmem
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := f.fiberToSpecResidueField y)

namespace ConnectedAlongSection

/-- The base change of a sectioned morphism along an arbitrary morphism `g : Z ⟶ Y`. -/
noncomputable def baseChange {Z : Scheme.{u}} (D : ConnectedAlongSection.{u}) (g : Z ⟶ D.Y) :
    ConnectedAlongSection.{u} where
  X := pullback D.f g
  Y := Z
  f := pullback.snd D.f g
  s := pullback.lift (g ≫ D.s) (𝟙 Z) (by simp [D.section_fac])
  section_fac := pullback.lift_snd _ _ _

/-- The locus `X⁰` of a base change is the preimage of the locus of the original morphism. -/
@[sga "3 VIB 4.2" "more general"]
theorem locus_baseChange {Z : Scheme.{u}} (D : ConnectedAlongSection.{u}) (g : Z ⟶ D.Y) :
    (D.baseChange g).locus = (pullback.fst D.f g) ⁻¹' D.locus :=
  locus_eq_preimage_of_isPullback D (D.baseChange g) (pullback.fst D.f g) g
    (IsPullback.of_hasPullback D.f g) (pullback.lift_fst _ _ _)

/-- The section of a sectioned morphism with reduced target lands in the closure of the image
of the selected component of the generic fibre. -/
theorem range_section_subset_closure_image_fiberComponent
    (D : ConnectedAlongSection.{u}) (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    Set.range D.s ⊆ closure (D.f.fiberι η '' D.fiberComponent η) := by
  rintro x ⟨y, rfl⟩
  have hηA : D.s η ∈ D.f.fiberι η '' D.fiberComponent η := by
    rw [← D.fiberι_sectionPoint]
    exact ⟨D.sectionPoint η, D.sectionPoint_mem_fiberComponent η, rfl⟩
  have hyη : y ∈ closure ({η} : Set D.Y) := by rw [hη.def]; exact Set.mem_univ y
  have hsclose : D.s y ∈ closure (D.s '' ({η} : Set D.Y)) :=
    image_closure_subset_closure_image (s := ({η} : Set D.Y)) D.s.continuous ⟨y, hyη, rfl⟩
  rw [Set.image_singleton] at hsclose
  exact closure_mono (Set.singleton_subset_iff.mpr hηA) hsclose

/-- The reduced induced closed subscheme of `X` on the closure of the image of the selected
component of the generic fibre, as the source of a sectioned morphism to `Y`. -/
noncomputable def genericComponentClosure (D : ConnectedAlongSection.{u}) [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) : ConnectedAlongSection.{u} :=
  let I : D.X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (D.f.fiberι η '' D.fiberComponent η), isClosed_closure⟩
  let hlift : ∃ s' : D.Y ⟶ I.subscheme, s' ≫ I.subschemeι = D.s :=
    (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support I D.s).2 (by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact range_section_subset_closure_image_fiberComponent D η hη)
  { X := I.subscheme
    Y := D.Y
    f := I.subschemeι ≫ D.f
    s := Classical.choose hlift
    section_fac := by rw [← Category.assoc, Classical.choose_spec hlift, D.section_fac] }

/-- The ideal sheaf data cutting out the source of `genericComponentClosure`: the reduced
induced structure on the closure of the image of the selected generic component. -/
noncomputable def genericComponentClosureIdeal (D : ConnectedAlongSection.{u}) (η : D.Y) :
    D.X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (D.f.fiberι η '' D.fiberComponent η), isClosed_closure⟩

/-- The image in `X` of the closed subscheme cut out by `genericComponentClosureIdeal`. -/
theorem range_genericComponentClosureIdeal (D : ConnectedAlongSection.{u}) (η : D.Y) :
    Set.range (D.genericComponentClosureIdeal η).subschemeι =
      closure (D.f.fiberι η '' D.fiberComponent η) := by
  rw [Scheme.IdealSheafData.range_subschemeι,
    genericComponentClosureIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The morphism of `genericComponentClosure` is the composite of the closed immersion cutting
out the closure of the generic component with `f`. -/
theorem genericComponentClosure_f (D : ConnectedAlongSection.{u}) [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    (D.genericComponentClosure η hη).f =
      (D.genericComponentClosureIdeal η).subschemeι ≫ D.f := rfl

/-- If `f` is locally of finite type, then so is the morphism of `genericComponentClosure`. -/
instance genericComponentClosure_locallyOfFiniteType (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [IsReduced D.Y] (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    LocallyOfFiniteType (D.genericComponentClosure η hη).f :=
  inferInstanceAs
    (LocallyOfFiniteType ((D.genericComponentClosureIdeal η).subschemeι ≫ D.f))

/-- If `f` is quasi-compact, then so is the morphism of `genericComponentClosure`. -/
instance genericComponentClosure_quasiCompact (D : ConnectedAlongSection.{u})
    [QuasiCompact D.f] [IsReduced D.Y] (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    QuasiCompact (D.genericComponentClosure η hη).f :=
  inferInstanceAs (QuasiCompact ((D.genericComponentClosureIdeal η).subschemeι ≫ D.f))

/-- The fibre of `genericComponentClosure` over `y` is homeomorphic to the trace on the fibre
of `f` over `y` of the closure of the image of the selected component of the generic fibre. -/
noncomputable def genericComponentClosureFiberHomeo (D : ConnectedAlongSection.{u})
    [IsReduced D.Y] (η : D.Y) (hη : IsGenericPoint η Set.univ) (y : D.Y) :
    (D.genericComponentClosure η hη).f.fiber y ≃ₜ
      {z : D.f.fiber y //
        D.f.fiberι y z ∈ closure (D.f.fiberι η '' D.fiberComponent η)} :=
  (idealSheafFiberHomeo D.f (D.genericComponentClosureIdeal η) y).trans
    (Homeomorph.setCongr (by rw [range_genericComponentClosureIdeal]))

/-- The section of a sectioned morphism induces a rational point of the fibre over `η`. -/
noncomputable def fiberSection (D : ConnectedAlongSection.{u}) (η : D.Y) :
    Spec (.of (D.Y.residueField η)) ⟶ D.f.fiber η :=
  pullback.lift (D.Y.fromSpecResidueField η ≫ D.s) (𝟙 _) (by simp [D.section_fac])

/-- `fiberSection` is a section of the projection of the fibre over `η` to the spectrum of the
residue field at `η`. -/
theorem fiberSection_fac (D : ConnectedAlongSection.{u}) (η : D.Y) :
    D.fiberSection η ≫ D.f.fiberToSpecResidueField η = 𝟙 _ := by
  dsimp only [fiberSection, Scheme.Hom.fiberToSpecResidueField]
  exact pullback.lift_snd _ _ _

/-- The generic fibre of `genericComponentClosure` is a connected space: it is homeomorphic to
the selected connected component of the generic fibre of `f`. -/
theorem genericComponentClosure_connectedSpace (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    ConnectedSpace ((D.genericComponentClosure η hη).f.fiber η) := by
  have hpreA : (D.f.fiberι η) ⁻¹' closure (D.f.fiberι η '' D.fiberComponent η) =
      D.fiberComponent η := by
    rw [← (D.f.fiberι η).isEmbedding.closure_eq_preimage_closure_image]
    exact (D.isClopen_fiberComponent η).1.closure_eq
  have hCconn : _root_.IsConnected (D.fiberComponent η) := by
    simpa [fiberComponent] using isConnected_connectedComponent (x := D.sectionPoint η)
  exact ((D.genericComponentClosureFiberHomeo η hη η).trans
    (Homeomorph.setCongr hpreA)).connectedSpace_iff.mpr (Subtype.connectedSpace hCconn)

/-- The generic fibre of `genericComponentClosure` is geometrically connected: it is connected
and carries a rational point supplied by the section. -/
theorem genericComponentClosure_geometricallyConnected (D : ConnectedAlongSection.{u})
    [LocallyOfFiniteType D.f] [QuasiCompact D.f] [IsReduced D.Y]
    (η : D.Y) (hη : IsGenericPoint η Set.univ) :
    GeometricallyConnected
      ((D.genericComponentClosure η hη).f.fiberToSpecResidueField η) := by
  let D' := D.genericComponentClosure η hη
  have : ConnectedSpace (D'.f.fiber η) := D.genericComponentClosure_connectedSpace η hη
  exact geometricallyConnected_of_connectedSpace_of_section
    (D'.f.fiberToSpecResidueField η) (D'.fiberSection η) (D'.fiberSection_fac η)

end ConnectedAlongSection

end AlgebraicGeometry

end
