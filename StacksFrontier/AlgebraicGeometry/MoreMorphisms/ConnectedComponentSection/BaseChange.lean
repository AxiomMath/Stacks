module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Connected.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint

/-!
# Connected components along a section and base change

For a morphism of schemes equipped with a section, the union of the fibrewise connected
components containing the section is preserved by arbitrary base change: in a cartesian square
of sectioned morphisms with compatible sections, the locus upstairs is the inverse image of the
locus downstairs.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.locus_eq_preimage_of_isPullback`: the distinguished
  locus of a base change is the inverse image of the original distinguished locus.

## Implementation notes

The base change is presented by an arbitrary pullback square; the hypothesis on the sections
records that the section upstairs is the one induced by the square, so the statement does not
depend on a chosen pullback object.

The proof reduces to the case of a scheme over a field with a rational point. There the
connected component of the rational point is stable under generalization, so it carries a flat
closed subscheme structure; such a subscheme is connected with a rational point, hence
*geometrically* connected, and geometric connectedness is stable under base change. That gives
the inclusion of the inverse image of the component in the component upstairs, and continuity of
the horizontal map gives the reverse inclusion. The general case follows by applying this to the
fibre squares, whose comparison maps are the base-change maps of fibres.

## References

* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- A connected component is stable under generalization. -/
private theorem connectedComponent_stableUnderGeneralization
    {X : Type u} [TopologicalSpace X] (x : X) :
    StableUnderGeneralization (connectedComponent x) := by
  intro a b hba ha
  rw [← connectedComponent_eq_iff_mem.mpr ha]
  exact isConnected_singleton.closure.subset_connectedComponent
    (specializes_iff_mem_closure.mp hba) (subset_closure rfl)

/-- The connected component of a point of a scheme carries a flat closed subscheme
structure. -/
private theorem exists_flat_closed_subscheme_of_connectedComponent
    {X : Scheme.{u}} (x : X) :
    ∃ I : X.IdealSheafData, Flat I.subschemeι ∧
      I.support = ⟨connectedComponent x, isClosed_connectedComponent⟩ :=
  (support_bijOn_flat_closedImmersions X).surjOn (connectedComponent_stableUnderGeneralization x)

/-- A closed subscheme supported on a connected component is a connected scheme. -/
private theorem connectedSpace_of_flat_connectedComponent
    {X : Scheme.{u}} (x : X) (I : X.IdealSheafData)
    (_hflat : Flat I.subschemeι)
    (hI : I.support = ⟨connectedComponent x, isClosed_connectedComponent⟩) :
    ConnectedSpace I.subscheme := by
  have hrange : Set.range I.subschemeι = connectedComponent x := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI]
    rfl
  have : Nonempty I.subscheme := Set.range_nonempty_iff_nonempty.mp <| by
    rw [hrange]
    exact connectedComponent_nonempty
  refine connectedSpace_iff_univ.mpr ⟨Set.univ_nonempty, ?_⟩
  refine (IsClosedImmersion.isClosedEmbedding
    I.subschemeι).isEmbedding.isInducing.isPreconnected_image.mp ?_
  rw [Set.image_univ, hrange]
  exact isConnected_connectedComponent.2

/-- The image of a point of the spectrum of a field lies in the connected component of the
image of its unique point. -/
private theorem range_subset_connectedComponent_of_field {k : Type u} [Field k]
    {X : Scheme.{u}} (s : Spec (.of k) ⟶ X) (z : Spec (.of k)) :
    Set.range s ⊆ connectedComponent (s z) := by
  rintro y ⟨w, rfl⟩
  obtain rfl : w = z := Subsingleton.elim _ _
  exact mem_connectedComponent

/-- For a scheme over a field with a section, the connected component of the rational point
carries a flat closed subscheme structure which is geometrically connected over the field. -/
@[ega "IV 4.5.14" "special case",
  ega "IV 4.5.15" "special case",
  ega "IV 4.5.21" "partial",
  sga "3 VIB 3.3" "more general"]
private theorem geometricallyConnected_flat_connectedComponent
    {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X)
    (hs : s ≫ p = 𝟙 _) :
    ∃ (I : X.IdealSheafData), Flat I.subschemeι ∧
      I.support = ⟨connectedComponent (s (Classical.choice inferInstance)),
        isClosed_connectedComponent⟩ ∧
      GeometricallyConnected (I.subschemeι ≫ p) := by
  let z : Spec (.of k) := Classical.choice inferInstance
  let x : X := s z
  obtain ⟨I, hflat, hI⟩ := exists_flat_closed_subscheme_of_connectedComponent x
  obtain ⟨sI, hfac⟩ :=
    (existsUnique_lift_of_flat_closedImmersion I s (by
      rw [hI]
      exact range_subset_connectedComponent_of_field s z)).exists
  have : ConnectedSpace I.subscheme := connectedSpace_of_flat_connectedComponent x I hflat hI
  exact ⟨I, hflat, hI, geometricallyConnected_of_connectedSpace_of_section (I.subschemeι ≫ p) sI
    (by rw [← Category.assoc, hfac, hs])⟩

/-- In a cartesian square of schemes over fields with compatible rational points, the connected
component of the rational point upstairs is the inverse image of the one downstairs. -/
private theorem connectedComponent_preimage_of_isPullback_over_fields
    {k K : Type u} [Field k] [Field K]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (q : Y ⟶ Spec (.of K)) (a : Y ⟶ X) (b : Spec (.of K) ⟶ Spec (.of k))
    (h : IsPullback a q p b)
    (s : Spec (.of k) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (t : Spec (.of K) ⟶ Y) (_ht : t ≫ q = 𝟙 _)
    (hcompat : t ≫ a = b ≫ s) :
    a ⁻¹' connectedComponent (s (Classical.choice inferInstance)) =
      connectedComponent (t (Classical.choice inferInstance)) := by
  let zₖ : Spec (.of k) := Classical.choice inferInstance
  let zK : Spec (.of K) := Classical.choice inferInstance
  let x : X := s zₖ
  let y : Y := t zK
  have hax : a y = x := by
    simpa [Scheme.Hom.comp_apply, x, y, zₖ, zK, Subsingleton.elim (b zK) zₖ] using
      congrArg (fun m : Spec (.of K) ⟶ X => m zK) hcompat
  obtain ⟨I, hflat, hI, hgc⟩ :=
    geometricallyConnected_flat_connectedComponent p s hs
  obtain ⟨sI, hfac⟩ :=
    (existsUnique_lift_of_flat_closedImmersion I s (by
      rw [hI]
      exact range_subset_connectedComponent_of_field s zₖ)).exists
  let P := pullback I.subschemeι a
  let j : P ⟶ Y := pullback.snd I.subschemeι a
  have : GeometricallyConnected (j ≫ q) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback I.subschemeι a).paste_vert h) hgc
  have : ConnectedSpace P :=
    GeometricallyConnected.connectedSpace_of_subsingleton (j ≫ q)
  let l : Spec (.of K) ⟶ P :=
    pullback.lift (b ≫ sI) t (by rw [Category.assoc, hfac, hcompat])
  have hmem : y ∈ Set.range j := ⟨l zK, by
    have h := congrArg (fun m : Spec (.of K) ⟶ Y => m zK) (pullback.lift_snd _ _ _ : l ≫ j = t)
    simp only [Scheme.Hom.comp_apply] at h
    exact h⟩
  have hrange : Set.range j = a ⁻¹' connectedComponent x := by
    rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι, hI]
    rfl
  refine Set.Subset.antisymm ?_ <| Set.image_subset_iff.mp <|
    (isConnected_connectedComponent.image a a.continuous.continuousOn).subset_connectedComponent
      ⟨y, mem_connectedComponent, hax⟩
  rw [← hrange]
  exact (isConnected_range j.continuous).subset_connectedComponent hmem

/-- The section, read as a morphism from the residue field into the fibre. -/
private noncomputable def sectionOverFiberPoint
    (D : ConnectedAlongSection.{u}) (y : D.Y) :
    Spec (D.Y.residueField y) ⟶ D.f.fiber y :=
  pullback.lift (D.Y.fromSpecResidueField y ≫ D.s) (𝟙 _)
    (by simp [Category.assoc, D.section_fac])

private theorem sectionOverFiberPoint_fac
    (D : ConnectedAlongSection.{u}) (y : D.Y) :
    sectionOverFiberPoint D y ≫ D.f.fiberToSpecResidueField y = 𝟙 _ :=
  pullback.lift_snd _ _ _

private theorem sectionOverFiberPoint_fiberι
    (D : ConnectedAlongSection.{u}) (y : D.Y) :
    sectionOverFiberPoint D y ≫ D.f.fiberι y = D.Y.fromSpecResidueField y ≫ D.s :=
  pullback.lift_fst _ _ _

private theorem sectionPoint_eq_sectionOverFiberPoint
    (D : ConnectedAlongSection.{u}) (y : D.Y) :
    D.sectionPoint y = sectionOverFiberPoint D y (Classical.choice inferInstance) := by
  apply (D.f.fiberι y).isEmbedding.injective
  rw [D.fiberι_sectionPoint]
  change (TopCat.Hom.hom D.s.base) y = (D.f.fiberι y)
    (sectionOverFiberPoint D y (Classical.choice inferInstance))
  calc
    (TopCat.Hom.hom D.s.base) y =
        (D.Y.fromSpecResidueField y ≫ D.s) (Classical.choice inferInstance) := by
      simp [Scheme.fromSpecResidueField_apply]
    _ = (sectionOverFiberPoint D y ≫ D.f.fiberι y)
          (Classical.choice inferInstance) :=
      congrArg (fun m : Spec (D.Y.residueField y) ⟶ D.X =>
        m (Classical.choice inferInstance)) (sectionOverFiberPoint_fiberι D y).symm
    _ = D.f.fiberι y (sectionOverFiberPoint D y (Classical.choice inferInstance)) := by
      simp

/-- The comparison map between the fibres of two sides of a cartesian square. -/
private noncomputable def fiberBaseChangeMap
    (D D' : ConnectedAlongSection.{u})
    (g' : D'.X ⟶ D.X) (g : D'.Y ⟶ D.Y)
    (h : IsPullback g' D'.f D.f g)
    (y' : D'.Y) : D'.f.fiber y' ⟶ D.f.fiber (g y') :=
  pullback.map D'.f (D'.Y.fromSpecResidueField y') D.f
    (D.Y.fromSpecResidueField (g y')) g'
    (Spec.map (g.residueFieldMap y')) g
    (by simpa using h.w.symm)
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g y').symm

private theorem fiberBaseChangeMap_fiberι
    (D D' : ConnectedAlongSection.{u})
    (g' : D'.X ⟶ D.X) (g : D'.Y ⟶ D.Y)
    (h : IsPullback g' D'.f D.f g) (y' : D'.Y) :
    fiberBaseChangeMap D D' g' g h y' ≫ D.f.fiberι (g y') =
      D'.f.fiberι y' ≫ g' :=
  pullback.lift_fst _ _ _

private theorem fiberBaseChangeMap_fiberToSpecResidueField
    (D D' : ConnectedAlongSection.{u})
    (g' : D'.X ⟶ D.X) (g : D'.Y ⟶ D.Y)
    (h : IsPullback g' D'.f D.f g) (y' : D'.Y) :
    fiberBaseChangeMap D D' g' g h y' ≫ D.f.fiberToSpecResidueField (g y') =
      D'.f.fiberToSpecResidueField y' ≫ Spec.map (g.residueFieldMap y') :=
  pullback.lift_snd _ _ _

private theorem sectionOverFiberPoint_comp_fiberBaseChangeMap
    (D D' : ConnectedAlongSection.{u})
    (g' : D'.X ⟶ D.X) (g : D'.Y ⟶ D.Y)
    (h : IsPullback g' D'.f D.f g)
    (hs : D'.s ≫ g' = g ≫ D.s) (y' : D'.Y) :
    sectionOverFiberPoint D' y' ≫ fiberBaseChangeMap D D' g' g h y' =
      Spec.map (g.residueFieldMap y') ≫ sectionOverFiberPoint D (g y') := by
  apply pullback.hom_ext
  · calc
      (sectionOverFiberPoint D' y' ≫ fiberBaseChangeMap D D' g' g h y') ≫
            D.f.fiberι (g y')
          = (sectionOverFiberPoint D' y' ≫ D'.f.fiberι y') ≫ g' := by
        rw [Category.assoc, fiberBaseChangeMap_fiberι, ← Category.assoc]
      _ = D'.Y.fromSpecResidueField y' ≫ (D'.s ≫ g') := by
        rw [sectionOverFiberPoint_fiberι, Category.assoc]
      _ = (Spec.map (g.residueFieldMap y') ≫ D.Y.fromSpecResidueField (g y')) ≫ D.s := by
        rw [hs, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
      _ = (Spec.map (g.residueFieldMap y') ≫ sectionOverFiberPoint D (g y')) ≫
            D.f.fiberι (g y') := by
        rw [Category.assoc, Category.assoc, sectionOverFiberPoint_fiberι]
  · calc
      (sectionOverFiberPoint D' y' ≫ fiberBaseChangeMap D D' g' g h y') ≫
            D.f.fiberToSpecResidueField (g y')
          = (sectionOverFiberPoint D' y' ≫ D'.f.fiberToSpecResidueField y') ≫
            Spec.map (g.residueFieldMap y') := by
        rw [Category.assoc, fiberBaseChangeMap_fiberToSpecResidueField, ← Category.assoc]
      _ = Spec.map (g.residueFieldMap y') := by
        rw [sectionOverFiberPoint_fac, Category.id_comp]
      _ = (Spec.map (g.residueFieldMap y') ≫ sectionOverFiberPoint D (g y')) ≫
            D.f.fiberToSpecResidueField (g y') := by
        rw [Category.assoc, sectionOverFiberPoint_fac, Category.comp_id]

private theorem fiberComponent_preimage
    (D D' : ConnectedAlongSection.{u})
    (g' : D'.X ⟶ D.X) (g : D'.Y ⟶ D.Y)
    (h : IsPullback g' D'.f D.f g)
    (hs : D'.s ≫ g' = g ≫ D.s) (y' : D'.Y) :
    (fiberBaseChangeMap D D' g' g h y') ⁻¹' D.fiberComponent (g y') =
      D'.fiberComponent y' := by
  change (fiberBaseChangeMap D D' g' g h y') ⁻¹'
      connectedComponent (D.sectionPoint (g y')) =
    connectedComponent (D'.sectionPoint y')
  rw [sectionPoint_eq_sectionOverFiberPoint D (g y'),
    sectionPoint_eq_sectionOverFiberPoint D' y']
  exact connectedComponent_preimage_of_isPullback_over_fields
    (D.f.fiberToSpecResidueField (g y')) (D'.f.fiberToSpecResidueField y')
    (fiberBaseChangeMap D D' g' g h y') (Spec.map (g.residueFieldMap y'))
    (isPullback_fiberToSpecResidueField_of_isPullback h y') (sectionOverFiberPoint D (g y'))
    (sectionOverFiberPoint_fac D (g y')) (sectionOverFiberPoint D' y')
    (sectionOverFiberPoint_fac D' y')
    (sectionOverFiberPoint_comp_fiberBaseChangeMap D D' g' g h hs y')

/-- **Stacks Project, Tag 055M.** In a cartesian square of sectioned morphisms, where the
sections are compatible with the horizontal maps, the union of the connected components of
the fibres containing the section pulls back to the corresponding union upstairs. -/
@[stacks 055M]
theorem locus_eq_preimage_of_isPullback
    (D D' : ConnectedAlongSection.{u})
    (g' : D'.X ⟶ D.X) (g : D'.Y ⟶ D.Y)
    (h : IsPullback g' D'.f D.f g)
    (hs : D'.s ≫ g' = g ≫ D.s) :
    D'.locus = g' ⁻¹' D.locus := by
  ext x
  let y' := D'.f x
  let a := fiberBaseChangeMap D D' g' g h y'
  have hm : D.f.fiberι (g y') (a (D'.f.asFiber x)) = g' x := by
    simpa [a, y', Scheme.Hom.comp_apply, D'.f.fiberι_asFiber] using
      congrArg (fun m : D'.f.fiber y' ⟶ D.X => m (D'.f.asFiber x))
        (fiberBaseChangeMap_fiberι D D' g' g h y')
  calc
    x ∈ D'.locus ↔ D'.f.asFiber x ∈ D'.fiberComponent y' := by
      rw [← fiberι_preimage_locus]
      simp [y', D'.f.fiberι_asFiber]
    _ ↔ a (D'.f.asFiber x) ∈ D.fiberComponent (g y') := by
      rw [← fiberComponent_preimage D D' g' g h hs y']
      rfl
    _ ↔ g' x ∈ D.locus := by
      rw [← fiberι_preimage_locus D (g y')]
      simp only [Set.mem_preimage, hm]

end ConnectedAlongSection

end AlgebraicGeometry

end
