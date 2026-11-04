module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SinglePointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# The residue-field point of a chosen neighborhood is a residual space

For a `ClosedPointNeighborhoods` datum `D` and an index `i`, the canonical morphism
`Spec κ(uᵢ) ⟶ X` from the residue-field point of the distinguished point of the `i`th chosen
neighborhood is a residual space of `X` at the chosen point `xᵢ`: it is a monomorphism from a
reduced, locally Noetherian algebraic space with exactly one point, and that point lies above
`xᵢ`.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isResidualSpaceAt_residualToSpace`: the
  morphism `Spec κ(uᵢ) ⟶ X` is a residual space of `X` at `xᵢ`.

## Implementation notes

Every clause is read off the datum: the source is the spectrum of a field, which supplies
reducedness and local Noetherianity through
`AlgebraicGeometry.Space.hasEtaleLocalProperty_of_representable`; monicity is the
`mono_residueField` field of the chosen elementary étale neighborhood; and the point above
`xᵢ` is its `map_point` field. In particular no choice is made from an existential, and no
local Noetherianity of `X` is assumed.

The two point-set clauses — that `Spec κ(uᵢ)` has exactly one point, and that this point lies
above `xᵢ` — are
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.subsingleton_points_residualObject`,
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.nonempty_points_residualObject` and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.pointsMap_residualToSpace` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationsAtClosedPointsResidualSubspace.lean`, where
the residue-field point and its two canonical morphisms are defined.

Nothing here is a statement of the Stacks project in its own right, so nothing carries a tag:
it is infrastructure inside the instantiation of Stacks 0BGY used by Stacks 0BHB.

## References

* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace ClosedPointNeighborhoods

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {n : ℕ}
    (D : ClosedPointNeighborhoods B S hS n)

/-- Precomposing a closed immersion of algebraic spaces with an isomorphism gives a closed
immersion. -/
private theorem isClosedImmersion_comp_of_isIso {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X ⟶ Y) [IsIso g] {f : Y ⟶ Z} (hf : IsClosedImmersion B S hS f) :
    IsClosedImmersion B S hS (g ≫ f) := by
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g _ hf

/-- The canonical morphism `Spec κ(uᵢ) ⟶ X` is étale-locally reduced on its source. -/
private theorem hasEtaleLocalProperty_isReduced_residualObject (i : Fin n) :
    HasEtaleLocalProperty B S hS (yoneda.obj (D.residualObject i))
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_of_representable B S hS (yoneda.obj (D.residualObject i))
    (fun Y : Scheme.{u} => IsReduced Y) (D.residualObject i) (Iso.refl _)
    (inferInstanceAs (IsReduced
      (Spec (.of ((D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point)))))

/-- **The residue-field point of the distinguished point of the `i`th chosen neighborhood is a
residual space of the space at the `i`th chosen point.** The morphism `Spec κ(uᵢ) ⟶ X` is a
monomorphism from a reduced, locally Noetherian algebraic space with exactly one point, and
that point lies above `xᵢ`. -/
theorem isResidualSpaceAt_residualToSpace (i : Fin n) :
    IsResidualSpaceAt B S hS D.space.obj (D.point i) (D.residualToSpace i) :=
  ⟨isAlgebraicSpace_yoneda B S hS _, (D.neighborhood i).mono_residueField,
    D.hasEtaleLocalProperty_isReduced_residualObject i,
    hasEtaleLocalProperty_of_representable B S hS (yoneda.obj (D.residualObject i))
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y) (D.residualObject i) (Iso.refl _)
      (inferInstanceAs (IsLocallyNoetherian
        (Spec (.of ((D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point))))),
    D.nonempty_points_residualObject i, D.subsingleton_points_residualObject i,
    D.pointsMap_residualToSpace i⟩

/-- The reduced closed subspace of the space on the `i`th chosen point. -/
private abbrev reducedPointSubspace (i : Fin n) : Subfunctor D.space.obj :=
  reducedClosedSubspace B S hS D.space.obj D.space.property {D.point i} (D.isClosed_point i)

/-- The reduced closed subspace on the `i`th chosen point has exactly one point. -/
private theorem subsingleton_points_reducedPointSubspace (i : Fin n) :
    Subsingleton (points B S hS (D.reducedPointSubspace i).toFunctor) := by
  have hmono : Mono (D.reducedPointSubspace i).ι := mono_of_isClosedImmersion B S hS _
    (isClosedSubspace_reducedClosedSubspace B S hS D.space.obj D.space.property
      {D.point i} (D.isClosed_point i)).2
  have hrange := range_pointsMap_ι_reducedClosedSubspace B S hS D.space.obj D.space.property
    {D.point i} (D.isClosed_point i)
  have h : ∀ y, pointsMap B S hS (D.reducedPointSubspace i).toFunctor
      (D.reducedPointSubspace i).ι y = D.point i := fun y => by
    have : pointsMap B S hS (D.reducedPointSubspace i).toFunctor
        (D.reducedPointSubspace i).ι y ∈ Set.range (pointsMap B S hS
          (D.reducedPointSubspace i).toFunctor (D.reducedPointSubspace i).ι) := ⟨y, rfl⟩
    rwa [hrange] at this
  exact ⟨fun y y' => pointsMap_injective_of_mono B S hS (D.reducedPointSubspace i).ι
    ((h y).trans (h y').symm)⟩

/-- The reduced closed subspace on the `i`th chosen point is nonempty. -/
private theorem nonempty_points_reducedPointSubspace (i : Fin n) :
    Nonempty (points B S hS (D.reducedPointSubspace i).toFunctor) := by
  obtain ⟨y, -⟩ : D.point i ∈ Set.range (pointsMap B S hS (D.reducedPointSubspace i).toFunctor
      (D.reducedPointSubspace i).ι) := by
    rw [range_pointsMap_ι_reducedClosedSubspace B S hS D.space.obj D.space.property
      {D.point i} (D.isClosed_point i)]
    exact Set.mem_singleton _
  exact ⟨y⟩

/-- **The canonical morphism `Spec κ(uᵢ) ⟶ X` is a closed immersion.**

It factors through the reduced closed subspace of `X` on `{xᵢ}` by Stacks 03JJ, its source
being reduced with image the single point `xᵢ`. That subspace is decent, being representable
over the decent space `X`, and reduced with a single point, so it is the spectrum of a field by
Stacks 047Z; the factoring morphism is a monomorphism into the spectrum of a field with
nonempty source, hence an isomorphism by Stacks 06MG. So `Spec κ(uᵢ) ⟶ X` is the inclusion of
that closed subspace up to an isomorphism of its source. -/
theorem isClosedImmersion_residualToSpace (i : Fin n) :
    IsClosedImmersion B S hS (D.residualToSpace i) := by
  have hRc : IsClosedSubspace B S hS (D.reducedPointSubspace i) :=
    isClosedSubspace_reducedClosedSubspace B S hS D.space.obj D.space.property
      {D.point i} (D.isClosed_point i)
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj (D.residualObject i)) :=
    isAlgebraicSpace_yoneda B S hS _
  -- the morphism factors through the reduced closed subspace on `{xᵢ}`
  have hsubset : Set.range (pointsMap B S hS (yoneda.obj (D.residualObject i))
      (D.residualToSpace i)) ⊆ Set.range (pointsMap B S hS
        (D.reducedPointSubspace i).toFunctor (D.reducedPointSubspace i).ι) := by
    rw [range_pointsMap_ι_reducedClosedSubspace B S hS D.space.obj D.space.property
      {D.point i} (D.isClosed_point i)]
    rintro _ ⟨z, rfl⟩
    exact Set.mem_singleton_iff.2 (D.pointsMap_residualToSpace i z)
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
    D.space.property hTalg (D.reducedPointSubspace i) hRc
    (D.hasEtaleLocalProperty_isReduced_residualObject i) (D.residualToSpace i)).mpr hsubset
  -- the reduced closed subspace on `{xᵢ}` is the spectrum of a field
  have hRdec : IsDecentSpace B S hS (D.reducedPointSubspace i).toFunctor :=
    isDecentSpace_of_relativelyRepresentable B S hS hRc.1 (D.reducedPointSubspace i).ι
      hRc.2.1 D.decent
  obtain ⟨M, K, hK, ⟨εM⟩, ⟨eR⟩⟩ := exists_iso_yoneda_spec_of_subsingleton_points B S hS hRc.1
    hRdec (D.nonempty_points_reducedPointSubspace i)
    (D.subsingleton_points_reducedPointSubspace i)
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS D.space.obj D.space.property
      {D.point i} (D.isClosed_point i))
  let _ : Field K := hK
  -- the factoring morphism is a monomorphism into the spectrum of a field, hence invertible
  have hmonofac : Mono (g ≫ (D.reducedPointSubspace i).ι) := by
    rw [hg]
    exact (D.neighborhood i).mono_residueField
  have _ : Mono g := mono_of_mono g (D.reducedPointSubspace i).ι
  have _ : Mono (g ≫ eR.hom) := inferInstance
  have hgiso : IsIso g := by
    have := (isEmpty_points_or_isIso_of_mono_to_fieldSpectrum B S hS M εM hTalg
      (g ≫ eR.hom)).resolve_left fun h => h.false (D.nonempty_points_residualObject i).some
    exact IsIso.of_isIso_comp_right g eR.hom
  -- so the morphism is the inclusion of a closed subspace up to an isomorphism of its source
  rw [← hg]
  exact isClosedImmersion_comp_of_isIso g hRc.2

/-- **The first standing hypothesis of Stacks 0BGY at `(Uᵢ ⟶ X, {xᵢ})`.** The subspace `{xᵢ}`
of `X` is a closed subspace: it is the image of the monomorphism `Spec κ(uᵢ) ⟶ X`, which is a
closed immersion, so its inclusion is that morphism precomposed with an isomorphism. -/
theorem isClosedSubspace_pointSubspace (i : Fin n) :
    IsClosedSubspace B S hS (D.pointSubspace i) := by
  have hmono : Mono (D.residualToSpace i) := (D.neighborhood i).mono_residueField
  have _ : IsIso (Subfunctor.toRange (D.residualToSpace i)) := inferInstance
  have hιeq : (asIso (Subfunctor.toRange (D.residualToSpace i))).inv ≫ D.residualToSpace i =
      (Subfunctor.range (D.residualToSpace i)).ι :=
    (asIso (Subfunctor.toRange (D.residualToSpace i))).inv_comp_eq.2
      (Subfunctor.toRange_ι (D.residualToSpace i)).symm
  rw [D.pointSubspace_eq_range i]
  refine ⟨(isAlgebraicSpace_yoneda B S hS (D.residualObject i)).of_iso
    (asIso (Subfunctor.toRange (D.residualToSpace i))), ?_⟩
  rw [← hιeq]
  exact isClosedImmersion_comp_of_isIso _ (D.isClosedImmersion_residualToSpace i)

/-- **The subspace `{xᵢ}` is the reduced closed subspace of `X` on the closed point `xᵢ`.**
It is a closed subspace, its point set is `{xᵢ}` and it is étale-locally reduced, so Stacks
03IQ identifies it with `AlgebraicGeometry.Space.reducedClosedSubspace`. -/
theorem pointSubspace_eq_reducedClosedSubspace (i : Fin n) :
    D.pointSubspace i = reducedClosedSubspace B S hS D.space.obj D.space.property
      {D.point i} (D.isClosed_point i) := by
  have hmono : Mono (D.residualToSpace i) := (D.neighborhood i).mono_residueField
  have _ : IsIso (Subfunctor.toRange (D.residualToSpace i)) := inferInstance
  exact eq_reducedClosedSubspace B S hS D.space.obj D.space.property {D.point i}
    (D.isClosed_point i) (D.pointSubspace i) (D.isClosedSubspace_pointSubspace i)
    (D.range_pointsMap_ι_pointSubspace i) <|
    hasEtaleLocalProperty_of_representable B S hS (D.pointSubspace i).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) (D.residualObject i)
      (asIso (Subfunctor.toRange (D.residualToSpace i))).symm
      (inferInstanceAs (IsReduced
        (Spec (.of ((D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point)))))

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
