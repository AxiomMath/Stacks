module

public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent

/-!
# Lifting along open immersions, and quasi-compact open neighbourhoods

* A morphism into an algebraic space whose points land in the image of an open immersion
  factors through it (Stacks 03IE for an open subspace, transported along the isomorphism of an
  open immersion onto its image).
* A closed immersion `Z ⟶ X` with set of points `T` and `Z` proper over `Y` makes `T` proper over
  `Y` in the sense of Stacks 0CZD (Stacks 0CZC).
* The image of a quasi-compact algebraic space in an algebraic space lies in a quasi-compact open
  subspace.

## Main results

* `AlgebraicGeometry.Space.exists_lift_of_isOpenImmersion`: a morphism whose points land in the
  image of an open immersion factors through it.
* `AlgebraicGeometry.Space.isProperOver_of_isClosedImmersion_of_range`: the point set of a closed
  immersion with proper source is proper over the base.
* `AlgebraicGeometry.Space.exists_isQuasiCompactSpace_openSubspace_containing_range`: the image of
  a quasi-compact algebraic space lies in a quasi-compact open subspace.

## References

* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A monomorphism has the same set of points as its range subfunctor. -/
private theorem range_pointsMap_range_ι {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : Z ⟶ X)
    [Mono i] : Set.range (pointsMap B S hS _ (Subfunctor.range i).ι) =
      Set.range (pointsMap B S hS Z i) := by
  have := pointsMap_surjective_of_isIso B S hS (Subfunctor.toRange i)
  conv_rhs => rw [← Subfunctor.toRange_ι i]
  rw [pointsMap_comp, Set.range_comp, this.range_eq, Set.image_univ]

/-- The inclusion of the range of a monomorphism satisfies a scheme-level representable property
that the monomorphism satisfies. -/
private theorem presheaf_range_ι {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : Z ⟶ X) [Mono i]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hi : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf i) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.range i).ι := by
  apply ((P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf.cancel_left_of_respectsIso
    (asIso (Subfunctor.toRange i)).hom _).mp
  simpa only [asIso_hom, Subfunctor.toRange_ι] using hi

/-- **Lifting along an open immersion.** A morphism into an algebraic space whose points land in
the image of an open immersion `j` factors through `j`. -/
theorem exists_lift_of_isOpenImmersion {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (j : Y ⟶ Z) (hj : IsOpenImmersion B S hS j) (f : X ⟶ Z)
    (hf : Set.range (pointsMap B S hS X f) ⊆ Set.range (pointsMap B S hS Y j)) :
    ∃ g : X ⟶ Y, g ≫ j = f := by
  have := mono_of_isOpenImmersion B S hS j hj
  let V := Subfunctor.range j
  let e : Y ≅ V.toFunctor := asIso (Subfunctor.toRange j)
  have he : e.hom ≫ V.ι = j := Subfunctor.toRange_ι j
  have hV : IsOpenSubspace B S hS V :=
    ⟨isAlgebraicSpace_of_iso B S hS e hY, presheaf_range_ι B S hS j _ hj⟩
  have hr : Set.range (pointsMap B S hS X f) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι) := by
    rw [range_pointsMap_range_ι]
    exact hf
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hZ hX V hV f).mpr hr
  exact ⟨g ≫ e.inv, by rwa [Category.assoc, ← he, Iso.inv_hom_id_assoc]⟩

/-- **Stacks 0CZC, through a closed immersion.** If `i : Z ⟶ X` is a closed immersion whose set
of points is `T` and `Z` is proper over `Y`, then `T` is proper over `Y`. -/
theorem isProperOver_of_isClosedImmersion_of_range {Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) (T : Set (points B S hS X))
    (hT : IsClosed T) (hr : Set.range (pointsMap B S hS Z i) = T)
    (hp : IsProper B S hS (i ≫ f)) : IsProperOver B S hS hX hY f hf T hT := by
  have := mono_of_isClosedImmersion B S hS i hi
  let V := Subfunctor.range i
  let e : Z ≅ V.toFunctor := asIso (Subfunctor.toRange i)
  have he : e.hom ≫ V.ι = i := Subfunctor.toRange_ι i
  have hV : IsClosedSubspace B S hS V :=
    ⟨isAlgebraicSpace_of_iso B S hS e hZ, presheaf_range_ι B S hS i _ hi⟩
  apply (isProper_reducedClosedSubspace_iff_exists B S hS hX hY f hf T hT).mpr
  refine ⟨V, hV, ?_, ?_⟩
  · rw [range_pointsMap_range_ι, hr]
  · simpa only [← he, Category.assoc, Iso.inv_hom_id_assoc] using
      isProper_comp' B S hS e.inv (i ≫ f) hZ hY (isProper_of_isIso B S hS e.inv) hp

/-- **The image of a quasi-compact algebraic space lies in a quasi-compact open subspace.** -/
theorem exists_isQuasiCompactSpace_openSubspace_containing_range
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXqc : IsQuasiCompactSpace B S hS X) (f : X ⟶ Y) :
    ∃ (V : Subfunctor Y) (_ : IsOpenSubspace B S hS V),
      IsQuasiCompactSpace B S hS V.toFunctor ∧
      Set.range (pointsMap B S hS X f) ⊆ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  classical
  have hc : IsCompact (Set.range (pointsMap B S hS X f)) := by
    have := compactSpace_points_of_isQuasiCompactSpace B S hS hX hXqc
    exact isCompact_range (continuous_pointsMap B S hS f)
  have hn (x : points B S hS Y) :
      ∃ O : Set (points B S hS Y), IsOpen O ∧ IsCompact O ∧ x ∈ O := by
    obtain ⟨O, hO, _⟩ := (hasBasis_nhds_isOpen_isCompact B S hS Y hY x).mem_iff.mp
      (Filter.univ_mem : Set.univ ∈ nhds x)
    exact ⟨O, hO.1, hO.2.1, hO.2.2⟩
  choose O ho hcO hxO using hn
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover O ho (fun x _ => Set.mem_iUnion.mpr ⟨x, hxO x⟩)
  let A := ⋃ x ∈ t, O x
  have hA : IsOpen A := isOpen_iUnion fun x => isOpen_iUnion fun _ => ho x
  have hAc : IsCompact A := t.isCompact_biUnion (fun x _ => hcO x)
  let V := (openSubspacesOrderIso B S hS Y hY).symm ⟨A, hA⟩
  have hrange : Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) = A := by
    rw [← openSubspacesOrderIso_apply B S hS Y hY V]
    exact congrArg (fun O : TopologicalSpace.Opens _ => O.1)
      ((openSubspacesOrderIso B S hS Y hY).apply_symm_apply _)
  refine ⟨V.1, V.2, ?_, by simpa only [hrange] using ht⟩
  exact isQuasiCompactSpace_of_isCompact_range B S hS hY V.2 (by rwa [hrange])

end AlgebraicGeometry.Space

end
