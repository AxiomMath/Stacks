module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# A morphism which is Zariski-locally a projective space is smooth

If `f : H ⟶ P` is Zariski-locally on `P` the projective space `ℙᵐ`
(`Stacks.ProjectiveBundle.IsLocallyProjectiveSpace`), then `f` is smooth: smoothness is local on
the target and `ℙᵐ_V ⟶ V` is smooth (`AlgebraicGeometry.projectiveSpaceOver.smooth`).

## Main results

* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.smooth`: `f` is smooth.
* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.smoothOfRelativeDimension`: `f` is smooth of
  relative dimension `m`.

## References

* [Stacks Project, Tag 01V8](https://stacks.math.columbia.edu/tag/01V8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ProjectiveBundle

/-- **A morphism which is Zariski-locally on the target a projective space is smooth.** -/
theorem IsLocallyProjectiveSpace.smooth {H P : Scheme.{u}} {f : H ⟶ P} {m : ℕ}
    (hbundle : IsLocallyProjectiveSpace f m) : Smooth f := by
  have : IsZariskiLocalAtTarget @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth) (Q := RingHom.Smooth)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (f := f) fun y => ?_
  obtain ⟨V, hyV, e, he⟩ := hbundle y
  refine ⟨V, hyV, ?_⟩
  rw [← he]
  exact inferInstanceAs (Smooth (e.hom ≫ (projectiveSpaceOver m V.toScheme ↘ V.toScheme)))

/-- **A morphism which is Zariski-locally on the target the projective space `ℙᵐ` is smooth of
relative dimension `m`**: it is smooth, and every fibre is equidimensional of dimension `m`, so
the fibre has dimension `m` at each of its points. -/
theorem IsLocallyProjectiveSpace.smoothOfRelativeDimension {H P : Scheme.{u}} {f : H ⟶ P}
    {m : ℕ} (hbundle : IsLocallyProjectiveSpace f m) : SmoothOfRelativeDimension m f := by
  have := hbundle.smooth
  have := hbundle.locallyOfFiniteType
  have hrel := hbundle.relativeDimension
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f m fun x => ?_
  have hFT : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    show LocallyOfFiniteType (pullback.snd f (P.fromSpecResidueField (f x)))
    infer_instance
  obtain ⟨heq, hdim⟩ := hrel (f x) ⟨f.asFiber x⟩
  exact AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional (P.residueField (f x))
    (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) heq hdim (f.asFiber x)

end Stacks.ProjectiveBundle
