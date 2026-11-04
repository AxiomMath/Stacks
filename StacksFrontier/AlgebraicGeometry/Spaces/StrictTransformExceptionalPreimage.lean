module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction

/-!
# Two reductions about the exceptional preimage of a strict transform

Two facts about the subsheaf of sections supported on the exceptional preimage of a strict
transform, used by Stacks 0866 and by Stacks 0869.  Neither is a clause of a tag: the first
is part (3) of Stacks 0859 with its hypotheses discharged in the situation of Stacks 0862, and
the second is Stacks 03H4 read at the base change of a morphism over `A`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSections_exceptionalPreimage`: the
  sections of a quasi-coherent module supported on the exceptional preimage of a locally
  principal closed subspace form a quasi-coherent submodule.
* `AlgebraicGeometry.Space.exceptionalPreimageSet_comp_eq_preimage`: the exceptional preimage
  of a composite is the inverse image of the exceptional preimage along the base change.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 083D](https://stacks.math.columbia.edu/tag/083D)
* [Stacks Project, Tag 083X](https://stacks.math.columbia.edu/tag/083X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Exceptional

variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **The sections supported on the exceptional preimage form a quasi-coherent submodule**,
whenever `E` is a locally principal closed subspace of `A'` and the ambient module is
quasi-coherent.

This is part (3) of Stacks 0859,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSectionsSubmodule`, with its three
hypotheses discharged exactly as
`AlgebraicGeometry.Space.strictTransform_exists_of_isLocallyPrincipal` discharges them for the
structure sheaf: the supported set is the point set of the closed subspace `pr_{A'}^{-1}E`,
hence closed; its complement is the point set of
`AlgebraicGeometry.Space.openComplement`, an open subspace; and the inclusion of that
complement is affine by Stacks 083X followed by Stacks 083D, hence quasi-compact. -/
theorem isQuasicoherentOnSite_supportedSections_exceptionalPreimage (E : Subfunctor A'.1)
    (hE : IsClosedSubspace B S hS E) (hlp : IsLocallyPrincipal B S hS A' ⟨E, hE⟩)
    (G : Modules.{u, u} B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2) (hG : G.IsQuasicoherentOnSite) :
    (supportedSectionsSubmodule B S hS (strictTransformPullback B S hS f b).1
        (strictTransformPullback B S hS f b).2 (exceptionalPreimageSet B S hS f b E)
        G).toSheafOfModules.IsQuasicoherentOnSite := by
  have hcl : IsClosedSubspace B S hS (exceptionalPreimage B S hS f b E) :=
    exceptionalPreimage_isClosedSubspace B S hS f b E hE
  have hTclosed : IsClosed (exceptionalPreimageSet B S hS f b E) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS
      (strictTransformPullback B S hS f b).2 _ hcl.2
  have hO := isOpenSubspace_openComplement B S hS (strictTransformPullback B S hS f b).2 _ hcl
  exact isQuasicoherentOnSite_supportedSectionsSubmodule B S hS
    (strictTransformPullback B S hS f b).2 G hG hTclosed hO
    (range_pointsMap_ι_openComplement B S hS _)
    (isQuasiCompact_of_isAffineHom' B S hS _ hO.1 (strictTransformPullback B S hS f b).2
      (isAffineHom_openComplement_exceptionalPreimage B S hS f b E hE hlp))

end Exceptional

section Composite

variable {A X Y A' : AlgebraicSpaces B S hS} (g : X ⟶ Y) (f : Y ⟶ A) (b : A' ⟶ A)

/-- **The exceptional preimage upstairs is the inverse image of the exceptional preimage
downstairs**, along the base change `g'` of `g`.

Both are inverse images of `E` along the projection to `A'`, and `g'` is a morphism over `A'`:
that is `AlgebraicGeometry.Space.strictTransformPullbackMap_toBlowUp`.  On points the inverse
image of a subspace is the inverse image of its points, Stacks 03H4 in the form
`AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage`. -/
theorem exceptionalPreimageSet_comp_eq_preimage (E : Subfunctor A'.1) :
    exceptionalPreimageSet B S hS (g ≫ f) b E =
      pointsMap B S hS (strictTransformPullback B S hS (g ≫ f) b).1
          (strictTransformPullbackMap B S hS g f b).hom ⁻¹'
        exceptionalPreimageSet B S hS f b E := by
  have hw : (strictTransformPullbackMap B S hS g f b).hom ≫
      (strictTransformPullbackToBlowUp B S hS f b).hom =
      (strictTransformPullbackToBlowUp B S hS (g ≫ f) b).hom :=
    congrArg (fun m : strictTransformPullback B S hS (g ≫ f) b ⟶ A' => m.hom)
      (strictTransformPullbackMap_toBlowUp B S hS g f b)
  rw [exceptionalPreimageSet_eq_preimage, exceptionalPreimageSet_eq_preimage,
    ← Set.preimage_comp, ← pointsMap_comp, hw]

end Composite

end AlgebraicGeometry.Space

end
