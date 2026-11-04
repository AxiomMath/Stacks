module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizedSiteStructureMap
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage

/-!
# The Beck-Chevalley comparison of the localization square is an isomorphism

`CategoryTheory.SliceTopos.localizedInverseImageMate` is the comparison
`(f')⁻¹ j_V⁻¹ ⟶ j_U⁻¹ f⁻¹` through which
`AlgebraicGeometry.RingedSite.Hom.fSharpSet_localized` expresses the structure map of the
localization of a morphism of ringed sites ([Stacks Project, Tag 04J0]).  This file records that
it is an isomorphism whenever the underlying continuous functor is a morphism of sites.

The reason is that it is *the same natural transformation* as
`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostMate` — both are the
Beck-Chevalley mate of clause (d) of [Stacks Project, Tag 03CF], and clause (d) is a strict
equality of functors, so the two are the same `mateEquiv.symm` applied to the same `eqToHom` —
and that transformation is clause (b) of Stacks 03CF, hence invertible, by
`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom` and
`CategoryTheory.SliceTopos.isIso_overPullbackCompSheafPullbackOverPostMate`.

## Main results

* `CategoryTheory.SliceTopos.localizedInverseImageMate_eq_mate` — the comparison of
  `LocalizedSiteStructureMap.lean` is the mate of
  `StacksFrontier/CategoryTheory/Sites/SliceTopos/InverseImage.lean`.  The two were defined
  independently, in two different developments of Stacks 03CF, and they are equal by `rfl`.
* `CategoryTheory.SliceTopos.isIso_localizedInverseImageMate` and
  `CategoryTheory.SliceTopos.isIso_localizedInverseImageMate_app` — it is an isomorphism, and so
  is each of its components.

## Implementation notes

Two notes in this repository said that invertibility of this mate was open, and both are wrong;
they are corrected where they stand.

* The implementation notes of
  `StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedSiteStructureMap.lean` said that `IsIso`
  of the mate "is exactly the input that `AlgebraicGeometry.RingedSite.Hom.localized` being a
  *locally ringed* morphism still needs", and that what was missing was "the identification of
  that isomorphism with the mate below".  That identification is
  `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom`, registered on
  Stacks 03CF.
* The module documentation of
  `StacksFrontier/CategoryTheory/Sites/SliceTopos/InverseImage.lean` said clause (b) "is nowhere
  compared with the mate" and that two facts were unproved.  Its own
  "Main results" section, further down the same docstring, announces both of them.

What invertibility does *not* by itself give is `IsLocallyRinged` of
`AlgebraicGeometry.RingedSite.Hom.localized`: that still needs the units square of the localized
morphism to be identified with the restriction of the units square of `f` along `j_U⁻¹`, which
is where the comparison is then transported.  So this file closes the input that was named as
the obstruction and leaves the transport, which was described as free.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.SliceTopos

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  (V : C) [u.IsContinuous J K]
  [(Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))]

/-- **The two developments' Beck-Chevalley comparisons for the localization square agree.**
`localizedInverseImageMate` and `overPullbackCompSheafPullbackOverPostMate` are both
`mateEquiv.symm` of `eqToHom` of clause (d) of Stacks 03CF, so they are the same transformation;
the continuity instance for `Over.post u` is a proof of a proposition and so does not separate
them. -/
theorem localizedInverseImageMate_eq_mate :
    localizedInverseImageMate J K u V = overPullbackCompSheafPullbackOverPostMate J K u V := rfl

/-- **The Beck-Chevalley comparison of the localization square is an isomorphism.**  It is the
mate of clause (d) of Stacks 03CF, which is clause (b) of the same tag by
`overPullbackCompSheafPullbackOverPostIso_hom` and therefore invertible. -/
theorem isIso_localizedInverseImageMate (hu : u.IsMorphismOfSites J K) :
    IsIso (localizedInverseImageMate J K u V) :=
  isIso_overPullbackCompSheafPullbackOverPostMate J K u V hu

/-- Each component of the Beck-Chevalley comparison is an isomorphism.  This is the form in which
the units square of `AlgebraicGeometry.RingedSite.Hom.localized` consumes it: the square has to be
transported at the two sheaves `O'` and `O'^*` and at nothing else. -/
theorem isIso_localizedInverseImageMate_app (hu : u.IsMorphismOfSites J K)
    (G : Sheaf J (Type u)) :
    IsIso ((localizedInverseImageMate J K u V).app G) :=
  have := isIso_localizedInverseImageMate J K u V hu
  NatIso.isIso_app_of_isIso (localizedInverseImageMate J K u V) G

end CategoryTheory.SliceTopos

end
