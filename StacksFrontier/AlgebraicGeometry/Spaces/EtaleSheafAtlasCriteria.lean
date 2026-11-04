module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion

/-!
# An étale sheaf with a smooth atlas is an algebraic space (Stacks 07WF, Stacks 0BH4)

Let `S` be a scheme contained in a chosen big fppf site `B`, and let `F` be a presheaf on the
big category over `S`, which is the common underlying category of the big fppf and the big étale
site of Stacks 03FF.  Stacks 07WF and Stacks 0BH4 say that `F` is an algebraic space as soon as
it is a sheaf for the *étale* topology and has a diagonal representable by algebraic spaces
together with a surjective smooth cover by a scheme, or a cover by an algebraic space which is
representable by algebraic spaces, surjective and étale.  The fppf sheaf condition of
Algebraic Spaces, Definition 025Y is part of the conclusion.

## Main results

* `AlgebraicGeometry.Space.coreCriterion_unconditional`: an étale sheaf with a surjective smooth
  atlas by an algebraic space, representable by algebraic spaces, is an algebraic space.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_etale_space_atlas_unconditional`:
  **Stacks 0BH4**.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas_unconditional`:
  **Stacks 07WF**.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_surjective_smooth_atlas_unconditional`: an fppf
  sheaf with an atlas by an object of the site which is surjective and smooth after every
  represented base change is an algebraic space.

## Implementation notes

Each result here is the criterion of the same name without the suffix, in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSheafSpaceCoverCriterion.lean` or
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothAtlasCriterion.lean`, with its Stacks 04S6
input, `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`, discharged by the proof of
Stacks 04S6 condition (1), `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`.

The proof is the source's.  With `R = X ×_F X` the kernel pair of the given cover, the fppf
quotient sheaf `X/R` of Stacks 044J is an algebraic space by **Stacks 04S6**: the two projections
of the kernel pair are smooth, hence flat and locally of finite presentation, and
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isBootstrap` derives condition (1)
for such a relation from condition (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.  Stacks 06PG and
Stacks 046O then make `X ⟶ X/R` surjective with kernel pair `R` again, and Stacks 0429 makes it
smooth, so both `X ⟶ F` and `X ⟶ X/R` are locally surjective for the étale topology with the
same kernel pair.  Stacks 086K identifies their targets
(`AlgebraicGeometry.Space.iso_of_isLocallySurjective_of_common_kernelPair`), and `F` inherits
the algebraic-space condition from `X/R`.

`quotientSheaf j` is an fppf sheaf by construction, so no fppf descent is assumed for `F`; the
étale sheaf hypothesis on `F` is what identifies `F` with `X/R`.

The criteria with the Stacks 04S6 input carried are in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSheafSpaceCoverCriterion.lean`, which sits below the
proof of Stacks 04S6 in the import graph; the unconditional forms are here, above it.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 086K](https://stacks.math.columbia.edu/tag/086K)
* [Stacks Project, Tag 07WF](https://stacks.math.columbia.edu/tag/07WF)
* [Stacks Project, Tag 0BH4](https://stacks.math.columbia.edu/tag/0BH4)
* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The core criterion -/

/-- The criterion of Stacks 0GE0 / 07WF / 0BH4, with nothing carried: an étale sheaf with a
surjective smooth atlas by an algebraic space, representable by algebraic spaces, is an algebraic
space.

This is `AlgebraicGeometry.Space.coreCriterion` with its Stacks 04S6 input discharged by
`AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`. -/
theorem coreCriterion_unconditional
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hX : IsAlgebraicSpace B S hS X) (a : X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha)
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) a ha) :
    IsAlgebraicSpace B S hS F :=
  coreCriterion B S hS hF hX a ha hsurj hsmooth (bootstrap04S6QuotientSheaf B S hS)

/-- **Stacks 0BH4.** Let `F` be a presheaf of sets on the big category over `S`, which is the
common underlying category of the chosen big fppf and big étale sites. If `F` is a sheaf for the
étale topology and there are an algebraic space `X` over `S` and a morphism `X ⟶ F` which is
representable by algebraic spaces, surjective and étale, then `F` is an algebraic space over `S`
in the sense of Algebraic Spaces, Definition 025Y.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_etale_space_atlas` with its
Stacks 04S6 input discharged by `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`. -/
@[stacks 0BH4]
theorem isAlgebraicSpace_of_isSheaf_etale_of_etale_space_atlas_unconditional
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (a : X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha)
    (hetale : HasProperty B S hS (etaleMorphisms B S hS) a ha) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_isSheaf_etale_of_etale_space_atlas B S hS F hF hX a ha hsurj hetale
    (bootstrap04S6QuotientSheaf B S hS)

/-- **Stacks 07WF.** Let `F` be a presheaf of sets on the big category over `S`, which is the
common underlying category of the chosen big fppf and big étale sites. If `F` is a sheaf for the
étale topology, its diagonal `Δ : F ⟶ F × F` is representable by algebraic spaces, and there are
an object `U` of the category over `S` and a morphism `h_U ⟶ F` which is surjective and smooth,
then `F` is an algebraic space over `S` in the sense of Algebraic Spaces, Definition 025Y.

The representability by algebraic spaces of the cover is not a further hypothesis: it follows
from the representable diagonal by
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal`, and the surjectivity and
smoothness are asked of that witness. This is
`AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas` with its
Stacks 04S6 input discharged by `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`. -/
@[stacks 07WF]
theorem isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas_unconditional
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
        (isAlgebraicSpace_yoneda B S hS U) a))
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) a
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
        (isAlgebraicSpace_yoneda B S hS U) a)) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas B S hS F hF hdiag U a hsurj hsmooth
    (bootstrap04S6QuotientSheaf B S hS)

/-! ### A surjective smooth atlas by an object of the site -/

/-- An fppf sheaf on the big fppf site of `S` which admits an atlas by an object of the site
that is surjective and smooth after every represented base change is an algebraic space
over `S`.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_of_surjective_smooth_atlas` with its
Stacks 04S6 input discharged by `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`. -/
theorem isAlgebraicSpace_of_surjective_smooth_atlas_unconditional
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hsmooth : (MorphismProperty.inverseImage (@Smooth.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_surjective_smooth_atlas B S hS hF U f hsurj hsmooth
    (bootstrap04S6QuotientSheaf B S hS)

end AlgebraicGeometry.Space

end
