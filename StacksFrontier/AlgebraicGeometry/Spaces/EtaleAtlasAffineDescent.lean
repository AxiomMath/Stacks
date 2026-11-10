module

public import StacksFrontier.AlgebraicGeometry.Descent.InvariantOpenCandidateDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenMonoDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalFromAtlas

/-!
# The étale atlas criterion from a descended affine hull

A sheaf on the big fppf site of `S` with a representable, surjective, étale atlas is an algebraic
space as soon as morphisms descend effectively along the surjective étale morphisms of the site at
the monomorphisms locally of finite type, by
`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent`. This file reduces
that hypothesis to `AlgebraicGeometry.Space.HasDescendedHull` at the *quasi-compact*
monomorphisms locally of finite type: the assertion that such a datum, over an affine base with
an affine chart, is an invariant open of the base change of some object over the base.

That assertion is effective descent for affine morphisms, Stacks 0245, in the shape the proof of
Stacks 0247 uses it. A quasi-compact monomorphism locally of finite type over an affine base is
separated and quasi-finite, hence quasi-affine, hence a quasi-compact open immersion into the
spectrum of the global sections of its source; that affine hull carries the descent datum by flat
base change for global sections, and the hull is what has to be descended. Everything after that
is a descent of invariant opens, which is unconditional.

So the chain from the criterion to its geometric input has three links, all proved: the diagonal
from the atlas, the removal of the quasi-compactness conjunct, and the passage from a descended
hull to the descended object.

## Main results

* `isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_hull`, in the
  namespace `AlgebraicGeometry.Space`: a descended hull for every quasi-compact monomorphic datum
  gives effective descent at the monomorphisms locally of finite type.
* `AlgebraicGeometry.relativelyRepresentable_diag_of_surjective_etale_atlas_of_hasDescendedHull`:
  the absolute diagonal of a sheaf with a representable surjective étale atlas is representable.
* `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_hasDescendedHull` and
  `isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_hasDescendedHull`: the criteria
  of Stacks 0BGQ and Stacks 0BGR from that one hypothesis.

## Implementation notes

The property `monomorphisms ⊓ LocallyOfFiniteType ⊓ QuasiCompact` is below the monomorphisms,
which is what lets
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_hasDescendedHull` turn a
candidate into representability with no further sheaf theory; the quasi-affine morphisms are not
below the monomorphisms, which is why the route through Stacks 0247 in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasQuasiAffineDescent` cannot be replaced by this
one termwise. The two reductions are independent: Stacks 0247 implies the hypothesis here, and this
hypothesis is strictly weaker than Stacks 0247 as a statement about which morphisms descend.

Its fppf descent is assembled by hand because quasi-compactness descends along the surjective flat
quasi-compact morphisms rather than along the surjective flat morphisms of finite presentation; the
passage is `AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc`.

*Where the tags sit.* Stacks 0BGQ and Stacks 0BGR are asserted without hypotheses by
`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas` and
`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_surjective_etale` of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional`; the criteria below
carry the hull hypothesis instead, so they are not a second home for those tags.

## References

* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

/-- Quasi-compact monomorphisms locally of finite type are stable under base change. -/
theorem monomorphisms_inf_locallyOfFiniteType_inf_quasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact) :=
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  .inf

/-- Quasi-compact monomorphisms locally of finite type satisfy fppf descent. -/
theorem monomorphisms_inf_locallyOfFiniteType_inf_quasiCompact_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _hm := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  have _hzq : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have _hq : MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of_descendsAlong_fpqc _
  MorphismProperty.DescendsAlong.inf

/-- Quasi-compact monomorphisms locally of finite type are monomorphisms. -/
theorem monomorphisms_inf_locallyOfFiniteType_inf_quasiCompact_le_monomorphisms :
    (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact) ≤
      MorphismProperty.monomorphisms Scheme.{u} :=
  fun _ _ _ hg ↦ hg.1.1

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Effective descent at the monomorphisms locally of finite type, from a descended hull.** If
every descent datum over an affine base with an affine chart whose leg is a quasi-compact
monomorphism locally of finite type is an invariant open of the base change of an object over that
base, then morphisms which are monomorphisms locally of finite type descend effectively along the
surjective étale morphisms of the big fppf site of `S`.

Two links: `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_hasDescendedHull`
cuts the datum out of the hull, and
`isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_quasiCompact`
removes the quasi-compactness conjunct by the second step of Stacks 02W8. -/
theorem isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_hull
    (H : HasDescendedHull B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  have _hbc := monomorphisms_inf_locallyOfFiniteType_inf_quasiCompact_isStableUnderBaseChange.{u}
  have _hd := monomorphisms_inf_locallyOfFiniteType_inf_quasiCompact_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_quasiCompact
    (isEffectiveDescentAlongSurjectiveEtale_of_hasDescendedHull
      monomorphisms_inf_locallyOfFiniteType_inf_quasiCompact_le_monomorphisms H)

end Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The absolute diagonal of a sheaf with a representable surjective étale atlas is
representable**, granted a descended hull for every quasi-compact monomorphic descent datum over
an affine base. -/
theorem relativelyRepresentable_diag_of_surjective_etale_atlas_of_hasDescendedHull
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (H : Space.HasDescendedHull B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)) :
    yoneda.relativelyRepresentable (diag F) :=
  relativelyRepresentable_diag_of_surjective_etale_atlas B S hS hF f hsurj hetale
    (Space.isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_hull
      H)

/-- **Stacks 0BGQ**, granted a descended hull for every quasi-compact monomorphic descent datum
over an affine base. A sheaf `F` on the big fppf site over `S` which has a representable,
surjective, étale morphism `f : h_U ⟶ F` from an object `U` of the site is an algebraic space
over `S`.

The hull hypothesis is the only hypothesis beyond the source's; the tag 0BGQ sits on the
hypothesis-free `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas` of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional`. -/
theorem isAlgebraicSpace_of_surjective_etale_atlas_of_hasDescendedHull
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (H : Space.HasDescendedHull B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent B S hS hF U f hsurj hetale
    (Space.isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_hull
      H)

/-- **Stacks 0BGR**, granted a descended hull for every quasi-compact monomorphic descent datum
over an affine base. A sheaf `F` on the big fppf site over `S` which has a representable,
surjective, étale morphism `a : G ⟶ F` from an algebraic space `G` over `S` is an algebraic space
over `S`.

Representability of `a` is not a separate hypothesis: it is the first component of
`CategoryTheory.MorphismProperty.presheaf`, which each of `hs` and `he` is. The tag 0BGR sits
on the hypothesis-free
`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_surjective_etale` of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional`. -/
theorem isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_hasDescendedHull
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (a : G ⟶ F)
    (hs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (he : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (H : Space.HasDescendedHull B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact)) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_etaleDescent B S hS hG hF a hs
    he
    (Space.isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType_of_hull
      H)

end AlgebraicGeometry

end
