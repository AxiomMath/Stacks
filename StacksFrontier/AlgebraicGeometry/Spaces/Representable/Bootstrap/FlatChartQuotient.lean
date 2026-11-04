module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A sheaf with a flat chart is the quotient of the kernel pair of that chart

Let `S` be a scheme contained in a big fppf site, let `F` be a sheaf on the big fppf site of
`S`, let `X` be an algebraic space over `S` and let `f : X ⟶ F` be representable by algebraic
spaces, surjective, flat and locally of finite presentation.  Write `R = X ×_F X` for the
kernel pair of `f`, with its two projections `t, s : R ⟶ X`.  Then the canonical morphism
`X/R ⟶ F` out of the quotient sheaf of Stacks 044J is an isomorphism: `F = X/R`.

## Main results

* `AlgebraicGeometry.Space.isIso_quotientSheafDesc_of_isPullback`: a morphism out of `U` to a
  sheaf which is a surjection of fppf sheaves and whose kernel pair is the pre-relation `j`
  identifies that sheaf with the quotient sheaf `U/R`.
* `AlgebraicGeometry.Space.isIso_quotientSheafDesc_of_flat_chart`: the same for a chart which
  is representable by algebraic spaces, surjective, flat and locally of finite presentation,
  surjectivity of sheaves being supplied by Stacks 04S1.
* `AlgebraicGeometry.Space.isIso_quotientSheafDesc_kernelPairRelation`: the identification
  `F = X/R` at the kernel-pair relation of the chart itself.

## Implementation notes

The recognition criterion used is Stacks 044M, whose hypothesis is that the comparison morphism
from `R` to the kernel pair of `U ⟶ A` is a surjection of sheaves.  Here that comparison is an
isomorphism, the square being cartesian, so the hypothesis is automatic; this is the only place
the cartesian condition enters.  Surjectivity of the chart as a morphism of sheaves is Stacks
04S1, which turns the three relative properties of Stacks 03XZ into local surjectivity for the
big fppf topology.

`AlgebraicGeometry.Space.quotientSheaf` is the sheafification of the coequalizer of
`j.target.left` and `j.source.left`, so it depends on a pre-relation only through those two
morphisms of presheaves and not on the base over which the pre-relation is taken.  The first
two statements are therefore phrased for an arbitrary base `Z` together with the cartesian
condition identifying the two maps of `j` with the kernel pair, which is what makes them
applicable to the pre-relation of a groupoid over any base.  The witness used in the third is
`AlgebraicGeometry.Space.kernelPairRelation`, taken over the base `F` itself, where the kernel
pair is the categorical self-product of `f`; it is a relation and an equivalence relation by
`AlgebraicGeometry.Space.mono_kernelPairRelation` and
`AlgebraicGeometry.Space.isEquivalenceRelation_kernelPairRelation`.

What this does not give is algebraicity of `X/R`.  That is the quotient of an equivalence
relation in algebraic spaces whose source and target are flat and locally of finite
presentation, which is condition (1) of Stacks 04S6.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 044M](https://stacks.math.columbia.edu/tag/044M)
* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-! ### Recognizing a sheaf as the quotient of a kernel pair -/

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- A morphism `k` from `U` to a sheaf `A` whose kernel pair is the pre-relation `j` and which
is a surjection of fppf sheaves identifies `A` with the quotient sheaf `U/R`.

This is Stacks 044M with its hypothesis on `R` discharged: the comparison morphism from `R` to
the kernel pair of `k` is the isomorphism of the cartesian square, hence surjective. -/
@[sga "3 IV 4.6.5" "partial"]
theorem isIso_quotientSheafDesc_of_isPullback (j : PreRelation R U)
    (A : Sheaf (BigFppfOver.topology B S hS) (Type u)) (k : U.left ⟶ A.obj)
    (hker : IsPullback j.target.left j.source.left k k)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) k) :
    IsIso (quotientSheafDesc j A k hker.w) := by
  refine isIso_quotientSheafDesc_of_isLocallySurjective j A k hker.w hsurj ?_
  have : IsIso (pullback.lift j.target.left j.source.left hker.w) := by
    have heq : pullback.lift j.target.left j.source.left hker.w = hker.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        exact hker.isoPullback_hom_fst.symm
      · rw [pullback.lift_snd]
        exact hker.isoPullback_hom_snd.symm
    rw [heq]
    infer_instance
  refine Presheaf.isLocallySurjective_of_surjective _ _ ?_
  intro T
  exact (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 inferInstance T)

/-! ### A flat chart presents its target as the quotient of its kernel pair -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `F` be a sheaf on the big fppf site of `S`, let `U` be an algebraic space over `S` and
let `f : U ⟶ F` be representable by algebraic spaces, surjective, flat and locally of finite
presentation.  If the two maps of the pre-relation `j` are the kernel pair of `f`, then the
canonical morphism `U/R ⟶ F` is an isomorphism.

This is the step `F = U/R` of the proof of Stacks 04S6: the chart is a surjection of fppf
sheaves by Stacks 04S1, and the identification is Stacks 044M. -/
theorem isIso_quotientSheafDesc_of_flat_chart (j : PreRelation R U)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hU : IsAlgebraicSpace B S hS U.left) (f : U.left ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf)
    (hflat : HasProperty B S hS (flatProperty B S hS) f hf)
    (hlfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf)
    (hker : IsPullback j.target.left j.source.left f f) :
    IsIso (quotientSheafDesc j ⟨F, hF⟩ f hker.w) :=
  isIso_quotientSheafDesc_of_isPullback j ⟨F, hF⟩ f hker
    (isLocallySurjective_of_isRepresentableByAlgebraicSpaces B S hS hU.isSheaf hF f hf hflat
      hlfp hsurj)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The two maps of the kernel-pair relation of `f` form a cartesian square over `f`. -/
theorem isPullback_kernelPairRelation (f : X ⟶ F) :
    IsPullback (kernelPairRelation f).target.left (kernelPairRelation f).source.left f f := by
  rw [kernelPairRelation_target_left, kernelPairRelation_source_left]
  exact IsPullback.of_hasPullback f f

/-- Let `F` be a sheaf on the big fppf site of `S`, let `X` be an algebraic space over `S` and
let `f : X ⟶ F` be representable by algebraic spaces, surjective, flat and locally of finite
presentation.  Then `F` is the quotient sheaf of the kernel pair `R = X ×_F X` of `f`: the
canonical morphism `X/R ⟶ F` is an isomorphism. -/
@[sga "3 IV 4.6.5" "special case"]
theorem isIso_quotientSheafDesc_kernelPairRelation
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf)
    (hflat : HasProperty B S hS (flatProperty B S hS) f hf)
    (hlfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf) :
    IsIso (quotientSheafDesc (kernelPairRelation f) ⟨F, hF⟩ f
      (isPullback_kernelPairRelation f).w) :=
  isIso_quotientSheafDesc_of_flat_chart (kernelPairRelation f) hF hX f hf hsurj hflat hlfp
    (isPullback_kernelPairRelation f)

end AlgebraicGeometry.Space

end
