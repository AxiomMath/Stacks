module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionCorrespondence

/-!
# The incidence correspondence of Tag 0B1S is proper over the parameter space

The clause-(2) bad locus of Tag 0B1S is produced as an *image*: Tag 0B2L bounds the codimension
of `[g]` in terms of the dimension of the fibre of the incidence correspondence
`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` over `[g]`, so the subset of `𝐏` the bound applies
to is the image under `π : T ⟶ 𝐏` of the locus in `T` where the fibre dimension jumps. For that
image to be the *closed* subset the genericity of Tag 0B2T consumes, `π` must be a closed map —
and the locus where the fibre dimension jumps is closed in `T`, being the complement of the dense
open of Tag 0B2L part (2b).

This file proves that `π` is proper. The reason is the one the source takes for granted when it
says "`B` is closed": `T` lies in `X × Y × 𝐏` with `X × Y` proper over the ground field, so the
projection forgetting `X × Y` is proper; nothing about `T` itself is used beyond its being a
closed subscheme of that product. Properness of `π` is got as properness over `Spec k` divided by
separatedness of `𝐏` over `Spec k`, which is the same step as in
`AlgebraicGeometry.ProjectiveSpaceOfModule.isFinite_endProjection_of_isClosedImmersion`.

Taking the correspondence over *all* of `𝐏` — rather than over the invertible classes, where the
source's incidence argument lives — is what makes this available: the projection from a product
with `PGL(V)` as its last factor is not proper, `PGL(V)` not being closed in `𝐏`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_tpFst`: the projection of the triple
  product `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` to its first two factors is proper.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_transitionProj`: so is the projection of the
  correspondence to `𝐏(V) ×_k 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_transitionVarietyToBase`: and so is the
  projection of the correspondence over any base to that base, properness being stable under base
  change.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionVarietyToPar_comp_toSpec`: the projection
  to the parameter space is a morphism over `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_transitionVarietyToPar` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar`: over a base
  proper over the ground field the projection to the parameter space is proper, hence carries
  closed subsets to closed subsets. **This is the closedness of the bad locus that the source
  asserts without proof.**

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- **The projection of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` to its first two factors is proper**, being the
base change of the structure morphism of the parameter space, which is proper. -/
public instance isProper_tpFst [Nontrivial (ParameterModule k V)] : IsProper (tpFst k V) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
    (isProper_projectiveSpaceOfModuleToSpec k (ParameterModule k V))

/-- **The projection of the incidence correspondence to `𝐏(V) ×_k 𝐏(V)` is proper**, being a
closed immersion followed by the proper projection of the triple product. -/
public instance isProper_transitionProj [Nontrivial (ParameterModule k V)] :
    IsProper (transitionProj k V) := by
  rw [transitionProj]
  infer_instance

/-- **The projection of the incidence correspondence over a base to that base is proper**,
properness being stable under base change. -/
public instance isProper_transitionVarietyToBase [Nontrivial (ParameterModule k V)]
    {S : Scheme.{u}} (f : S ⟶ prodTwo k V) : IsProper (transitionVarietyToBase k V f) :=
  MorphismProperty.of_isPullback (isPullback_transitionVariety k V f)
    (isProper_transitionProj k V)

omit [Nontrivial V] in
/-- **The projection of the incidence correspondence over a base to the parameter space is a
morphism over `Spec k`**, the structure morphism of the total space being the one the base
inherits from `𝐏(V) ×_k 𝐏(V)`. -/
public theorem transitionVarietyToPar_comp_toSpec {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    transitionVarietyToPar k V f ≫ projectiveSpaceOfModuleToSpec k (ParameterModule k V) =
      transitionVarietyToBase k V f ≫ f ≫ prodTwoToSpec k V := by
  have hfst : tpFst k V ≫ prodTwoToSpec k V =
      tpPar k V ≫ projectiveSpaceOfModuleToSpec k (ParameterModule k V) :=
    pullback.condition
  calc transitionVarietyToPar k V f ≫
        projectiveSpaceOfModuleToSpec k (ParameterModule k V)
      = transitionVarietyToSubscheme k V f ≫ transitionSubschemeι k V ≫
          tpPar k V ≫ projectiveSpaceOfModuleToSpec k (ParameterModule k V) := by
        rw [transitionVarietyToPar, transitionProjPar]
        simp only [Category.assoc]
    _ = transitionVarietyToSubscheme k V f ≫ transitionProj k V ≫ prodTwoToSpec k V := by
        rw [← hfst, transitionProj]
        simp only [Category.assoc]
    _ = transitionVarietyToBase k V f ≫ f ≫ prodTwoToSpec k V := by
        rw [← Category.assoc, ← Category.assoc,
          (isPullback_transitionVariety k V f).w]

omit [Nontrivial V] in
/-- **Over a base proper over the ground field the projection of the incidence correspondence to
the parameter space is proper.** The total space is proper over `Spec k`, being proper over the
base, and the parameter space is separated over `Spec k`; a morphism whose composite with a
separated morphism is proper is proper. -/
public theorem isProper_transitionVarietyToPar [Nontrivial (ParameterModule k V)]
    {S : Scheme.{u}} (f : S ⟶ prodTwo k V) (hS : IsProper (f ≫ prodTwoToSpec k V)) :
    IsProper (transitionVarietyToPar k V f) := by
  have : IsProper (transitionVarietyToPar k V f ≫
      projectiveSpaceOfModuleToSpec k (ParameterModule k V)) := by
    rw [transitionVarietyToPar_comp_toSpec]
    infer_instance
  exact IsProper.of_comp _ (projectiveSpaceOfModuleToSpec k (ParameterModule k V))

omit [Nontrivial V] in
/-- **The image of a closed subset of the incidence correspondence in the parameter space is
closed.** This is the step the source of Tag 0B1S asserts without proof — "Moreover, `B` is
closed" — for the bad locus it produces as the image of the fibre-dimension jump locus. -/
public theorem isClosed_image_transitionVarietyToPar [Nontrivial (ParameterModule k V)]
    {S : Scheme.{u}} (f : S ⟶ prodTwo k V) (hS : IsProper (f ≫ prodTwoToSpec k V))
    {C : Set (transitionVariety k V f)} (hC : IsClosed C) :
    IsClosed ((transitionVarietyToPar k V f).base '' C) := by
  have := isProper_transitionVarietyToPar k V f hS
  exact (transitionVarietyToPar k V f).isClosedMap C hC

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
