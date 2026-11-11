module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset

/-!
# The hypotheses of the generalized derived existence theorem

Tag 0DIR proposes a generalization of Grothendieck's existence theorem in its derived form for
algebraic spaces (Tag 0DIQ) in which the structure morphism `X → Spec A` is assumed only
separated and of finite presentation, and each `Kₙ` only pseudo-coherent relative to `Aₙ` and
supported on a closed subset of `Xₙ` proper over `Aₙ`. Its precise form and proof, for `X` flat,
are in `StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupported` and
`…DerivedExistenceSupportedAffine`; without flatness it fails
(`StacksFrontier.Examples.Spaces.DerivedExistenceNotFlat`).

What is proved here is the comparison of hypotheses on the geometry. In a situation of
Tag 0DIK the structure morphism `X → Spec A` is proper, hence separated, and is of finite
presentation, so the two conditions the generalization places on `X` hold; and every closed
subset of an infinitesimal base change `Xₙ` is proper over `Spec Aₙ`, because `Xₙ → Spec Aₙ`
is proper, so the support condition the generalization places on `Kₙ` holds for every `Kₙ`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_of_isProper`: every closed subset of an algebraic
  space proper over `Y` is proper over `Y`.
* `AlgebraicGeometry.Space.DerivedExistenceSituation.isSeparated_and_isFinitePresentation`:
  in a situation of Tag 0DIK the structure morphism `X → Spec A` is separated and of finite
  presentation.
* `AlgebraicGeometry.Space.DerivedExistenceSituation.isProperOver_stageProjection`: in a
  situation of Tag 0DIK every closed subset of `Xₙ` is proper over `Spec Aₙ`.

## Implementation notes

Properness over a base of a closed subset of the points of an algebraic space is Tag 0CZD,
`AlgebraicGeometry.Space.IsProperOver`: properness of the reduced induced closed subspace on
that subset. Its inclusion into the ambient space is proper unconditionally, by
`AlgebraicGeometry.Space.isProper_ι_reducedClosedSubspace`, so the general statement is that
inclusion composed with a proper morphism, which is Tag 04XY.

The comparison here stops at the geometry. Pseudo-coherence relative to `Aₙ` is Tag 0CSY,
`AlgebraicGeometry.Space.IsRelativelyPseudoCoherent`, and its identification with
pseudo-coherence on `Xₙ` for a flat morphism locally of finite presentation (Tag 0DII) is
`AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent`; the comparison of the
condition the generalization places on `Kₙ` with the pseudo-coherence hypothesis of Tag 0DIK
through those results is not carried out in this file. The generalized theorem is stated and
proved elsewhere (see above).

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A closed subset of the points of an algebraic space proper over `Y` is proper over `Y`:
the inclusion of the reduced induced closed subspace is proper, and a composite of proper
morphisms is proper. -/
theorem isProperOver_of_isProper (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hproper : IsProper B S hS f) (T : Set (points B S hS X)) (hT : _root_.IsClosed T) :
    IsProperOver B S hS hX hY f hf T hT :=
  isProper_comp' B S hS (reducedClosedSubspace B S hS X hX T hT).ι f hX hY
    (isProper_ι_reducedClosedSubspace B S hS X hX T hT) hproper

namespace DerivedExistenceSituation

variable (D : DerivedExistenceSituation.{u})

/-- In a situation of Stacks 0DIK the structure morphism `X → Spec A` is separated, being
proper, and is of finite presentation: the two conditions that the generalization proposed in
Stacks 0DIR places on `X` hold. -/
theorem isSeparated_and_isFinitePresentation :
    IsSeparated D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom ∧
      IsFinitePresentation D.B (limitBase D.system) D.containsLimitBase D.X.hom.hom :=
  ⟨D.proper.1, D.finitePresentation⟩

/-- In a situation of Stacks 0DIK every closed subset of the infinitesimal base change `Xₙ` is
proper over `Spec Aₙ`, since `Xₙ → Spec Aₙ` is proper: the support condition that the
generalization proposed in Stacks 0DIR places on `Kₙ` holds for every object of `D(𝒪_{Xₙ})`. -/
theorem isProperOver_stageProjection (n : ℕ)
    (T : Set (points D.B (limitBase D.system) D.containsLimitBase
      (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).1))
    (hT : _root_.IsClosed T) :
    IsProperOver D.B (limitBase D.system) D.containsLimitBase
      (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).2
      (schemeSpace
        (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).2
      (D.stageProjection n).hom (D.isLocallyOfFiniteType_stageProjection n) T hT :=
  isProperOver_of_isProper D.B (limitBase D.system) D.containsLimitBase _ _ _ _
    (D.isProper_stageProjection n) T hT

end DerivedExistenceSituation

end AlgebraicGeometry.Space

end
