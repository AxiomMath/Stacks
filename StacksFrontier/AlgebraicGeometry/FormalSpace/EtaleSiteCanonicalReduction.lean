module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSiteCanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition

/-!
# Stacks 0DED: the small étale site of a representable étale morphism of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S` which is representable by algebraic spaces and étale. Stacks 0DED
attaches to `f` a functor `j : X_étale ⟶ Y_étale` between the small étale sites of Stacks 0DEA,
asserts that `j` is cocontinuous, that the morphism of topoi `f_small` of Stacks 0DEC, part (3),
is the morphism of topoi that Sites 00XO attaches to `j`, and that `j` is continuous as well, so
that Sites 00XR applies to it.

The small étale site of a formal algebraic space is by definition the small étale site of its
reduction, and Stacks 0AIN says that a reduction exists. The reduction here is
`AlgebraicGeometry.FormalSpace.canonicalReduction`, the one chosen from that existence
statement, so the four assertions are about `f` and nothing else.

## Main definitions

* `AlgebraicGeometry.FormalSpace.canonicalSmallEtalePostcomp`: **Stacks 0DED**, the functor
  `j : X_étale ⟶ Y_étale`.
* `AlgebraicGeometry.FormalSpace.canonicalSmallToposMorphism_pushforwardIso`: **Stacks 0DED**,
  the identification of `f_small` with the morphism of topoi of Sites 00XO attached to `j`.
* `AlgebraicGeometry.FormalSpace.canonicalSmallToposMorphism_inverseImageObjObjIso`:
  **Stacks 0DED**, the formula on sections that Sites 00XR gives for a functor which is
  continuous as well as cocontinuous.

## Main results

* `AlgebraicGeometry.FormalSpace.isEtale_canonicalReductionMap`: **Stacks 0DED**, the induced
  morphism of reductions is étale. This is the content of the proof.
* `AlgebraicGeometry.FormalSpace.canonicalSmallEtalePostcomp_isCocontinuous` and
  `AlgebraicGeometry.FormalSpace.canonicalSmallEtalePostcomp_isContinuous`: **Stacks 0DED**, the
  two site properties of `j`.

## Implementation notes

`AlgebraicGeometry.FormalSpace.canonicalReduction`, and the passage from the shape in which
Stacks 0AIN produces a reduction to the bundled datum the étale sites are built from, are in
`StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSiteCanonical`, beside the sites of Stacks 0DEA
read at that reduction. Nothing
depends on the choice the canonical reduction makes: two reductions of one formal algebraic
space are canonically isomorphic by `AlgebraicGeometry.FormalSpace.Reduction.iso`, so the sites
of Stacks 0DEA at two choices are isomorphic as well.

The four assertions are not reproved here. They are the declarations of
`StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition`, which state them for an
arbitrary reduction datum and whose proofs carry the mathematics — étaleness of the induced
morphism of reductions, and Stacks 03LP for everything about the sites and the topoi — read at
the canonical reduction.

## References

* [Stacks Project, Tag 0DED](https://stacks.math.columbia.edu/tag/0DED)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DEC](https://stacks.math.columbia.edu/tag/0DEC)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : FppfSheaf B S hS}

/-! ### Stacks 0DED -/

/-- **Stacks 0DED**, the content of the proof. Let `f : X ⟶ Y` be a morphism of formal algebraic
spaces over `S` which is representable by algebraic spaces and étale. Then the induced morphism
of reductions `X_red ⟶ Y_red` is an étale morphism of algebraic spaces over `S`. -/
@[stacks 0DED "étaleness of the induced morphism of reductions, which is the content of the
  proof"]
theorem isEtale_canonicalReductionMap (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    Space.IsEtale B S hS ((canonicalReduction hX).map (canonicalReduction hY) f).hom :=
  Reduction.isEtale_map hX hY (canonicalReduction hX) (canonicalReduction hY) f hrep het

/-- **Stacks 0DED.** The functor `j : X_étale ⟶ Y_étale` attached to a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` which is representable by algebraic spaces and étale:
postcomposition of an étale scheme chart of `X_red` with the induced étale morphism of
reductions, which is the functor of Stacks 03LP at that morphism. -/
@[stacks 0DED "the functor `j : X_étale ⟶ Y_étale`"]
noncomputable def canonicalSmallEtalePostcomp (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    (canonicalReduction hX).SmallEtale ⥤ (canonicalReduction hY).SmallEtale :=
  Reduction.smallEtalePostcomp hX hY (canonicalReduction hX) (canonicalReduction hY) f hrep het

/-- **Stacks 0DED.** The functor `j` is cocontinuous: a covering sieve of `jU` in `Y_étale`
pulls back to a covering sieve of `U` in `X_étale`. -/
@[stacks 0DED "cocontinuity of `j`"]
instance canonicalSmallEtalePostcomp_isCocontinuous (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    (canonicalSmallEtalePostcomp hX hY f hrep het).IsCocontinuous
      (canonicalReduction hX).smallEtaleTopology (canonicalReduction hY).smallEtaleTopology :=
  Reduction.smallEtalePostcomp_isCocontinuous hX hY (canonicalReduction hX)
    (canonicalReduction hY) f hrep het

/-- **Stacks 0DED.** The functor `j` is continuous as well, so Sites 00XR applies to it. -/
@[stacks 0DED "continuity of `j`, which is what makes Sites 00XR applicable"]
instance canonicalSmallEtalePostcomp_isContinuous (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    (canonicalSmallEtalePostcomp hX hY f hrep het).IsContinuous
      (canonicalReduction hX).smallEtaleTopology (canonicalReduction hY).smallEtaleTopology :=
  Reduction.smallEtalePostcomp_isContinuous hX hY (canonicalReduction hX)
    (canonicalReduction hY) f hrep het

/-- **Stacks 0DED.** The morphism of topoi `f_small` of Stacks 0DEC, part (3), is the morphism
of topoi that Sites 00XO attaches to the cocontinuous functor `j`: its direct image is the
direct image of `j`. -/
@[stacks 0DED "`f_small` is the morphism of topoi that Sites 00XO attaches to `j`, identified on
  direct images"]
noncomputable def canonicalSmallToposMorphism_pushforwardIso
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep) :
    ((canonicalReduction hX).smallToposMorphism (canonicalReduction hY) f).pushforward ≅
      (canonicalSmallEtalePostcomp hX hY f hrep het).sheafPushforwardCocontinuous
        (Type (u + 1)) (canonicalReduction hX).smallEtaleTopology
        (canonicalReduction hY).smallEtaleTopology :=
  Reduction.smallToposMorphism_pushforwardIso hX hY (canonicalReduction hX)
    (canonicalReduction hY) f hrep het

/-- **Stacks 0DED**, the consequence of continuity of `j` recorded by Sites 00XR: the inverse
image of `f_small` is restriction along `j`, so a section of `f_small^{-1} G` over an étale
chart `U` of `X_red` is a section of `G` over the chart `jU` of `Y_red`. -/
@[stacks 0DED "the formula on sections which Sites 00XR gives for `j`, continuous as well as
  cocontinuous"]
noncomputable def canonicalSmallToposMorphism_inverseImageObjObjIso
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f.hom hrep)
    (G : Sheaf (canonicalReduction hY).smallEtaleTopology (Type (u + 1)))
    (U : (canonicalReduction hX).SmallEtale) :
    (((canonicalReduction hX).smallToposMorphism (canonicalReduction hY) f).inverseImage.obj
        G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op ((canonicalSmallEtalePostcomp hX hY f hrep het).obj U)) :=
  Reduction.smallToposMorphism_inverseImageObjObjIso hX hY (canonicalReduction hX)
    (canonicalReduction hY) f hrep het G U

end AlgebraicGeometry.FormalSpace

end
