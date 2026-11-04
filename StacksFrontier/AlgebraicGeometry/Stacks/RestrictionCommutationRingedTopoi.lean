module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionProjection

/-!
# The restriction square of a morphism of categories representable by algebraic spaces

Let `S` be a scheme in a big fppf site and let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred
in groupoids over `(Sch/S)_{fppf}`, with `𝒳` representable by an algebraic space `F` and `𝒴` by
an algebraic space `G`. Writing `f : F ⟶ G` for the induced morphism of algebraic spaces and
`f_small : Sh(F_étale) ⟶ Sh(G_étale)` for the associated morphism of small étale ringed topoi,
Stacks 073N asserts that the square

```
(Sh(𝒳_étale), 𝒪_𝒳) ---f---> (Sh(𝒴_étale), 𝒪_𝒴)
       |                            |
      π_F                          π_G
       |                            |
       v                            v
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
```

commutes as a diagram of ringed topoi, i.e. that its two composites `π_G ∘ f` and
`f_small ∘ π_F` are 2-isomorphic in the sense of Stacks 04IC.

This file states that square: it gives the two composites and assembles a 2-isomorphism between
them from a comparison of their direct images. The square is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionRingedSquareCommutes.lean`.

## Main definitions

* `AlgebraicGeometry.Space.restrictionSquareFibredLeg` is the composite `π_G ∘ f`, the way around
  the square that restricts after pushing forward along the 1-morphism.
* `AlgebraicGeometry.Space.restrictionSquareSpaceLeg` is the composite `f_small ∘ π_F`, the way
  around the square that pushes forward on small étale sites after restricting.
* `AlgebraicGeometry.Space.restrictionRingedSquare`: the square, assembled from a comparison
  of the two direct images and its compatibility with the structure sheaves. Stacks 073N itself
  is `AlgebraicGeometry.Space.restrictionRingedSquareTwoIso`, in
  `StacksFrontier/AlgebraicGeometry/Stacks/RestrictionRingedSquareCommutes.lean`.

## Main results

* `AlgebraicGeometry.Space.restrictionSquareFibredLeg_pushforward` and
  `AlgebraicGeometry.Space.restrictionSquareSpaceLeg_pushforward`: the direct images of the two
  composites are `π_{G,*} ∘ f_*` and `f_{small,*} ∘ π_{F,*}`, with both projections spelled as
  restriction along the functor `F_étale ⥤ 𝒳` of Stacks 073M. This is what identifies the
  2-isomorphism the square asserts with the source's identity
  `f_{small,*}π_{F,*}𝒢 = π_{G,*}f_*𝒢`, and it is what makes the hypothesis of
  `restrictionRingedSquare` a statement about restriction of sections rather than about an
  opaque composite.
* `AlgebraicGeometry.Space.restrictionSquareFibredLeg_forgetFSharp` and
  `AlgebraicGeometry.Space.restrictionSquareSpaceLeg_forgetFSharp`: the structure maps of the two
  composites, on underlying sheaves of sets, as the composites of the structure maps of their two
  factors. These are what reduce the compatibility half of the square to the hypothesis `hsq`
  below, which mentions only the structure maps of the four morphisms of the square and none of
  the composites.

## Implementation notes

**Where the square is proved.** Stacks 073N has two halves. One is the comparison itself: a
natural isomorphism `π_{G,*}f_* ≅ f_{small,*}π_{F,*}` of the two direct images. The other is that
this comparison is compatible with the two structure maps, which is what upgrades it from a
2-isomorphism of morphisms of topoi to one of morphisms of *ringed* topoi. This file states the
square and reduces the compatibility field of the 2-isomorphism to `hsq`, a statement about the
four structure maps of the square. The comparison is the canonical map of equation 075M,
`AlgebraicGeometry.Space.restrictedDirectImageComparison`, which is invertible by
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison` and satisfies `hsq` by
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`; the two are
put together, at the induced morphism of algebraic spaces and with no size hypothesis, in
`AlgebraicGeometry.Space.restrictionRingedSquareTwoIso`.

**Orientation.** `π_F` is the morphism of ringed topoi *out of* `Sh(𝒳_étale)`, whose direct image
is restriction along the functor `F_étale ⥤ 𝒳`
(`AlgebraicGeometry.Space.projectionRingedToposHom`). It is not
`AlgebraicGeometry.Space.restrictionRingedToposHom`, which is the morphism `i_F` of the same
Stacks 073M, pointing the other way, from `Sh(F_étale)` to `Sh(𝒳_étale)`, and whose *inverse*
image is that restriction. Equation 075K identifies the two restrictions, `ℱ|_{F_étale} =
i_F⁻¹ℱ = π_{F,*}ℱ`, but only `π_F` composes on the correct side to form this square.

**The morphism of algebraic spaces.** The parameter `fSpace` here is a free morphism
`F ⟶ G`, because nothing in the statement of the square needs it to be compatible with
`f : 𝒳 ⥤ 𝒴`. Stacks 073N is about the induced morphism
`AlgebraicGeometry.Space.inducedSpacesHom`, and that is the one
`AlgebraicGeometry.Space.restrictionRingedSquareTwoIso` uses.

## References

* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 075K](https://stacks.math.columbia.edu/tag/075K)
* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w v' w'

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)

/-! ### The two composites around the square -/

section Legs

variable (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)
  (fSpace : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  [∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P]

/-- The composite `π_G ∘ f` of the square of Stacks 073N: push forward along the 1-morphism
`f : 𝒳 ⥤ 𝒴`, then restrict to the small étale site of `G`. -/
noncomputable def restrictionSquareFibredLeg :
    RingedToposHom (FibredSite.associatedRingedTopos B S hS p hp .etale)
      (smallEtaleRingedTopos B S hS ⟨G, hG⟩) :=
  RingedToposHom.comp (X := FibredSite.associatedRingedTopos B S hS p hp .etale)
    (Y := FibredSite.associatedRingedTopos B S hS q hq .etale)
    (Z := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
    (projectionRingedToposHom B S hS G q hq hG eG)
    (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)

/-- The composite `f_small ∘ π_F` of the square of Stacks 073N: restrict to the small étale site
of `F`, then push forward along the induced morphism of algebraic spaces. -/
noncomputable def restrictionSquareSpaceLeg :
    RingedToposHom (FibredSite.associatedRingedTopos B S hS p hp .etale)
      (smallEtaleRingedTopos B S hS ⟨G, hG⟩) :=
  RingedToposHom.comp (X := FibredSite.associatedRingedTopos B S hS p hp .etale)
    (Y := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
    (Z := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
    (smallEtaleRingedToposHom B S hS fSpace)
    (projectionRingedToposHom B S hS F p hp hF eF)

/-- The direct image of `π_G ∘ f` is `f_*` followed by restriction along the functor
`G_étale ⥤ 𝒴` of Stacks 073M, that is, `(π_{G,*}f_*𝒢)(V) = (f_*𝒢)(u_G V)`. -/
theorem restrictionSquareFibredLeg_pushforward :
    letI := restrictionFunctor_isContinuous B S hS G q hq eG
    (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf).toToposHom.pushforward =
      (FibredSite.ringedToposMorphism B S hS p q hp hq f hf
            .etale).toToposHom.pushforward ⋙
        (restrictionFunctor B S hS G q eG).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS G)
          (BigFppfOver.associatedTopology B S hS q .etale) :=
  rfl

/-- The direct image of `f_small ∘ π_F` is restriction along the functor `F_étale ⥤ 𝒳` of
Stacks 073M followed by the small étale direct image of Stacks 03G2, that is,
`(f_{small,*}π_{F,*}𝒢)(V) = (π_{F,*}𝒢)(V ×_G F)`. -/
theorem restrictionSquareSpaceLeg_pushforward :
    letI := restrictionFunctor_isContinuous B S hS F p hp eF
    (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace).toToposHom.pushforward =
      (restrictionFunctor B S hS F p eF).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS F)
          (BigFppfOver.associatedTopology B S hS p .etale) ⋙
        (smallToposMorphismTypeU B S hS fSpace).pushforward :=
  rfl

/-- The structure map of `π_G ∘ f`, on underlying sheaves of sets: the structure map of `π_G`
followed by the direct image under `π_G` of the structure map of `f`. -/
theorem restrictionSquareFibredLeg_forgetFSharp :
    RingedToposHom.forgetFSharp
        (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf) =
      RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
        (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)) :=
  RingedToposHom.forgetFSharp_comp (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
    (B := FibredSite.associatedRingedTopos B S hS q hq .etale)
    (C := smallEtaleRingedTopos B S hS ⟨G, hG⟩) _ _

/-- The structure map of `f_small ∘ π_F`, on underlying sheaves of sets: the structure map of
`f_small` followed by the direct image under `f_small` of the structure map of `π_F`. -/
theorem restrictionSquareSpaceLeg_forgetFSharp :
    RingedToposHom.forgetFSharp
        (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) ≫
        (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF)) :=
  RingedToposHom.forgetFSharp_comp (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
    (B := smallEtaleRingedTopos B S hS ⟨F, hF⟩)
    (C := smallEtaleRingedTopos B S hS ⟨G, hG⟩) _ _

/-- The square of ringed topoi of Stacks 073N, assembled from a comparison of the two direct
images and its compatibility with the structure sheaves.

The argument `cmp` is a natural isomorphism of the two direct images
`π_{G,*}f_* ≅ f_{small,*}π_{F,*}`, which by `restrictionSquareFibredLeg_pushforward` and
`restrictionSquareSpaceLeg_pushforward` is the source's identity
`π_{G,*}f_*𝒢(V) = f_{small,*}π_{F,*}𝒢(V)`, naturally in `𝒢`. The argument `hsq` is its
compatibility with the structure sheaves, written in terms of the structure maps of the four
morphisms of the square and not of the two composites.

This is the assembly step only. Stacks 073N itself, with both arguments supplied by the canonical
comparison of equation 075M at the induced morphism of algebraic spaces, is
`AlgebraicGeometry.Space.restrictionRingedSquareTwoIso`. -/
noncomputable def restrictionRingedSquare
    (cmp : (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf).toToposHom.pushforward ≅
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace).toToposHom.pushforward)
    (hsq : RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS G q hq hG eG) ≫
        (projectionRingedToposHom B S hS G q hq hG eG).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp
            (FibredSite.ringedToposMorphism B S hS p q hp hq f hf .etale)) ≫
        cmp.hom.app ((FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.obj
          (FibredSite.associatedRingedTopos B S hS p hp .etale).O) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS fSpace) ≫
        (smallEtaleRingedToposHom B S hS fSpace).toToposHom.pushforward.map
          (RingedToposHom.forgetFSharp (projectionRingedToposHom B S hS F p hp hF eF))) :
    RingedToposHom.TwoIso
      (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
      (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
      (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf)
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF fSpace) where
  e := cmp
  commutes :=
    (congrArg (fun z ↦ z ≫ cmp.hom.app
        ((FibredSite.associatedRingedTopos B S hS p hp .etale).forgetRing.obj
          (FibredSite.associatedRingedTopos B S hS p hp .etale).O))
      (restrictionSquareFibredLeg_forgetFSharp B S hS G p q hp hq hG eG f hf)).trans
      ((Category.assoc _ _ _).trans
        (hsq.trans
          (restrictionSquareSpaceLeg_forgetFSharp B S hS F G p hp hF hG eF fSpace).symm))

end Legs

end AlgebraicGeometry.Space

end
