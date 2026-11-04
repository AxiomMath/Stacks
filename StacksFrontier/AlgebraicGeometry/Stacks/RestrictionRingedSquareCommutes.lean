module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageComparisonIso

/-!
# The restriction square of Stacks 073N commutes

Let `S` be a scheme and let `f : 𝒳 ⥤ 𝒴` be a morphism of categories fibred in groupoids over
`(Sch/S)_{fppf}`, with `𝒳` and `𝒴` representable by algebraic spaces `F` and `G`. Write
`f : F ⟶ G` for the induced morphism of algebraic spaces and `f_small` for the corresponding
morphism of small étale ringed topoi. This file states and proves Stacks 073N: the square

```
(Sh(𝒳_étale), 𝒪_𝒳) ---f---> (Sh(𝒴_étale), 𝒪_𝒴)
       |                            |
      π_F                          π_G
       v                            v
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
```

is a commutative diagram of ringed topoi, with no hypothesis beyond those of the source.

## Main definitions

* `AlgebraicGeometry.Space.restrictionRingedSquareTwoIso`: **Stacks 073N**, the 2-isomorphism
  of morphisms of ringed topoi between the two composites `π_G ∘ f` and `f_small ∘ π_F`.

## Implementation notes

The two composites are `AlgebraicGeometry.Space.restrictionSquareFibredLeg` and
`AlgebraicGeometry.Space.restrictionSquareSpaceLeg`; the morphisms `π_F` and `π_G` are those of
Stacks 073M (`AlgebraicGeometry.Space.projectionRingedToposHom`), the upper arrow is the morphism
of ringed topoi of Stacks 06TW (`AlgebraicGeometry.FibredSite.ringedToposMorphism`), and the
morphism of algebraic spaces is constructed from `f`
(`AlgebraicGeometry.Space.inducedSpacesHom`), not assumed.

The proof is the source's: the underlying isomorphism of direct images is the canonical
comparison of equation 075M, which is invertible because both sides are computed chartwise —
the left-hand side through the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` (Stacks 06W6) and the
right-hand side as an equalizer over étale charts of `F ×_G V` (Stacks 03H7, 03G2) — and its
structure-sheaf compatibility is checked on charts. The direct image along `f` needs a right Kan
extension along `f.op`; in the situation of Stacks 073N it exists unconditionally
(`AlgebraicGeometry.Space.hasPointwiseRightKanExtension_op_of_equivalenceOver`), so it is
supplied here rather than assumed.

## References

* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v w v' w'

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)

/-- Let `f : 𝒳 ⥤ 𝒴` be a morphism of categories fibred in groupoids over `(Sch/S)_{fppf}`,
with `𝒳` and `𝒴` representable by algebraic spaces `F` and `G` through the chosen equivalences
`eF` and `eG`. Write `f : F ⟶ G` for the induced morphism of algebraic spaces
(`AlgebraicGeometry.Space.inducedSpacesHom`) and `f_small` for the corresponding morphism of
small étale ringed topoi (`AlgebraicGeometry.Space.smallEtaleRingedToposHom`). Then the square
```
(Sh(𝒳_étale), 𝒪_𝒳) ---f---> (Sh(𝒴_étale), 𝒪_𝒴)
       |                            |
      π_F                          π_G
       v                            v
(Sh(F_étale), 𝒪_F) --f_small--> (Sh(G_étale), 𝒪_G)
```
is a commutative diagram of ringed topoi: this is a 2-isomorphism of morphisms of ringed topoi
(Stacks 04IC) between its two composites `π_G ∘ f`
(`AlgebraicGeometry.Space.restrictionSquareFibredLeg`) and `f_small ∘ π_F`
(`AlgebraicGeometry.Space.restrictionSquareSpaceLeg`), where `π_F` and `π_G` are the morphisms of
ringed topoi of Stacks 073M and the upper arrow is the morphism of ringed topoi of Stacks 06TW.

Its underlying isomorphism `π_{G,*}f_* ≅ f_{small,*}π_{F,*}` is the canonical comparison map of
equation 075M, which is invertible by
`AlgebraicGeometry.Space.isIso_restrictedDirectImageComparison`, and its compatibility with the
structure sheaves is
`AlgebraicGeometry.Space.restrictedDirectImageComparison_structureSheafCompatible`. The direct
image `f_*` exists with no size hypothesis, by
`AlgebraicGeometry.Space.hasPointwiseRightKanExtension_op_of_equivalenceOver`. -/
@[stacks 073N "the square of ringed topoi formed by pi_F, pi_G, the morphism induced by f and \
f_small commutes: its two composites are 2-isomorphic morphisms of ringed topoi"]
noncomputable def restrictionRingedSquareTwoIso :
    letI : ∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P :=
      hasPointwiseRightKanExtension_op_of_equivalenceOver B S hS F p G q eF eG f
    RingedToposHom.TwoIso
      (A := FibredSite.associatedRingedTopos B S hS p hp .etale)
      (B := smallEtaleRingedTopos B S hS ⟨G, hG⟩)
      (restrictionSquareFibredLeg B S hS G p q hp hq hG eG f hf)
      (restrictionSquareSpaceLeg B S hS F G p hp hF hG eF
        (inducedSpacesHom B S hS (X := ⟨F, hF⟩) (Y := ⟨G, hG⟩) p q eF eG f hf.comp_eq)) :=
  letI : ∀ P : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension P :=
    hasPointwiseRightKanExtension_op_of_equivalenceOver B S hS F p G q eF eG f
  restrictionRingedSquareOfInduced B S hS F G p q hp hq hF hG eF eG f hf

end AlgebraicGeometry.Space

end
