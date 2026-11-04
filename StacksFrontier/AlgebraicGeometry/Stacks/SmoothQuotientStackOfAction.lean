module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack

/-!
# The quotient stack of a flat group action is smooth over the base (Stacks 0DLS)

Let `X ⟶ Y` be a smooth morphism of algebraic spaces over a scheme `S` of a big fppf site, let
`G` be a group algebraic space over `Y` which is flat and locally of finite presentation over
`Y`, and let `G` act on `X` over `Y`. **Stacks 0DLS** says that the quotient stack `[X/G]` is
smooth over `Y`.

The source's proof descends smoothness along the atlas `X ⟶ [X/G]`, which is surjective, flat
and locally of finite presentation by Stacks 06FH; the descent itself is Stacks 0AHE. Stacks 06FH
asks the source and the target of the groupoid to be flat and locally of finite presentation. For
the action groupoid `(X, G ×_Y X, pr₂, a, m)` of Stacks 0444 the source `pr₂` is the base change
of `G ⟶ Y` along `X ⟶ Y`, and the target `a` is `pr₂` precomposed with the involution
`(g, x) ↦ (g⁻¹, g · x)`, so both inherit every property of `G ⟶ Y` which is étale local on the
source and the target and stable under base change.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_actionGroupoid`: the source and the target of
  the action groupoid inherit such a property from `G ⟶ Y`.
* `AlgebraicGeometry.Stack.isSmooth_quotientStackModelToBaseOfGroupoid_of_action`: the
  smoothness of `[X/G] ⟶ Y` for any construction of the action groupoid.
* `AlgebraicGeometry.Stack.isSmooth_quotientStackModelToBase`: **Stacks 0DLS**.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Stacks/SmoothQuotientStack.lean`, the quotient stack is read
on a model: an object `𝒳` of `AlgebraicGeometry.Stack.AlgebraicStacks` with an equivalence `e`
over the big fppf site between `[X/G]` and `𝒳`. The stackification of Stacks 044Q has its
morphisms one universe above those of that 2-category, where smoothness of a 1-morphism of
algebraic stacks (Stacks 075U) is defined, so `[X/G]` itself is not an object of it; smoothness
being invariant under equivalence over the site, the conclusion at every model is the source's
claim. The atlas properties of Stacks 06FH on the model are
`AlgebraicGeometry.Stack.quotientModelAtlasFppf`, the identification of Stacks 044R is
`AlgebraicGeometry.Stack.representingMap_quotientStackModelProjection_comp`, and the descent is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_of_fppf`.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 0AHE](https://stacks.math.columbia.edu/tag/0AHE)
* [Stacks Project, Tag 0DLS](https://stacks.math.columbia.edu/tag/0DLS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **The structure maps of an action groupoid inherit the properties of the group.** Let `P` be
a property of morphisms of schemes which is étale local on the source and the target and stable
under base change, and let a group algebraic space `G` over an algebraic space `B` act on an
algebraic space `X` over `B`. If `G ⟶ B` has `P` on every étale chart, then so do the source and
the target of the action groupoid of Stacks 0444.

The source is the second projection of `G ×_B X`, the base change of `G ⟶ B` along `X ⟶ B`, and
the target is the source precomposed with the inversion involution `(g, x) ↦ (g⁻¹, g · x)`. -/
theorem holdsOnEveryEtaleChart_actionGroupoid (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) [P.IsStableUnderBaseChange]
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (A : ActionGroupoidConstruction B G X hG hX)
    (hGP : HoldsOnEveryEtaleChart C S hS P G.hom) :
    HoldsOnEveryEtaleChart C S hS P A.groupoid.source.hom ∧
      HoldsOnEveryEtaleChart C S hS P A.groupoid.target.hom := by
  have hsnd : HoldsOnEveryEtaleChart C S hS P (snd G X).left :=
    (holdsOnEveryEtaleChart_isStableUnderBaseChange C S hS P hP).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct C S hS
        (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
        (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B)) hGP
  have hinv : (Stacks.Groupoids.ActionGroupoid.inverse G X).left ≫
      (Stacks.Groupoids.ActionGroupoid.inverse G X).left = 𝟙 _ :=
    congrArg (fun q : (G ⊗ X) ⟶ (G ⊗ X) => q.left)
      (Stacks.Groupoids.ActionGroupoid.inverse_comp_inverse G X)
  have htgt : HoldsOnEveryEtaleChart C S hS P (γ[G, X] : G ⊗ X ⟶ X).left :=
    holdsOnEveryEtaleChart_of_isoSource P
      ⟨(Stacks.Groupoids.ActionGroupoid.inverse G X).left,
        (Stacks.Groupoids.ActionGroupoid.inverse G X).left, hinv, hinv⟩
      (congrArg (fun q : (G ⊗ X) ⟶ X => q.left)
        (Stacks.Groupoids.ActionGroupoid.inverse_target G X)) hsnd
  have transport : ∀ {F F' H H' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : F' ⟶ H'),
      F' = F → H' = H → HEq f g → HoldsOnEveryEtaleChart C S hS P g →
        HoldsOnEveryEtaleChart C S hS P f := by
    intro F F' H H' f g hF hH hfg hg
    subst hF hH
    rwa [eq_of_heq hfg]
  have hobj : X.left = A.groupoid.objects.obj :=
    (congrArg (fun Z : AlgebraicSpaces C S hS => Z.obj) A.objects_eq).symm
  have hars : pullback G.hom X.hom = A.groupoid.arrows.obj :=
    (congrArg (fun Z : AlgebraicSpaces C S hS => Z.obj) A.arrows_eq).symm
  exact ⟨transport _ _ hars hobj A.source_eq hsnd, transport _ _ hars hobj A.target_eq htgt⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quotient stack of a flat group action is smooth over the base, for any construction of
the action groupoid.** Let `X ⟶ Y` be a smooth morphism of algebraic spaces over `S`, let `G` be
a group algebraic space over `Y` which is flat and locally of finite presentation over `Y`, acting
on `X` over `Y`, and let `A` be an action groupoid of Stacks 0444 for this action. Then for every
algebraic stack `𝒳` equivalent over the site to the quotient stack of `A`, the canonical morphism
`𝒳 ⟶ Y` of Stacks 044R is smooth. -/
theorem isSmooth_quotientStackModelToBaseOfGroupoid_of_action
    (Y : AlgebraicSpaces B S hS) (G X : Over Y.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left)
    (A : Space.ActionGroupoidConstruction Y G X hG hX)
    (hXsmooth : Space.IsSmooth B S hS X.hom)
    (hGflat : Space.IsFlat B S hS G.hom)
    (hGlfp : Space.IsLocallyOfFinitePresentation B S hS G.hom)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack A.groupoid).p 𝒳.val.val.p) :
    AlgebraicStacks.IsSmooth B S hS
      (quotientStackModelToBaseOfGroupoid.{u, w} B S hS Y A.groupoid 𝒳 e) := by
  obtain ⟨hsFlat, htFlat⟩ := Space.holdsOnEveryEtaleChart_actionGroupoid _
    Flat.isEtaleLocalOnSourceAndTarget Y G X hG hX A hGflat
  obtain ⟨hsLfp, htLfp⟩ := Space.holdsOnEveryEtaleChart_actionGroupoid _
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget Y G X hG hX A hGlfp
  have hbase : ∀ (Z : AlgebraicSpaces B S hS) (f : Z ⟶ Y), Z = ⟨X.left, hX⟩ →
      HEq f.hom X.hom → Space.IsSmooth B S hS f.hom := by
    intro Z f hZ hf
    subst hZ
    rw [eq_of_heq hf]
    exact hXsmooth
  exact isSmooth_quotientStackModelToBaseOfGroupoid.{u, w} B S hS Y A.groupoid
    (hbase _ _ A.objects_eq A.objectsToBase_eq) 𝒳 e
    (quotientModelAtlasFppf A.groupoid 𝒳 e hsFlat htFlat hsLfp htLfp)

/-- **Stacks 0DLS.** Let `X ⟶ Y` be a smooth morphism of algebraic spaces over `S`, let `G` be a
group algebraic space over `Y` which is flat and locally of finite presentation over `Y`, and let
`G` act on `X` over `Y`. Then the quotient stack `[X/G]` is smooth over `Y`: for every algebraic
stack `𝒳` equivalent over the big fppf site to `[X/G]`, the canonical morphism `[X/G] ⟶ Y` of
Stacks 044R, read on `𝒳`, is a smooth 1-morphism of algebraic stacks in the sense of
Stacks 075U. -/
@[stacks 0DLS]
theorem isSmooth_quotientStackModelToBase
    (Y : AlgebraicSpaces B S hS) (G X : Over Y.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left)
    (hXsmooth : Space.IsSmooth B S hS X.hom)
    (hGflat : Space.IsFlat B S hS G.hom)
    (hGlfp : Space.IsLocallyOfFinitePresentation B S hS G.hom)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (actionGroupoid B S hS Y G X hG hX)).p 𝒳.val.val.p) :
    AlgebraicStacks.IsSmooth B S hS
      (quotientStackModelToBase.{u, w} B S hS Y G X hG hX 𝒳 e) :=
  isSmooth_quotientStackModelToBaseOfGroupoid_of_action.{u, w} B S hS Y G X hG hX
    (Space.groupoidOfAction Y G X hG hX) hXsmooth hGflat hGlfp 𝒳 e

end AlgebraicGeometry.Stack

end
