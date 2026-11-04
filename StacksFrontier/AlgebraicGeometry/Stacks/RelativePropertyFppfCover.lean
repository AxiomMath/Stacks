module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty

/-!
# Checking a relative property after an fppf cover of algebraic stacks (Stacks 06TY)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks representable by algebraic spaces, and let `g : 𝒵 ⟶ 𝒴` be representable by algebraic
spaces, surjective, flat and locally of finite presentation. Then `f` has the relative property
`P` of Stacks 03YK exactly when the first projection of a 2-fibre product of the cospan `(g, f)`
does.

## Main results

Both live in the namespace `AlgebraicGeometry.Stack`:

* `AlgebraicStacks.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`: a
  surjective, flat, locally finitely presented 1-morphism of algebraic stacks is locally
  essentially surjective on fibres for the big fppf topology.
* `hasRelativeProperty_iff_of_fppfCover`: **Stacks 06TY**.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 06TY](https://stacks.math.columbia.edu/tag/06TY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks over `S` which is representable by algebraic spaces,
surjective, flat and locally of finite presentation is locally essentially surjective on fibres:
every object of a fibre of the target becomes, after restriction to a covering sieve of the big
fppf topology, isomorphic to the image of an object of the source. -/
theorem AlgebraicStacks.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    {𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hSurj : IsSurjective B S hS g)
    (hFlat : AlgebraicStacks.IsFlat B S hS g)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒵.val.val.obj,
            ∃ φ : (CatFiberedInGroupoids.homFunctor g.hom).obj z ⟶ y.1,
              𝒴.val.val.p.IsHomLift k φ := by
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    B S hS g.hom hg ?_
  intro U y hy F hF he
  exact ⟨(pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hg).1
      hSurj U y hy F hF he,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒵.property 𝒴.property
      g.hom hg).1 hFlat U y hy F hF he,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      𝒵.property 𝒴.property g.hom hg).1
        ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
          𝒵.property 𝒴.property g.hom).1 hLfp) U y hy F hF he⟩

/-- Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base
change and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` representable by algebraic spaces, and let `g : 𝒵 ⟶ 𝒴` be
representable by algebraic spaces, surjective, flat and locally of finite presentation. Then `f`
has the relative property `P` of Stacks 03YK if and only if the projection to `𝒵` of a 2-fibre
product of the cospan `(g, f)` has it. -/
@[stacks 06TY]
theorem hasRelativeProperty_iff_of_fppfCover
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom)
    (hSurj : IsSurjective B S hS g)
    (hFlat : AlgebraicStacks.IsFlat B S hS g)
    (hLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q) :
    HasRelativeProperty B S hS P f.hom hf ↔
      ∃ hfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom,
        HasRelativeProperty B S hS P Q.fst.hom hfst := by
  have hD : Bicategory.IsTwoFibreProduct
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS Q) :=
    AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS Q hQ
  have hrep : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val 𝒴.val 𝒵.val
      f.hom g.hom (AlgebraicStacks.toCatFiberedInGroupoids B S hS Q) hD hf
  exact ⟨fun h => ⟨hrep, hasRelativeProperty_baseChange.{u, u, u + 1} B S hS P 𝒳.val 𝒴.val 𝒵.val
      f.hom g.hom (AlgebraicStacks.toCatFiberedInGroupoids B S hS Q) hD hf h⟩,
    fun ⟨_, h⟩ => hasRelativeProperty_of_baseChange.{u, u, u + 1, u} B S hS 𝒳.val 𝒴.val 𝒵.val P
      f.hom g.hom (AlgebraicStacks.toCatFiberedInGroupoids B S hS Q) hD hf
      (AlgebraicStacks.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation
        B S hS g hg hSurj hFlat hLfp) h⟩

end AlgebraicGeometry.Stack

end
