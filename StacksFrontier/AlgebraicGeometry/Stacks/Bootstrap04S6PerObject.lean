module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal

/-!
# The per-object shape of condition (3) of Stacks 04S6

`AlgebraicGeometry.Stack.Bootstrap04S6` asks condition (3) of [Stacks Project, Tag 04S6] of the
big fppf site over *every* object `T` of the big fppf site over `S`, for a morphism carrying its
properties as a single relatively representable hypothesis
`(Surjective ⊓ Flat ⊓ LocallyOfFinitePresentation).presheaf` rather than as three instances of
`AlgebraicGeometry.Space.HasProperty`. It follows from
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` over every object of the
site, and hence from condition (1), `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`.

## Main results

* `AlgebraicGeometry.Space.hasProperty_flatProperty_of_presheaf` and
  `AlgebraicGeometry.Space.hasProperty_locallyOfFinitePresentationProperty_of_presheaf`: the
  relatively representable forms of flatness and of local finite presentation give the forms of
  [Stacks Project, Tag 03XZ].
* `AlgebraicGeometry.Stack.bootstrap04S6_of_isBootstrapAlgebraicSpaceAlongFlatSurjection`:
  `AlgebraicGeometry.Stack.Bootstrap04S6` from
  `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` over every object.
* `AlgebraicGeometry.Stack.bootstrap04S6_of_quotientSheaf`: `AlgebraicGeometry.Stack.Bootstrap04S6`
  from condition (1) over every object.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a property of scheme morphisms is preserved by precomposition with étale morphisms, a
morphism of presheaves with the property after every represented base change has it on every
étale chart of each of its represented base changes. -/
private theorem holdsOnEveryEtaleChart_pullback_fst_of_presheaf (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y Z : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ Z), Etale i → P p → P (i ≫ p))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f)
    (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G) :
    HoldsOnEveryEtaleChart B S hS P (pullback.fst ξ f) :=
  presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS P hP _
    (presheaf_of_isPullback B S hS (IsPullback.of_hasPullback ξ f).flip hf)

/-- A morphism of presheaves on the big fppf site of `S` which is flat after every represented
base change is flat in the sense of Stacks 03XZ. -/
theorem hasProperty_flatProperty_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hflat : (MorphismProperty.inverseImage (@Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    HasProperty B S hS (flatProperty B S hS) f hf :=
  holdsOnEveryEtaleChart_pullback_fst_of_presheaf B S hS _
    (fun i p (_ : Etale i) (_ : Flat p) => inferInstance) hflat

/-- A morphism of presheaves on the big fppf site of `S` which is locally of finite presentation
after every represented base change is locally of finite presentation in the sense of
Stacks 03XZ. -/
theorem hasProperty_locallyOfFinitePresentationProperty_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hlfp : (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf :=
  holdsOnEveryEtaleChart_pullback_fst_of_presheaf B S hS _
    (fun i p (_ : Etale i) (_ : LocallyOfFinitePresentation p) => inferInstance) hlfp

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- If `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` holds over every
object of the big fppf site over `S`, then `AlgebraicGeometry.Stack.Bootstrap04S6` holds. -/
theorem bootstrap04S6_of_isBootstrapAlgebraicSpaceAlongFlatSurjection
    (h : ∀ T : BigFppfOver C S hS,
      Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection C T.left.1 T.left.2) :
    Bootstrap04S6 C S hS := by
  intro T F' hF' G' hG' g hg hgP
  have hrep : Space.IsRepresentableByAlgebraicSpaces C T.left.1 T.left.2 g :=
    Space.IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hg
  exact h T g hF' hG' hrep
    (Space.hasProperty_surjectiveMorphismProperty_of_presheaf _ _ _ g
      (Space.presheaf_inverseImage_mono _ _ _ (fun _ hp => hp.1.1) hgP) hrep)
    (Space.hasProperty_flatProperty_of_presheaf _ _ _ g
      (Space.presheaf_inverseImage_mono _ _ _ (fun _ hp => hp.1.2) hgP) hrep)
    (Space.hasProperty_locallyOfFinitePresentationProperty_of_presheaf _ _ _ g
      (Space.presheaf_inverseImage_mono _ _ _ (fun _ hp => hp.2) hgP) hrep)

/-- If the fppf quotient sheaf of a flat, locally finitely presented equivalence relation of
algebraic spaces is an algebraic space over every object of the big fppf site over `S`, then
`AlgebraicGeometry.Stack.Bootstrap04S6` holds. -/
theorem bootstrap04S6_of_quotientSheaf
    (h04S6 : ∀ T : BigFppfOver C S hS,
      Space.Bootstrap04S6QuotientSheaf C T.left.1 T.left.2) :
    Bootstrap04S6 C S hS :=
  bootstrap04S6_of_isBootstrapAlgebraicSpaceAlongFlatSurjection C S hS fun T =>
    Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf C T.left.1 T.left.2
      (h04S6 T)

end AlgebraicGeometry.Stack

end
