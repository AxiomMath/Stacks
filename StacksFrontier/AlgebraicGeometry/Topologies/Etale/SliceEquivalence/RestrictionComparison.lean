module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction along an arrow of the small étale site is inverse image

Let `B` be a big étale site, `X` a scheme in it, `J` the small étale topology of `X` and
`g : V ⟶ W` an arrow of the small étale site of `X`. There are two ways to restrict a sheaf on
`J` to the object `V`:

* localize twice — restrict to the slice `J.over W` with
  `CategoryTheory.GrothendieckTopology.overPullback`, then restrict along `g` with
  `CategoryTheory.GrothendieckTopology.overMapPullback`, then read the result on the small étale
  site of the *scheme* `V` through `AlgebraicGeometry.smallEtaleEquivalenceOver`;
* take the inverse image `(smallEtaleBaseChange B V.obj.hom).sheafPullback` along the structure
  morphism of `V`.

This file identifies the two. Together with the fact that restriction to the slice over the
final object loses nothing — `AlgebraicGeometry.SmallEtale.sheafOverFinalEquivalence`, the
small étale instance of `CategoryTheory.GrothendieckTopology.sheafOverTerminalEquivalence` —
this is what lets a statement about inverse images along the members of a covering of `X` be
handed to a descent theorem phrased on the localized site `J.over (SmallEtale.final B X hX)`,
where the members of the covering are arrows of a single slice category.

The two ingredients are both already available: the composition law
`CategoryTheory.GrothendieckTopology.overPullbackCompOverMapPullback`, which reduces the double
localization to a single one, and `AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose`
together with the equality `AlgebraicGeometry.overPullback_comp_sheafCongr_inverse`, which
identify a single localization with the inverse image.

## Main results

* `AlgebraicGeometry.SmallEtale.sheafOverFinalEquivalence` — restriction to the slice of the
  small étale site over its final object is an equivalence of sheaf categories.
* `AlgebraicGeometry.smallEtaleSheafPullbackIsoOverMapPullback` — the identification of the
  inverse image along the structure morphism of `V` with the double localization.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **Restriction to the slice of the small étale site over its final object is an equivalence
of sheaf categories.** The final object of the small étale site of `X` is `X` itself, which is
terminal there, so this is `CategoryTheory.GrothendieckTopology.sheafOverTerminalEquivalence`. -/
public def SmallEtale.sheafOverFinalEquivalence (A : Type w) [Category.{t} A] :
    Sheaf (SmallEtale.topology B X hX) A ≌
      Sheaf ((SmallEtale.topology B X hX).over (SmallEtale.final B X hX)) A :=
  (SmallEtale.topology B X hX).sheafOverTerminalEquivalence A
    (SmallEtale.finalIsTerminal B X hX)

/-- The functor of `AlgebraicGeometry.SmallEtale.sheafOverFinalEquivalence` is restriction to
the slice site. -/
public theorem SmallEtale.sheafOverFinalEquivalence_functor (A : Type w) [Category.{t} A] :
    (SmallEtale.sheafOverFinalEquivalence B X hX A).functor =
      (SmallEtale.topology B X hX).overPullback A (SmallEtale.final B X hX) :=
  rfl

/-- **The equivalence of sheaf categories over the final object carries sheafified
representables to sheafified representables.** If a sheaf on the slice of the small étale site
over its final object is represented by an object `V` of that slice, then the sheaf on the small
étale site it comes from is represented by the underlying object of `V`.

This is the small étale instance of
`CategoryTheory.GrothendieckTopology.sheafifiedYonedaCompSheafOverTerminalEquivalenceInverse`. -/
public def SmallEtale.sheafifiedYonedaCompSheafOverFinalEquivalenceInverse :
    Sheaf.sheafifiedYoneda ((SmallEtale.topology B X hX).over (SmallEtale.final B X hX)) ⋙
        (SmallEtale.sheafOverFinalEquivalence B X hX (Type (u + 1))).inverse ≅
      Over.forget (SmallEtale.final B X hX) ⋙
        Sheaf.sheafifiedYoneda (SmallEtale.topology B X hX) :=
  CategoryTheory.GrothendieckTopology.sheafifiedYonedaCompSheafOverTerminalEquivalenceInverse.{u,
    u + 1} (SmallEtale.topology B X hX) (SmallEtale.finalIsTerminal B X hX)

variable {V W : SmallEtale B X hX} (g : V ⟶ W) (A : Type w) [Category.{t} A]
  [((smallEtaleBaseChange B V.obj.hom).sheafPushforwardContinuous A
    (SmallEtale.topology B X hX)
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).IsRightAdjoint]

/-- **Inverse image along the structure morphism of `V` is restriction to the slice over `W`
followed by restriction along `g : V ⟶ W`.** The right-hand side reads the doubly localized
sheaf on the small étale site of the scheme `V` through the slice equivalence
`AlgebraicGeometry.smallEtaleEquivalenceOver`.

For `W` the final object of the site this is the comparison that connects a hypothesis about the
inverse images of a sheaf along the members of a covering of `X` to the componentwise data that
a descent theorem on the localized site `J.over (SmallEtale.final B X hX)` consumes. -/
@[sga "4 VII 1.6" "more general"]
public def smallEtaleSheafPullbackIsoOverMapPullback :
    (smallEtaleBaseChange B V.obj.hom).sheafPullback A (SmallEtale.topology B X hX)
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property) ≅
      (SmallEtale.topology B X hX).overPullback A W ⋙
        (SmallEtale.topology B X hX).overMapPullback A g ⋙
        ((smallEtaleEquivalenceOver B X hX V).sheafCongr
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
          ((SmallEtale.topology B X hX).over V) A).inverse :=
  smallEtaleSheafPullbackIsoPostcompose B X hX V A ≪≫
    eqToIso (overPullback_comp_sheafCongr_inverse B X hX V A).symm ≪≫
    Functor.isoWhiskerRight
      ((SmallEtale.topology B X hX).overPullbackCompOverMapPullback A g).symm _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry

end
