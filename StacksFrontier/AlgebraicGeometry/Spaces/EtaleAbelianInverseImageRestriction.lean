module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportInjective
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# The inverse image of abelian sheaves along an étale morphism is restriction

For a morphism `f : X ⟶ Y` of algebraic spaces with representable underlying morphism, the
inverse image of abelian sheaves on the small étale sites,
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImage`, is defined as the *left adjoint* of
restriction along base change of étale charts, and so is not visibly a restriction.  When `f` is
moreover étale there is a second functor with the same right adjoint — restriction along
postcomposition of étale charts, the functor `j` of Stacks 03LP — and the two therefore agree.

This is the abelian-sheaf analogue of
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is Stacks Equation 03LW for
modules, and it is what lets a statement about the inverse image of abelian sheaves be read as a
statement about restriction, where `AlgebraicGeometry.Space.modulePullbackCompToSheafIso` leaves
it.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSheafPostcompBaseChangeAdjunction`: restriction along
  postcomposition of étale charts is left adjoint to restriction along base change of étale
  charts, with coefficients in an arbitrary category.
* `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageIsoPostcompRestriction`: the inverse
  image of abelian sheaves along an étale representable morphism *is* restriction along
  postcomposition.
* `AlgebraicGeometry.Space.modulePullbackCompToSheafInverseImageIso`: the abelian sheaf
  underlying the pullback of an `𝒪_Y`-module along an étale morphism is the inverse image of the
  abelian sheaf underlying it, with the coefficients lifted to the universe at which the
  geometric stalk of an abelian sheaf exists.

## Implementation notes

The adjunction is the site-level one, `Stacks 03G2 part (4)` against Stacks 03LP — that is
`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction` — carried to sheaves.  Mathlib
has that transport only for sheaves of *modules*
(`SheafOfModules.pushforwardPushforwardAdj`); for plain `A`-valued sheaves it is assembled here
from `CategoryTheory.Adjunction.whiskerLeft`, which is the adjunction between the two
precomposition functors on presheaves, restricted to the sheaf subcategories with
`CategoryTheory.Adjunction.restrictFullyFaithful`.  Both commutation isomorphisms that the
restriction asks for are `Iso.refl`, `AlgebraicGeometry.Space.smallEtaleAbelianPushforward` and
its postcomposition analogue being defined as that very precomposition.

The coefficient category of the adjunction is arbitrary, which is what makes the last result
possible: `AlgebraicGeometry.Space.modulePullbackCompToSheafIso` lands at the universe `u` of the
module sections, while `AlgebraicGeometry.Space.smallEtaleAbelianInverseImage` is pinned at
`u + 1`, and restriction along a site functor commutes with the universe lift on the nose because
both are read on the same sections.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)

/-- **Restriction along postcomposition of étale charts is left adjoint to restriction along
base change of étale charts.**  For an étale morphism `f : X ⟶ Y` of algebraic spaces with
representable underlying morphism, and with coefficients in an arbitrary category, the two
restrictions induced by the site-level adjunction of
`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction` are adjoint.

The right-hand functor is `AlgebraicGeometry.Space.smallEtaleAbelianPushforward` when the
coefficients are abelian groups at `u + 1`. -/
def smallEtaleSheafPostcompBaseChangeAdjunction (A : Type w) [Category.{v} A] :
    letI := (smallBaseChange_isMorphismOfSites B S hS f hrep).toIsContinuous
    (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) ⊣
      (smallBaseChange B S hS f hrep).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hrep).toIsContinuous
  Adjunction.restrictFullyFaithful
    (Adjunction.whiskerLeft A
      (smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).op)
    (fullyFaithfulSheafToPresheaf (SmallEtale.topology B S hS Y.1) A)
    (fullyFaithfulSheafToPresheaf (SmallEtale.topology B S hS X.1) A)
    (Iso.refl _) (Iso.refl _)

/-- **The inverse image of abelian sheaves along an étale representable morphism is restriction
along postcomposition of étale charts.**  Both functors are left adjoint to restriction along
base change of étale charts — the first by
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageAdjunction`, the second by
`AlgebraicGeometry.Space.smallEtaleSheafPostcompBaseChangeAdjunction` — so they agree by
uniqueness of left adjoints.

This is the abelian-sheaf form of Stacks Equation 03LW, whose module form is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`. -/
def smallEtaleAbelianInverseImageIsoPostcompRestriction :
    smallEtaleAbelianInverseImage B S hS f hrep ≅
      (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Adjunction.leftAdjointUniq
    (smallEtaleAbelianInverseImageAdjunction B S hS f hrep)
    (smallEtaleSheafPostcompBaseChangeAdjunction B S hS f hf hrep AddCommGrpCat.{u + 1})

/-- Restriction along postcomposition of étale charts commutes with the universe lift of abelian
groups, on the nose: both sides are the same sections over the same composite chart, lifted. -/
theorem smallEtalePostcompRestriction_comp_sheafCompose :
    (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) ⋙
        sheafCompose (SmallEtale.topology B S hS X.1)
          AddCommGrpCat.uliftFunctor.{u + 1, u} =
      sheafCompose (SmallEtale.topology B S hS Y.1)
          AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
        (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  rfl

/-- **The abelian sheaf underlying the pullback of an `𝒪_Y`-module along an étale morphism is the
inverse image of the abelian sheaf underlying it.**  This is
`AlgebraicGeometry.Space.modulePullbackCompToSheafIso` restated against the inverse image of
abelian sheaves, with the coefficients lifted from the universe `u` of the module sections to the
universe `u + 1` at which the geometric stalk of an abelian sheaf exists.

Together with `AlgebraicGeometry.Space.modulePushforwardCompToSheafIso` this is the dictionary
between the four functors the `𝒪_X`-module of Stacks 0AEX is built from and the four abelian
functors the two-term complexes of Stacks 0AER are built from. -/
def modulePullbackCompToSheafInverseImageIso :
    modulePullback B S hS f ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
        sheafCompose (SmallEtale.topology B S hS X.1)
          AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) ⋙
        sheafCompose (SmallEtale.topology B S hS Y.1)
            AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
          smallEtaleAbelianInverseImage B S hS f hrep :=
  Functor.isoWhiskerRight (modulePullbackCompToSheafIso B S hS f hf)
      (sheafCompose (SmallEtale.topology B S hS X.1)
        AddCommGrpCat.uliftFunctor.{u + 1, u}) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y))
      (Functor.isoWhiskerLeft
        (sheafCompose (SmallEtale.topology B S hS Y.1)
          AddCommGrpCat.uliftFunctor.{u + 1, u})
        (smallEtaleAbelianInverseImageIsoPostcompRestriction B S hS f hf hrep).symm)

end AlgebraicGeometry.Space

end
