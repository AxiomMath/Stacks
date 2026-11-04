module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.Bootstrap04S6PerObject

/-!
# The bootstrap theorem (Stacks 04S6)

Condition (1) of [Stacks, Tag 04S6], `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`, says
that the fppf quotient of an algebraic space by a flat, locally finitely presented equivalence
relation of algebraic spaces is an algebraic space. This file deduces conditions (3) and (4) of
[Stacks, Tag 04S6], and condition (1) for groupoids in algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`: a sheaf receiving a
  morphism from an algebraic space which is representable by algebraic spaces, surjective, flat
  and locally of finite presentation is an algebraic space.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_flat_scheme_chart`: the same with a scheme chart.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_relativelyRepresentable_of_presheaf`: the same
  with a chart representable by schemes whose base changes to schemes are surjective, flat and
  locally of finite presentation.
* `AlgebraicGeometry.Space.theorem04S6Quotient`: condition (1) for a groupoid in algebraic
  spaces.
* `AlgebraicGeometry.Stack.bootstrap04S6Spaces`: condition (3), as
  `AlgebraicGeometry.Stack.Bootstrap04S6Spaces`.
* `AlgebraicGeometry.Stack.bootstrap04S6`: condition (3) over every object of the site, with a
  chart representable by schemes.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `F` be a sheaf on the big fppf site of `S`, and suppose there are an algebraic space `X`
over `S` and a morphism `X ⟶ F` which is representable by algebraic spaces, surjective, flat and
locally of finite presentation. Then `F` is an algebraic space over `S`. -/
@[stacks 04S6 "condition (3): a sheaf with a surjective, flat, locally finitely presented chart \
from an algebraic space, representable by algebraic spaces, is an algebraic space"]
theorem isBootstrapAlgebraicSpaceAlongFlatSurjection :
    IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS :=
  isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf B S hS
    (bootstrap04S6QuotientSheaf B S hS)

/-- Let `F` be a sheaf on the big fppf site of `S`, and suppose there are a scheme `U` of the site
and a morphism `h_U ⟶ F` which is representable by algebraic spaces (in particular, one
representable by schemes), surjective, flat and locally of finite presentation. Then `F` is an
algebraic space over `S`. -/
@[stacks 04S6 "condition (4)"]
theorem isAlgebraicSpace_of_flat_scheme_chart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf)
    (hFlat : HasProperty B S hS (flatProperty B S hS) f hf)
    (hLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf) :
    IsAlgebraicSpace B S hS F :=
  isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS f hF (isAlgebraicSpace_yoneda B S hS U) hf
    hSurj hFlat hLfp

/-- A sheaf `F` on the big fppf site of `S` receiving a morphism `g : G ⟶ F` from an algebraic
space which is representable by schemes and whose base changes to schemes are surjective, flat and
locally of finite presentation is an algebraic space. -/
theorem isAlgebraicSpace_of_relativelyRepresentable_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : IsAlgebraicSpace B S hS G) (g : G ⟶ F) (hg : yoneda.relativelyRepresentable g)
    (hgP : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) g) :
    IsAlgebraicSpace B S hS F := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS g :=
    IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hg
  exact isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS g hF hG hrep
    (hasProperty_surjectiveMorphismProperty_of_presheaf B S hS g
      (presheaf_inverseImage_mono B S hS (fun _ hp => hp.1.1) hgP) hrep)
    (hasProperty_flatProperty_of_presheaf B S hS g
      (presheaf_inverseImage_mono B S hS (fun _ hp => hp.1.2) hgP) hrep)
    (hasProperty_locallyOfFinitePresentationProperty_of_presheaf B S hS g
      (presheaf_inverseImage_mono B S hS (fun _ hp => hp.2) hgP) hrep)

/-- The quotient of a groupoid in algebraic spaces over an algebraic space whose pre-relation is
an equivalence relation and whose source and target are flat and locally of finite presentation
is an algebraic space. -/
theorem theorem04S6Quotient [HasSheafify (BigFppfOver.topology B S hS) (Type u)] :
    Theorem04S6Quotient B S hS :=
  theorem04S6Quotient_of_quotientSheaf B S hS (bootstrap04S6QuotientSheaf B S hS)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf on the big fppf site of `S` receiving a morphism from an algebraic space which is
representable by algebraic spaces, surjective, flat and locally of finite presentation is an
algebraic space. -/
theorem bootstrap04S6Spaces : Bootstrap04S6Spaces B S hS :=
  bootstrap04S6Spaces_of_quotientSheaf B S hS (Space.bootstrap04S6QuotientSheaf B S hS)

/-- For every object `T` of the big fppf site of `S`, a sheaf on the big fppf site of `T`
receiving a morphism from an algebraic space which is representable by schemes and whose base
changes to schemes are surjective, flat and locally of finite presentation is an algebraic
space. -/
theorem bootstrap04S6 : Bootstrap04S6 B S hS :=
  bootstrap04S6_of_quotientSheaf B S hS fun T =>
    Space.bootstrap04S6QuotientSheaf B T.left.1 T.left.2

end AlgebraicGeometry.Stack

end
