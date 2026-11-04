module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.CanonicalSystem

/-!
# A carried derived pullback is the canonical one

`AlgebraicGeometry.Space.DerivedModulePullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` is the derived pullback of
`𝒪`-modules along a morphism of algebraic spaces carried as data: a functor between the unbounded
derived categories together with a counit exhibiting it as a total left derived functor, along the
quasi-isomorphisms, of the degreewise inverse image of Stacks 03LU.  Stacks 09RI is stated for such
carried data, assembled into a
`AlgebraicGeometry.Space.DescentSituation.DerivedPullbackSystem`, and
`AlgebraicGeometry.Space.derivedModulePullbackCanonical` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom/CanonicalSystem.lean` is the
construction, the inverse image of the coherent pseudofunctor of Stacks 06YY.

**This file identifies the two.**  Any two `AlgebraicGeometry.Space.DerivedModulePullback`s along
one morphism are canonically isomorphic, by the universal property each of them carries; the
isomorphism is compatible with the two counits and is the unique morphism that is.  In particular a
carried derived pullback is isomorphic to the one of the pseudofunctor.

This is what makes the phrase "so this is `Lf^*` and not an arbitrary functor" in the
documentation of `AlgebraicGeometry.Space.DerivedModulePullback` a theorem rather than a reading of
the definition: the universal property pins the functor up to a unique compatible isomorphism, and
that isomorphism is produced here.

Nothing is assumed beyond the additivity of the degreewise inverse image, which is already an
instance argument of `AlgebraicGeometry.Space.DerivedModulePullback` itself.

## Main results

* `AlgebraicGeometry.Space.DerivedModulePullback.functorIso`: two carried derived pullbacks along
  one morphism have isomorphic functors.
* `AlgebraicGeometry.Space.DerivedModulePullback.functorIso_hom_app_counit`: the isomorphism is
  compatible with the two counits.
* `AlgebraicGeometry.Space.DerivedModulePullback.hom_ext_of_counit`: a morphism out of a carried
  derived pullback is determined by its effect on the counits, so the isomorphism above is the
  only compatible one.
* `AlgebraicGeometry.Space.DerivedModulePullback.isoPull`: a carried derived pullback is
  isomorphic to the inverse image of the pseudofunctor of Stacks 06YY.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [(modulePullback B S hS f).Additive]

namespace DerivedModulePullback

/-- **Two carried derived pullbacks along one morphism have isomorphic functors.**  Both are total
left derived functors of `AlgebraicGeometry.Space.modulePullbackOnHomotopy` along the
quasi-isomorphisms, so `CategoryTheory.Functor.leftDerivedUnique` compares them. -/
def functorIso (P Q : DerivedModulePullback B S hS f) : P.functor ≅ Q.functor :=
  have := P.isLeftDerived
  have := Q.isLeftDerived
  Functor.leftDerivedUnique Q.functor P.functor P.counit Q.counit
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.obj Y.property) (ComplexShape.up ℤ))

/-- **The comparison of two carried derived pullbacks is compatible with their counits**: at the
image of a complex it carries the counit of the second to the counit of the first. -/
theorem functorIso_hom_app_counit (P Q : DerivedModulePullback B S hS f)
    (M : HomotopyCategory (Modules.{u, u} B S hS Y.obj Y.property) (ComplexShape.up ℤ)) :
    (functorIso B S hS f P Q).hom.app (DerivedCategory.Qh.obj M) ≫ Q.counit.app M =
      P.counit.app M := by
  have := P.isLeftDerived
  have := Q.isLeftDerived
  refine Eq.trans ?_ (Category.comp_id _)
  exact Functor.leftDerivedNatTrans_app P.functor Q.functor P.counit Q.counit
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.obj Y.property) (ComplexShape.up ℤ))
    (𝟙 _) M

/-- **A morphism into a carried derived pullback is determined by its effect on the counit.**
Together with `AlgebraicGeometry.Space.DerivedModulePullback.functorIso_hom_app_counit` this says
that the comparison of two carried derived pullbacks is the *unique* isomorphism compatible with
the two counits. -/
theorem hom_ext_of_counit (Q : DerivedModulePullback B S hS f)
    (G : DerivedCategory (Modules.{u, u} B S hS Y.obj Y.property) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.obj X.property)) (γ₁ γ₂ : G ⟶ Q.functor)
    (h : Functor.whiskerLeft DerivedCategory.Qh γ₁ ≫ Q.counit =
      Functor.whiskerLeft DerivedCategory.Qh γ₂ ≫ Q.counit) :
    γ₁ = γ₂ :=
  have := Q.isLeftDerived
  Functor.leftDerived_ext Q.functor Q.counit
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.obj Y.property) (ComplexShape.up ℤ))
    G γ₁ γ₂ h

/-- **A carried derived pullback is the inverse image of the pseudofunctor of Stacks 06YY.**  This
is `AlgebraicGeometry.Space.DerivedModulePullback.functorIso` against
`AlgebraicGeometry.Space.derivedModulePullbackCanonical`. -/
def isoPull (P : DerivedModulePullback B S hS f) :
    P.functor ≅ (smallEtaleDerivedPullbackData B S hS).pull f :=
  functorIso B S hS f P (derivedModulePullbackCanonical B S hS f)

end DerivedModulePullback

end AlgebraicGeometry.Space

end
