module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan`

Morphisms from an fppf sheaf to an arbitrary scheme, and the conditions (2) and (3) of Stacks 0AIC
stated with the morphism to `Spec A` given as such a morphism.

## Main definitions

* `AlgebraicGeometry.FormalSpace.MapToScheme`: a morphism of fppf sheaves from `X` to a scheme `Z`,
  given as a natural family of morphisms of schemes indexed by the `T`-points of `X`.
* `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`: condition (2) of
  Stacks 0AIC.
* `AlgebraicGeometry.FormalSpace.HasSchemeClosedImmersionCriterionMapToSpec`: condition (3) of
  Stacks 0AIC.

## Main results

* `HasSchemeClosedImmersionCriterionMapToSpec.hasAffineClosedImmersionCriterionMapToSpec`:
  condition (3) implies condition (2).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves from `X` to a scheme `Z` which need **neither** be an object of
the site **nor** carry a structure morphism to `S`. By the Yoneda lemma such a morphism is the
same as a family, natural in the object `T` of the site, sending a `T`-point of `X` to a
morphism of schemes `T ⟶ Z`, and that family is taken as the definition: it presupposes no bound
on the size of `Z`, whereas `AlgebraicGeometry.Sheaf.sheafifiedYoneda` is available only for
objects of the site. -/
structure MapToScheme (Z : Scheme.{u}) (X : FppfSheaf B S hS) where
  /-- The morphism of schemes attached to a `T`-point of `X`. -/
  app : ∀ T : BigFppfOver B S hS,
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X) →
      ((BigFppfOver.toScheme B S hS).obj T ⟶ Z)
  /-- The family is natural in the object of the site. -/
  app_naturality : ∀ (T T' : BigFppfOver B S hS) (u : T' ⟶ T)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X),
    app T' ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map u ≫ g) =
      (BigFppfOver.toScheme B S hS).map u ≫ app T g

/-- Condition (2) of Stacks 0AIC, with the morphism to `Spec A` recorded as a
`AlgebraicGeometry.FormalSpace.MapToScheme`: `X` is an affine formal algebraic space and there
are a ring `A` and a morphism `X ⟶ Spec A` of fppf sheaves such that every closed immersion of an
affine scheme into `X` composes to a closed immersion of schemes.

This differs from `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterion` in that
`Spec A` is required neither to be an object of the site nor to carry a morphism to `S`, exactly
as in the source. Condition (1) bounds the size only of the quotients of the presenting ring, so
demanding that `Spec A` lie in the site would make this member of the equivalence stronger than
Stacks' condition (2); and the presenting ring is the inverse limit of the stage rings, whose
spectrum admits no morphism to a non-affine `S`, so demanding a structure morphism would in
addition sever the arrow from condition (4). -/
abbrev HasAffineClosedImmersionCriterionMapToSpec (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧
    ∃ (A : CommRingCat.{u}) (f : MapToScheme B S hS (Spec A) X),
      ∀ (T : BigAffineFppf B S hS)
        (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X),
        IsClosedImmersionInto B S hS g →
        IsClosedImmersion (f.app ((BigAffineFppf.inclusion B S hS).obj T) g)

/-- Condition (3) of Stacks 0AIC, with the morphism to `Spec A` recorded as a
`AlgebraicGeometry.FormalSpace.MapToScheme`: as
`AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`, but the closed
immersions into `X` range over all schemes of the site rather than only the affine ones. -/
abbrev HasSchemeClosedImmersionCriterionMapToSpec (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧
    ∃ (A : CommRingCat.{u}) (f : MapToScheme B S hS (Spec A) X),
      ∀ (T : BigFppfOver B S hS)
        (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X),
        IsClosedImmersionInto B S hS g → IsClosedImmersion (f.app T g)

/-- **Stacks 0AIC, condition (3) implies condition (2)**, for the conditions with the morphism
to `Spec A` recorded as a `AlgebraicGeometry.FormalSpace.MapToScheme`. The affine schemes of the
site are among its schemes, so the criterion for all schemes restricts to them. -/
@[stacks 0AIC "(3) implies (2)"]
theorem HasSchemeClosedImmersionCriterionMapToSpec.hasAffineClosedImmersionCriterionMapToSpec
    {X : FppfSheaf B S hS} (hX : HasSchemeClosedImmersionCriterionMapToSpec B S hS X) :
    HasAffineClosedImmersionCriterionMapToSpec B S hS X := by
  obtain ⟨hA, A, f, hf⟩ := hX
  exact ⟨hA, A, f, fun T g hg ↦ hf ((BigAffineFppf.inclusion B S hS).obj T) g hg⟩

end AlgebraicGeometry.FormalSpace

end
