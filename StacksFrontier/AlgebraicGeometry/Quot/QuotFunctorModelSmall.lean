module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SubmoduleSmall
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel

/-!
# The Quot presheaf has a model in the universe of the site

A section of the Quot presheaf `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf` over a
scheme `T` of the big fppf site is a morphism `T ⟶ B` together with a quotient of `F_T`, recorded
by its kernel, a subobject of `F_T`. Such sections form a set in the universe of the site: the
morphisms `T ⟶ B` are the points of `B` over `T`, and the subobjects of a sheaf of modules on the
small étale site of `X_T` form a small set. Hence the Quot presheaf always has a model in the
universe of the site, the form in which Stacks 09TU is stated.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.quotFamilyOverEquivSigma`: a section of the Quot
  presheaf is a morphism to the base together with a quotient over the resulting test scheme.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.small_hom_schemeSpace`: the morphisms from a scheme of
  the site to an algebraic space form a small set.
* `AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel`: the Quot presheaf has a
  model in the universe of the site.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- The morphisms from a scheme of the site to an algebraic space form a small set: they are the
points of the space over the scheme. -/
instance small_hom_schemeSpace (T : BigFppfOver B S hS) (Y : AlgebraicSpaces B S hS) :
    Small.{u} ((schemeSpaceFunctor B S hS).obj T ⟶ Y) :=
  small_of_injective (f := fun b : (schemeSpaceFunctor B S hS).obj T ⟶ Y => yonedaEquiv b.hom)
    fun _ _ h => ObjectProperty.hom_ext _ (yonedaEquiv.injective h)

/-- A section of the Quot presheaf is a morphism to the base together with a member of the set of
quotients over the resulting test scheme. -/
def quotFamilyOverEquivSigma (T : BigFppfOver B S hS) :
    QuotFamilyOver D T ≃ Σ b : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y,
      D.properlySupportedQuotients (CostructuredArrow.mk b) where
  toFun q := ⟨q.toBase, q.subobject, q.mem⟩
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The Quot presheaf has a model in the universe of the site** (an auxiliary step towards
Stacks 09TU): a presheaf of `Type u` whose sections over every scheme of the site are exactly the
sections of the Quot presheaf of Stacks 09TR and whose morphism to `B` is the canonical one. -/
theorem exists_quotSitePresheafModel :
    ∃ M : QuotSitePresheafModel D,
      (∀ T : (BigFppfOver B S hS)ᵒᵖ, Nonempty (M.presheaf.obj T ≃ QuotFamilyOver D T.unop)) ∧
        Functor.whiskerRight M.toBase uliftFunctor.{u + 1, u} =
          M.iso.hom ≫ D.quotSitePresheafToBase :=
  D.exists_quotSitePresheafModel_of_small fun T => D.small_quotFamilyOver T

end AlgebraicGeometry.Space.QuotSituation

end
