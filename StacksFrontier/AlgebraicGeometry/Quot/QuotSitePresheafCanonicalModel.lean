module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward

/-!
# The canonical model of the Quot presheaf in the universe of the site

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module.  A quotient of `F_T`
classified by `Quot_{F/X/B}(T)` is recorded by its kernel, a subobject of `F_T`, so the Quot
presheaf of Stacks 09TR takes values one universe above the site.  The set of quotients over a
scheme of the site is nevertheless small: the subobjects of an `𝒪`-module on an algebraic space
form a small set, because the `𝒪`-modules form a Grothendieck abelian category (the small étale
site being essentially small), and a Grothendieck abelian category is well-powered; and the
morphisms from a scheme of the site to `B` form a small set by the Yoneda lemma.

So the size hypothesis of
`AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel_of_small` always holds, and
the Quot presheaf has a canonical model in the universe of the site.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheafModel`: the canonical model of the Quot
  presheaf in the universe of the site.

## Main results

* `AlgebraicGeometry.Space.small_subobject_modules`: the subobjects of an `𝒪`-module on an
  algebraic space form a small set.
* `AlgebraicGeometry.Space.QuotSituation.small_quotFamilyOver`: the quotients classified by the
  Quot functor over a scheme of the site form a small set.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The subobjects of an `𝒪`-module on an algebraic space form a small set.**  The
`𝒪`-modules form a Grothendieck abelian category, the small étale site being essentially small,
and a Grothendieck abelian category is well-powered. -/
theorem small_subobject_modules (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) : Small.{u} (Subobject M) := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  have : WellPowered.{u} (Modules.{u, u} B S hS X.1 X.2) := IsGrothendieckAbelian.wellPowered _
  exact WellPowered.subobject_small M

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The quotients classified by the Quot functor over a scheme of the site form a small set.**
Such a quotient is a morphism to `B`, of which there is a small set by the Yoneda lemma, together
with a subobject of a module on an algebraic space, of which there is a small set by
`AlgebraicGeometry.Space.small_subobject_modules`. -/
theorem small_quotFamilyOver (T : BigFppfOver B S hS) : Small.{u} (QuotFamilyOver D T) := by
  have : Small.{u} ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y) :=
    small_of_injective (f := fun b : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y =>
      yonedaEquiv b.hom) fun a b hab =>
        ObjectProperty.hom_ext _ (yonedaEquiv.injective hab)
  have : ∀ b : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y,
      Small.{u} (Subobject (D.baseChangeModule (CostructuredArrow.mk b))) :=
    fun b => small_subobject_modules _ _
  exact small_of_injective
    (f := fun x : QuotFamilyOver D T => (⟨x.toBase, x.subobject⟩ :
      Σ b : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y,
        Subobject (D.baseChangeModule (CostructuredArrow.mk b))))
    fun x y hxy => QuotFamilyOver.ext (congrArg Sigma.fst hxy)
      (Sigma.ext_iff.1 hxy).2

/-- **The canonical model of the Quot presheaf** in the universe of the site: the presheaf whose
sections over a scheme of the site are a copy in `Type u` of the quotients classified by the Quot
functor over it.  It exists because those quotients form a small set,
`AlgebraicGeometry.Space.QuotSituation.small_quotFamilyOver`. -/
def quotSitePresheafModel : QuotSitePresheafModel D :=
  have : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} (D.quotSitePresheaf.obj T) :=
    fun T => D.small_quotFamilyOver T.unop
  ⟨shrinkSitePresheaf D.quotSitePresheaf, shrinkSitePresheafIso D.quotSitePresheaf⟩

end QuotSituation

end AlgebraicGeometry.Space

end
