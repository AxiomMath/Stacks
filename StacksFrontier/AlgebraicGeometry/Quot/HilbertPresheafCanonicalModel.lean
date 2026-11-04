module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SubfunctorSmall

/-!
# The canonical model of the Hilbert presheaf

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site. A
section of the Hilbert presheaf `AlgebraicGeometry.Space.hilbertPresheaf` of Stacks 0CZY over a
scheme `T` of the site is a morphism `T ⟶ Y` together with a closed subfunctor of `X_T`, so it
lives one universe above the sections of an algebraic space. This file shows that nevertheless
every set of sections is small, and so produces, for an arbitrary morphism `f` and with nothing
assumed, a model of the Hilbert presheaf in the universe of the site
(`AlgebraicGeometry.Space.HilbertPresheafModel`).

The size bound has nothing to do with the geometry of `f`: the big fppf site is essentially
small (`AlgebraicGeometry.essentiallySmall_bigFppfOver`), a subfunctor of a presheaf on an
essentially small category is determined by its values on the objects of a small model
(`CategoryTheory.Subfunctor.small`), and a morphism from a representable presheaf to `Y` is a
section of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.HilbertPresheafModel.canonical`: the model of the Hilbert presheaf of
  `f` whose sections over `T` are a copy in `Type u` of the families over `T`.

## Main results

* `AlgebraicGeometry.Space.small_subfunctor`: the subfunctors of a presheaf on the big fppf site
  form a small type.
* `AlgebraicGeometry.Space.HilbertFamilyOver.small`: the families classified by the Hilbert
  functor over a scheme of the site form a small type.

## References

* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- The subfunctors of a presheaf on the big fppf site of `S` form a small type, because the site
is essentially small. -/
instance small_subfunctor (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Small.{u} (Subfunctor F) :=
  have := essentiallySmall_bigFppfOver B S hS
  Subfunctor.small F

/-- The families classified by the Hilbert functor of `f` over a scheme `T` of the site form a
small type: such a family is a morphism `T ⟶ Y`, which is a section of `Y`, together with a
subfunctor of the base change of `X` along it, and the remaining fields are propositions. -/
instance HilbertFamilyOver.small (f : X ⟶ Y) (T : BigFppfOver B S hS) :
    Small.{u} (HilbertFamilyOver f T) := by
  have : Small.{u} (yoneda.obj T ⟶ Y.obj) := small_of_injective yonedaEquiv.injective
  exact small_of_injective (β := Σ b : yoneda.obj T ⟶ Y.obj,
    Subfunctor (schemeBaseChange f (CostructuredArrow.mk b)))
    (f := fun x => ⟨x.toBase, x.family.Z⟩)
    fun _ _ hab => HilbertFamilyOver.ext (Sigma.mk.inj hab).1 (Sigma.mk.inj hab).2

/-- **The canonical model of the Hilbert presheaf.** For an arbitrary morphism `f : X ⟶ Y` of
algebraic spaces over `S`, the Hilbert presheaf of Stacks 0CZY has a model in the universe of the
site: its sections over a scheme `T` are a copy in `Type u` of the families over `T`, and its
universe lift is identified with the Hilbert presheaf by
`AlgebraicGeometry.Space.shrinkSitePresheafIso`. -/
def HilbertPresheafModel.canonical (f : X ⟶ Y) : HilbertPresheafModel f :=
  have : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} ((hilbertPresheaf f).obj T) :=
    fun T => HilbertFamilyOver.small f T.unop
  ⟨shrinkSitePresheaf (hilbertPresheaf f), shrinkSitePresheafIso (hilbertPresheaf f)⟩

end AlgebraicGeometry.Space

end
