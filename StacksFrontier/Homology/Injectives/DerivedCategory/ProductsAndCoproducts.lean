module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Homology.Injectives.DerivedCategory.KInjectiveProducts

/-!
# Existence of direct sums in the derived category of a Grothendieck abelian category

Let `A` be a Grothendieck abelian category. Its unbounded derived category has arbitrary
direct sums, indexed by any type in the universe relative to which `A` is Grothendieck.

Existence reduces to the computation of direct sums by termwise direct sums. Every object of
`D(A)` is isomorphic to the image under `Q` of a complex, so a family of objects may be
replaced by a family of complexes; the termwise direct sum of that family is then sent by `Q`
to a direct sum of the original family, because `Q` preserves coproducts
(`derivedCategoryQ_preservesCoproducts`). Transporting the resulting colimit along the
isomorphisms that identify the chosen representatives with the original objects gives the
colimit of the original diagram.

The argument runs at an arbitrary model of the derived category: `Q` preserves coproducts at
every model, so no comparison between models is needed.

## Main results

* `Stacks.Injectives.hasCoproducts_derivedCategory`: `D(A)` has direct sums.

## Implementation notes

Direct sums are expressed as categorical coproducts, so the content is an instance of
`HasCoproducts`. The universe of morphisms of the chosen derived category is a parameter
independent of the index universe, which is why the statement carries both
`IsGrothendieckAbelian.{w}` and `HasDerivedCategory.{z}`.

## References

* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe z w v u

-- ===== merged from StacksDraft.Ch19.Sec13.DerivedCategoryTermwiseDirectSums =====

/-!
# Termwise direct sums in the derived category of a Grothendieck abelian category

Let `A` be a Grothendieck abelian category. The localization functor
`Q : C(A) ⥤ D(A)` preserves direct sums of every shape: the termwise direct sum of a family
of complexes represents, in the unbounded derived category, the direct sum of the objects
they represent, with the canonical inclusions as the legs of the cocone.

The proof factors `Q` as the homotopy quotient followed by `Qh` and treats the two steps
separately. Passing to the homotopy category is handled by
`HomotopyCategoryCoproduct.cleanColimit`, which needs no exactness and no restriction on the
index type: a map out of a termwise direct sum is determined by its legs, and homotopies
between two such maps can be assembled degreewise. Localizing at the quasi-isomorphisms is
then handled by the observation that it suffices to test the universal property against
objects on which `Qh` is bijective on morphism sets — and every object of `D(A)` is
represented by a K-injective complex, for which bijectivity holds. That last input is where
the Grothendieck hypothesis enters, through the functorial K-injective resolutions of
Tag 079P.

## Main results

* `Stacks.Injectives.derivedCategoryQ_preservesCoproducts`: `Q` preserves coproducts indexed
  by any type in the universe relative to which `A` is Grothendieck.

## Implementation notes

The statement is for an arbitrary model `[HasDerivedCategory A]` of the derived category: the
argument only uses the localization functor `Qh` and the K-injective resolutions, which exist
at every model.

The K-injective resolution is the only step that uses the Grothendieck hypothesis, and it is
supplied to the shared `exists_map_bijective_Qh_of_exists_quasiIso_isKInjective` by Tag 079P
(`exists_quasiIso_isKInjective_of_isGrothendieckAbelian`). The library already proves the same
conclusion for an arbitrary index type in
`derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives`, but from exact countable
products rather than from `IsGrothendieckAbelian`; countable products are not exact in a
general Grothendieck abelian category, so neither statement implies the other, which is why
that shared lemma takes the resolution as a hypothesis instead of an instance.

## References

* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Injectives

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- The localization functor from complexes to the unbounded derived category preserves direct
sums; thus the image of the termwise direct sum of any family of complexes is its direct sum in
the derived category. -/
@[stacks 07D9 "direct_sums_termwise"]
instance derivedCategoryQ_preservesCoproducts [IsGrothendieckAbelian.{w} A] (I : Type w) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) := by
  constructor
  intro F
  let K : I → CochainComplex A ℤ := fun i => F.obj ⟨i⟩
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hc := (isColimit_mapCofan_of_exists_map_bijective DerivedCategory.Qh
    (exists_map_bijective_Qh_of_exists_quasiIso_isKInjective A
      (fun M => by
        obtain ⟨L, f, hL, hf⟩ := exists_quasiIso_isKInjective_of_isGrothendieckAbelian A M
        exact ⟨L, f, hf, hL⟩))
    (fun i => q.map (Sigma.ι K i))
    (HomotopyCategoryCoproduct.cleanColimit A K)).some
  have : PreservesColimit (Discrete.functor K) (q ⋙ DerivedCategory.Qh) :=
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
      ((isColimitMapCoconeCofanMkEquiv (q ⋙ DerivedCategory.Qh) K (Sigma.ι K)).symm hc)
  have : PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A)) :=
    preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A)
  exact preservesColimit_of_iso_diagram
    (K₁ := Discrete.functor K) DerivedCategory.Q
    (Discrete.natIso (fun ⟨i⟩ => Iso.refl _))

end Stacks.Injectives

namespace Stacks.Injectives

/-- The unbounded derived category of a Grothendieck abelian category has direct sums. -/
@[stacks 07D9 "direct_sums_exist"]
instance hasCoproducts_derivedCategory (A : Type u) [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A] :
    HasCoproducts.{w} (DerivedCategory A) := fun _ => ⟨fun F =>
  hasColimit_of_iso (F := Discrete.functor (fun i =>
    DerivedCategory.Q.objPreimage (F.obj ⟨i⟩)) ⋙ DerivedCategory.Q)
    (Discrete.natIso (fun i => (DerivedCategory.Q.objObjPreimageIso (F.obj i)).symm))⟩

end Stacks.Injectives

-- ===== merged from StacksDraft.Ch19.Sec13.DerivedCategoryProducts =====

/-!
# Existence of products in the derived category of a Grothendieck abelian category

Let `A` be a Grothendieck abelian category. Its unbounded derived category has arbitrary
products, indexed by any type in the universe relative to which `A` is Grothendieck.

Unlike direct sums, products in `D(A)` are not computed by termwise products of arbitrary
representatives: products in a Grothendieck abelian category need not be exact, so a termwise
product of quasi-isomorphisms need not be a quasi-isomorphism. The remedy is to choose the
representatives K-injective. Replacing each object of the family by the K-injective resolution
of a representing complex, the termwise product of those resolutions does represent the
product (`isLimit_productFanInDerivedCategory`), and transporting that limit along the
isomorphisms identifying the resolutions with the original objects gives the product of the
original diagram.

## Main results

* `Stacks.Injectives.hasProducts_derivedCategory`: `D(A)` has products.

## Implementation notes

Products are indexed by types in the universe relative to which `A` is Grothendieck and
locally small; the universe of morphisms of the chosen derived category is an independent
parameter, which is why the statement carries both `IsGrothendieckAbelian.{w}` and
`HasDerivedCategory.{w'}`.

## References

* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w'

namespace Stacks.Injectives

/-- The unbounded derived category of a Grothendieck abelian category has arbitrary
products. -/
@[stacks 07D9 "products_exist"]
instance hasProducts_derivedCategory (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [IsGrothendieckAbelian.{w} 𝒜] [HasDerivedCategory.{w'} 𝒜] :
    HasProducts.{w} (DerivedCategory 𝒜) := by
  refine fun I => ⟨fun X => ?_⟩
  let K (i : I) := (kInjectiveResolutionFunctor 𝒜).obj
    (DerivedCategory.Q.objPreimage (X.obj (Discrete.mk i)))
  have hp : HasProduct (fun i => DerivedCategory.Q.obj (K i)) :=
    ⟨⟨_, Classical.choice <|
      isLimit_productFanInDerivedCategory K (fun i => inferInstance)⟩⟩
  exact hasLimit_of_iso (show Discrete.functor (fun i : I =>
    DerivedCategory.Q.obj (K i)) ≅ X from Discrete.natIso (fun i =>
    ((asIso (DerivedCategory.Q.map ((kInjectiveResolutionInclusion 𝒜).app
      (DerivedCategory.Q.objPreimage (X.obj i))))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (X.obj i))))

end Stacks.Injectives
