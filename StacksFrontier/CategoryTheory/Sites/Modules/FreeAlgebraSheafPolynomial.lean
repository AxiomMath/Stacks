module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.StandardResolution
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafSiteLocalIso

/-!
# The free algebra sheaf of the standard resolution is the sheafified polynomial presheaf

The standard resolution of a morphism of sheaves of commutative rings is built from the free
`A`-algebra sheaf functor `CategoryTheory.Sheaf.freeAlgebraSheaf`, which sends a sheaf of sets `E`
to the coproduct `A ⨿ ℤ[E]` of `A` with the sheafification of the pointwise free commutative ring
on `E`. The free algebra development on a site builds instead
`Stacks.Sites.FreeAlgebra.freeAlgebraSheaf`, the sheafification of the presheaf of polynomial
rings `U ↦ A(U)[E(U)]`, with its structural morphism from `A`.

This file identifies the two, as sheaves of `A`-algebras. Both are free `A`-algebras on `E`, so
the identification is the comparison of two solutions to one universal problem: the morphism out
of the first is classified by the variables of the second, the morphism out of the second is
classified by the unit of the first, and each composite is the identity because it is classified
by the data classifying the identity.

## Main definitions

* `CategoryTheory.Sheaf.polynomialAlgebraSheaf`: the sheafification of `U ↦ A(U)[E(U)]`, as a
  sheaf of `A`-algebras.
* `CategoryTheory.Sheaf.freeAlgebraSheafComparison` and
  `CategoryTheory.Sheaf.freeAlgebraSheafComparisonInv`: the two comparison morphisms.
* `CategoryTheory.Sheaf.freeAlgebraSheafIso`: the identification, as an isomorphism of sheaves of
  `A`-algebras.
* `CategoryTheory.Sheaf.freeAlgebraSheafRightIso`: the underlying isomorphism of sheaves of
  commutative rings.

## Main results

* `CategoryTheory.Sheaf.unit_comp_freeAlgebraSheafComparison`: the first comparison is classified
  by the variables.
* `CategoryTheory.Sheaf.freeAlgebraSheafComparison_comp_inv` and
  `CategoryTheory.Sheaf.freeAlgebraSheafComparisonInv_comp_comparison`: the two composites are
  the identity.

## Implementation notes

`Stacks.Sites.FreeAlgebra.freeAlgebraSheaf` and `CategoryTheory.Sheaf.freeAlgebraSheaf` are two
different declarations with the same final name component, so this file opens the former's
namespace selectively and spells that one out in full.

The universal property used on the sheafified-polynomial-presheaf side is
`Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext` together with
`Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc`; on the coproduct side it is the
injectivity of `CategoryTheory.Adjunction.homEquiv` for
`CategoryTheory.Sheaf.freeAlgebraSheafAdjunction`. Nothing about either construction is unfolded:
the variables of the one and the unit of the other are the only data that enter.

## References

* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheafCoefficientMap
  freeAlgebraSheafVariable freeAlgebraSheafDesc freeAlgebraSheafCoefficientMap_comp_desc
  freeAlgebraSheafVariable_comp_desc freeAlgebraSheaf_hom_ext
  whiskerRight_sheafToPresheaf_map_comp whiskerRight_sheafToPresheaf_map_id)

universe v u w

noncomputable section

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{max u v w}) (E : Sheaf J (Type (max u v w)))

/-- The sheafification of the presheaf of polynomial rings `U ↦ A(U)[E(U)]`, as a sheaf of
`A`-algebras. -/
abbrev polynomialAlgebraSheaf : Under A :=
  Under.mk (freeAlgebraSheafCoefficientMap J A E.obj)

/-- The underlying morphism of presheaves of sets of a morphism of sheaves of `A`-algebras. -/
theorem forgetAlgebraSheaf_map_hom {X Y : Under A} (g : X ⟶ Y) :
    ((forgetAlgebraSheaf J A).map g).hom =
      Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{max u v w}).map g.right)
        (forget CommRingCat.{max u v w}) :=
  rfl

/-- The variables of the sheafified polynomial presheaf, as a morphism of sheaves of sets. -/
def polynomialAlgebraSheafVariable :
    E ⟶ (forgetAlgebraSheaf J A).obj (polynomialAlgebraSheaf J A E) :=
  Sheaf.Hom.mk (freeAlgebraSheafVariable J A E.obj)

/-- The comparison morphism `A ⨿ ℤ[E] ⟶ A[E]`, classified by the variables of the sheafified
polynomial presheaf. -/
def freeAlgebraSheafComparison :
    (freeAlgebraSheaf J A).obj E ⟶ polynomialAlgebraSheaf J A E :=
  ((freeAlgebraSheafAdjunction J A).homEquiv E (polynomialAlgebraSheaf J A E)).symm
    (polynomialAlgebraSheafVariable J A E)

/-- The comparison morphism is classified by the variables. -/
theorem unit_comp_freeAlgebraSheafComparison :
    (freeAlgebraSheafAdjunction J A).unit.app E ≫
        (forgetAlgebraSheaf J A).map (freeAlgebraSheafComparison J A E) =
      polynomialAlgebraSheafVariable J A E := by
  exact ((freeAlgebraSheafAdjunction J A).homEquiv_unit ..).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- The comparison morphism carries the unit of the free-forgetful adjunction to the variables. -/
theorem unit_hom_comp_freeAlgebraSheafComparison :
    ((freeAlgebraSheafAdjunction J A).unit.app E).hom ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{max u v w}).map
          (freeAlgebraSheafComparison J A E).right) (forget CommRingCat.{max u v w}) =
      freeAlgebraSheafVariable J A E.obj := by
  exact congrArg (·.hom) (unit_comp_freeAlgebraSheafComparison J A E)

/-- The comparison morphism `A[E] ⟶ A ⨿ ℤ[E]`, classified by the unit of the free-forgetful
adjunction for sheaves of `A`-algebras. -/
def freeAlgebraSheafComparisonInv :
    polynomialAlgebraSheaf J A E ⟶ (freeAlgebraSheaf J A).obj E :=
  Under.homMk
    (freeAlgebraSheafDesc J A ((freeAlgebraSheaf J A).obj E).right E.obj
      ((freeAlgebraSheaf J A).obj E).hom ((freeAlgebraSheafAdjunction J A).unit.app E).hom)
    (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _)

/-- The second comparison morphism carries the variables to the unit. -/
theorem variable_comp_freeAlgebraSheafComparisonInv :
    freeAlgebraSheafVariable J A E.obj ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{max u v w}).map
          (freeAlgebraSheafComparisonInv J A E).right) (forget CommRingCat.{max u v w}) =
      ((freeAlgebraSheafAdjunction J A).unit.app E).hom := by
  simp only [freeAlgebraSheafComparisonInv, Under.homMk_right]
  exact freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

/-- The composite `A ⨿ ℤ[E] ⟶ A[E] ⟶ A ⨿ ℤ[E]` of the two comparison morphisms is the identity. -/
theorem freeAlgebraSheafComparison_comp_inv :
    freeAlgebraSheafComparison J A E ≫ freeAlgebraSheafComparisonInv J A E =
      𝟙 ((freeAlgebraSheaf J A).obj E) := by
  apply ((freeAlgebraSheafAdjunction J A).homEquiv E ((freeAlgebraSheaf J A).obj E)).injective
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    ← Category.assoc, unit_comp_freeAlgebraSheafComparison, Sheaf.hom_ext_iff]
  exact variable_comp_freeAlgebraSheafComparisonInv J A E

/-- The composite `A[E] ⟶ A ⨿ ℤ[E] ⟶ A[E]` of the two comparison morphisms is the identity. -/
theorem freeAlgebraSheafComparisonInv_comp_comparison :
    freeAlgebraSheafComparisonInv J A E ≫ freeAlgebraSheafComparison J A E =
      𝟙 (polynomialAlgebraSheaf J A E) := by
  have h₁ : freeAlgebraSheafCoefficientMap J A E.obj ≫
      (freeAlgebraSheafComparisonInv J A E).right =
      ((freeAlgebraSheaf J A).obj E).hom := Under.w (freeAlgebraSheafComparisonInv J A E)
  have h₂ : ((freeAlgebraSheaf J A).obj E).hom ≫ (freeAlgebraSheafComparison J A E).right =
      freeAlgebraSheafCoefficientMap J A E.obj := Under.w (freeAlgebraSheafComparison J A E)
  have key : (freeAlgebraSheafComparisonInv J A E).right ≫
      (freeAlgebraSheafComparison J A E).right =
      𝟙 (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E.obj) := by
    refine freeAlgebraSheaf_hom_ext J A _ E.obj ?_ ?_
    · rw [Category.comp_id, ← Category.assoc, h₁, h₂]
    · rw [whiskerRight_sheafToPresheaf_map_comp, whiskerRight_sheafToPresheaf_map_id,
        Category.comp_id, ← Category.assoc, variable_comp_freeAlgebraSheafComparisonInv]
      exact unit_hom_comp_freeAlgebraSheafComparison J A E
  exact (Under.forget A).map_injective key

/-- **The free `A`-algebra sheaf on a sheaf of sets is the sheafification of the presheaf of
polynomial rings.** The sheaf `A ⨿ ℤ[E]` is isomorphic, as a sheaf of `A`-algebras, to the
sheafification of `U ↦ A(U)[E(U)]`. -/
def freeAlgebraSheafIso :
    (freeAlgebraSheaf J A).obj E ≅ polynomialAlgebraSheaf J A E where
  hom := freeAlgebraSheafComparison J A E
  inv := freeAlgebraSheafComparisonInv J A E
  hom_inv_id := freeAlgebraSheafComparison_comp_inv J A E
  inv_hom_id := freeAlgebraSheafComparisonInv_comp_comparison J A E

/-- The underlying isomorphism of sheaves of commutative rings. -/
def freeAlgebraSheafRightIso :
    ((freeAlgebraSheaf J A).obj E).right ≅
      Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E.obj :=
  (Under.forget A).mapIso (freeAlgebraSheafIso J A E)

end CategoryTheory.Sheaf

end

end
