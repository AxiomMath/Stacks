module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Finite products in the big fppf slice, and the comparison with schemes over the base

The big fppf category over `S` is the slice `Over (B.obj hS)` of the cutoff category of schemes,
and `CategoryTheory.Over.post B.inclusion` compares it with the slice `Over S` of all schemes.
That comparison functor is fully faithful, and it preserves finite products: the inclusion of
the cutoff category creates, hence preserves, fibre products by
`CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion`, which gives binary products
in the slices, and the final object of a slice is the identity of its base, which the comparison
sends to the identity of `S`.

Two consequences recorded here are what makes a finite product formed inside the site agree
with the corresponding fibre product of schemes over `S`, and what identifies the functor of
points of an object of the site with the restriction along the comparison functor of the functor
of points of the scheme over `S` that it names.

## Main results

* `AlgebraicGeometry.hasFiniteProducts_bigFppfOver`: the big fppf category over `S` has finite
  products.
* `AlgebraicGeometry.preservesFiniteProducts_overPost_bigFppfInclusion`: the comparison functor
  from the big fppf category over `S` to schemes over `S` preserves finite products.
* `AlgebraicGeometry.fullyFaithful_overPost_bigFppfInclusion`: it is fully faithful.
* `AlgebraicGeometry.bigFppfRestrictedYoneda`: the functor of points of a scheme over `S`,
  restricted to the big fppf category over `S`.
* `AlgebraicGeometry.bigFppfOverRestrictedYonedaIso`: restricting the functor of points of the
  scheme over `S` named by an object of the site gives the functor of points of that object.
* `AlgebraicGeometry.contains_left_overPost_bigFppfInclusion_obj`: the scheme over `S` named by
  an object of the site belongs to the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison functor to schemes over `S` preserves the final object.** The final object
of either slice is the identity of its base, and the comparison functor sends the identity of
`B.obj hS` to the identity of `S`. -/
theorem preservesTerminal_overPost_bigFppfInclusion :
    PreservesLimitsOfShape (Discrete.{0} PEmpty)
      (Over.post (X := B.obj hS) B.inclusion) := by
  have h : IsTerminal ((Over.post (X := B.obj hS) B.inclusion).obj
      (⊤_ (BigFppfOver B S hS))) :=
    IsTerminal.ofIso (Over.mkIdTerminal (X := S))
      ((Over.post (X := B.obj hS) B.inclusion).mapIso
        (terminalIsTerminal.uniqueUpToIso (isTerminal_mkId_bigFppfOver B S hS))).symm
  have := preservesTerminal_of_iso (Over.post (X := B.obj hS) B.inclusion)
    (h.uniqueUpToIso terminalIsTerminal)
  exact preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- **The big fppf category over `S` has finite products**, having a final object and binary
products. -/
instance hasFiniteProducts_bigFppfOver : HasFiniteProducts (BigFppfOver B S hS) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **The comparison functor to schemes over `S` preserves finite products.** A binary product in
a slice is a fibre product over the base, which the inclusion of the cutoff category of schemes
preserves, and the final object is preserved by
`AlgebraicGeometry.preservesTerminal_overPost_bigFppfInclusion`. -/
theorem preservesFiniteProducts_overPost_bigFppfInclusion :
    PreservesFiniteProducts (Over.post (X := B.obj hS) B.inclusion) := by
  have := preservesTerminal_overPost_bigFppfInclusion B S hS
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- **The comparison functor to schemes over `S` is fully faithful**, the inclusion of the cutoff
category of schemes being the inclusion of a full subcategory. -/
def fullyFaithful_overPost_bigFppfInclusion :
    (Over.post (X := B.obj hS) B.inclusion).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful B.inclusion).over (X := B.obj hS)

/-- **The scheme over `S` named by an object of the big fppf category over `S` belongs to the
site**, being that object's underlying scheme. -/
theorem contains_left_overPost_bigFppfInclusion_obj (W : BigFppfOver B S hS) :
    B.Contains ((Over.post (X := B.obj hS) B.inclusion).obj W).left :=
  W.left.property

/-- **The functor of points of a scheme over `S`, restricted to the big fppf category over
`S`**: the functor of points in `Over S`, precomposed with the comparison functor. Being a
composite of the Yoneda embedding with a restriction along a functor, it preserves all limits
that the category of presheaves of `u`-types has. -/
abbrev bigFppfRestrictedYoneda : Over S ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post (X := B.obj hS) B.inclusion).op

/-- **The functor of points of an object of the big fppf category over `S`**, computed from the
scheme over `S` that it names: restricting the functor of points of that scheme along the
comparison functor gives the functor of points of the object, because the comparison functor is
fully faithful. -/
def bigFppfOverRestrictedYonedaIso (W : BigFppfOver B S hS) :
    (Over.post (X := B.obj hS) B.inclusion).op ⋙
        yoneda.obj ((Over.post (X := B.obj hS) B.inclusion).obj W) ≅ yoneda.obj W := by
  let F := Over.post (X := B.obj hS) B.inclusion
  let FF : F.FullyFaithful := fullyFaithful_overPost_bigFppfInclusion B S hS
  refine NatIso.ofComponents
    (fun X => Equiv.toIso (FF.homEquiv (X := X.unop) (Y := W)).symm) ?_
  intro X Y f
  ext g
  change F.obj X.unop ⟶ F.obj W at g
  apply FF.map_injective
  change F.map (FF.preimage (F.map f.unop ≫ g)) = F.map (f.unop ≫ FF.preimage g)
  simp

end AlgebraicGeometry

end
