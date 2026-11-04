module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheafLocalIso
public import StacksFrontier.CategoryTheory.Sites.Modules.PolynomialPresheafMap

/-!
# The free algebra functor preserves local bijectivity

Let `A` be a sheaf of commutative rings on a site `(C, J)` and let `e : E₁ ⟶ E₂` be a morphism of
presheaves of sets on `C`. The induced morphism `A[E₁] ⟶ A[E₂]` of free algebra sheaves is an
isomorphism as soon as `e` becomes an isomorphism after sheafification, in particular as soon as
`e` is locally bijective, that is, both locally injective and locally surjective.

This is the general-site form of `Stacks.Sites.FreeAlgebra.isIso_freeAlgebraSheafMap`, which is
proved stalkwise and therefore only available on a topological space. No hypothesis on the site
(such as having enough points) is needed: the argument is the universal property of `A[E]` rather
than a computation of stalks. Indeed `A ↦ A[E]` is a left adjoint in the variable `E`, with values
in sheaves of rings, so it only sees `E` through the sheaf of sets it generates; the class of
morphisms of presheaves inverted by sheafification is by definition the class of morphisms `e` such
that precomposition with `e` is bijective on morphisms into any sheaf, which is exactly what is
needed to invert `A[E₁] ⟶ A[E₂]`.

## Main definitions

* `Stacks.Sites.FreeAlgebra.liftVariable`: the morphism `E₂ ⟶ A[E₁]` which extends the variables
  of `E₁` along a morphism `e : E₁ ⟶ E₂` inverted by sheafification.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafMapInv`: the inverse of `A[E₁] ⟶ A[E₂]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafMapIsoOfW`: the resulting isomorphism
  `A[E₁] ≅ A[E₂]`.

## Main results

* `Stacks.Sites.FreeAlgebra.isSheaf_underlyingPresheaf`: the underlying presheaf of sets of a sheaf
  of commutative rings is a sheaf of sets.
* `Stacks.Sites.FreeAlgebra.bijective_comp_underlyingPresheaf`: a morphism of presheaves of sets
  inverted by sheafification induces a bijection on the morphisms into the underlying presheaf of
  sets of a sheaf of commutative rings.
* `Stacks.Sites.FreeAlgebra.isIso_freeAlgebraSheafMap_of_W`: a morphism of presheaves of sets
  inverted by sheafification induces an isomorphism of free algebra sheaves.
* `Stacks.Sites.FreeAlgebra.isIso_freeAlgebraSheafMap_of_isLocallyBijective`: a locally bijective
  morphism of presheaves of sets induces an isomorphism of free algebra sheaves.
* `Stacks.Sites.FreeAlgebra.presheafToSheaf_map_polynomialPresheafMap`: the morphism of free
  algebra sheaves is the sheafification of the morphism of polynomial presheaves.
* `Stacks.Sites.FreeAlgebra.isLocallyInjective_polynomialPresheafMap` and
  `Stacks.Sites.FreeAlgebra.isLocallySurjective_polynomialPresheafMap`: renaming variables along
  a locally bijective morphism of presheaves of sets gives a locally bijective morphism of
  presheaves of commutative rings. This is the form used in an induction over the terms of a
  standard resolution.

## Implementation notes

`J.W` is `CategoryTheory.ObjectProperty.isLocal (CategoryTheory.Presheaf.IsSheaf J)`, so a term of
`J.W e` *is* the statement that precomposition with `e` is bijective on morphisms into any sheaf;
`CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective` produces one from local injectivity
and local surjectivity, given the instance `J.WEqualsLocallyBijective (Type w)`, which holds for
instance when `w = max u v`.

The hypothesis `J.HasSheafCompose (forget CommRingCat)` only serves to know that the underlying
presheaf of sets of a sheaf of rings is a sheaf; it is automatic as soon as the forgetful functor
preserves limits of the relevant size.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
-/

@[expose] public section

open CategoryTheory

universe v u w

noncomputable section

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget CommRingCat.{w})]
  (A : Sheaf J CommRingCat.{w}) {E₁ E₂ : Functor Cᵒᵖ (Type w)}

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- The underlying presheaf of sets of a sheaf of commutative rings is a sheaf of sets. -/
theorem isSheaf_underlyingPresheaf (B : Sheaf J CommRingCat.{w}) :
    Presheaf.IsSheaf J (underlyingPresheaf J B) :=
  ((sheafCompose J (forget CommRingCat.{w})).obj B).property

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- Whiskering the underlying morphism of presheaves of a composition of morphisms of sheaves of
commutative rings with the forgetful functor. -/
theorem whiskerRight_sheafToPresheaf_map_comp {B₁ B₂ B₃ : Sheaf J CommRingCat.{w}}
    (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) :
    Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map (g₁ ≫ g₂))
        (forget CommRingCat.{w}) =
      Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map g₁)
          (forget CommRingCat.{w}) ≫
        Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map g₂)
          (forget CommRingCat.{w}) := by
  rw [CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp]

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- Whiskering the underlying morphism of presheaves of an identity of sheaves of commutative
rings with the forgetful functor. -/
theorem whiskerRight_sheafToPresheaf_map_id (B : Sheaf J CommRingCat.{w}) :
    Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map (𝟙 B))
      (forget CommRingCat.{w}) = 𝟙 (underlyingPresheaf J B) := by
  rw [CategoryTheory.Functor.map_id, Functor.whiskerRight_id']
  rfl

section

variable (e : E₁ ⟶ E₂)

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- A morphism of presheaves of sets which becomes an isomorphism after sheafification induces a
bijection on the morphisms into the underlying presheaf of sets of a sheaf of commutative rings. -/
theorem bijective_comp_underlyingPresheaf (he : J.W e) (B : Sheaf J CommRingCat.{w}) :
    Function.Bijective (fun g : E₂ ⟶ underlyingPresheaf J B => e ≫ g) :=
  he _ (isSheaf_underlyingPresheaf J B)

/-- The morphism `E₂ ⟶ A[E₁]` extending the variables of `E₁` along a morphism `e : E₁ ⟶ E₂` of
presheaves of sets which becomes an isomorphism after sheafification. -/
def liftVariable (he : J.W e) : E₂ ⟶ underlyingPresheaf J (freeAlgebraSheaf J A E₁) :=
  ((bijective_comp_underlyingPresheaf J e he (freeAlgebraSheaf J A E₁)).surjective
    (freeAlgebraSheafVariable J A E₁)).choose

/-- `liftVariable` does extend the variables of `E₁` along `e`. -/
theorem comp_liftVariable (he : J.W e) :
    e ≫ liftVariable J A e he = freeAlgebraSheafVariable J A E₁ :=
  ((bijective_comp_underlyingPresheaf J e he (freeAlgebraSheaf J A E₁)).surjective
    (freeAlgebraSheafVariable J A E₁)).choose_spec

/-- The morphism `A[E₂] ⟶ A[E₁]` inverse to the morphism induced by a morphism `e : E₁ ⟶ E₂` of
presheaves of sets which becomes an isomorphism after sheafification: it is the morphism of
`A`-algebras sending the variable `[t]`, for `t` a section of `E₂`, to the variable `[s]` for any
local section `s` of `E₁` with `e s = t`. -/
def freeAlgebraSheafMapInv (he : J.W e) :
    freeAlgebraSheaf J A E₂ ⟶ freeAlgebraSheaf J A E₁ :=
  freeAlgebraSheafDesc J A (freeAlgebraSheaf J A E₁) E₂
    (freeAlgebraSheafCoefficientMap J A E₁) (liftVariable J A e he)

/-- The morphism `A[E₁] ⟶ A[E₂]` induced by `e`, followed by `freeAlgebraSheafMapInv`, is the
identity of `A[E₁]`. -/
theorem freeAlgebraSheafMap_comp_inv (he : J.W e) :
    freeAlgebraSheafMap J A e ≫ freeAlgebraSheafMapInv J A e he = 𝟙 _ := by
  refine freeAlgebraSheaf_hom_ext J A _ E₁ ?_ ?_
  · rw [Category.comp_id, ← Category.assoc, freeAlgebraSheafCoefficientMap_comp_map,
      freeAlgebraSheafMapInv, freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [whiskerRight_sheafToPresheaf_map_comp, whiskerRight_sheafToPresheaf_map_id,
      Category.comp_id, ← Category.assoc, freeAlgebraSheafVariable_comp_map, Category.assoc,
      freeAlgebraSheafMapInv, freeAlgebraSheafVariable_comp_desc, comp_liftVariable]

/-- `freeAlgebraSheafMapInv`, followed by the morphism `A[E₁] ⟶ A[E₂]` induced by `e`, is the
identity of `A[E₂]`. -/
theorem freeAlgebraSheafMapInv_comp_map (he : J.W e) :
    freeAlgebraSheafMapInv J A e he ≫ freeAlgebraSheafMap J A e = 𝟙 _ := by
  refine freeAlgebraSheaf_hom_ext J A _ E₂ ?_ ?_
  · rw [Category.comp_id, ← Category.assoc, freeAlgebraSheafMapInv,
      freeAlgebraSheafCoefficientMap_comp_desc, freeAlgebraSheafCoefficientMap_comp_map]
  · refine (bijective_comp_underlyingPresheaf J e he (freeAlgebraSheaf J A E₂)).injective ?_
    show e ≫ _ = e ≫ _
    rw [whiskerRight_sheafToPresheaf_map_comp, whiskerRight_sheafToPresheaf_map_id,
      Category.comp_id, freeAlgebraSheafMapInv,
      ← Category.assoc (freeAlgebraSheafVariable J A E₂),
      freeAlgebraSheafVariable_comp_desc, ← Category.assoc, comp_liftVariable,
      freeAlgebraSheafVariable_comp_map]

/-- **The free algebra functor inverts a morphism of presheaves of sets inverted by
sheafification.** If `e : E₁ ⟶ E₂` becomes an isomorphism after sheafification then the induced
morphism `A[E₁] ⟶ A[E₂]` of free algebra sheaves is an isomorphism. -/
theorem isIso_freeAlgebraSheafMap_of_W (he : J.W e) : IsIso (freeAlgebraSheafMap J A e) :=
  ⟨freeAlgebraSheafMapInv J A e he, freeAlgebraSheafMap_comp_inv J A e he,
    freeAlgebraSheafMapInv_comp_map J A e he⟩

/-- The isomorphism `A[E₁] ≅ A[E₂]` induced by a morphism `e : E₁ ⟶ E₂` of presheaves of sets
which becomes an isomorphism after sheafification. -/
def freeAlgebraSheafMapIsoOfW (he : J.W e) :
    freeAlgebraSheaf J A E₁ ≅ freeAlgebraSheaf J A E₂ :=
  have := isIso_freeAlgebraSheafMap_of_W J A e he
  asIso (freeAlgebraSheafMap J A e)

/-- The forward morphism of `freeAlgebraSheafMapIsoOfW` is the morphism `A[E₁] ⟶ A[E₂]` induced
by `e`. -/
@[simp]
theorem freeAlgebraSheafMapIsoOfW_hom (he : J.W e) :
    (freeAlgebraSheafMapIsoOfW J A e he).hom = freeAlgebraSheafMap J A e :=
  rfl

/-- **The free algebra functor carries a locally bijective morphism of presheaves of sets to a
locally bijective morphism of presheaves of rings.** On an arbitrary site, if `e : E₁ ⟶ E₂` is
locally injective and locally surjective then the induced morphism `A[E₁] ⟶ A[E₂]` of free algebra
sheaves is an isomorphism, hence locally bijective. -/
theorem isIso_freeAlgebraSheafMap_of_isLocallyBijective
    [J.WEqualsLocallyBijective (Type w)] [Presheaf.IsLocallyInjective J e]
    [Presheaf.IsLocallySurjective J e] : IsIso (freeAlgebraSheafMap J A e) :=
  isIso_freeAlgebraSheafMap_of_W J A e (J.W_of_isLocallyBijective e)

/-! ### The morphism of polynomial presheaves

The morphism `A[E₁] ⟶ A[E₂]` of free algebra sheaves is the sheafification of the morphism
`A(-)[E₁(-)] ⟶ A(-)[E₂(-)]` of presheaves of polynomial rings which renames the variables along
`e`. The results above therefore say that renaming variables along a locally bijective morphism of
presheaves of sets gives a locally bijective morphism of presheaves of commutative rings, which is
the form in which the statement is used in an induction over the terms of a standard resolution. -/

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- Renaming variables carries the variable `[x]` to the variable `[e x]`. -/
theorem polynomialVariable_comp_polynomialPresheafMap :
    polynomialVariable J A E₁ ≫ Functor.whiskerRight (polynomialPresheafMap J A e)
        (forget CommRingCat.{w}) = e ≫ polynomialVariable J A E₂ := by
  ext U x
  exact MvPolynomial.eval₂Hom_X' _ _ _

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- Naturality of the unit of the sheafification adjunction at the morphism of polynomial
presheaves. -/
theorem toSheafification_comp_presheafToSheaf_map :
    (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E₁) ≫
        (sheafToPresheaf J CommRingCat.{w}).map
          ((presheafToSheaf J CommRingCat.{w}).map (polynomialPresheafMap J A e)) =
      polynomialPresheafMap J A e ≫
        (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E₂) :=
  ((toSheafification J CommRingCat.{w}).naturality (polynomialPresheafMap J A e)).symm

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The sheafification of the morphism of polynomial presheaves respects the structural morphisms
from `A`. -/
theorem freeAlgebraSheafCoefficientMap_comp_presheafToSheaf_map :
    freeAlgebraSheafCoefficientMap J A E₁ ≫
        (presheafToSheaf J CommRingCat.{w}).map (polynomialPresheafMap J A e) =
      freeAlgebraSheafCoefficientMap J A E₂ := by
  apply (fullyFaithfulSheafToPresheaf J CommRingCat.{w}).homEquiv.injective
  show polynomialCoefficientMap J A E₁ ≫
      ((toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E₁) ≫
        (sheafToPresheaf J CommRingCat.{w}).map
          ((presheafToSheaf J CommRingCat.{w}).map (polynomialPresheafMap J A e))) =
    polynomialCoefficientMap J A E₂ ≫
      (toSheafification J CommRingCat.{w}).app (polynomialPresheaf J A E₂)
  rw [toSheafification_comp_presheafToSheaf_map, ← Category.assoc,
    polynomialCoefficientMap_comp_polynomialPresheafMap]

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The sheafification of the morphism of polynomial presheaves carries the variable `[x]` to the
variable `[e x]`. -/
theorem freeAlgebraSheafVariable_comp_presheafToSheaf_map :
    freeAlgebraSheafVariable J A E₁ ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map
          ((presheafToSheaf J CommRingCat.{w}).map (polynomialPresheafMap J A e)))
        (forget CommRingCat.{w}) = e ≫ freeAlgebraSheafVariable J A E₂ := by
  have key := congrArg (fun f => Functor.whiskerRight f (forget CommRingCat.{w}))
    (toSheafification_comp_presheafToSheaf_map J A e)
  simp only [Functor.whiskerRight_comp] at key
  show polynomialVariable J A E₁ ≫ (Functor.whiskerRight ((toSheafification J CommRingCat.{w}).app
      (polynomialPresheaf J A E₁)) (forget CommRingCat.{w}) ≫ Functor.whiskerRight
      ((sheafToPresheaf J CommRingCat.{w}).map
        ((presheafToSheaf J CommRingCat.{w}).map (polynomialPresheafMap J A e)))
      (forget CommRingCat.{w})) = _
  rw [key, ← Category.assoc, polynomialVariable_comp_polynomialPresheafMap, Category.assoc]
  rfl

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The morphism `A[E₁] ⟶ A[E₂]` of free algebra sheaves is the sheafification of the morphism
of polynomial presheaves renaming the variables along `e`. -/
theorem presheafToSheaf_map_polynomialPresheafMap :
    (presheafToSheaf J CommRingCat.{w}).map (polynomialPresheafMap J A e) =
      freeAlgebraSheafMap J A e :=
  freeAlgebraSheaf_hom_ext J A _ E₁
    ((freeAlgebraSheafCoefficientMap_comp_presheafToSheaf_map J A e).trans
      (freeAlgebraSheafCoefficientMap_comp_map J A e).symm)
    ((freeAlgebraSheafVariable_comp_presheafToSheaf_map J A e).trans
      (freeAlgebraSheafVariable_comp_map J A e).symm)

/-- Renaming variables along a morphism of presheaves of sets inverted by sheafification gives a
morphism of presheaves of commutative rings inverted by sheafification. -/
theorem W_polynomialPresheafMap (he : J.W e) : J.W (polynomialPresheafMap J A e) := by
  rw [GrothendieckTopology.W_iff, presheafToSheaf_map_polynomialPresheafMap]
  exact isIso_freeAlgebraSheafMap_of_W J A e he

/-- **The free algebra functor carries a locally bijective morphism of presheaves of sets to a
locally bijective morphism of presheaves of rings**, first half: local injectivity. -/
instance isLocallyInjective_polynomialPresheafMap [J.WEqualsLocallyBijective (Type w)]
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Presheaf.IsLocallyInjective J e]
    [Presheaf.IsLocallySurjective J e] :
    Presheaf.IsLocallyInjective J (polynomialPresheafMap J A e) :=
  (W_polynomialPresheafMap J A e (J.W_of_isLocallyBijective e)).isLocallyInjective

/-- **The free algebra functor carries a locally bijective morphism of presheaves of sets to a
locally bijective morphism of presheaves of rings**, second half: local surjectivity. -/
instance isLocallySurjective_polynomialPresheafMap [J.WEqualsLocallyBijective (Type w)]
    [J.WEqualsLocallyBijective CommRingCat.{w}] [Presheaf.IsLocallyInjective J e]
    [Presheaf.IsLocallySurjective J e] :
    Presheaf.IsLocallySurjective J (polynomialPresheafMap J A e) :=
  (W_polynomialPresheafMap J A e (J.W_of_isLocallyBijective e)).isLocallySurjective

end

end Stacks.Sites.FreeAlgebra

end

end
