module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
import StacksCore.Tactic.EgaSgaAttribute

/-! # The tensor–internal-Hom bijection as an adjunction

Let `(C, O)` be a ringed site and let `B` be an object of `D(O)`. Stacks 08J8 is the bijection

`(A ⟶ RSheafHom(B, Z)) ≃ (A ⊗^L_O B ⟶ Z)`,

`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, and its naturality in `A` and in `Z` are
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` and
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target`. Those are exactly the two
clauses of `CategoryTheory.Adjunction.CoreHomEquiv`, so the bijection assembles into an honest
adjunction

`− ⊗^L_O B ⊣ RSheafHom(B, −)`

between endofunctors of `D(O)`. That is the content of this file.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorRight`: `− ⊗^L_O B`, the derived tensor product
  with a fixed right factor.
* `AlgebraicGeometry.RingedSite.derivedTensorHomAdjunction`: the adjunction
  `− ⊗^L_O B ⊣ RSheafHom(B, −)`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorHomAdjunction_homEquiv_symm_apply`: the adjunction's
  bijection is the one of Stacks 08J8, with no further identification.
* `AlgebraicGeometry.RingedSite.commShift_derivedSheafHom`: **`RSheafHom(B, −)` commutes with the
  shift.** This is the transport of the commutation of `− ⊗^L_O B` with the shift along the
  adjunction, by `CategoryTheory.Adjunction.rightAdjointCommShift`. It is registered as an
  instance.

## Implementation notes

*Why no tag.* Stacks 08DI and Stacks 08J8 are *equation* tags: each asserts only the bijection of
morphism groups, and each is already registered in this development — 08J8 on
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and 08DI on
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`. The functoriality in the three objects is
the assertion of Stacks 08J9, which is registered on
`AlgebraicGeometry.RingedSite.derivedCurryNatIso` and
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural`. So the adjunction below states no clause
that is not already carried, and nothing here is tagged; it is a *spelling* of existing content, in
the shape the shift transport needs.

*Why the left adjoint, and not the right one, carries the shift datum.* The commutation of the
derived tensor product with the shift is a field of the derived tensor product of Stacks 06YU,
`Stacks.SheafOfModules.DerivedTensorProduct.commShift_left`, obtained by descending the
commutation of the total tensor complex with the shift along the localization. The derived
internal Hom has no such descent available: its cochain model is the internal Hom complex into
the chosen K-injective *resolution* of the target, and that resolution is not known to commute
with the shift. Transport along the adjunction is therefore the only route to a `CommShift` for
`RSheafHom(B, −)`, and it is the route the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness` record as
unavailable *because* Stacks 08DI was present only as a family of additive equivalences. With
`derivedTensorHomAdjunction` it becomes available, and `commShift_derivedSheafHom` is it.

*What this does not give.* The adjunction is for a **fixed** second argument `B`, so the
`CommShift` it transports is the one of the covariant variable `RSheafHom(B, −)`. It says nothing
about the contravariant variable `RSheafHom(−, Z)`, for which the corresponding statement would
be an adjunction with a fixed *source*, and `RSheafHom(−, Z)` has no left adjoint in sight.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- `− ⊗^L_O B`, the derived tensor product of Stacks 06YU with a fixed right factor `B`. -/
abbrev derivedTensorRight :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.obj B

/-- The bijection of Stacks 08J8 in the shape an adjunction wants it: a plain equivalence
`(A ⊗^L_O B ⟶ Z) ≃ (A ⟶ RSheafHom(B, Z))`, read off the additive equivalence
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` by forgetting the additivity and inverting.

Taking the underlying equivalence as a *projection* of the additive one, rather than rebuilding
it from `toFun` and `invFun`, is deliberate: the two coercion paths for `⇑` on an `AddEquiv` of
derived-category morphism groups do not unify without unfolding the whole composite that
`derivedCurryHomEquiv` is, and the structure literal exceeds the elaborator's recursion depth on
its `left_inv` field. -/
def derivedCurryEquivFlip
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorRight X B).obj A ⟶ Z) ≃
      (A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :=
  (derivedCurryHomEquiv X A B Z).toEquiv.symm

/-- Naturality of `derivedCurryEquivFlip` in the source variable: the first clause of
`CategoryTheory.Adjunction.CoreHomEquiv`, which is Stacks 08J8's naturality in `A`.

It is a declaration of its own, and not written inline in the adjunction below, because the
`exact` that matches it against the field's statement exceeds the elaborator's recursion depth
when the surrounding structure instance still carries metavariables. -/
theorem derivedCurryEquivFlip_naturality_left_symm
    {A A' Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A' ⟶ A)
    (g : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    (derivedCurryEquivFlip X B A' Z).symm (f ≫ g) =
      (derivedTensorRight X B).map f ≫ (derivedCurryEquivFlip X B A Z).symm g := by
  simp only [derivedCurryEquivFlip, Equiv.symm_symm]
  exact derivedCurryHomEquiv_naturality_source X f g

/-- Naturality of `derivedCurryEquivFlip` in the target variable: the second clause of
`CategoryTheory.Adjunction.CoreHomEquiv`, which is Stacks 08J8's naturality in `Z`.

It is a declaration of its own for the reason recorded on
`derivedCurryEquivFlip_naturality_left_symm`. -/
theorem derivedCurryEquivFlip_naturality_right
    {A Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : (derivedTensorRight X B).obj A ⟶ Z) (g : Z ⟶ Z') :
    derivedCurryEquivFlip X B A Z' (f ≫ g) =
      derivedCurryEquivFlip X B A Z f ≫ ((derivedSheafHomBifunctor X).obj (op B)).map g := by
  simp only [derivedCurryEquivFlip]
  have h := derivedCurryHomEquiv_naturality_target X g
    ((derivedCurryHomEquiv X A B Z).symm f)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← h]
  exact (derivedCurryHomEquiv X A B Z').symm_apply_apply _

/-- The bijection of Stacks 08J8 together with its two naturality clauses, as the datum
`CategoryTheory.Adjunction.CoreHomEquiv` an adjunction is assembled from.

The source clause is discharged by `apply` rather than by `exact` or by giving the term: with the
structure instance's remaining fields still metavariables, matching
`derivedCurryEquivFlip_naturality_left_symm` against this field by `exact` exceeds the
elaborator's recursion depth, while the same match outside the structure instance succeeds.
`apply`, which unifies the conclusion first, does not. -/
def derivedTensorHomCore :
    Adjunction.CoreHomEquiv (derivedTensorRight X B)
      ((derivedSheafHomBifunctor X).obj (op B)) where
  homEquiv := derivedCurryEquivFlip X B
  homEquiv_naturality_left_symm _ _ := by apply derivedCurryEquivFlip_naturality_left_symm
  homEquiv_naturality_right f g := derivedCurryEquivFlip_naturality_right X B f g

/-- **The tensor–internal-Hom adjunction.** Tensoring with `B` is left adjoint to the derived
internal Hom out of `B`,

`− ⊗^L_O B ⊣ RSheafHom(B, −)`,

the bijection being that of Stacks 08J8 and the two naturality clauses its naturality in the
source and in the target. -/
@[sga "4½ Etat_0 6.2" "more general"]
def derivedTensorHomAdjunction :
    derivedTensorRight X B ⊣ (derivedSheafHomBifunctor X).obj (op B) :=
  Adjunction.mkOfHomEquiv (derivedTensorHomCore X B)

/-- **The adjunction's bijection is the bijection of Stacks 08J8.** Its inverse sends
`h : A ⟶ RSheafHom(B, Z)` to the morphism `A ⊗^L_O B ⟶ Z` that
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` matches with `h`, with no intervening
identification. -/
theorem derivedTensorHomAdjunction_homEquiv_symm_apply
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    ((derivedTensorHomAdjunction X B).homEquiv A Z).symm h = derivedCurryHomEquiv X A B Z h := by
  simp only [derivedTensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv, derivedTensorHomCore,
    derivedCurryEquivFlip, Equiv.symm_symm]
  rfl

/-- **The derived internal Hom out of a fixed object commutes with the shift.** The derived
tensor product with a fixed right factor commutes with the shift (Stacks 06YU,
`Stacks.SheafOfModules.DerivedTensorProduct.commShift_left`), and
`derivedTensorHomAdjunction` makes `RSheafHom(B, −)` its right adjoint, so
`CategoryTheory.Adjunction.rightAdjointCommShift` transports the commutation. -/
instance commShift_derivedSheafHom :
    (((derivedSheafHomBifunctor X).obj (op B))).CommShift ℤ :=
  (derivedTensorHomAdjunction X B).rightAdjointCommShift ℤ

/-- The transported commutation is compatible with the adjunction, which is the uniqueness
clause of `CategoryTheory.Adjunction.rightAdjointCommShift`. -/
instance commShift_derivedTensorHomAdjunction :
    (derivedTensorHomAdjunction X B).CommShift ℤ :=
  (derivedTensorHomAdjunction X B).commShift_of_leftAdjoint ℤ

end AlgebraicGeometry.RingedSite

end
