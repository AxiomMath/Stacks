module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-! # The contravariant commutation of the derived internal hom with the translation, on a
ringed space

Let `(X, O_X)` be a ringed space. This file reads the contravariant commutation

`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[-b]`

of `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift`
off along `Stacks.SheafOfModules.ringedSite`, in the vocabulary of
`Stacks.SheafOfModules.StructureSheafModules`, with no comparison layer between the two
settings: a topological space with a sheaf of commutative rings *is* a ringed site.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHomSourceShiftIso`: the commutation
  `RSheafHom(K[b], L) ≅ RSheafHom(K, L)[-b]`.
* `Stacks.SheafOfModules.derivedSheafHomOpShiftNatIso`: the same as a natural isomorphism of
  functors on `D(O_X)ᵒᵖ`, which is the `commShiftIso` datum of a
  `CategoryTheory.Functor.CommShift ℤ` on `RSheafHom(-, M)` for the opposite shift of
  `CategoryTheory.Pretriangulated.Opposite`.
* `Stacks.SheafOfModules.commShift_derivedSheafHomFlip`: `RSheafHom(-, M)` commutes with the
  shift, with both coherence equations, as soon as the contravariant internal hom *complex*
  does.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomSourceShiftIso_hom_naturality`: the commutation is
  natural in both variables, for arbitrary morphisms of `D(O_X)`.

## What is still missing, and what it blocks

The implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness` record that the
contravariant variable `RSheafHom(-, N)` carries no `CategoryTheory.Functor.CommShift`. The
*datum* of one is `derivedSheafHomOpShiftNatIso` below; what is not proved is the pair of
coherence equations `CategoryTheory.Functor.CommShift.commShiftIso_zero` and `commShiftIso_add`,
so nothing here is registered as an instance and that note's conclusion still stands as stated.

They are not left standing bare, though: `commShift_derivedSheafHomFlip` below derives both of
them from the corresponding structure on the ordinary internal hom complex, by the localization
descent of `AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip`, so what remains open is
a statement about complexes of `O_X`-modules alone.

That residual is the residual of Stacks 0GM7 clause (1): the dévissage
`Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_of_generatedByOp`
of `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/InternalHomPullbackDevissage.lean`
carries five shift binders, of which the two `CategoryTheory.Functor.CommShift` ones are
`RSheafHom(-, M)` composed with the derived pullback — which does carry a commutation — so an
instance here would discharge both by `CategoryTheory.Functor.CommShift.comp`.

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The derived internal hom of a ringed space commutes with the translation in its
contravariant variable.** For arbitrary objects `K`, `L` of `D(O_X)` and every integer `b`,

`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[-b]`.

This is `AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso` at the site of opens. -/
def derivedSheafHomSourceShiftIso
    (K L : DerivedCategory (StructureSheafModules Rc)) (b : ℤ) :
    ((derivedSheafHom Rc).obj (op (K⟦b⟧))).obj L ≅
      (((derivedSheafHom Rc).obj (op K)).obj L)⟦-b⟧ :=
  RingedSite.derivedSheafHomSourceShiftIso (ringedSite Rc) K L b

/-- The contravariant commutation with the index of the outer shift in general position:
`RSheafHom(K[b], L) ≅ RSheafHom(K, L)[c]` whenever `b + c = 0`. -/
def derivedSheafHomSourceShiftIso'
    (K L : DerivedCategory (StructureSheafModules Rc)) (b c : ℤ) (h : b + c = 0) :
    ((derivedSheafHom Rc).obj (op (K⟦b⟧))).obj L ≅
      (((derivedSheafHom Rc).obj (op K)).obj L)⟦c⟧ :=
  RingedSite.derivedSheafHomSourceShiftIso' (ringedSite Rc) K L b c h

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The contravariant commutation is natural in both variables**, for arbitrary morphisms of
`D(O_X)`: for `φ : K' ⟶ K` and `ψ : L ⟶ L'` the morphism induced by `φ[b]` and `ψ` is carried to
the `(-b)`-shift of the morphism induced by `φ` and `ψ`.

This is `AlgebraicGeometry.RingedSite.derivedSheafHomSourceShiftIso_hom_naturality` at the site
of opens. -/
theorem derivedSheafHomSourceShiftIso_hom_naturality
    {K K' L L' : DerivedCategory (StructureSheafModules Rc)} (φ : K' ⟶ K) (ψ : L ⟶ L')
    (b : ℤ) :
    (((derivedSheafHom Rc).map
              ((CategoryTheory.shiftFunctor
                (DerivedCategory (StructureSheafModules Rc)) b).map φ).op).app L ≫
          ((derivedSheafHom Rc).obj (op (K'⟦b⟧))).map ψ) ≫
        (derivedSheafHomSourceShiftIso Rc K' L' b).hom =
      (derivedSheafHomSourceShiftIso Rc K L b).hom ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (StructureSheafModules Rc)) (-b)).map
          (((derivedSheafHom Rc).map φ.op).app L ≫
            ((derivedSheafHom Rc).obj (op K')).map ψ) :=
  RingedSite.derivedSheafHomSourceShiftIso_hom_naturality (ringedSite Rc) φ ψ b

open scoped CategoryTheory.Pretriangulated.Opposite

/-- **The commutation of `RSheafHom(-, M)` with the shift on a ringed space, as a natural
isomorphism of functors on `D(O_X)ᵒᵖ`.** This is the `commShiftIso` datum of a
`CategoryTheory.Functor.CommShift ℤ` on the contravariant derived internal hom; its component at
`op K` is `RSheafHom(K[-n], M) ≅ RSheafHom(K, M)[n]`, because the opposite shift of
`CategoryTheory.Pretriangulated.Opposite` presents `(op K)[n]` as `op (K[-n])`.

The two coherence equations of `CategoryTheory.Functor.CommShift` are not proved, so this is not
registered as an instance. -/
def derivedSheafHomOpShiftNatIso (M : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    CategoryTheory.shiftFunctor (DerivedCategory (StructureSheafModules Rc))ᵒᵖ n ⋙
        (derivedSheafHom Rc).flip.obj M ≅
      (derivedSheafHom Rc).flip.obj M ⋙
        CategoryTheory.shiftFunctor (DerivedCategory (StructureSheafModules Rc)) n :=
  RingedSite.derivedSheafHomOpShiftNatIso (ringedSite Rc) M n

/-- **The contravariant derived internal hom of a ringed space commutes with the shift, as soon
as the contravariant internal hom *complex* does.**  This is
`AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip` at the site of opens: the whole
residual of the two `CategoryTheory.Functor.CommShift` coherence equations is the hypothesis
`hco`, a statement about complexes of `O_X`-modules in which no derived category, no K-injective
resolution and no localization appears. -/
@[instance_reducible]
def commShift_derivedSheafHomFlip
    (hco : ∀ I : CochainComplex (StructureSheafModules Rc) ℤ,
      ((RingedSite.sheafHomComplexBifunctor (ringedSite Rc)).flip.obj I).CommShift ℤ)
    (M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedSheafHom Rc).flip.obj M).CommShift ℤ :=
  RingedSite.commShift_derivedSheafHomFlip (ringedSite Rc) hco M

end Stacks.SheafOfModules

end
