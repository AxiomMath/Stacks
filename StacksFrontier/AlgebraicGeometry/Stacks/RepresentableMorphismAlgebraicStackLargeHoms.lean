module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory

/-!
# The source of a representable morphism into an algebraic stack, for large morphism types

Stacks 05UM says that if `j : 𝒳 ⟶ 𝒴` is a 1-morphism of categories fibred in groupoids over the
big fppf site of `S` which is representable by algebraic spaces, and `𝒴` is an algebraic stack,
then so is `𝒳`. Its form
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces` has the
total categories in the universes of the site. Categories such as `Complexes_{X/B}` of Stacks
0DLE have morphisms in a larger universe, and this file states Stacks 05UM for them.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_largeHoms`:
  Stacks 05UM for categories whose morphism types are not small, provided the diagonal of the
  source is representable by algebraic spaces.

## Implementation notes

A category fibred in groupoids whose diagonal is representable by algebraic spaces is locally
small (`AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicSpaceIsomPresheaf`), so it has the
small model `CategoryTheory.BasedCategory.shrinkHoms`, equivalent to it over the site. The
1-morphism `j` is carried to the small models, where it stays representable by Stacks 0457
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`). Stacks 05UM
applies there, and algebraicity comes back by Stacks 03YQ in independent universes
(`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver`).

The diagonal of `𝒳` is a hypothesis because the comparison of diagonals,
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpaces`, is
itself stated in the universes of the site, and local smallness of `𝒳` is needed before its
small model can be formed.

## References

* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05UM, for categories whose morphism types are not small.** Let `j : 𝒳 ⟶ 𝒴` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S`, whose total categories
have their morphisms in an arbitrary universe. If `j` is representable by algebraic spaces, the
diagonal of `𝒳` is representable by algebraic spaces and `𝒴` is an algebraic stack, then `𝒳` is
an algebraic stack.

Both categories are locally small, so `j` is carried to their small models, where Stacks 05UM
applies; algebraicity returns along the equivalence of `𝒳` with its small model
(Stacks 03YQ in independent universes). -/
theorem isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_largeHoms
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  have h𝒴diag : HasRepresentableDiagonal B S hS 𝒴 := h𝒴.2.2.1
  have : LocallySmall.{u} 𝒳.val.obj := locallySmall_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp hdiag)
  have : LocallySmall.{u} 𝒴.val.obj := locallySmall_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒴
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mp h𝒴diag)
  let e𝒳 := BasedCategory.shrinkHomsEquivalenceOver 𝒳.val
  let e𝒴 := BasedCategory.shrinkHomsEquivalenceOver 𝒴.val
  let E𝒳 : BasedCategory.Equivalence 𝒳.val 𝒳.val.shrinkHoms := e𝒳.toBasedEquivalence
  let E𝒴 : BasedCategory.Equivalence 𝒴.val 𝒴.val.shrinkHoms := e𝒴.toBasedEquivalence
  let 𝒳s : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳.val.shrinkHoms
      (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e𝒳.symm 𝒳.2)
  let 𝒴s : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒴.val.shrinkHoms
      (StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e𝒴.symm 𝒴.2)
  -- `j` carried to the small models
  let js : 𝒳s.val ⥤ᵇ 𝒴s.val :=
    BasedFunctor.comp E𝒳.inverse (BasedFunctor.comp j.hom E𝒴.functor)
  let α : BasedFunctor.comp E𝒳.inverse j.hom ≅ BasedFunctor.comp js E𝒴.inverse :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft (BasedFunctor.comp E𝒳.inverse j.hom).toFunctor
        (BasedFunctor.toFunctorIso E𝒴.functor E𝒴.inverse E𝒴.unitIso).symm)
      (fun a => E𝒴.unitIso.inv.isHomLift ((BasedFunctor.comp E𝒳.inverse j.hom).w_obj a))
  have : Functor.IsEquivalence E𝒳.inverse.toFunctor := E𝒳.symm.equiv.isEquivalence_functor
  have : Functor.IsEquivalence E𝒴.inverse.toFunctor := E𝒴.symm.equiv.isEquivalence_functor
  have hjs : IsRepresentableByAlgebraicSpaces B S hS js :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (𝒳' := 𝒳s) (𝒳 := 𝒳)
      (𝒴' := 𝒴s) (𝒴 := 𝒴) js j.hom E𝒳.inverse E𝒴.inverse α).mp hj
  have h𝒴s : IsAlgebraicStack.{u, w} B S hS 𝒴s.val :=
    isAlgebraicStack_of_equivalenceOver B S hS e𝒴 h𝒴
  have h𝒳s : IsAlgebraicStack.{u, w} B S hS 𝒳s.val :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
      (Bicategory.InducedBicategory.mkHom js : 𝒳s ⟶ 𝒴s) hjs h𝒴s
  exact isAlgebraicStack_of_equivalenceOver B S hS e𝒳.symm h𝒳s

end AlgebraicGeometry.Stack

end
