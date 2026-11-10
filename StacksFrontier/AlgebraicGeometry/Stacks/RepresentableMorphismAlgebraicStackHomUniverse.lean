module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Stacks 05UM for categories whose morphisms are not small

`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces` is
Stacks 05UM for categories fibred in groupoids whose hom types live in the universe of the
schemes. Categories of sheaves on the members of a family, such as the stack of coherent sheaves
of Stacks 08KB or the Picard stack of Stacks 0372, have hom types one universe up. This file gives
05UM at an arbitrary hom universe.

The proof brings both categories down to their hom-shrunk models
(`CategoryTheory.BasedCategory.shrinkHoms`). The target is locally small because it is an
algebraic stack (`AlgebraicGeometry.Stack.locallySmall_of_isAlgebraicStack`). The source is
locally small because a 1-morphism representable by algebraic spaces is faithful
(`AlgebraicGeometry.Stack.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`). Both
facts are proved, not assumed. Representability is invariant under the two equivalences
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`), 05UM applies to
the small models, and algebraicity comes back along the equivalence over the site (Stacks 03YQ in
independent universes).

## Main results

* `Stack.locallySmall_source_of_isRepresentableByAlgebraicSpaces`: the source of a 1-morphism
  representable by algebraic spaces into a locally small category is locally small.
* `Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse`: Stacks 05UM at
  an arbitrary hom universe.

## References

* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The source of a representable 1-morphism into a locally small category is locally small.**
A 1-morphism representable by algebraic spaces is faithful, so the hom types of its source embed
into those of its target. -/
theorem locallySmall_source_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom) [LocallySmall.{u} 𝒴.val.obj] :
    LocallySmall.{u} 𝒳.val.obj :=
  have := faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS j hj
  locallySmall_of_faithful (CatFiberedInGroupoids.homFunctor j)

/-- **Stacks 05UM, at an arbitrary hom universe.** If a 1-morphism `j : 𝒳 ⟶ 𝒴` of categories
fibred in groupoids over the big fppf site of `S` is representable by algebraic spaces and `𝒴` is
an algebraic stack over `S`, then `𝒳` is an algebraic stack over `S`. The hom types of `𝒳` and
`𝒴` may live in any universe. -/
theorem isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  have : LocallySmall.{u} 𝒴.val.obj := locallySmall_of_isAlgebraicStack B S hS h𝒴
  have : LocallySmall.{u} 𝒳.val.obj :=
    locallySmall_source_of_isRepresentableByAlgebraicSpaces B S hS j hj
  let 𝒳s : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳.val.shrinkHoms
      (BasedCategory.isFiberedInGroupoids_shrinkHoms 𝒳.val 𝒳.isFiberedInGroupoids)
  let 𝒴s : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒴.val.shrinkHoms
      (BasedCategory.isFiberedInGroupoids_shrinkHoms 𝒴.val 𝒴.isFiberedInGroupoids)
  -- the two comparison functors out of the small models, and the one into the small target
  let a : 𝒳s.val ⥤ᵇ 𝒳.val := ⟨ShrinkHoms.inverse.{u} 𝒳.val.obj, rfl⟩
  let b : 𝒴s.val ⥤ᵇ 𝒴.val := ⟨ShrinkHoms.inverse.{u} 𝒴.val.obj, rfl⟩
  let c : 𝒴.val ⥤ᵇ 𝒴s.val :=
    ⟨ShrinkHoms.functor.{u} 𝒴.val.obj, BasedCategory.shrinkHoms_functor_comp 𝒴.val⟩
  let js : 𝒳s ⟶ 𝒴s :=
    Bicategory.InducedBicategory.mkHom (BasedFunctor.comp (BasedFunctor.comp a j.hom) c)
  have he : BasedFunctor.comp a j.hom = BasedFunctor.comp js.hom b := by
    refine BasedCategory.BasedFunctor.ext' ?_
    change a.toFunctor ⋙ j.hom.toFunctor =
      a.toFunctor ⋙ j.hom.toFunctor ⋙ (ShrinkHoms.functor.{u} 𝒴.val.obj ⋙
        ShrinkHoms.inverse.{u} 𝒴.val.obj)
    rw [BasedCategory.shrinkHoms_functor_comp_inverse 𝒴.val, Functor.comp_id]
  have : Functor.IsEquivalence a.toFunctor :=
    (ShrinkHoms.equivalence.{u} 𝒳.val.obj).isEquivalence_inverse
  have : Functor.IsEquivalence b.toFunctor :=
    (ShrinkHoms.equivalence.{u} 𝒴.val.obj).isEquivalence_inverse
  have hjs : IsRepresentableByAlgebraicSpaces B S hS js.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS js.hom j.hom a b
      (eqToIso he)).mp hj
  have h𝒴s : IsAlgebraicStack.{u, w} B S hS 𝒴s.val := isAlgebraicStack_shrinkHoms B S hS h𝒴
  have h𝒳s : IsAlgebraicStack.{u, w} B S hS 𝒳s.val :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS js hjs h𝒴s
  exact isAlgebraicStack_of_equivalenceOver B S hS
    (BasedCategory.shrinkHomsEquivalenceOver 𝒳.val).symm h𝒳s

end AlgebraicGeometry.Stack

end
