module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRetarget

/-!
# A strictly full subcategory inherits a representable diagonal

Let `j : 𝒳 ⟶ 𝒴` be a 1-morphism of categories over the big fppf site of `S` whose underlying
functor is full and faithful — for instance the inclusion of a strictly full subcategory. This
file shows that `𝒳` inherits from `𝒴` the property of having a diagonal representable by
algebraic spaces.

The reason is that a fully faithful `j` does not change the 2-fibre products that
representability by algebraic spaces is about. For a 1-morphism `f : 𝒜 ⟶ 𝒳` and a point
`y : 𝒰 ⟶ 𝒳`, the 2-fibre product `𝒰 ×_𝒳 𝒜` is the category of quadruples `(T, t, a, φ)` with
`φ : y t ≅ f a` vertical, and the comparison isomorphism of the corresponding object of
`𝒰 ×_𝒴 𝒜` is `j φ`. Since `j` is bijective on morphisms between objects in its image, the two
2-fibre products are isomorphic as categories over `𝒰`; that comparison is
`CategoryTheory.TwoFibreProductOver.mapBaseFstEquivalenceOver`. So representability of `f ≫ j`
already implies representability of `f`, and the criterion carries over to the diagonal through
the equivalence of conditions (1), (2) and (3) of **Stacks 045G**.

No universe coincidence is needed anywhere: the three categories may have arbitrary and
pairwise unrelated morphism and object universes, because nothing below is stated in the
2-category `CategoryTheory.CatFiberedInGroupoids`, whose 1-morphisms exist only between objects
with equal universes. That is what makes this the available route for a subcategory of a
category fibred in groupoids whose morphism universe exceeds that of the site, such as the
category of families of curves.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_comp_fullyFaithful`: a fully
  faithful 1-morphism reflects representability by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_fullyFaithful`: condition (3) of
  Stacks 045G passes from the target of a fully faithful 1-morphism to its source.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_fullyFaithful`: a representable diagonal
  passes from the target of a fully faithful 1-morphism to its source.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory

universe u v₁ v₂ v₃ w₁ w₂ w₃

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A fully faithful 1-morphism reflects representability by algebraic spaces.** If
`b : 𝒴 ⟶ 𝒵` is a 1-morphism of categories over the big fppf site of `S` whose underlying functor
is full and faithful, and the composite `f ≫ b` of a 1-morphism `f : 𝒳 ⟶ 𝒴` with it is
representable by algebraic spaces, then `f` itself is.

Representability of `f` is a statement about the 2-fibre products `𝒰 ×_𝒴 𝒳` taken along the
scheme-valued points of `𝒴`. Postcomposing both legs with `b` changes the comparison
isomorphism of an object from `φ` to `b φ` and nothing else, so for a fully faithful `b` it is
an isomorphism of categories over `𝒰`
(`CategoryTheory.TwoFibreProductOver.mapBaseFstEquivalenceOver`); an algebraic space
representing one side therefore represents the other. -/
theorem isRepresentableByAlgebraicSpaces_of_comp_fullyFaithful
    {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
    {𝒵 : BasedCategory.{v₃, w₃} (BigFppfOver B S hS)}
    (f : 𝒳 ⥤ᵇ 𝒴) (b : 𝒴 ⥤ᵇ 𝒵) [b.toFunctor.Full] [b.toFunctor.Faithful]
    (h : IsRepresentableByAlgebraicSpaces B S hS (f.comp b)) :
    IsRepresentableByAlgebraicSpaces B S hS f := by
  intro U 𝒰 p𝒰 y hy
  obtain ⟨F, hF, ⟨e⟩⟩ := h U (y ⋙ b.toFunctor) (by rw [Functor.assoc, b.w]; exact hy)
  exact ⟨F, hF, ⟨(TwoFibreProductOver.mapBaseFstEquivalenceOver
    (G := y) (F := f.toFunctor) b.w).trans e⟩⟩

/-- **Condition (3) of Stacks 045G passes to the source of a fully faithful 1-morphism.** If
every 1-morphism to `𝒴` from the category represented by a scheme over `S` is representable by
algebraic spaces, and `j : 𝒳 ⟶ 𝒴` is fully faithful, then every 1-morphism to `𝒳` from the
category represented by a scheme is representable by algebraic spaces: compose it with `j` and
apply `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_comp_fullyFaithful`. -/
theorem isRepresentableFromSchemes_of_fullyFaithful
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    (j : 𝒳.val ⥤ᵇ 𝒴.val) [j.toFunctor.Full] [j.toFunctor.Faithful]
    (h : IsRepresentableFromSchemes B S hS 𝒴) :
    IsRepresentableFromSchemes B S hS 𝒳 := fun U x =>
  isRepresentableByAlgebraicSpaces_of_comp_fullyFaithful B S hS x j (h U (x.comp j))

/-- **A representable diagonal passes to the source of a fully faithful 1-morphism.** If the
diagonal of `𝒴` is representable by algebraic spaces and `j : 𝒳 ⟶ 𝒴` is a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` whose underlying functor is full
and faithful, then the diagonal of `𝒳` is representable by algebraic spaces.

This is `AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_fullyFaithful` read through the
equivalence of conditions (1), (2) and (3) of Stacks 045G. In particular the diagonal of a
strictly full subcategory of a category fibred in groupoids is representable as soon as the
diagonal of the ambient category is. -/
theorem hasRepresentableDiagonal_of_fullyFaithful
    {𝒳 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    (j : 𝒳.val ⥤ᵇ 𝒴.val) [j.toFunctor.Full] [j.toFunctor.Faithful]
    (h : HasRepresentableDiagonal B S hS 𝒴) :
    HasRepresentableDiagonal B S hS 𝒳 :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mpr
    ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mpr
      (isRepresentableFromSchemes_of_fullyFaithful B S hS j
        ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mp
          ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mp h))))

end AlgebraicGeometry.Stack

end
