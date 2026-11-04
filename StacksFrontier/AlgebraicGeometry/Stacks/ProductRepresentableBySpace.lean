module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The final object and the product are representable by algebraic spaces (Stacks 0300, 04SV)

Let `S` be a scheme contained in a big fppf site `B`. The 2-category of categories fibred in
groupoids over the big fppf site of `S` has a final object
`AlgebraicGeometry.Stack.terminalCFG`, the site itself with the identity as structure functor,
and the product `𝒳₁ × 𝒳₂` is by definition the 2-fibre product of `𝒳₁` and `𝒳₂` over it.

This file records that the final object is *represented by an algebraic space* over `S`, and
deduces that a product of two categories fibred in groupoids each represented by an algebraic
space is again represented by an algebraic space.

The final object is not literally the slice of the site over a scheme, so Stacks 04SV for a
slice (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory`) does not
apply to it on the nose: the slice of the site over the terminal object `S/S` has total category
the *iterated* slice `(Sch/S)/(S/S)`, while the final object has total category `(Sch/S)` itself.
The two are equivalent over the site, and the equivalence is strict in the direction needed:
`CategoryTheory.Over.iteratedSliceBackward` composed with the forgetful functor of the iterated
slice is `CategoryTheory.Over.map (𝟙 S)`, which *is* the identity functor
(`CategoryTheory.Over.mapId_eq`). So the representability transports along
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`, which asks for exactly a
strictly commuting equivalence between two categories fibred in groupoids.

## Main results

* `CategoryTheory.Over.iteratedSliceBackward_forget_id`: the iterated slice of a category over
  the identity is strictly a slice of it over the base.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_terminalCFG`: the final object of the
  2-category is represented by an algebraic space over `S`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_toTerminalCFG`: the structure
  1-morphism of a category represented by an algebraic space to the final object is
  representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_product`: a product of two categories
  fibred in groupoids each represented by an algebraic space is represented by an algebraic
  space.

## Implementation notes

The product is the 2-fibre product over the final object *on the nose*: with `𝒴 = terminalCFG`
and both legs the structure 1-morphisms,
`AlgebraicGeometry.Stack.twoFibreProduct` and `CategoryTheory.CatFiberedInGroupoids.product`
have the same underlying based category, and the remaining field of a
`CategoryTheory.CatFiberedInGroupoids` is a proof, so the two agree definitionally. The last
result is therefore Stacks 0300
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`) read at that
cospan, with no comparison to build.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Over

universe v₁ u₁

variable {T : Type u₁} [Category.{v₁} T]

/-- The slice of `T/X` over the terminal object `𝟙 X` of `T/X`, followed by its forgetful
functor to `T/X`, is the identity: the comparison is
`CategoryTheory.Over.iteratedSliceBackward_forget`, whose value `Over.map (𝟙 X)` is the identity
functor by `CategoryTheory.Over.mapId_eq`. -/
lemma iteratedSliceBackward_forget_id (X : T) :
    iteratedSliceBackward (Over.mk (𝟙 X)) ⋙ Over.forget (Over.mk (𝟙 X)) = 𝟭 (Over X) := by
  rw [Over.iteratedSliceBackward_forget]
  exact Over.mapId_eq _

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The final object of the 2-category is represented by an algebraic space.** The site itself,
with the identity as structure functor, is represented by the algebraic space of points of the
terminal object `S/S` of the site.

The slice of the site over `S/S` is represented by it (Stacks 04SV for a slice), and
`CategoryTheory.Over.iteratedSliceBackward` is an equivalence onto that slice which commutes
strictly with the two structure functors by
`CategoryTheory.Over.iteratedSliceBackward_forget_id`. -/
theorem isRepresentableByAlgebraicSpace_terminalCFG :
    IsRepresentableByAlgebraicSpace B S hS (terminalCFG B S hS) := by
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))
  obtain ⟨e₀⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (p₁ := 𝟭 (BigFppfOver B S hS)) (p₂ := Over.forget (Over.mk (𝟙 (B.obj hS))))
    Functor.isFiberedInGroupoids_id (Functor.IsFiberedInGroupoids.over_forget _)
    (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))))
    (Over.iteratedSliceBackward_forget_id (B.obj hS))
    (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).isEquivalence_inverse
  exact ⟨F, hF, ⟨e₀.trans e⟩⟩

/-- **Stacks 02ZZ at the final object.** The structure 1-morphism to the final object of a
category fibred in groupoids represented by an algebraic space over `S` is representable by
algebraic spaces: both its source and its target are represented by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_toTerminalCFG
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS (toTerminalCFG B S hS 𝒳) :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)) h𝒳
    (isRepresentableByAlgebraicSpace_terminalCFG B S hS)

/-- **Stacks 0300 for the product.** The product of two categories fibred in groupoids over the
big fppf site of `S`, each represented by an algebraic space over `S`, is represented by an
algebraic space over `S`.

The product is the 2-fibre product over the final object, so this is Stacks 0300 applied to the
cospan of the two structure 1-morphisms, the second of which is representable by algebraic
spaces by `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_toTerminalCFG`. -/
theorem isRepresentableByAlgebraicSpace_product
    (𝒳₁ 𝒳₂ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳₁ : IsRepresentableByAlgebraicSpace B S hS 𝒳₁)
    (h𝒳₂ : IsRepresentableByAlgebraicSpace B S hS 𝒳₂) :
    IsRepresentableByAlgebraicSpace B S hS (CatFiberedInGroupoids.product 𝒳₁ 𝒳₂) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS (terminalCFG B S hS) 𝒳₁ 𝒳₂
    (toTerminalCFG B S hS 𝒳₁) (toTerminalCFG B S hS 𝒳₂)
    (isRepresentableByAlgebraicSpaces_toTerminalCFG B S hS 𝒳₂ h𝒳₂) h𝒳₁

end AlgebraicGeometry.Stack

end
