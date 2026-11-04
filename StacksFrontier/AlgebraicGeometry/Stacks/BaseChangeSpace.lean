module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The algebraic space representing a base change, and its structure morphism (Stacks 0402)

Let `S` be a scheme contained in a big fppf site and let `f : 𝒳 ⥤ᵇ 𝒴` be a 1-morphism of
categories over `(Sch/S)_fppf` representable by algebraic spaces (Stacks 02ZW). For a scheme `U`
over `S` and a point `y : (Sch/U)_fppf ⟶ 𝒴`, the display of **Stacks 0402** names the algebraic
space `F_y` over `U` representing the 2-fibre product `(Sch/U)_fppf ×_{y, 𝒴} 𝒳`, together with
its structure morphism `f_y : F_y ⟶ U`:

```
F_y  ⤳  (Sch/U)_fppf ×_{y, 𝒴} 𝒳  ⟶  𝒳
 ↓ f_y         ↓ pr₀                 ↓ f
 U   ⤳     (Sch/U)_fppf        ⟶y    𝒴
```

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeSpace`: **Stacks 0402**, the algebraic space `F_y`.
* `AlgebraicGeometry.Stack.baseChangeSpaceOverBase`: `F_y` read as an algebraic space over `S`
  with a morphism to the representable algebraic space of `U`.
* `AlgebraicGeometry.Stack.baseChangeStructureMap`: **Stacks 0402**, the morphism `f_y`.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_baseChangeSpace`: **Stacks 0402**, the
  squiggly arrow — `F_y` does represent the 2-fibre product, i.e. its category of elements is
  equivalent over `(Sch/U)_fppf` to the first projection of the 2-fibre product.
* `AlgebraicGeometry.Stack.prop_baseChangeStructureMap`: a 1-morphism with the relative property
  `P` of Stacks 03YK has `P` for the structure morphism `f_y` of this particular representative.

## Implementation notes

Representability by algebraic spaces is by definition the *existence*, for each `(U, y)`, of such
an `F` together with such an equivalence, so the content of Stacks 0402 is not an existence
statement — it is the naming of a choice. The declarations here make that choice once and for
all with `Exists.choose`, so that a consumer can speak of `F_y` and `f_y` as objects rather than
having to destructure a witness at every use; this is why they are noncomputable. Nothing depends
on *which* representative is chosen: any two are equivalent over the site, and the conditions of
Stacks 03YK quantify over all of them, which is what
`AlgebraicGeometry.Stack.prop_baseChangeStructureMap` exploits.

The right-hand square of the display, with its projections `pr₀`, `pr₁` and its 2-cell, is not
re-expressed here: it is the canonical 2-fibre product
`CategoryTheory.TwoFibreProductOver` with its defining `fst`, `snd` and comparison isomorphism,
which the library already has, and the equivalence above is stated against
`CategoryTheory.TwoFibreProductOver.fst` directly.

Passing from an algebraic space over `U` to one over `S` with a morphism to `U` is the forward
functor `AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG, and the structure
morphism is read off it by `AlgebraicGeometry.algebraicSpaceMap`. That this reading is the
expected one on sections — a section of the lower-shriek extension indexed by a factorization
`ψ : T ⟶ U` is sent to `ψ` — is
`AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app`, already in the
library, so it is not restated.

`𝒳` and `𝒴` are arbitrary categories over the site with independent universes rather than
bundled categories fibred in groupoids, matching
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` itself; the display of Stacks 0402 uses
nothing else.

## References

* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0402](https://stacks.math.columbia.edu/tag/0402)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v v₁ v₂ w w₁ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Choice

variable {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
  (f : 𝒳 ⥤ᵇ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f)
  (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
  (hy : y ⋙ 𝒴.p = Over.map U.hom)

/-- **Stacks 0402.** The algebraic space `F_y` over `U` representing the 2-fibre product
`(Sch/U)_fppf ×_{y, 𝒴} 𝒳` of a 1-morphism `f` representable by algebraic spaces along a point
`y` of its target over `U`.

This is a choice of representative; see the implementation notes. -/
@[stacks 0402 "the representing algebraic space F_y"]
noncomputable def baseChangeSpace : AlgebraicSpaces B U.left.1 U.left.2 :=
  ⟨(hf U y hy).choose, (hf U y hy).choose_spec.1⟩

/-- **Stacks 0402, the squiggly arrow.** The category of elements of
`AlgebraicGeometry.Stack.baseChangeSpace` is equivalent, over the big fppf site of `U`, to the
first projection of the 2-fibre product `(Sch/U)_fppf ×_{y, 𝒴} 𝒳`. -/
@[stacks 0402 "F_y represents the 2-fibre product"]
theorem nonempty_equivalenceOver_baseChangeSpace :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor)
      (presheafOfCategories ((baseChangeSpace B S hS f hf U y hy).1 ⋙ typeToCat)).p) :=
  (hf U y hy).choose_spec.2

/-- The algebraic space `F_y` of `AlgebraicGeometry.Stack.baseChangeSpace`, read as an algebraic
space over `S` equipped with a morphism to the representable algebraic space of `U`, through the
forward functor of Stacks 04SG. -/
noncomputable abbrev baseChangeSpaceOverBase :
    SpacesOverSmallerBase B U.left.1 S U.left.2 hS U.hom :=
  (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
    (baseChangeSpace B S hS f hf U y hy)

/-- **Stacks 0402.** The structure morphism `f_y : F_y ⟶ U` of the display, as a morphism of
algebraic spaces over `S` from `AlgebraicGeometry.Stack.baseChangeSpace` to the representable
algebraic space of `U`. -/
@[stacks 0402 "the structure morphism f_y"]
noncomputable abbrev baseChangeStructureMap :
    (⟨(baseChangeSpaceOverBase B S hS f hf U y hy).1.left,
      (baseChangeSpaceOverBase B S hS f hf U y hy).property⟩ : AlgebraicSpaces B S hS) ⟶
      (schemeSpace (Over.mk U.hom) :
        AlgebraicSpaces B S hS) :=
  algebraicSpaceMap B S hS U (baseChangeSpaceOverBase B S hS f hf U y hy)

end Choice

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` with the
relative property `P` of Stacks 03YK has `P` for the structure morphism `f_y` of the
representative `AlgebraicGeometry.Stack.baseChangeSpace` chosen here.

This instantiates the universal quantifier of Stacks 03YK at that representative, which is
legitimate for any choice because the condition quantifies over all of them. -/
theorem prop_baseChangeStructureMap
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty B S hS P f hf)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    P (baseChangeStructureMap B S hS f.hom hf U y hy) :=
  hP U y hy _ (baseChangeSpace B S hS f.hom hf U y hy).property
    (nonempty_equivalenceOver_baseChangeSpace B S hS f.hom hf U y hy)

end AlgebraicGeometry.Stack

end
