module

public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Basic

/-!
# `Č ⁿ(𝒰, f, ℱ) = f_* 𝔠 ⁿ(𝒰, ℱ)` as complexes

The proof of [Stacks, Tag 01XL] asserts an *equality of complexes*

> `Č ⁼(𝒰, f, ℱ) = f_* 𝔠 ⁼(𝒰, ℱ)`

between the relative Čech complex of `f` and the pushforward along `f` of the absolute Čech
resolution of `ℱ`.  That assertion is what lets Leray's acyclicity lemma ([Stacks, Tag 015E]),
which is about the complex `𝔠 ⁼(𝒰, ℱ)` in `X.Modules`, say anything about the complex
`Č ⁼(𝒰, f, ℱ)` in `S.Modules` that the fourth label of [Stacks, Tag 01XL] states its derived
isomorphism for.

**It is an isomorphism, not an equality.** The degree-`n` term is a product over the
`(n + 1)`-tuples of indices, and `f_*` commutes with a product only up to the comparison map
`CategoryTheory.Limits.piComparison`.  Degreewise that comparison is invertible because `f_*`
is a right adjoint; `Stacks.CechPushforward` supplies its compatibility with the alternating
Čech differential.

## Main results

* `relativeCechPresheaf_eq`: the coefficient presheaf of [Stacks, Tag 01XL] *is* the absolute
  coefficient presheaf `A ↦ A.hom_* A.hom ^* ℱ` postcomposed with `f_*`, as an equality of
  functors.
* `absoluteCechComplexCompPushforwardIso`: the canonical isomorphism
  `f_* 𝔠 ⁼(𝒰, ℱ) ≅ Č ⁼(𝒰, f, ℱ)` of `ℕ`-indexed complexes, natural in the quasi-coherent
  module.

## Implementation notes

The absolute coefficient presheaf is spelled with `(relativeMonad X).flip`, not as
`relativeCechPresheaf (𝟙 X)`: the value of the latter at `A` is `(A.hom ≫ 𝟙 X)_* A.hom ^* ℱ`,
whose structure morphism is not syntactically `A.hom`, and crossing that needs a transport
along `Category.comp_id`.  This is the spelling that
`Stacks.RightAcyclicProduct.rightAcyclic_absoluteCechComplex_X` already uses for the acyclicity
of the same complex's terms, so the two line up with no comparison inserted.

`relativeCechPresheaf_eq` crosses the `Functor.flip` layer with
`Stacks.CechPushforward.flip_comp_whiskerings` rather than with a direct `rfl`.  That is not a
stylistic choice: a direct `rfl` for the same statement elaborates and then **fails in the
kernel with a deterministic timeout**, which is the obstruction the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeCech/Basic.lean` record as "an unaffordable `rfl`".
Proving the general `flip`/whiskering identity once, where no scheme data occurs, makes the
instance free.

**What is not here, and why.** The two results below are stated at the two spellings that are
*syntactically* available: the complex isomorphism's target is the Čech complex of
`absoluteCechPresheaf X ⋙ f_*`, and `relativeCechPresheaf_eq` says that functor equals
`relativeCechPresheaf f`.  Composing them — rewriting the target of the isomorphism along that
equality — requires a reassociation of `⋙` underneath `cechComplexFunctor`, and every route
tried for it (`eqToIso` with `congrArg`, with `rw`, with `simp only [Functor.assoc]`, and with
explicit `Functor.assoc` terms) hits the same `whnf` heartbeat ceiling.  So the composite is
left to the consumer, who can take it degreewise where the transport is cheap.

Both complexes are the `ℕ`-indexed ones of `CategoryTheory.cechComplexFunctor`, which is the
indexing the source's `𝔠 ⁼` and `Č ⁼` carry.  The `relativeCechComplex` of
[Stacks, Tag 01XL] is the further image of `Č ⁼(𝒰, f, ℱ)` under
`ComplexShape.embeddingUpNat.extendFunctor` and the `CochainComplex.Plus` lift; pinned Mathlib
proves no commutation of `extendFunctor` with
`CategoryTheory.Functor.mapHomologicalComplex`, so that last transport is not done here either.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.CechPushforwardComplex

open Stacks.AlgebraicGeometry.RelativeCech

variable {X S : Scheme.{u}}

/-- The pushforward of module sheaves along a morphism of schemes preserves products: it is the
right adjoint of the pullback. -/
public instance preservesLimitsOfShape_pushforward (f : X ⟶ S) (J : Type u) :
    PreservesLimitsOfShape (Discrete J) (Scheme.Modules.pushforward f) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.1

/-- The absolute Čech coefficient presheaf `A ↦ A.hom_* A.hom ^* ℱ` on `Over X`, as a functor of
the quasi-coherent module `ℱ`.  This is `𝔠(𝒰, ℱ)` in the notation of [Stacks, Tag 01XL]. -/
public noncomputable abbrev absoluteCechPresheaf (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      ((Over X)ᵒᵖ ⥤ X.Modules) :=
  ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙ (relativeMonad X).flip

/-- **The coefficient presheaf of [Stacks, Tag 01XL] IS `f_*` of the absolute one**, as an
equality of functors.  The value of `relativeCechPresheaf f` at `A : Over X` is `f_*` of
`A.hom_* A.hom ^* ℱ`, and its restriction maps are `f_*` of the canonical restriction maps of the
presheaf of monads, both on the nose. -/
public theorem relativeCechPresheaf_eq (f : X ⟶ S) :
    relativeCechPresheaf f =
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        (relativeMonad X).flip ⋙
          (Functor.whiskeringRight (Over X)ᵒᵖ X.Modules S.Modules).obj
            (Scheme.Modules.pushforward f) :=
  Stacks.CechPushforward.flip_comp_whiskerings (relativeMonad X)
    (Scheme.Modules.pushforward f)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))

/-- **`f_* 𝔠 ⁼(𝒰, ℱ) ≅ Č ⁼(𝒰, f, ℱ)`, the "equality of complexes" of [Stacks, Tag 01XL].**
Applying `f_*` termwise to the absolute Čech complex of the family `Over.mk (T.f i)` gives the
Čech complex of the absolute coefficient presheaf postcomposed with `f_*`, naturally in the
quasi-coherent module; and that presheaf is `relativeCechPresheaf f` by
`relativeCechPresheaf_eq`.

No hypothesis is placed on `f`, on `T` or on the schemes: the content is that `f_*` is additive
and preserves products, which holds for every morphism. -/
public noncomputable def absoluteCechComplexCompPushforwardIso (f : X ⟶ S)
    (T : X.AffineOpenCover) :
    absoluteCechPresheaf X ⋙ CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) ⋙
        (Scheme.Modules.pushforward f).mapHomologicalComplex _ ≅
      absoluteCechPresheaf X ⋙
        (Functor.whiskeringRight (Over X)ᵒᵖ X.Modules S.Modules).obj
            (Scheme.Modules.pushforward f) ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) :=
  Functor.isoWhiskerLeft (absoluteCechPresheaf X)
    (Stacks.CechPushforward.cechComplexFunctorCompMapHomologicalComplexIso
      (Scheme.Modules.pushforward f) (fun i ↦ Over.mk (T.f i)))

end Stacks.AlgebraicGeometry.CechPushforwardComplex

end
