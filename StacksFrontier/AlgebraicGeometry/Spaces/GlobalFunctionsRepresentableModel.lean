module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# A `u`-model of the global functions of an affine algebraic space

An affine algebraic space `X` over `S` is isomorphic to the presheaf represented by an object `T`
of the big fppf site of `S` with affine underlying scheme, and
`AlgebraicGeometry.Space.globalFunctionsYonedaEquiv` identifies the global functions of that
representable presheaf with the ring `Γ(T, 𝒪_T)` of regular functions of the representing scheme.
Composing with the pullback of global functions along the isomorphism gives a `u`-model of the
global functions of `X` itself, namely `Γ(T, 𝒪_T)`.

## Main definitions

* `AlgebraicGeometry.Space.isoOfPresheafIso`: an isomorphism of the underlying presheaves of two
  algebraic spaces, as an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.globalFunctionsRingEquivOfIso`: pullback of global functions along an
  isomorphism of presheaves, as a ring isomorphism.
* `AlgebraicGeometry.Space.globalFunctionsAffineEquiv`: the resulting identification of the global
  functions of a presheaf isomorphic to `yoneda.obj T` with `Γ(T, 𝒪_T)`.

## Implementation notes

Pullback of global functions is functorial — `AlgebraicGeometry.Space.globalFunctionsMap_id` and
`AlgebraicGeometry.Space.globalFunctionsMap_comp` — so the pullbacks along the two directions of an
isomorphism are mutually inverse ring homomorphisms. The isomorphism is lifted to the category of
algebraic spaces over `S`, where `globalFunctionsMap` is defined, by
`CategoryTheory.ObjectProperty.homMk` in both directions.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of the underlying presheaves of two algebraic spaces over `S`, as an
isomorphism in the category of algebraic spaces over `S`. -/
def isoOfPresheafIso {U V : AlgebraicSpaces B S hS} (e : U.obj ≅ V.obj) : U ≅ V where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := ObjectProperty.hom_ext _ e.hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ e.inv_hom_id

/-- Pullback of global functions along an isomorphism of the underlying presheaves, as a ring
isomorphism. -/
def globalFunctionsRingEquivOfIso {U V : AlgebraicSpaces B S hS} (e : U.obj ≅ V.obj) :
    globalFunctions B S hS V.obj ≃+* globalFunctions B S hS U.obj :=
  RingEquiv.ofBijective (globalFunctionsMap B S hS (isoOfPresheafIso B S hS e).hom)
    (Function.bijective_iff_has_inverse.mpr
      ⟨globalFunctionsMap B S hS (isoOfPresheafIso B S hS e).inv,
        fun x => by
          have h : (globalFunctionsMap B S hS (isoOfPresheafIso B S hS e).inv).comp
              (globalFunctionsMap B S hS (isoOfPresheafIso B S hS e).hom) = RingHom.id _ := by
            rw [← globalFunctionsMap_comp, (isoOfPresheafIso B S hS e).inv_hom_id,
              globalFunctionsMap_id]
          simpa using DFunLike.congr_fun h x,
        fun x => by
          have h : (globalFunctionsMap B S hS (isoOfPresheafIso B S hS e).hom).comp
              (globalFunctionsMap B S hS (isoOfPresheafIso B S hS e).inv) = RingHom.id _ := by
            rw [← globalFunctionsMap_comp, (isoOfPresheafIso B S hS e).hom_inv_id,
              globalFunctionsMap_id]
          simpa using DFunLike.congr_fun h x⟩)

/-- The global functions of an algebraic space `X` with an isomorphism `X ≅ yoneda.obj T` are
identified with the regular functions `Γ(T, 𝒪_T)` of the representing scheme. -/
def globalFunctionsAffineEquiv (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (e : X.obj ≅ yoneda.obj T) :
    globalFunctions B S hS X.obj ≃+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  (globalFunctionsRingEquivOfIso B S hS
      (U := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (V := X) e.symm).trans
    (globalFunctionsYonedaEquiv B S hS T)

end AlgebraicGeometry.Space

end
