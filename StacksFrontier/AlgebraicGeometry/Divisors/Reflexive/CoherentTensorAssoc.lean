module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentTensor

/-!
# Associativity of the tensor product of coherent reflexive modules

Let `X` be an integral locally Noetherian scheme and `𝒞` the category of coherent reflexive
`𝒪_X`-modules, with its hull tensor product `ℱ ⊗_𝒞 𝒢 = (ℱ ⊗_{𝒪_X} 𝒢)^∨∨`.  Associativity does
not follow from associativity of `⊗_{𝒪_X}` alone, because the hull is taken at every
parenthesis.  What makes it work is that the hull may be *deferred*: for a coherent module `𝒯`
and a coherent reflexive `𝒦` the canonical comparison

`(𝒯 ⊗_{𝒪_X} 𝒦)^∨∨ ⟶ (𝒯^∨∨ ⊗_{𝒪_X} 𝒦)^∨∨`

is an isomorphism.  Both sides corepresent `ℋ ↦ Hom(𝒯, ℋom_{𝒪_X}(𝒦, ℋ))` — through
[Stacks, Tag 01CN] and the reflexive-hull adjunction — so the comparison is an isomorphism by
Yoneda.

## Main definitions

* `tensorCoh T K`: the ordinary tensor product of a coherent module with a coherent reflexive
  one, as a coherent module.
* `hullTensorUnit T K`: the comparison `𝒯 ⊗ 𝒦 ⟶ 𝒯^∨∨ ⊗ 𝒦`.
* `hullHomEquiv S H`, `hullTensorHomEquiv T K H`, `hullUnitHomEquiv T I`: the three bijections
  the Yoneda argument is assembled from.
* `tensorObjAssoc F G K`: the associativity isomorphism of `⊗_𝒞`.

## Main results

* `isIso_hullReflection_map_hullTensorUnit`: deferring the hull is an isomorphism.
* `tensorObjAssoc`: **Stacks, Tag 0EBH's associativity.**

## Implementation notes

The associativity isomorphism is assembled from the ordinary associativity constraint
`Stacks.SheafOfModules.tensorSheafAssociator` and the braiding
`Stacks.SheafOfModules.Invertible.tensorProductBraiding`; the braiding appears because
`isIso_hullReflection_map_hullTensorUnit` defers the hull in the *left* factor only, so the
right-hand parenthesization is turned around before the hull is deferred there.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive reflexiveHull toDoubleDual
  reflexiveHullFunctor toDoubleDual_naturality)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.CoherentReflexive

attribute [local implicit_reducible] Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The ordinary tensor product of a coherent module with a coherent reflexive one, as a
coherent module. -/
noncomputable abbrev tensorCoh (T : CoherentModules X) (K : CoherentReflexiveModules X) :
    CoherentModules X :=
  ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (T.obj)).obj (K.obj.obj)),
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace T.obj K.obj.obj
      T.property K.obj.property⟩

/-- Morphisms from the reflexive hull of a coherent module into a coherent reflexive module are
morphisms of the underlying `𝒪_X`-modules out of the coherent module itself. -/
noncomputable def hullHomEquiv (S : CoherentModules X) (H : CoherentReflexiveModules X) :
    ((hullReflection X).obj S ⟶ H) ≃ (S.obj ⟶ H.obj.obj) :=
  ((hullReflectionAdjunction X).homEquiv S H).trans (homEquivCoh S H)

/-- The bijection of `hullHomEquiv` is precomposition with the canonical map to the double
dual. -/
theorem hullHomEquiv_apply (S : CoherentModules X) (H : CoherentReflexiveModules X)
    (ψ : (hullReflection X).obj S ⟶ H) :
    hullHomEquiv S H ψ = toDoubleDual S.obj ≫ ψ.hom.hom :=
  hullReflectionAdjunction_homEquiv_apply X S H ψ

/-- Morphisms between coherent reflexive modules are morphisms between their images in the
coherent modules. -/
noncomputable def homEquivι (A B : CoherentReflexiveModules X) :
    ((inclusion X).obj A ⟶ (inclusion X).obj B) ≃ (A ⟶ B) where
  toFun f := ObjectProperty.homMk f
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl

/-- Precomposing with the canonical map `𝒯 ⟶ 𝒯^∨∨` identifies the morphisms out of the hull of
`𝒯^∨∨` with those out of the hull of `𝒯`. -/
noncomputable def hullUnitHomEquiv (T : CoherentModules X) (I : CoherentReflexiveModules X) :
    ((hullReflection X).obj ((hullReflection X).obj T).obj ⟶ I) ≃
      ((hullReflection X).obj T ⟶ I) :=
  ((hullReflectionAdjunction X).homEquiv ((hullReflection X).obj T).obj I).trans
    (homEquivι ((hullReflection X).obj T) I)

/-- The underlying morphism of `hullUnitHomEquiv` is precomposition with the canonical map to
the double dual. -/
theorem hullUnitHomEquiv_hom_hom (T : CoherentModules X) (I : CoherentReflexiveModules X)
    (χ : (hullReflection X).obj ((hullReflection X).obj T).obj ⟶ I) :
    (hullUnitHomEquiv T I χ).hom.hom =
      toDoubleDual ((hullReflection X).obj T).obj.obj ≫ χ.hom.hom :=
  hullReflectionAdjunction_homEquiv_apply X ((hullReflection X).obj T).obj I χ

/-- The two hull hom bijections are related by the canonical map to the double dual. -/
theorem hullHomEquiv_hullUnitHomEquiv (T : CoherentModules X) (I : CoherentReflexiveModules X)
    (χ : (hullReflection X).obj ((hullReflection X).obj T).obj ⟶ I) :
    hullHomEquiv T I (hullUnitHomEquiv T I χ) =
      toDoubleDual T.obj ≫ hullHomEquiv ((hullReflection X).obj T).obj I χ :=
  (hullHomEquiv_apply T I _).trans (congrArg (fun z => toDoubleDual T.obj ≫ z)
    ((hullUnitHomEquiv_hom_hom T I χ).trans
      (hullHomEquiv_apply ((hullReflection X).obj T).obj I χ).symm))

/-- The hull-tensor hom bijection: morphisms out of `(𝒯 ⊗ 𝒦)^∨∨` are morphisms out of `𝒯^∨∨`
into the internal Hom from `𝒦`. -/
noncomputable def hullTensorHomEquiv (T : CoherentModules X)
    (K H : CoherentReflexiveModules X) :
    ((hullReflection X).obj (tensorCoh T K) ⟶ H) ≃
      ((hullReflection X).obj T ⟶ internalHomObj K H) :=
  (hullHomEquiv (tensorCoh T K) H).trans
    ((Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace T.obj K.obj.obj H.obj.obj).trans
      (hullHomEquiv T (internalHomObj K H)).symm)

/-- The comparison `𝒯 ⊗ 𝒦 ⟶ 𝒯^∨∨ ⊗ 𝒦`, the canonical map to the double dual tensored with the
identity. -/
noncomputable def hullTensorUnit (T : CoherentModules X) (K : CoherentReflexiveModules X) :
    tensorCoh T K ⟶ tensorCoh ((hullReflection X).obj T).obj K :=
  ObjectProperty.homMk
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map (X := (T.obj, K.obj.obj))
        (Y := (((hullReflection X).obj T).obj.obj, K.obj.obj))
        ((toDoubleDual T.obj, 𝟙 K.obj.obj) : (T.obj, K.obj.obj) ⟶
        (((hullReflection X).obj T).obj.obj, K.obj.obj))))

/-- Deferring the hull: the hull hom bijection of `𝒯 ⊗ 𝒦` composed with the comparison is the
hull hom bijection of `𝒯^∨∨ ⊗ 𝒦` followed by tensoring the canonical map with the identity. -/
theorem hullHomEquiv_hullReflection_map_hullTensorUnit (T : CoherentModules X)
    (K H : CoherentReflexiveModules X)
    (φ : (hullReflection X).obj (tensorCoh ((hullReflection X).obj T).obj K) ⟶ H) :
    hullHomEquiv (tensorCoh T K) H ((hullReflection X).map (X := tensorCoh T K)
        (Y := tensorCoh ((hullReflection X).obj T).obj K) (hullTensorUnit T K) ≫ φ) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩)).map
          (X := (T.obj, K.obj.obj)) (Y := (((hullReflection X).obj T).obj.obj, K.obj.obj))
          ((toDoubleDual T.obj, 𝟙 K.obj.obj) : (T.obj, K.obj.obj) ⟶
          (((hullReflection X).obj T).obj.obj, K.obj.obj))) ≫
        hullHomEquiv (tensorCoh ((hullReflection X).obj T).obj K) H φ :=
  congrArg (fun morphism : tensorCoh T K ⟶ (inclusion X).obj H => morphism.hom)
    ((hullReflectionAdjunction X).homEquiv_naturality_left (hullTensorUnit T K) φ)

/-- The hull hom bijection of a hull-tensor hom equals the tensor hom bijection of the hull hom
bijection. -/
private theorem hullHomEquiv_hullTensorHomEquiv (T : CoherentModules X)
    (K H : CoherentReflexiveModules X) (φ : (hullReflection X).obj (tensorCoh T K) ⟶ H) :
    hullHomEquiv T (internalHomObj K H) (hullTensorHomEquiv T K H φ) =
      Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace T.obj K.obj.obj H.obj.obj
        (hullHomEquiv (tensorCoh T K) H φ) :=
  (hullHomEquiv T (internalHomObj K H)).apply_symm_apply _

/-- Deferring the hull commutes with the hull-tensor hom bijections. -/
theorem hullTensorHomEquiv_hullReflection_map_hullTensorUnit (T : CoherentModules X)
    (K H : CoherentReflexiveModules X)
    (φ : (hullReflection X).obj (tensorCoh ((hullReflection X).obj T).obj K) ⟶ H) :
    hullTensorHomEquiv T K H ((hullReflection X).map (X := tensorCoh T K)
        (Y := tensorCoh ((hullReflection X).obj T).obj K) (hullTensorUnit T K) ≫ φ) =
      hullUnitHomEquiv T (internalHomObj K H)
        (hullTensorHomEquiv ((hullReflection X).obj T).obj K H φ) :=
  (hullHomEquiv T (internalHomObj K H)).injective
    ((hullHomEquiv_hullTensorHomEquiv T K H _).trans
      (((congrArg (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace T.obj K.obj.obj H.obj.obj)
          (hullHomEquiv_hullReflection_map_hullTensorUnit T K H φ)).trans
        (tensorSheafHomEquiv_natural_left X.toRingedSpace (toDoubleDual T.obj)
          (hullHomEquiv (tensorCoh ((hullReflection X).obj T).obj K) H φ))).trans
        ((congrArg (fun z => toDoubleDual T.obj ≫ z)
          (hullHomEquiv_hullTensorHomEquiv ((hullReflection X).obj T).obj K H φ).symm).trans
          (hullHomEquiv_hullUnitHomEquiv T (internalHomObj K H)
            (hullTensorHomEquiv ((hullReflection X).obj T).obj K H φ)).symm)))

/-- **Deferring the hull is an isomorphism.**  For a coherent module `𝒯` and a coherent
reflexive `𝒦`, the comparison `(𝒯 ⊗ 𝒦)^∨∨ ⟶ (𝒯^∨∨ ⊗ 𝒦)^∨∨` is an isomorphism.

Both sides corepresent `ℋ ↦ Hom_{𝒪_X}(𝒯, ℋom_{𝒪_X}(𝒦, ℋ))`, by the hull adjunction and
[Stacks, Tag 01CN], and precomposition with the comparison realizes that identification; the
conclusion is Yoneda. -/
theorem isIso_hullReflection_map_hullTensorUnit (T : CoherentModules X)
    (K : CoherentReflexiveModules X) :
    IsIso ((hullReflection X).map (X := tensorCoh T K)
      (Y := tensorCoh ((hullReflection X).obj T).obj K) (hullTensorUnit T K)) := by
  rw [CategoryTheory.isIso_iff_coyoneda_map_bijective]
  intro H
  have key : (fun φ => (hullReflection X).map (X := tensorCoh T K)
      (Y := tensorCoh ((hullReflection X).obj T).obj K) (hullTensorUnit T K) ≫ φ) =
      fun φ => (hullTensorHomEquiv T K H).symm (hullUnitHomEquiv T (internalHomObj K H)
        (hullTensorHomEquiv ((hullReflection X).obj T).obj K H φ)) := by
    funext φ
    exact ((hullTensorHomEquiv T K H).eq_symm_apply).2
      (hullTensorHomEquiv_hullReflection_map_hullTensorUnit T K H φ)
  rw [key]
  exact ((hullTensorHomEquiv ((hullReflection X).obj T).obj K H).trans
    ((hullUnitHomEquiv T (internalHomObj K H)).trans
      (hullTensorHomEquiv T K H).symm)).bijective

/-- **Stacks Project, Tag 0EBH.**  The tensor product of the category of coherent reflexive
modules is associative. -/
@[stacks 0EBH "associativity"]
noncomputable def tensorObjAssoc (F G K : CoherentReflexiveModules X) :
    tensorObj (tensorObj F G) K ≅ tensorObj F (tensorObj G K) := by
  haveI := isIso_hullReflection_map_hullTensorUnit (ordinaryTensor F G) K
  haveI := isIso_hullReflection_map_hullTensorUnit (ordinaryTensor G K) F
  have eAssoc :
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
          (G.obj.obj))))).obj (K.obj.obj)) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
            (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G.obj.obj)).obj
            (K.obj.obj))))) :=
    Stacks.SheafOfModules.tensorSheafAssociator X.presheaf X.ringCatSheaf.2 F.obj.obj G.obj.obj
      K.obj.obj
  have eComm :
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G.obj.obj)).obj
          (K.obj.obj))))) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G.obj.obj)).obj
            (K.obj.obj))))).obj (F.obj.obj)) :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
      F.obj.obj (ordinaryTensor G K).obj
  have eRight :
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
          ((reflexiveHull ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G.obj.obj)).obj
          (K.obj.obj)))))) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((reflexiveHull ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G.obj.obj)).obj
            (K.obj.obj)))))).obj (F.obj.obj)) :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
      F.obj.obj (reflexiveHull (ordinaryTensor G K).obj)
  have e3 : (tensorCoh (ordinaryTensor F G) K ≅ tensorCoh (ordinaryTensor G K) F) :=
    ObjectProperty.isoMk _ (eAssoc ≪≫ eComm)
  have e4 : (ordinaryTensor F (tensorObj G K) ≅
      tensorCoh ((hullReflection X).obj (ordinaryTensor G K)).obj F) :=
    ObjectProperty.isoMk _ eRight
  exact (asIso ((hullReflection X).map
    (X := tensorCoh (ordinaryTensor F G) K)
    (Y := tensorCoh ((hullReflection X).obj (ordinaryTensor F G)).obj K)
    (hullTensorUnit (ordinaryTensor F G) K))).symm ≪≫
    (hullReflection X).mapIso
      (X := tensorCoh (ordinaryTensor F G) K) (Y := tensorCoh (ordinaryTensor G K) F) e3 ≪≫
    asIso ((hullReflection X).map
      (X := tensorCoh (ordinaryTensor G K) F)
      (Y := tensorCoh ((hullReflection X).obj (ordinaryTensor G K)).obj F)
      (hullTensorUnit (ordinaryTensor G K) F)) ≪≫
    ((hullReflection X).mapIso (X := ordinaryTensor F (tensorObj G K))
      (Y := tensorCoh ((hullReflection X).obj (ordinaryTensor G K)).obj F) e4).symm

end AlgebraicGeometry.CoherentReflexive

end
