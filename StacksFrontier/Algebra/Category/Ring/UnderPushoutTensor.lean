module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change in `Under CommRingCat` as a tensor product of algebras

`CategoryTheory.Under.pushout (algebraMap C A)` is base change along `C ⟶ A` on the category of
`C`-algebras, computed as a categorical pushout of ring maps. This file identifies it with the
tensor product `A ⊗[C] B` carrying the algebra structures it is *given* by
`Algebra.TensorProduct`, naturally in `B`.

Mathlib has such an identification, `CommRingCat.tensorProdIsoPushout`, but its tensor product is
formed with the `Algebra ↑C ↑B` structure that `CategoryTheory.Under` manufactures from the
structure map of `B`, namely `RingHom.toAlgebra`. That structure is *not* the same term as a
pre-existing `Algebra C B`, so a statement about `A ⊗[C] B` for a ring `B` that already is a
`C`-algebra cannot be read off it: the two tensor products are different terms, each a quotient of
a free module over its own `Module C B`. The identification here is built from
`CommRingCat.isPushout_tensorProduct`, which speaks of the given algebra structures.

## Main definitions

* `CommRingCat.underTensor`: `A ⊗[C] B` as an `A`-algebra, i.e. as an object of `Under (of A)`.
* `CommRingCat.underAlgHom`: a `C`-algebra map as a morphism of `Under (of C)`.
* `CommRingCat.underTensorMap`: the base change of a `C`-algebra map, as a morphism of
  `Under (of A)`.
* `CommRingCat.underTensorIso`: **the identification of `A ⊗[C] B` with the pushout** of
  `C ⟶ A` and `C ⟶ B`, as objects of `Under (of A)`.

## Main results

* `CommRingCat.isoPushout_naturality`: naturality of the identification on the underlying rings.
* `CommRingCat.underTensorMap_comp_underTensorIso`: the identification is **natural in `B`**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CommRingCat

variable (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
variable {B B' : Type u} [CommRing B] [CommRing B'] [Algebra C B] [Algebra C B']

/-- The tensor product `A ⊗[C] B` as an object of `Under (of A)`, its structure map being the
inclusion of the left factor. -/
abbrev underTensor (B : Type u) [CommRing B] [Algebra C B] : Under (CommRingCat.of A) :=
  Under.mk (ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[C] B))

/-- A `C`-algebra map, as a morphism of `Under (of C)`. -/
def underAlgHom (φ : B →ₐ[C] B') :
    Under.mk (ofHom (algebraMap C B)) ⟶ Under.mk (ofHom (algebraMap C B')) :=
  Under.homMk (ofHom (φ : B →+* B')) (by ext c; exact φ.commutes c)

/-- The underlying ring map of `underAlgHom C φ` is `φ`. -/
@[simp]
theorem underAlgHom_right (φ : B →ₐ[C] B') :
    (underAlgHom C φ).right = ofHom (φ : B →+* B') :=
  rfl

/-- The base change `A ⊗[C] φ` of a `C`-algebra map, as a morphism of `Under (of A)`. -/
def underTensorMap (φ : B →ₐ[C] B') : underTensor C A B ⟶ underTensor C A B' :=
  Under.homMk (ofHom (Algebra.TensorProduct.map (AlgHom.id A A) φ : A ⊗[C] B →+* A ⊗[C] B'))
    (by ext a; simp)

/-- The underlying ring map of `underTensorMap C A φ` is
`Algebra.TensorProduct.map (AlgHom.id A A) φ`. -/
@[simp]
theorem underTensorMap_right (φ : B →ₐ[C] B') :
    (underTensorMap C A φ).right =
      ofHom (Algebra.TensorProduct.map (AlgHom.id A A) φ : A ⊗[C] B →+* A ⊗[C] B') :=
  rfl

/-- **`A ⊗[C] B` is the base change of `B` along `C ⟶ A`.** The tensor product, with the algebra
structures `Algebra.TensorProduct` gives it, is the categorical pushout of `C ⟶ A` and `C ⟶ B`
in `Under (of A)`. -/
noncomputable def underTensorIso (B : Type u) [CommRing B] [Algebra C B] :
    underTensor C A B ≅
      (Under.pushout (ofHom (algebraMap C A))).obj (Under.mk (ofHom (algebraMap C B))) :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct C A B).flip.isoPushout
    (IsPushout.inr_isoPushout_hom _)

/-- **Naturality of the identification, at the level of the underlying rings.** For a `C`-algebra
map `φ : B →ₐ[C] B'`, composing `A ⊗[C] φ` with the isomorphism `A ⊗[C] B' ≅ pushout` equals
composing the isomorphism `A ⊗[C] B ≅ pushout` with the map of pushouts induced by `φ`; `w` is the
compatibility defining that induced map. -/
theorem isoPushout_naturality (φ : B →ₐ[C] B')
    (w : ofHom (algebraMap C B) ≫ ofHom (φ : B →+* B') ≫
        pushout.inl (ofHom (algebraMap C B')) (ofHom (algebraMap C A)) =
      ofHom (algebraMap C A) ≫ pushout.inr (ofHom (algebraMap C B')) (ofHom (algebraMap C A))) :
    ofHom (Algebra.TensorProduct.map (AlgHom.id A A) φ : A ⊗[C] B →+* A ⊗[C] B') ≫
        (CommRingCat.isPushout_tensorProduct C A B').flip.isoPushout.hom =
      (CommRingCat.isPushout_tensorProduct C A B).flip.isoPushout.hom ≫
        pushout.desc (ofHom (φ : B →+* B') ≫
            pushout.inl (ofHom (algebraMap C B')) (ofHom (algebraMap C A)))
          (pushout.inr (ofHom (algebraMap C B')) (ofHom (algebraMap C A))) w := by
  have hl : ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[C] B) ≫
      ofHom (Algebra.TensorProduct.map (AlgHom.id A A) φ : A ⊗[C] B →+* A ⊗[C] B') =
      ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[C] B') := by
    ext a; simp
  have hr : ofHom (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[C] B) ≫
      ofHom (Algebra.TensorProduct.map (AlgHom.id A A) φ : A ⊗[C] B →+* A ⊗[C] B') =
      ofHom (φ : B →+* B') ≫
        ofHom (Algebra.TensorProduct.includeRight.toRingHom : B' →+* A ⊗[C] B') := by
    ext b; simp
  refine (CommRingCat.isPushout_tensorProduct C A B).hom_ext ?_ ?_
  · rw [reassoc_of% hl, IsPushout.inr_isoPushout_hom, IsPushout.inr_isoPushout_hom_assoc,
      pushout.inr_desc]
  · rw [reassoc_of% hr, IsPushout.inl_isoPushout_hom, IsPushout.inl_isoPushout_hom_assoc,
      pushout.inl_desc]

/-- **The identification of the tensor product with the pushout is natural in `B`.** -/
theorem underTensorMap_comp_underTensorIso (φ : B →ₐ[C] B') :
    underTensorMap C A φ ≫ (underTensorIso C A B').hom =
      (underTensorIso C A B).hom ≫
        (Under.pushout (ofHom (algebraMap C A))).map (underAlgHom C φ) :=
  Under.UnderMorphism.ext (isoPushout_naturality C A φ _)

end CommRingCat

end
