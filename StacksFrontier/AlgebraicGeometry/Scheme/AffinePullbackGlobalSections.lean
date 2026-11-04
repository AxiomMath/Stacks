module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of an affine base change are a tensor product

Let `X` be an affine scheme with a morphism to `Spec R` presented as `Spec` of a ring map
`α : R ⟶ Γ(X, ⊤)`, and let `P` be a fibre product of `X` with `Spec T` over `Spec R` along a ring
map `t : R ⟶ T`. Then `Γ(P, ⊤)` is the pushout of `α` and `t`, hence is identified with the
tensor product `Γ(X, ⊤) ⊗[R] T`.

`AlgebraicGeometry.isPushout_appTop_of_isPullback` says that `Γ` carries the cartesian square to
a cocartesian one; here the two corners `Γ(Spec R, ⊤)` and `Γ(Spec T, ⊤)` are replaced by `R`
and `T` themselves, so that the square is the one whose pushout Mathlib computes as a tensor
product (`CommRingCat.isPushout_tensorProduct`).

## Main results

* `AlgebraicGeometry.isPushout_appTop_of_isPullback_specMap`: **`Γ(P, ⊤)` is the pushout of
  `α` and `t`.**
* `AlgebraicGeometry.tensorAppTopIso`: the resulting identification of `Γ(X, ⊤) ⊗[R] T` with
  `Γ(P, ⊤)`, together with the two lemmas `tensorAppTopIso_includeLeft` and
  `tensorAppTopIso_includeRight` describing it on the two tensor factors.

## Implementation notes

The morphism `X ⟶ Spec R` is taken in the form `X.isoSpec.hom ≫ Spec.map α` rather than as an
arbitrary morphism of affine schemes, because that is the form in which the structure morphisms of
the groupoid schemes of [Stacks Project, Tag 0DT9] are defined, and because it makes `α` — and
hence the algebra structure on `Γ(X, ⊤)` used to form the tensor product — an argument rather
than something recovered from the morphism.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

affine scheme, base change, tensor product, pushout, global sections
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The global sections of an affine base change form a pushout square.** For a cartesian
square whose bottom edge is `Spec` of a ring map `t : R ⟶ T` and whose right edge is `Spec` of a
ring map `α : R ⟶ Γ(X, ⊤)` read through the canonical isomorphism of the affine scheme `X` with
the spectrum of its global functions, the square of rings formed by `α`, `t` and the two maps on
global functions is cocartesian. -/
@[sga "3 V 4.1" "more general"]
theorem isPushout_appTop_of_isPullback_specMap {R T : CommRingCat.{u}} {X P : Scheme.{u}}
    [IsAffine X] (α : R ⟶ Γ(X, ⊤)) (t : R ⟶ T) {b : P ⟶ X} {c : P ⟶ Spec T}
    (h : IsPullback b c (X.isoSpec.hom ≫ Spec.map α) (Spec.map t)) :
    IsPushout α t b.appTop ((Scheme.ΓSpecIso T).inv ≫ c.appTop) := by
  have hspec : ∀ {R' S' : CommRingCat.{u}} (φ : R' ⟶ S'), (Spec.map φ).appTop =
      (Scheme.ΓSpecIso R').hom ≫ φ ≫ (Scheme.ΓSpecIso S').inv := fun φ ↦ by
    simp [Scheme.ΓSpecIso_inv_naturality]
  refine (isPushout_appTop_of_isPullback h).of_iso (Scheme.ΓSpecIso R) (Iso.refl Γ(X, ⊤))
    (Scheme.ΓSpecIso T) (Iso.refl Γ(P, ⊤)) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Scheme.Hom.comp_appTop, hspec α, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_appTop]
    simp
  · rw [hspec t]
    simp
  · simp
  · simp

section Tensor

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] {X P : Scheme.{u}} [IsAffine X]
  [Algebra R Γ(X, ⊤)] {b : P ⟶ X} {c : P ⟶ Spec (CommRingCat.of T)}
  (h : IsPullback b c (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap R T))))

/-- **The identification of `Γ(X, ⊤) ⊗[R] T` with the global sections of the base change.** -/
noncomputable def tensorAppTopIso : CommRingCat.of (Γ(X, ⊤) ⊗[R] T) ≅ Γ(P, ⊤) :=
  (CommRingCat.isPushout_tensorProduct R Γ(X, ⊤) T).isoIsPushout _ _
    (isPushout_appTop_of_isPullback_specMap _ _ h)

/-- On the left tensor factor the identification is pullback of global functions along the
projection to `X`. -/
theorem tensorAppTopIso_includeLeft :
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[R] T) ≫
      (tensorAppTopIso h).hom = b.appTop :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- On the right tensor factor the identification is pullback of global functions along the
projection to `Spec T`. -/
theorem tensorAppTopIso_includeRight :
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : T →+* Γ(X, ⊤) ⊗[R] T) ≫
      (tensorAppTopIso h).hom =
      (Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ c.appTop :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

end Tensor

end AlgebraicGeometry

end
