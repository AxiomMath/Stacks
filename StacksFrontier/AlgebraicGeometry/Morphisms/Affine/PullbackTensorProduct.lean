module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The affine base change `Γ(V ×_Y X) = Γ(V) ⊗_{Γ(Y)} Γ(X)`

Let
```
U --snd--> X
|fst       |q
V --b-->   Y
```
be a cartesian square of schemes whose three corners `X`, `V` and `Y` are affine. Then `U` is
affine too, and this file identifies its ring of global sections with the tensor product:

`Γ(U, 𝒪_U) = Γ(V, 𝒪_V) ⊗_{Γ(Y, 𝒪_Y)} Γ(X, 𝒪_X)`,

the two algebra structures on the right being the ones `b` and `q` induce on global sections, and
the identification carrying `o ⊗ x` to the product of the restrictions of `o` and `x` along the
two projections.

## Main results

* `AlgebraicGeometry.tensorProductΓEquivOfIsPullback`: the identification, as a ring
  isomorphism, together with `AlgebraicGeometry.tensorProductΓEquivOfIsPullback_tmul`,
  `AlgebraicGeometry.tensorProductΓEquivOfIsPullback_tmul_one` and
  `AlgebraicGeometry.tensorProductΓEquivOfIsPullback_one_tmul` describing it on pure tensors.
* `AlgebraicGeometry.isPullback_specTensorProduct`: the same identification read as a
  cartesian square, namely that `Spec(Γ(V) ⊗_{Γ(Y)} Γ(X))` together with the two inclusions is a
  fibre product of `V` and `X` over `Y`.
* `AlgebraicGeometry.specTensorProductIsoPullback`: the induced isomorphism
  `Spec(Γ(V) ⊗_{Γ(Y)} Γ(X)) ≅ V ×_Y X`.

## Implementation notes

The whole content is the comparison of two pushout squares of rings. Mathlib's
`AlgebraicGeometry.isPushout_appTop_of_isPullback` says that the square of global sections of a
cartesian square of schemes with three affine corners is a pushout in `CommRingCat`, and
`CommRingCat.isPushout_tensorProduct` says the same of the tensor product; the uniqueness of a
pushout, `CategoryTheory.IsPushout.isoIsPushout`, gives the isomorphism, and its two
compatibilities with the inclusions give the formulas on pure tensors.

Statements are about an arbitrary cartesian square rather than about
`CategoryTheory.Limits.pullback`, so that a consumer which has built its fibre product in some
other way — as the spectrum of a ring, or by shrinking a larger one — can use them without first
transporting along an isomorphism; `AlgebraicGeometry.specTensorProductIsoPullback` is the
instance for Mathlib's own fibre product.

The three affineness hypotheses are on `X`, `V` and `Y`; affineness of `U` is a consequence, by
`AlgebraicGeometry.IsAffine.of_isPullback`, and is not assumed.

`AlgebraicGeometry.affinePullbackΓTensorEquiv` is the case `U = V ×_Y X` of Mathlib's own fibre
product, in the opposite direction.

No Stacks tag is claimed: the identification of the ring of a fibre product of affine schemes
with a tensor product is part of the construction of fibre products of schemes, which the source
performs in Tag 01JO without stating this consequence separately.

## References

* [Stacks Project, Tag 01JO](https://stacks.math.columbia.edu/tag/01JO)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {U X V Y : Scheme.{u}} {fst : U ⟶ V} {snd : U ⟶ X} {b : V ⟶ Y} {q : X ⟶ Y}

section

variable [IsAffine X] [IsAffine V] [IsAffine Y]

/-- **The affine base change on global sections.** For a cartesian square
`fst ≫ b = snd ≫ q` of schemes with `X`, `V` and `Y` affine, the ring of global sections of the
fibre product `U` is the tensor product `Γ(V, 𝒪_V) ⊗_{Γ(Y, 𝒪_Y)} Γ(X, 𝒪_X)`. -/
def tensorProductΓEquivOfIsPullback (h : IsPullback fst snd b q) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    (Γ(V, ⊤) ⊗[Γ(Y, ⊤)] Γ(X, ⊤)) ≃+* Γ(U, ⊤) :=
  letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  ((CommRingCat.isPushout_tensorProduct Γ(Y, ⊤) Γ(V, ⊤) Γ(X, ⊤)).isoIsPushout _ _
    (isPushout_appTop_of_isPullback h)).commRingCatIsoToRingEquiv

/-- The identification of `AlgebraicGeometry.tensorProductΓEquivOfIsPullback` carries
`o ⊗ 1` to the restriction of `o` along the projection to `V`. -/
theorem tensorProductΓEquivOfIsPullback_tmul_one (h : IsPullback fst snd b q)
    (o : Γ(V, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    tensorProductΓEquivOfIsPullback h (o ⊗ₜ[Γ(Y, ⊤)] 1) = fst.appTop.hom o := by
  let _ : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom
    ((CommRingCat.isPushout_tensorProduct Γ(Y, ⊤) Γ(V, ⊤) Γ(X, ⊤)).inl_isoIsPushout_hom _ _
      (isPushout_appTop_of_isPullback h))) o

/-- The identification of `AlgebraicGeometry.tensorProductΓEquivOfIsPullback` carries
`1 ⊗ x` to the restriction of `x` along the projection to `X`. -/
theorem tensorProductΓEquivOfIsPullback_one_tmul (h : IsPullback fst snd b q)
    (x : Γ(X, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    tensorProductΓEquivOfIsPullback h (1 ⊗ₜ[Γ(Y, ⊤)] x) = snd.appTop.hom x := by
  let _ : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom
    ((CommRingCat.isPushout_tensorProduct Γ(Y, ⊤) Γ(V, ⊤) Γ(X, ⊤)).inr_isoIsPushout_hom _ _
      (isPushout_appTop_of_isPullback h))) x

/-- The identification of `AlgebraicGeometry.tensorProductΓEquivOfIsPullback` carries a
pure tensor `o ⊗ x` to the product of the restrictions of `o` and `x` along the two
projections. -/
theorem tensorProductΓEquivOfIsPullback_tmul (h : IsPullback fst snd b q)
    (o : Γ(V, ⊤)) (x : Γ(X, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    tensorProductΓEquivOfIsPullback h (o ⊗ₜ[Γ(Y, ⊤)] x) =
      fst.appTop.hom o * snd.appTop.hom x := by
  let _ : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  rw [show o ⊗ₜ[Γ(Y, ⊤)] x = (o ⊗ₜ[Γ(Y, ⊤)] (1 : Γ(X, ⊤))) * (1 ⊗ₜ[Γ(Y, ⊤)] x) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul,
    tensorProductΓEquivOfIsPullback_tmul_one, tensorProductΓEquivOfIsPullback_one_tmul]

end

/-! ### The fibre product as the spectrum of a tensor product -/

section Spec

variable [IsAffine X] [IsAffine V] [IsAffine Y]

/-- **The spectrum of `Γ(V) ⊗_{Γ(Y)} Γ(X)` is a fibre product of `V` and `X` over `Y`.** The
two projections are the spectra of the two inclusions of the tensor product, followed by the
identifications of `Spec Γ(V, 𝒪_V)` with `V` and of `Spec Γ(X, 𝒪_X)` with `X`. -/
theorem isPullback_specTensorProduct (b : V ⟶ Y) (q : X ⟶ Y) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom (S := CommRingCat.of (Γ(V, ⊤) ⊗[Γ(Y, ⊤)] Γ(X, ⊤)))
        Algebra.TensorProduct.includeLeftRingHom) ≫ V.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (S := CommRingCat.of (Γ(V, ⊤) ⊗[Γ(Y, ⊤)] Γ(X, ⊤)))
        Algebra.TensorProduct.includeRight.toRingHom) ≫ X.isoSpec.inv) b q := by
  let _ : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  refine (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(Y, ⊤) Γ(V, ⊤) Γ(X, ⊤))).of_iso'
      (Iso.refl _) V.isoSpec X.isoSpec Y.isoSpec (by simp) (by simp) ?_ ?_
  · exact Scheme.isoSpec_hom_naturality b
  · exact Scheme.isoSpec_hom_naturality q

/-- **The fibre product of two affine schemes over an affine scheme is the spectrum of the
tensor product of their rings of global sections.** -/
def specTensorProductIsoPullback (b : V ⟶ Y) (q : X ⟶ Y) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    Spec (CommRingCat.of (Γ(V, ⊤) ⊗[Γ(Y, ⊤)] Γ(X, ⊤))) ≅ pullback b q :=
  letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  (isPullback_specTensorProduct b q).isoPullback

end Spec

end AlgebraicGeometry

end
