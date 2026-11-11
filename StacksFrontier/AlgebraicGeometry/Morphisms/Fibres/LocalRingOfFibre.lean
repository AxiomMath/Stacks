module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The local ring of a fibre

Let `f : X ⟶ S` be a morphism of schemes, `x ∈ X` and `s = f x`. Viewing `x` as the point
`AlgebraicGeometry.Scheme.Hom.asFiber f x` of the scheme-theoretic fibre `X_s`, the local ring
of the fibre at `x` is

```
𝒪_{X_s,x}  ≅  𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}  ≅  𝒪_{X,x} ⊗[𝒪_{S,s}] κ(s),
```

both isomorphisms being compatible with the canonical maps out of `𝒪_{X,x}`.

## Main definitions

* `AlgebraicGeometry.tensorResidueFieldEquivFiberStalk`: the isomorphism
  `𝒪_{X,x} ⊗[𝒪_{S,s}] κ(s) ≃+* 𝒪_{X_s,x}`.

## Main results

* `AlgebraicGeometry.quotientStalkEquivFiberStalk` (from
  `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk`) is the first isomorphism
  `𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x} ≃+* 𝒪_{X_s,x}`, with
  `AlgebraicGeometry.quotientStalkEquivFiberStalk_mk` saying it is induced by the stalk map of
  the inclusion of the fibre; it is registered here for Tag 0HA1.
* `AlgebraicGeometry.tensorResidueFieldEquivFiberStalk_tmul`: the second isomorphism sends
  `b ⊗ residue a` to the image of `b · f^♯(a)` under the stalk map of the inclusion of the fibre.

## Implementation notes

The residue field `κ(s)` is `IsLocalRing.ResidueField 𝒪_{S,s}`, which is
`AlgebraicGeometry.Scheme.residueField S s` by definition; it carries its `𝒪_{S,s}`-algebra
structure. The second isomorphism is the first composed with Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, the algebraic Remark 0H9M.

## References

* [Stacks Project, Tag 0HA1](https://stacks.math.columbia.edu/tag/0HA1)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

add_to_stacks 0HA1 "first isomorphism `𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x} ≅ 𝒪_{X_s,x}`, with `x` viewed as the
point `f.asFiber x` of the fibre; it is induced by the stalk map of the inclusion of the fibre
(`AlgebraicGeometry.quotientStalkEquivFiberStalk_mk`)"
  AlgebraicGeometry.quotientStalkEquivFiberStalk

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **The local ring of a fibre is a base change of the local ring.** Let `f : X ⟶ S` be a
morphism of schemes and `x ∈ X` with image `s = f x`. With `x` viewed as the point
`f.asFiber x` of the scheme-theoretic fibre `X_s`, and `𝒪_{X,x}` an `𝒪_{S,s}`-algebra through
the stalk map of `f`, this is the ring isomorphism `𝒪_{X,x} ⊗[𝒪_{S,s}] κ(s) ≅ 𝒪_{X_s,x}`, the
composite of `𝒪_{X,x} ⊗[𝒪_{S,s}] κ(s) ≅ 𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}` with
`AlgebraicGeometry.quotientStalkEquivFiberStalk`. -/
@[stacks 0HA1 "second isomorphism `𝒪_{X,x} ⊗_{𝒪_{S,s}} κ(s) ≅ 𝒪_{X_s,x}`, with `x` viewed as the
point `f.asFiber x` of the fibre; compatibility with the canonical maps is
`AlgebraicGeometry.tensorResidueFieldEquivFiberStalk_tmul`. The first isomorphism is
`AlgebraicGeometry.quotientStalkEquivFiberStalk`"]
noncomputable def tensorResidueFieldEquivFiberStalk :
    letI := (f.stalkMap x).hom.toAlgebra
    (X.presheaf.stalk x) ⊗[S.presheaf.stalk (f x)]
        IsLocalRing.ResidueField (S.presheaf.stalk (f x)) ≃+*
      (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
  letI := (f.stalkMap x).hom.toAlgebra
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).toRingEquiv.symm.trans
    (quotientStalkEquivFiberStalk f x)

/-- **The isomorphism `𝒪_{X,x} ⊗[𝒪_{S,s}] κ(s) ≅ 𝒪_{X_s,x}` is induced by the canonical maps**:
it sends `b ⊗ residue a` to the image of `b · f^♯(a)` under the stalk map of the inclusion of
the fibre `X_s ⟶ X` at `x`. -/
theorem tensorResidueFieldEquivFiberStalk_tmul (b : X.presheaf.stalk x)
    (a : S.presheaf.stalk (f x)) :
    letI := (f.stalkMap x).hom.toAlgebra
    tensorResidueFieldEquivFiberStalk f x (b ⊗ₜ IsLocalRing.residue _ a) =
      ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom
          (b * (f.stalkMap x).hom a)) := by
  let := (f.stalkMap x).hom.toAlgebra
  let m := IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))
  have h : b ⊗ₜ[S.presheaf.stalk (f x)] IsLocalRing.residue _ a =
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x) m
        (Ideal.Quotient.mk _ (b * (f.stalkMap x).hom a)) := by
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    have h1 : (IsLocalRing.residue _ a : IsLocalRing.ResidueField (S.presheaf.stalk (f x))) =
        a • (1 : IsLocalRing.ResidueField (S.presheaf.stalk (f x))) :=
      Algebra.algebraMap_eq_smul_one a
    rw [h1, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    rfl
  rw [h]
  change quotientStalkEquivFiberStalk f x
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x) m).symm
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk x) m
          (Ideal.Quotient.mk _ (b * (f.stalkMap x).hom a)))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact quotientStalkEquivFiberStalk_mk f x _

end AlgebraicGeometry
