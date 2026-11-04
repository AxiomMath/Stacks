module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalizationAlgebraCriterion

/-!
# Direct image reflects isomorphisms between spaces affine over the base

Let `X` be an algebraic space over `S` and let `Y`, `Z` be algebraic spaces affine over `X`.  A
morphism `g : Y ⟶ Z` over `X` whose direct-image map `g_* : Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` is an
isomorphism of `𝒪_X`-algebras is itself an isomorphism.  This is the conservativity of the
functor `Y ↦ Y_* 𝒪_Y` of Stacks 081V, and it is what turns an identification of algebras into an
identification of algebraic spaces over `X`.

It is applied to the factorization `Y ⟶ X' ⟶ X` of a morphism through an algebraic space affine
over `X` whose algebra is the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y`: when `f` is integral
the inclusion `𝒪' ⊂ f_* 𝒪_Y` is an isomorphism, so the factorization is.  That is the content of
Stacks 0825.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_pushforwardAlgebraMap`: a morphism of algebraic
  spaces affine over `X` inducing an isomorphism of direct-image algebras is an isomorphism.
* `AlgebraicGeometry.Space.isIso_of_pushforwardAlgebraMap_eq_integralClosureInclusion`: for an
  integral `f : Y ⟶ X`, a factorization of `f` through an algebraic space `X'` affine over `X`
  whose direct-image map is the inclusion of the integral closure `𝒪' ⊂ f_* 𝒪_Y` is an
  isomorphism over `X`.

## Implementation notes

Both directions of the anti-equivalence are used only through the two halves of it which are
available unconditionally: direct image is faithful on morphisms into a space affine over `X`
(`AlgebraicGeometry.Space.eq_of_pushforwardAlgebraMap_eq`) and, from a source representable over
`X`, full (`AlgebraicGeometry.Space.exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable`).
Fullness produces a candidate inverse from the inverse algebra map, and faithfulness, with the
contravariant functoriality of `f ↦ f_* 𝒪`, makes it two-sided.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0825](https://stacks.math.columbia.edu/tag/0825)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Direct image reflects isomorphisms between algebraic spaces affine over `X`.**  A morphism
`g : Y ⟶ Z` over `X` of algebraic spaces affine over `X` whose direct-image map
`Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` is an isomorphism is an isomorphism over `X`.

Fullness of direct image from the representable `Y` into the affine `Z`, read the other way
round, gives `k : Z ⟶ Y` inducing the inverse algebra map; both composites induce the identity
algebra map, so they are identities by faithfulness. -/
theorem isIso_of_isIso_pushforwardAlgebraMap {X : AlgebraicSpaces B S hS}
    (Y Z : AffineOver B S hS X) (g : Y.obj ⟶ Z.obj)
    [IsIso (pushforwardAlgebraMap B S hS g)] : IsIso g := by
  obtain ⟨k, hk⟩ := exists_pushforwardAlgebraMap_eq_of_relativelyRepresentable B S hS
    (relativelyRepresentable_of_isAffineHom B S hS Z.obj.hom Z.property) Y
    (inv (pushforwardAlgebraMap B S hS g))
  refine ⟨k, ?_, ?_⟩
  · refine eq_of_pushforwardAlgebraMap_eq B S hS Y ?_
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id, hk, IsIso.inv_hom_id]
  · refine eq_of_pushforwardAlgebraMap_eq B S hS Z ?_
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id, hk, IsIso.hom_inv_id]

/-- **A factorization of an integral morphism through its integral closure is an
isomorphism.**  Let `f : Y ⟶ X` be an integral morphism of algebraic spaces over `S`, let `X'`
be an algebraic space affine over `X` and `f' : Y ⟶ X'` a morphism over `X`, and suppose that
`ν_* 𝒪_{X'}` is identified with the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` so that the map
induced by `f'` is the inclusion `𝒪' ⊂ f_* 𝒪_Y`.  Then `f'` is an isomorphism over `X`.

`f` is affine and universally closed by Stacks 0415, so `Y` is affine over `X` and `f_* 𝒪_Y` is
integral over `𝒪_X` by the first assertion of Stacks 0A0Q; the integral closure of `𝒪_X` in an
integral algebra is all of it, so the direct-image map of `f'` is an isomorphism, and direct
image reflects isomorphisms between spaces affine over `X`. -/
theorem isIso_of_pushforwardAlgebraMap_eq_integralClosureInclusion
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom)
    (X' : AffineOver B S hS X) (f' : Over.mk f ⟶ X'.obj)
    (e : AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)) ≅
      pushforwardAlgebra B S hS X'.obj)
    (he : e.hom ≫ pushforwardAlgebraMap B S hS f' =
      AlgebraSheaf.integralClosureInclusion (pushforwardAlgebra B S hS (Over.mk f))) :
    IsIso f' := by
  have : IsIso (AlgebraSheaf.integralClosureInclusion
      (pushforwardAlgebra B S hS (Over.mk f))) :=
    AlgebraSheaf.isIso_integralClosureInclusion_of_isIntegral
      (isIntegral_pushforwardAlgebra_of_isIntegralHom B S hS f hf)
  have : IsIso (pushforwardAlgebraMap B S hS f') := by
    rw [(Iso.eq_inv_comp e).mpr he]
    infer_instance
  exact isIso_of_isIso_pushforwardAlgebraMap B S hS
    ⟨Over.mk f, isAffineHom_of_isIntegralHom f.hom hf⟩ X' f'

end AlgebraicGeometry.Space

end
