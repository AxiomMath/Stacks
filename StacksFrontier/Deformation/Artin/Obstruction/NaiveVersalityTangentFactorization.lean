module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory

/-!
# The map on tangent spaces, through the augmentation of the naive cotangent complex

Hypothesis (ii) of Stacks 07YM supplies a functorial isomorphism `T_x(-) ⟶ Ext⁰_A(E, -)` from
the tangent functor of Stacks 07Y9 to degree-zero derived Hom out of a bounded-above complex
`E`, together with one normalization: it carries the canonical element of `T_x(Ω_{A/Λ})` of
Stacks 07YC to the composite of `ξ : E ⟶ NL_{A/Λ}` with the augmentation
`Deformation.Artin.naiveCotangentToDifferentials`.

This file draws the consequence the tag uses. The map on tangent spaces of Stacks 07YC sends a
tangent vector `θ : Ω_{A/Λ} →ₗ[A] k` to the canonical element pushed along `θ`, so under the
isomorphism its image is `ξ` followed by the augmentation followed by `θ`. In particular the
map `Der_Λ(A, k) ⟶ T_x(k)` is, after the identification, precomposition with `ξ` restricted to
the classes that factor through the augmentation -- which is what makes its surjectivity the
surjectivity of `Ext⁰_A(NL_{A/Λ}, k) ⟶ Ext⁰_A(E, k)`.

## Main results

* `Deformation.Artin.tangentEquiv_canonicalTangentMap` — the factorization.

## Implementation notes

The content is the naturality of the functorial isomorphism at the morphism of site modules
attached to `θ`, followed by its prescribed value at the canonical element.
`Deformation.Artin.canonicalTangentMap` is *defined* as the image of the canonical element
under that morphism, so nothing else is computed.

The isomorphism, its naturality and its normalization are taken as data in exactly the shape
hypothesis (ii) states them: a family of additive equivalences indexed by the site modules,
not a natural isomorphism of functors, since the target of the tangent functor is a type and
the `Ext⁰` side is a morphism set of the derived category.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

attribute [local instance] HasDerivedCategory.standard

section TangentFactorization

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (E : DerivedCategory (ModuleCat.{u} A))
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)

include tangentEquiv_natural tangentEquiv_canonical in
/-- **Stacks 07YM, hypothesis (ii) in use.** Under the functorial isomorphism
`T_x(-) ≅ Ext⁰_A(E, -)` of hypothesis (ii), the map on tangent spaces of Stacks 07YC sends a
tangent vector `θ : Ω_{A/Λ} →ₗ[A] k` to `ξ` followed by the augmentation
`Deformation.Artin.naiveCotangentToDifferentials` followed by `θ`.

This is the naturality of the isomorphism at the morphism of site modules attached to `θ`,
together with its prescribed value at the canonical element:
`Deformation.Artin.canonicalTangentMap` is by definition the image of the canonical element
under that morphism. -/
@[stacks 07YM "the map on tangent spaces factors through the augmentation"]
public theorem tangentEquiv_canonicalTangentMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    tangentEquiv (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
        (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
          baseFactorization θ) =
      ξ ≫ naiveCotangentToDifferentials Λ A ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (ModuleCat.ofHom θ) := by
  rw [canonicalTangentMap, tangentEquiv_natural, tangentEquiv_canonical, Category.assoc]

end TangentFactorization

end Deformation.Artin
