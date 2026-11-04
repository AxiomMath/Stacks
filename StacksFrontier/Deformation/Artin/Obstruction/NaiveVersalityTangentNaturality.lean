module

public import StacksFrontier.Deformation.Artin.Infinitesimal.CanonicalElement

/-!
# Naturality of the canonical tangent map

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S`, lying
over `Spec A`, and let `A` be a `Λ`-algebra. For a `Λ`-derivation `θ : Ω[A⁄Λ] →ₗ[A] k` of `A`
valued in an `A`-module `k`, `Deformation.Artin.canonicalTangentMap` carries the canonical
element of `T_x(Ω_{A/Λ})` to the element `canonicalTangentMap θ` of `T_x(k)` obtained by
pushing forward along `θ`. This file identifies the isomorphism class of the canonical
*representative* lift under pushforward along `θ` with the class of `canonicalTangentMap θ`
under the tangent functor's identification with isomorphism classes of lifts: this is exactly
the naturality field of the tangent functor data, specialized at the module map `θ` and the
canonical element.

This is the second piece of the comparison, for Stacks tag 07YM, between the lifting property
defining `Deformation.Artin.IsVersalAt` and the tangent-space description of versality: it
identifies the class produced by pushing the canonical lift forward along `θ` with the class
of the tangent-space element `canonicalTangentMap θ`, which is what lets a witness of the
lifting property at the canonical representative be read off as a value of
`canonicalTangentMap`.

The tangent functor data also records that the same pushforward is realized by a *cartesian*
arrow, through its `liftEquiv_natural` field; this is the companion fact
`Deformation.Artin.isPullbackOfSquareZeroLift_canonicalTangentMap`, proved exactly as the first
by using `liftEquiv_natural` in place of `naturality`.

## Main results

* `Deformation.Artin.isCanonicalLiftTransition_canonicalTangentMap` — the canonical
  representative lift and its pushforward along `θ` realize the canonical pullback
  transition `Deformation.Artin.IsCanonicalLiftTransition` relating the class of the
  canonical element and the class of `canonicalTangentMap θ`.
* `Deformation.Artin.isPullbackOfSquareZeroLift_canonicalTangentMap` — the same two classes
  are also related by `Deformation.Artin.IsPullbackOfSquareZeroLift`, the cartesian form of
  the canonical pullback transition.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

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

/-- **Stacks 07YM.** The class of the canonical representative lift and the class of
`canonicalTangentMap θ` realize the canonical pullback transition along `θ`: pushing the
canonical representative forward along the module map underlying `θ` recovers a lift whose
class is that of `canonicalTangentMap θ`. This is the tangent functor's naturality field,
specialized at the canonical element. -/
public theorem isCanonicalLiftTransition_canonicalTangentMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    IsCanonicalLiftTransition A B S hS toS hA p x hx
      (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
      (Quotient.mk _ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
        baseMap baseFactorization).representative)
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
        (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
          baseFactorization θ)) := by
  have h := (tangentFunctor A B S hS toS hA p x hx hp hRS).naturality
    (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
      baseMap baseFactorization).element
  rwa [(canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
    baseMap baseFactorization).representative_class] at h

/-- **Stacks 07YM.** The class of the canonical representative lift and the class of
`canonicalTangentMap θ` are also related by the cartesian form of the canonical pullback
transition: pushing the canonical representative forward along `θ` by a *cartesian* arrow
recovers a lift whose class is that of `canonicalTangentMap θ`. This is the tangent functor's
`liftEquiv_natural` field, specialized at the canonical element. -/
public theorem isPullbackOfSquareZeroLift_canonicalTangentMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    IsPullbackOfSquareZeroLift A B S hS toS hA p x hx
      (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
      (Quotient.mk _ (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
        baseMap baseFactorization).representative)
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
        (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
        (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
          baseFactorization θ)) := by
  have h := (tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv_natural
    (⟨ModuleCat.ofHom θ⟩ : differentialsSiteModule Λ A B hΩ ⟶
      (⟨ModuleCat.of A k, hk⟩ : SiteModule A B))
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
      baseMap baseFactorization).element
  rwa [(canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ
    baseMap baseFactorization).representative_class] at h

end Deformation.Artin
