module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldClassEquation

/-!
# The class equation of Stacks 07YM, at an arbitrary connecting arrow

The class equation `Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap`
computes the class of `Deformation.Artin.canonicalTangentMap θ` as the class of the *chosen*
connecting arrow `Deformation.Artin.canonicalDualNumbersConnectingArrow`, the one produced from
the universal property of a lift `(y, φ)` of `x` along `canonicalDualNumbersArrow θ`. This file
records the same equation for *any* arrow `χ : x₀ ⟶ y` over the square-zero immersion
`Spec k ⟶ Spec k[k]` which factors the chosen restriction arrow `η : x₀ ⟶ x` through `φ`: such
a `χ` is the chosen connecting arrow, by the uniqueness half of the universal property of the
strongly Cartesian arrow `φ`.

This is the form the class equation is used in. In the implication `(1) ⇒ (2)` of Stacks 07YM
one starts from an infinitesimal deformation of `x₀` over the dual numbers of `k`, that is from
a class in `Deformation.Artin.squareZeroLiftClasses`, whose representative is an arrow `χ` over
the square-zero immersion; versality supplies the `φ` extending it to `x`, and nothing picks out
the chosen connecting arrow. With this statement that class is exhibited as the image of `θ`
under the map on tangent spaces, which is what the surjectivity of that map means.

## Main results

* `Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap_of_fac` — the class
  equation at an arbitrary connecting arrow.

## Implementation notes

The hypotheses on `χ` and the membership proof witnessing that `Under.mk χ` lies in the fibre
are stated inside the conclusion, after the `letI` supplying `p.IsFibered` from the
fibred-in-groupoids hypothesis: the chosen pullback of `x` to `Spec k`, which is `χ`'s domain,
is only available once that instance is.

The uniqueness is `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`, applied twice — once
to `χ` and once to the chosen connecting arrow — rather than by unfolding
`canonicalDualNumbersConnectingArrow` to the `map` it is. As in that definition, the instance
witnessing that the chosen restriction arrow `η` lies over
`Deformation.Artin.algebraOverMapOfRingHom` is supplied explicitly rather than through
`synthInstance`, which compares candidates at a transparency that does not unfold
`CategoryTheory.Functor.chosenPullbacks`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hAk x hx hp hRS hΩ hk hkk baseMap baseFactorization in
/-- **Stacks 07YM, the class equation at an arbitrary connecting arrow.** Let `(y, φ)` be a lift
of `x` along `Deformation.Artin.canonicalDualNumbersArrow θ`, and let `χ : x₀ ⟶ y` be any arrow
from the chosen pullback of `x` to `Spec k`, lying over the square-zero immersion
`Spec k ⟶ Spec k[k]`, which factors the chosen restriction arrow `η : x₀ ⟶ x` through `φ`. Then
the class of `χ` as an infinitesimal deformation of `x₀` over the dual numbers of `k` is the
image of `θ` under the map on tangent spaces, moved across the identification
`Deformation.Artin.canonicalFieldBaseChangeEquiv` of lift classes over `A[k]` with lift classes
over `k[k]`.

Such a `χ` is the chosen connecting arrow
`Deformation.Artin.canonicalDualNumbersConnectingArrow`: both lie over the square-zero immersion
and both factor `η` through `φ`, so both are the arrow produced by the universal property of the
strongly Cartesian arrow `φ`. The statement then reduces to
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap`. -/
@[stacks 07YM "the class equation at an arbitrary connecting arrow"]
public theorem canonicalFieldBaseChangeEquiv_canonicalTangentMap_of_fac
    (θ : Ω[A⁄Λ] →ₗ[A] k) (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    ∀ (χ : (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
          ⟨x, hx⟩).1 ⟶ y),
      p.IsHomLift
          (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
            (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) χ →
        χ ≫ φ = (Functor.chosenPullbacks p).map
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩ →
          ∀ hmem : (Under.post p).obj (Under.mk χ) =
            Under.mk (eqToHom (((Functor.chosenPullbacks p).pullbackFunctor
                (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
                  (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj
                ⟨x, hx⟩).2 ≫
              squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
                (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)),
          canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
              ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
                (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
                (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
                  baseFactorization θ)) =
            Quotient.mk _ ⟨Under.mk χ, hmem⟩ := by
  let : p.IsFibered := hp.isFibered
  intro χ hχ hfac hmem
  have := hφ
  have := hχ
  have hφSC : p.IsStronglyCartesian
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ :=
    hp.isStronglyCartesian_homLift _ φ
  have hconnSC := isStronglyCartesian_canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA
    hAk p x hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ
  have hχeq : χ = canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
      hkk baseMap baseFactorization θ y φ hφ := by
    have := hconnSC.toIsHomLift
    exact Functor.IsStronglyCartesian.ext p
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) <| hfac.trans
      (canonicalDualNumbersConnectingArrow_fac Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
        baseMap baseFactorization θ y φ hφ).symm
  subst hχeq
  exact canonicalFieldBaseChangeEquiv_canonicalTangentMap Λ A k B S hS toS hA hAk p x hx hp hRS
    hΩ hk hkk baseMap baseFactorization θ y φ hφ

end Deformation.Artin
