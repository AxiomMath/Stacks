module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldLift

/-!
# A lift over the field's own dual numbers through `canonicalDualNumbersArrow`

Let `x` be an object of a category `𝒳` fibred in groupoids over the big fppf site of `S`,
lying over `Spec A`, and let `θ : Ω_{A/Λ} →ₐ k` be an `A`-linear map into a residue field `k`
of `A`. Since `𝒳` is fibred in groupoids over the site, the morphism
`Deformation.Artin.canonicalDualNumbersArrow θ : Spec k[k] ⟶ Spec A` of step (a) lifts through
`x` to an arrow of `𝒳`: this is step (b) of the construction connecting the canonical tangent
map to the lifting description of `Deformation.Artin.IsVersalAt`, for Stacks tag 07YM.

## Main results

* `Deformation.Artin.exists_canonicalDualNumbersLift` — the existence of a lift of `x` along
  `Deformation.Artin.canonicalDualNumbersArrow θ`, supplied by
  `CategoryTheory.Functor.IsFiberedInGroupoids.exists_lift`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

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
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hkk p x hx hp hRS hΩ baseMap baseFactorization in
/-- **Step (b) of Stacks 07YM.** Since `p` is fibred in groupoids, the morphism
`canonicalDualNumbersArrow θ : Spec k[k] ⟶ Spec A` lifts through `x` to an arrow `y ⟶ x` of the
total category, with `y` lying over `Spec k[k]`. -/
public theorem exists_canonicalDualNumbersLift (θ : Ω[A⁄Λ] →ₗ[A] k) :
    ∃ (y : X) (φ : y ⟶ x),
      p.obj y = squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ∧
      p.IsHomLift
        (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
          baseFactorization θ) φ := by
  obtain ⟨y, φ, hφ⟩ := hp.exists_lift
    (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ) x hx
  have := hφ
  exact ⟨y, φ, IsHomLift.domain_eq p
    (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ) φ, hφ⟩

end Deformation.Artin
