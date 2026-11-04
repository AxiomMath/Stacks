module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldCartesianLift

/-!
# Compatibility of the dual-numbers lift with the augmentation to `Spec A`

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S`, lying
over `Spec A`, and let `θ : Ω_{A/Λ} →ₐ k` be an `A`-linear map into a residue field `k` of `A`.
The ring map `Deformation.Artin.canonicalDualNumbersMap θ : A → k[k]` of step (a) is, by
construction, a lift of `algebraMap A k` through the dual-numbers augmentation
`k[k] → k`: composing it with the augmentation recovers `algebraMap A k`. This file records the
corresponding fact at the level of the site over `S`, for the arrow
`Deformation.Artin.canonicalDualNumbersArrow θ` of step (a): composing the square-zero
immersion `Spec k ⟶ Spec k[k]` with `canonicalDualNumbersArrow θ` recovers the restriction map
`Spec k ⟶ Spec A` determined by the `A`-algebra structure on `k`. This is the base-level fact
used to compare step (b)'s lift of `x` along `canonicalDualNumbersArrow θ` with the canonical
representative's restriction along `θ`, for Stacks tag 07YM.

## Main results

* `Deformation.Artin.squareZeroArrow_comp_canonicalDualNumbersArrow` — the square-zero
  immersion at `k`, followed by `canonicalDualNumbersArrow θ`, is the restriction map of the
  site over `S` determined by `algebraMap A k`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

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
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- The square-zero immersion `Spec k ⟶ Spec k[k]`, followed by
`Deformation.Artin.canonicalDualNumbersArrow θ`, is the restriction morphism of the site over
`S` determined by `algebraMap A k`. Unfolding `canonicalDualNumbersArrow` into its base-change
and section factors, the commuting square `Deformation.Artin.algebraOverMap_comp_squareZeroArrow`
at `algebraMap A k` moves the square-zero immersion at `k` past the base-change factor, landing
on the square-zero immersion at `A`, which the canonical section's right-inverse property
`CanonicalDeformationData.section_isRightInverse` then cancels against the section factor. -/
public theorem squareZeroArrow_comp_canonicalDualNumbersArrow (θ : Ω[A⁄Λ] →ₗ[A] k) :
    squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫
      canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ =
      algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl := by
  unfold canonicalDualNumbersArrow
  rw [← Category.assoc,
    ← algebraOverMap_comp_squareZeroArrow (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl
      (differentialsSiteModule Λ A B hΩ) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
      θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ),
    Category.assoc,
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).section_isRightInverse,
    Category.comp_id]

end Deformation.Artin
