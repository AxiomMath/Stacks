module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldBaseChange

/-!
# The lift at the field's dual numbers determined by a tangent vector

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S`, lying
over `Spec A`, and let `θ : Ω_{A/Λ} →ₐ k` be an `A`-linear map into a residue field `k` of
`A`. Pushing the canonical section `a ↦ (a, d a) : A → A[Ω_{A/Λ}]` forward along `θ` and then
base-changing along `A → k` produces a ring map

`A → k[k],  a ↦ (ψ a, θ (d a))`,

exactly the shape forced on a lift of `ψ : A → k` through the dual-numbers augmentation by
`Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq`. Pulling `x` back along the
corresponding morphism of spectra produces a lift of `x` over `Spec k[k]`, which is step (a) of
the construction connecting the canonical tangent map to this lifting description, for Stacks
tag 07YM.

## Main definitions

* `Deformation.Artin.canonicalDualNumbersMap` — the base-changed ring map `A → k[k]`, as a
  composite of the canonical section and the base-change map of a module homomorphism.
* `Deformation.Artin.canonicalDualNumbersArrow` — the corresponding morphism of the site over
  `S`, from the square-zero extension of `k` by itself to `Spec A`.

## Main results

* `Deformation.Artin.canonicalDualNumbersMap_apply` — the base-changed ring map has the shape
  forced by `Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq`.

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

/-- An `A`-linear map `Ω_{A⁄Λ} → k`, read as an `A`-linear map into `k`, pushes forward from
`A`-module to `k`-module scalars along `algebraMap A k` semilinearly. -/
public theorem differential_toAddMonoidHom_smul (θ : Ω[A⁄Λ] →ₗ[A] k) (a : A)
    (m : Ω[A⁄Λ]) :
    θ.toAddMonoidHom (a • m) = algebraMap A k a • θ.toAddMonoidHom m := by
  show θ (a • m) = algebraMap A k a • θ m
  rw [map_smul, Algebra.smul_def, smul_eq_mul]

include B S hS toS hA p x hx hp hRS hΩ baseMap baseFactorization in
/-- The ring map `A → k[k]` obtained by pushing the canonical section
`a ↦ (a, d a) : A → A[Ω_{A⁄Λ}]` forward along `θ : Ω_{A⁄Λ} → k` and then base-changing the
square-zero extension along `algebraMap A k`. -/
public def canonicalDualNumbersMap (θ : Ω[A⁄Λ] →ₗ[A] k) :
    A →+* (squareZeroRing k (ModuleCat.of k k) : Type u) :=
  (squareZeroRingBaseMap (M := differentialsModule Λ A) (N := ModuleCat.of k k)
      (algebraMap A k) θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ)).comp
    ((canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionRing :
      A →+* (squareZeroRing A (differentialsModule Λ A) : Type u))

include B S hS toS hA p x hx hp hRS hΩ baseMap baseFactorization in
/-- The base-changed ring map has the shape forced on a lift of `algebraMap A k` through the
dual-numbers augmentation by `Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq`. -/
public theorem canonicalDualNumbersMap_apply (θ : Ω[A⁄Λ] →ₗ[A] k) (a : A) :
    canonicalDualNumbersMap Λ A k B S hS toS hA p x hx hp hRS hΩ baseMap baseFactorization θ a =
      TrivSqZeroExt.inl (algebraMap A k a) +
        TrivSqZeroExt.inr (θ (KaehlerDifferential.D Λ A a)) := by
  show squareZeroRingBaseMap (M := differentialsModule Λ A) (N := ModuleCat.of k k)
      (algebraMap A k) θ.toAddMonoidHom
      (differential_toAddMonoidHom_smul Λ A k θ)
      ((canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).sectionRing a) = _
  rw [squareZeroRingBaseMap_apply, (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS
    hΩ baseMap baseFactorization).sectionRing_apply]
  refine TrivSqZeroExt.ext ?_ ?_
  · show algebraMap A k a = algebraMap A k a + (0 : k)
    simp
  · show θ (KaehlerDifferential.D Λ A a) = (0 : k) + θ (KaehlerDifferential.D Λ A a)
    simp

include B S hS toS hA hkk p x hx hp hRS hΩ baseMap baseFactorization in
/-- Step (a) of the construction relating `canonicalTangentMap` to the lifting description of
`Deformation.Artin.IsVersalAt`, for Stacks tag 07YM. The morphism of the site over `S`, from
the square-zero extension of `k` by itself to `Spec A`, attached to a tangent vector
`θ : Ω_{A⁄Λ} →ₐ k`: the base-change of the canonical section of `A[Ω_{A⁄Λ}]` along `θ`
followed by base-change along `algebraMap A k`, then the canonical cartesian arrow of the
section back to `x`'s base. -/
public def canonicalDualNumbersArrow (θ : Ω[A⁄Λ] →ₗ[A] k) :
    squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ⟶
      algebraOver A B S hS toS hA :=
  squareZeroOverBaseMap (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) rfl
      (differentialsSiteModule Λ A B hΩ) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
      θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ) ≫
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).sectionScheme

include B S hS toS hA p x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- The morphism `canonicalDualNumbersArrow` is the morphism of spectra determined by
`canonicalDualNumbersMap`. -/
public theorem canonicalDualNumbersArrow_spec (θ : Ω[A⁄Λ] →ₗ[A] k) :
    (BigFppfOver.toScheme B S hS).map
        (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
          baseFactorization θ) =
      Spec.map (CommRingCat.ofHom
        (canonicalDualNumbersMap Λ A k B S hS toS hA p x hx hp hRS hΩ baseMap
          baseFactorization θ)) := by
  unfold canonicalDualNumbersArrow canonicalDualNumbersMap
  exact squareZeroOverBaseMap_comp_spec (algebraMap A k) B S hS toS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA rfl
    (differentialsSiteModule Λ A B hΩ) (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
    θ.toAddMonoidHom (differential_toAddMonoidHom_smul Λ A k θ)
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).sectionScheme
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).sectionRing
    (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization).sectionScheme_spec

end Deformation.Artin
