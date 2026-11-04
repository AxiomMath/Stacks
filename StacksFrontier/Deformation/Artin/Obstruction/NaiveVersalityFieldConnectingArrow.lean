module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldAugmentation

/-!
# The arrow connecting the restriction of `x` to a lift of step (b)

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S`, lying
over `Spec A`, and let `θ : Ω_{A/Λ} →ₐ k` be an `A`-linear map into a residue field `k` of `A`.
Step (b) produces, for any lift `(y, φ)` of `x` along `canonicalDualNumbersArrow θ`, a morphism
`φ : y ⟶ x`. Restricting `x` to `Spec k` along the point determined by the `A`-algebra
structure on `k` instead produces a chosen pullback arrow `η : x' ⟶ x`, where `x'` is the
chosen pullback object. Since `canonicalDualNumbersArrow θ` factors the restriction arrow
through the square-zero immersion at `k` (`Deformation.Artin.squareZeroArrow_comp_
canonicalDualNumbersArrow`), and `φ` is strongly cartesian because the total category is fibred
in groupoids, the universal property of `φ` produces a connecting arrow `χ : x' ⟶ y` lying over
the square-zero immersion, with `χ ≫ φ = η`. This is step (c), part (ii), of the construction
connecting the canonical tangent map to the lifting description of
`Deformation.Artin.IsVersalAt`, for Stacks tag 07YM.

## Main definitions

* `Deformation.Artin.canonicalDualNumbersConnectingArrow` — the arrow `χ : x' ⟶ y` lying over
  the square-zero immersion at `k`, connecting the chosen restriction of `x` to `Spec k` to a
  given lift `(y, φ)` of step (b).

## Main results

* `Deformation.Artin.canonicalDualNumbersConnectingArrow_fac` — `χ` factors the chosen
  restriction arrow `η` through `φ`.
* `Deformation.Artin.isStronglyCartesian_canonicalDualNumbersConnectingArrow` — `χ` is itself
  strongly cartesian over the square-zero immersion `Spec k ⟶ Spec k[k]`.

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
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hAk x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- **Step (c)(ii) of Stacks 07YM.** Given a lift `(y, φ)` of `x` along
`canonicalDualNumbersArrow θ`, as produced by `Deformation.Artin.exists_canonicalDualNumbersLift`,
the connecting arrow `χ : x' ⟶ y` from the chosen pullback `x'` of `x` to `Spec k`, lying over
the square-zero immersion `Spec k ⟶ Spec k[k]`, obtained from the universal property of `φ` (a
strongly cartesian arrow, since the total category is fibred in groupoids) applied to the
chosen pullback arrow `η : x' ⟶ x`, using that `canonicalDualNumbersArrow θ` factors `η`'s base
arrow through the square-zero immersion. -/
public def canonicalDualNumbersConnectingArrow (θ : Ω[A⁄Λ] →ₗ[A] k) (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    (((Functor.chosenPullbacks p).pullbackFunctor
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).1 ⟶ y := by
  haveI : p.IsFibered := hp.isFibered
  haveI := hφ
  haveI : p.IsStronglyCartesian
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ :=
    hp.isStronglyCartesian_homLift _ φ
  have hSC : p.IsStronglyCartesian
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
      ((Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩) :=
    (Functor.chosenPullbacks p).isStronglyCartesian
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩
  haveI : p.IsHomLift
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
      ((Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩) :=
    hSC.toIsHomLift
  have hfa : algebraOverMapOfRingHom (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl =
      squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫
        canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
          baseFactorization θ :=
    (squareZeroArrow_comp_canonicalDualNumbersArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ
      hkk baseMap baseFactorization θ).symm
  -- The instance argument supplying `IsHomLift p (algebraOverMapOfRingHom ...) (...)` is given
  -- explicitly (as `hSC.toIsHomLift`) rather than through instance synthesis: `synthInstance`
  -- compares candidates at a transparency that does not unfold `Functor.chosenPullbacks`, so it
  -- cannot see that the locally-derived instance and the one buried in the goal agree, even
  -- though they are definitionally equal. Supplying the term directly lets ordinary
  -- type-checking (which does unfold it) confirm the match.
  exact @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
    (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ) φ _ _ _ _ _ hfa
    ((Functor.chosenPullbacks p).map
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)
    hSC.toIsHomLift

/-- The connecting arrow factors the chosen pullback arrow through `φ` and is strongly
cartesian over the square-zero immersion. -/
private theorem canonicalDualNumbersConnectingArrow_fac_and_isStronglyCartesian
    (θ : Ω[A⁄Λ] →ₗ[A] k) (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ y φ hφ ≫ φ =
      (Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩ ∧
    p.IsStronglyCartesian
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
      (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ y φ hφ) := by
  have : p.IsFibered := hp.isFibered
  have := hφ
  have hφSC : p.IsStronglyCartesian
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ :=
    hp.isStronglyCartesian_homLift _ φ
  have hSC := (Functor.chosenPullbacks p).isStronglyCartesian
    (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩
  have hfa := (squareZeroArrow_comp_canonicalDualNumbersArrow Λ A k B S hS toS hA hAk p x hx hp
    hRS hΩ hkk baseMap baseFactorization θ).symm
  -- The instance argument `hSC.toIsHomLift` is given explicitly rather than through instance
  -- synthesis: `synthInstance` does not unfold `Functor.chosenPullbacks`, so it cannot see that
  -- the instance it finds agrees with the one buried in the goal, though they are definitionally
  -- equal.
  have hfac := @Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
    (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ) φ _ _ _ _ _ hfa
    ((Functor.chosenPullbacks p).map
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)
    hSC.toIsHomLift
  refine ⟨hfac, ?_⟩
  have hχlift : p.IsHomLift _ (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x
      hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ) :=
    @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _
    (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ) φ _ _ _ _ _ hfa
    ((Functor.chosenPullbacks p).map
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)
    hSC.toIsHomLift
  have hcomp : p.IsStronglyCartesian
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫
        canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
          baseFactorization θ)
      (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap
          baseFactorization θ y φ hφ ≫ φ) := by
    rw [← hfa]
    rwa [← hfac] at hSC
  exact Functor.IsStronglyCartesian.of_comp p
    (g := canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ)
    (ψ := φ)

include B S hS toS hA hAk x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- The connecting arrow `Deformation.Artin.canonicalDualNumbersConnectingArrow` factors the
chosen pullback arrow `η : x' ⟶ x` through the given lift `φ`. -/
public theorem canonicalDualNumbersConnectingArrow_fac (θ : Ω[A⁄Λ] →ₗ[A] k) (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ y φ hφ ≫ φ =
      (Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩ :=
  (canonicalDualNumbersConnectingArrow_fac_and_isStronglyCartesian Λ A k B S hS toS hA hAk p x
    hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ).1

include B S hS toS hA hAk x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- The connecting arrow `Deformation.Artin.canonicalDualNumbersConnectingArrow` is itself
strongly cartesian over the square-zero immersion `Spec k ⟶ Spec k[k]`, not merely a lift of
it. Obtained from `Functor.IsStronglyCartesian.of_comp`, applied to the same factorization
`squareZeroArrow_comp_canonicalDualNumbersArrow` used to construct `χ`: the composite `χ ≫ φ`
is strongly cartesian over the composite arrow (being, by
`canonicalDualNumbersConnectingArrow_fac`, the pullback arrow `η` lying strongly cartesian
over that composite by the chosen-pullbacks structure), and `φ` itself is strongly cartesian,
so `of_comp` promotes the already-known `IsHomLift` of `χ` to the strong form. -/
public theorem isStronglyCartesian_canonicalDualNumbersConnectingArrow (θ : Ω[A⁄Λ] →ₗ[A] k)
    (y : X) (φ : y ⟶ x)
    (hφ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) φ) :
    letI : p.IsFibered := hp.isFibered
    p.IsStronglyCartesian
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))
      (canonicalDualNumbersConnectingArrow Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ y φ hφ) :=
  (canonicalDualNumbersConnectingArrow_fac_and_isStronglyCartesian Λ A k B S hS toS hA hAk p x
    hx hp hRS hΩ hkk baseMap baseFactorization θ y φ hφ).2

end Deformation.Artin
