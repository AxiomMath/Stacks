module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import StacksFrontier.RingTheory.Localization.AtPrimeOfLocalRing

/-!
# The local ring at a point of an affine morphism as a localization of the pushforward stalk

For an affine morphism of schemes `f : X ⟶ Y` and a point `x : X`, the local ring `𝒪_{X,x}` is a
localization of the stalk `(f_* 𝒪_X)_{f x}` of the pushforward: namely the localization at the
prime cut out by `x`, which is the kernel of the evaluation `(f_* 𝒪_X)_{f x} ⟶ κ(x)`. When `f` is
integral that prime is the maximal ideal which `x` names under the bijection
`AlgebraicGeometry.Scheme.Hom.fiberEquivMaximalSpectrum` between the fibre and the maximal
spectrum of the pushforward stalk.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isLocalization_atPrime_ker_fiberResidue` and
  `AlgebraicGeometry.Scheme.Hom.isLocalization_atPrime_stalkPushforward`: for an affine morphism,
  `𝒪_{X,x}` is the localization of `(f_* 𝒪_X)_{f x}` at the kernel of the evaluation into `κ(x)`.
* `AlgebraicGeometry.Scheme.Hom.isLocalization_atPrime_fiberMaximalIdeal`: for an integral
  morphism that prime is the maximal ideal given by `x` in the maximal spectrum.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For an affine morphism `f` and a point `x` of `X`, the local ring `𝒪_{X,x}` is the
localization of the stalk `(f_* 𝒪_X)_{f x}` of the pushforward at the kernel of the evaluation
`(f_* 𝒪_X)_{f x} ⟶ κ(x)`, for any `(f_* 𝒪_X)_{f x}`-algebra structure on `𝒪_{X,x}` whose
structure map is `stalkPushforward`. -/
theorem isLocalization_atPrime_ker_fiberResidue [IsAffineHom f] (x : X)
    [Algebra (f.pushforwardStalk (f x)) (X.presheaf.stalk x)]
    (halg : algebraMap (f.pushforwardStalk (f x)) (X.presheaf.stalk x) =
      (f.stalkPushforward x).hom) :
    IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker (f.fiberResidue x).hom) := by
  obtain ⟨V, hV, hx, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  let : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk (f x)) :=
    (f.pushforwardGerm V (f x) hx).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hpf : IsLocalization
      ((hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk (f x)) :=
    f.isLocalization_pushforwardStalk hV hx
  have hst : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
  have hle : (hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl.map (f.app V).hom ≤
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := x) V hV (f ⁻¹ᵁ V) hU
      (le_refl (f ⁻¹ᵁ V)) hx
    rw [Scheme.Hom.appLE_eq_app] at h
    rintro _ ⟨r, hr, rfl⟩
    exact fun hmem ↦ hr (congrArg PrimeSpectrum.asIdeal h ▸ hmem)
  have htower : IsScalarTower Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk (f x))
      (X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [halg]
    change (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom =
      (f.stalkPushforward x).hom.comp (f.pushforwardGerm V (f x) hx).hom
    rw [← CommRingCat.hom_comp]
    exact (congrArg CommRingCat.Hom.hom
      (TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base X.presheaf V x hx)).symm
  have := IsLocalization.isLocalization_of_submonoid_le
    (R := Γ(X, f ⁻¹ᵁ V)) (f.pushforwardStalk (f x)) (X.presheaf.stalk x)
    ((hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl.map (f.app V).hom)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hle
  exact isLocalization_atPrime_of_eq_under_maximalIdeal (X.presheaf.stalk x)
    (Submonoid.map (algebraMap Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk (f x)))
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    (by rw [ker_fiberResidue, Ideal.under, halg])

/-- For an affine morphism `f` and a point `x` of `X`, the local ring `𝒪_{X,x}` is the
localization of the stalk `(f_* 𝒪_X)_{f x}` of the pushforward at the kernel of the evaluation
into `κ(x)`, for the algebra structure given by `stalkPushforward`. -/
theorem isLocalization_atPrime_stalkPushforward [IsAffineHom f] (x : X) :
    letI : Algebra (f.pushforwardStalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkPushforward x).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker (f.fiberResidue x).hom) :=
  let : Algebra (f.pushforwardStalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkPushforward x).hom.toAlgebra
  f.isLocalization_atPrime_ker_fiberResidue x (RingHom.algebraMap_toAlgebra _)

/-- For an integral morphism `f` and a point `x` of `X`, the local ring `𝒪_{X,x}` is the
localization of the stalk `(f_* 𝒪_X)_{f x}` of the pushforward at the maximal ideal
`AlgebraicGeometry.Scheme.Hom.fiberMaximalIdeal` given by `x`, for any algebra structure whose
structure map is `stalkPushforward`. -/
theorem isLocalization_atPrime_fiberMaximalIdeal [IsIntegralHom f] (x : X)
    [Algebra (f.pushforwardStalk (f x)) (X.presheaf.stalk x)]
    (halg : algebraMap (f.pushforwardStalk (f x)) (X.presheaf.stalk x) =
      (f.stalkPushforward x).hom) :
    IsLocalization.AtPrime (X.presheaf.stalk x)
      (f.fiberMaximalIdeal (y := f x) ⟨x, rfl⟩).asIdeal := by
  have := f.isLocalization_atPrime_ker_fiberResidue x halg
  exact isLocalization_atPrime_of_eq_under_maximalIdeal (X.presheaf.stalk x)
    (RingHom.ker (f.fiberResidue x).hom).primeCompl (by
      change RingHom.ker (f.fiberResidueOfEq x rfl).hom = _
      rw [fiberResidueOfEq_rfl, ker_fiberResidue, Ideal.under, halg])

end Scheme.Hom

end AlgebraicGeometry
