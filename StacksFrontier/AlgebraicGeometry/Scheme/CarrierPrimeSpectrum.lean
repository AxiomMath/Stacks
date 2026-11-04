module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The points of an affine scheme as the primes of its ring of global functions

An affine scheme `X` is isomorphic to `Spec Γ(X, ⊤)` by `AlgebraicGeometry.Scheme.isoSpec`, so its
points are the prime ideals of `Γ(X, ⊤)` and a morphism of affine schemes is, on points,
contraction of primes along the induced map of rings of global functions. This file records that
equivalence and its naturality.

## Main definitions

* `AlgebraicGeometry.Scheme.carrierEquivPrimeSpectrum`: the points of an affine scheme are the
  primes of its ring of global functions.

## Main results

* `AlgebraicGeometry.Scheme.carrierEquivPrimeSpectrum_naturality`: on points, a morphism of affine
  schemes is contraction along the induced map of rings of global functions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The points of an affine scheme are the primes of its ring of global functions.** -/
def Scheme.carrierEquivPrimeSpectrum (X : Scheme.{u}) [IsAffine X] :
    X ≃ PrimeSpectrum Γ(X, ⊤) where
  toFun x := X.isoSpec.hom.base x
  invFun p := X.isoSpec.inv.base p
  left_inv x := congrArg (fun k : X ⟶ X => k.base x) X.isoSpec.hom_inv_id
  right_inv p := congrArg (fun k : Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤) => k.base p) X.isoSpec.inv_hom_id

/-- The prime of `Γ(X, ⊤)` corresponding to a point `x` of an affine scheme `X` is the image of `x`
under `X.isoSpec`. -/
@[simp]
theorem Scheme.carrierEquivPrimeSpectrum_apply (X : Scheme.{u}) [IsAffine X] (x : X) :
    X.carrierEquivPrimeSpectrum x = X.isoSpec.hom.base x :=
  rfl

/-- On points, a morphism of affine schemes is contraction of prime ideals along the induced map
of rings of global functions. -/
theorem Scheme.carrierEquivPrimeSpectrum_naturality {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (x : X) :
    Y.carrierEquivPrimeSpectrum (f.base x) =
      PrimeSpectrum.comap f.appTop.hom (X.carrierEquivPrimeSpectrum x) :=
  (congrArg (fun k : X ⟶ Spec Γ(Y, ⊤) => k.base x) (Scheme.isoSpec_hom_naturality f)).symm

end AlgebraicGeometry

end

end
