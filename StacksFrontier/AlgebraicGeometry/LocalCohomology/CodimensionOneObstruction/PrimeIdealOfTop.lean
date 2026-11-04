module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The prime of the top open of an affine scheme

For a commutative ring `R`, the point of `Spec R` viewed as a prime of the sections over the top
open is the point itself, transported along `Scheme.ΓSpecIso`.

## Main results

* `AlgebraicGeometry.primeIdealOf_top_spec` identifies `(isAffineOpen_top (Spec R)).primeIdealOf`
  with `PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On the top open of `Spec R`, the prime of the sections attached to a point is that point,
read through `Scheme.ΓSpecIso`. -/
theorem primeIdealOf_top_spec (R : CommRingCat.{u}) (x : Spec R) :
    (isAffineOpen_top (Spec R)).primeIdealOf ⟨x, trivial⟩
      = PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom x := by
  have key : ∀ P : PrimeSpectrum Γ(Spec R, ⊤),
      PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom
        (PrimeSpectrum.comap (Scheme.ΓSpecIso R).inv.hom P) = P := by
    intro P
    rw [← PrimeSpectrum.comap_comp_apply, ← CommRingCat.hom_comp,
      Iso.hom_inv_id, CommRingCat.hom_id, PrimeSpectrum.comap_id]
  have h : PrimeSpectrum.comap (Scheme.ΓSpecIso R).inv.hom
      ((isAffineOpen_top (Spec R)).primeIdealOf ⟨x, trivial⟩) = x := by
    have h0 := (isAffineOpen_top (Spec R)).fromSpec_primeIdealOf ⟨x, trivial⟩
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h0
    exact h0
  exact (key _).symm.trans (congrArg (PrimeSpectrum.comap (Scheme.ΓSpecIso R).hom.hom) h)

end AlgebraicGeometry

end
