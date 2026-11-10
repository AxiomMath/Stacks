module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# The stalk at a point of the ideal sheaf of its reduced closure

Let `X` be a scheme and let `x` be a point of `X`. The reduced closed subscheme supported on the
closure of `{x}` is cut out by `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of
`TopologicalSpace.Closeds.closure {x}`, and this file identifies the ideal that closed subscheme
induces in the local ring at `x` with the maximal ideal of that local ring.

The computation is local: on an affine open neighbourhood `U` of `x` the ideal of the subscheme is
the vanishing ideal of the preimage of `closure {x}` in `Spec Γ(X, U)`. That preimage is the
closure of the single point of `Spec Γ(X, U)` corresponding to `x`, because the canonical map
`Spec Γ(X, U) ⟶ X` is an open embedding and so commutes with closures; and the vanishing ideal of
the closure of a point is the prime ideal of that point. The stalk ideal is the image of this
prime under the germ map, and the local ring at `x` is the localization of `Γ(X, U)` at it, so
that image is the maximal ideal.

No closedness hypothesis is needed: the statement is about the reduced closure of `{x}`, which is
a closed subscheme for every point. When `{x}` is already closed the closure may be dropped, and
`Stacks.Divisors.stalk_vanishingIdeal_singleton_of_isClosed` is that reading.

This is what turns a generator of the maximal ideal of `𝒪_{X,x}` into a generator of the ideal
sheaf in the stalk, which is the hypothesis `Stacks Project, Tag 0AG8` takes in the form
`Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor`.

## Main results

* `Stacks.Divisors.ideal_vanishingIdeal_closure_singleton`: on an affine open neighbourhood of `x`
  the ideal of the reduced closure of `{x}` is the prime ideal of `x`.
* `Stacks.Divisors.stalk_vanishingIdeal_closure_singleton`: the stalk at `x` of the ideal sheaf of
  the reduced closure of `{x}` is the maximal ideal of `𝒪_{X,x}`.
* `Stacks.Divisors.stalk_vanishingIdeal_singleton_of_isClosed`: the same for a closed point, with
  the closure dropped.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

section VanishingIdealStalk

variable {X : Scheme.{u}}

/-- On an affine open neighbourhood `U` of `x` the ideal cut out by the reduced closure of `{x}`
is the prime ideal of `Γ(X, U)` corresponding to `x`. -/
theorem ideal_vanishingIdeal_closure_singleton (x : X) (U : X.affineOpens)
    (hU : IsAffineOpen (U.1 : X.Opens)) (hx : x ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).ideal U =
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hsingleton : hU.fromSpec ⁻¹' ({x} : Set X) = {hU.primeIdealOf ⟨x, hx⟩} := by
    ext z
    change hU.fromSpec z = x ↔ z = hU.primeIdealOf ⟨x, hx⟩
    have hfrom : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x :=
      hU.fromSpec_primeIdealOf ⟨x, hx⟩
    exact ⟨fun h ↦ hU.fromSpec.isOpenEmbedding.injective (h.trans hfrom.symm),
      fun h ↦ h ▸ hfrom⟩
  have hclosure : hU.fromSpec ⁻¹' (Closeds.closure ({x} : Set X) : Set X) =
      closure {hU.primeIdealOf ⟨x, hx⟩} :=
    (hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous ({x} : Set X)).trans (congrArg closure hsingleton)
  change PrimeSpectrum.vanishingIdeal
    (hU.fromSpec ⁻¹' (Closeds.closure ({x} : Set X) : Set X)) = _
  exact (congrArg PrimeSpectrum.vanishingIdeal hclosure).trans
    ((PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _))

/-- **The ideal sheaf of the reduced closure of a point has the maximal ideal as its stalk at that
point.** For a point `x` of a scheme `X`, the ideal that the reduced closed subscheme supported on
`closure {x}` induces in `𝒪_{X,x}` is `IsLocalRing.maximalIdeal (X.presheaf.stalk x)`. -/
theorem stalk_vanishingIdeal_closure_singleton (x : X) :
    IdealSheafData.stalk
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  let U' : X.affineOpens := ⟨U, hU⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U' hx,
    ideal_vanishingIdeal_closure_singleton x U' hU hx]
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ (X.presheaf.stalk x)

/-- Alias of `AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton`: the ideal sheaf
of a closed point has the maximal ideal as its stalk at that point. -/
alias stalk_vanishingIdeal_singleton_of_isClosed :=
  AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton

end VanishingIdealStalk

end Stacks.Divisors

end
