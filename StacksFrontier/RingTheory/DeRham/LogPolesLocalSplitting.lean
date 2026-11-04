module

public import StacksFrontier.RingTheory.DeRham.LogPolesSequence
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso

/-!
# The relations of the pair model along a tower

Let `A → R` be a ring map, let `t ∈ R`, and let `R → R'` be a further map of `A`-algebras. The
relations `Stacks.LogPoles.logRel` of the pair model of the de Rham complex of log poles are
defined by `t ω + dt ∧ η = 0`, an equation in `⋀^{p+1} Ω[R⁄A]`. This file shows that the maps of
relative forms induced by the tower carry a relation for `t` to a relation for the image of `t`.

The point of carrying relations along a tower is the mismatch of hypotheses around Stacks Tag
0FMW. The source's hypothesis, Stacks Tag 0FMV, asserts its two conditions at the *local ring*
`𝒪_{X, y}` of each point of the divisor and for each local equation there; the library's affine form
of Tag 0FMW, `Stacks.LogPoles.shortExact_logShortComplex`, asserts both on `R` itself. For the
torsion-freeness that is no difference, since multiplication by `t` is injective on a module
exactly when it is injective on every localization. For the splitting it is a difference: a
retraction of `g ↦ g · dt` over `R_𝔭` for every `𝔭 ⊇ (t)` does not assemble into one over `R`.
Reading the relation over `R_𝔭` is the first step of the argument that closes that gap — the
remaining step, that membership in the logarithmic submodule is itself local, is not proved here.

Nothing in this file constructs a sheaf: the scheme-theoretic statement of Tag 0FMW is not
proved in this repository, affine-locally or otherwise beyond
`Stacks.LogPoles.shortExact_logShortComplex`.

## Main results

* `Stacks.LogPoles.mem_logRel_algebraMap_of_mem_logRel`: a relation for `t` over `R` maps to a
  relation for the image of `t` over `R'`.

## References

* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), whose two conditions are
  stalkwise
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose affine local form
  is `Stacks.LogPoles.shortExact_logShortComplex`
-/

@[expose] public noncomputable section

open KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable (A R R' : Type u) [CommRing A] [CommRing R] [CommRing R'] [Algebra A R] [Algebra A R']
  [Algebra R R'] [IsScalarTower A R R']

/-- **The relations of the pair model are carried along a tower.** If `t ω + dt ∧ η = 0` over `R`
then the same equation holds over `R'` for the image of `t` and the images of `ω` and `η`: the
maps of relative forms are `R`-linear and compatible with wedging by a one-form, and they carry
`dt` to `d` of the image of `t`. -/
theorem mem_logRel_algebraMap_of_mem_logRel (t : R) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    (mapExteriorPower A R R' (p + 1) x.1, mapExteriorPower A R R' p x.2) ∈
      logRel A (algebraMap R R' t) p := by
  have h := (mem_logRel_iff A t p).mp hx
  have himg := congrArg (mapExteriorPower A R R' (p + 1)) h
  rw [map_add, map_zero, map_smul, mapExteriorPower_wedgeLeft, KaehlerDifferential.map_D] at himg
  rw [mem_logRel_iff, algebraMap_smul]
  exact himg

end Stacks.LogPoles

end
