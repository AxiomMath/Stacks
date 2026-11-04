module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.StandardChart
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# The size of a blowup, and of the relative `Proj` of a Rees algebra

The blowup of a scheme `X` in a quasi-coherent sheaf of ideals `ℐ` has size at most the size
of `X`, with no hypothesis on `ℐ` — in particular none of finite generation.

The estimate has the three steps the cardinality layer uses everywhere: bound each affine
piece, bound the index set of the covering, bound the total.

* *Each piece.*  The standard affine charts of Stacks tag 0804 are the spectra of the affine
  blowup algebras `Γ(X, U)[ℐ(U)/a]`, for `U` an affine open of `X` and `a ∈ ℐ(U)`
  (`AlgebraicGeometry.blowUpAffineChartCover`).  The affine blowup algebra is by construction a
  *subalgebra* of the localization `Γ(X, U)_a`, so its cardinality is at most
  `max ℵ₀ #Γ(X, U)` by `Cardinal.mk_le_of_isLocalization`, and `Stacks 000P` turns that into a
  bound on the size of its spectrum.
* *The index set.*  The charts are indexed by `Σ U : X.affineOpens, ℐ(U)`.  There are at most
  `size X` affine opens, and `ℐ(U) ⊆ Γ(X, U)` has at most `size X` elements, so the sigma type
  has at most `size X * size X = size X` elements.
* *The total.*  `Stacks 000Q` (`AlgebraicGeometry.Scheme.size_le_of_iSup_eq_top`) assembles the
  two into the bound on the glued scheme.

The same bound then holds for the relative `Proj` of `Stacks.Blowup.reesSituation`, the
explicitly built Rees algebra that the blowup of an *algebraic space* is constructed from,
because `Stacks.Blowup.reesSituationBlowUpIso` identifies it with `AlgebraicGeometry.blowUp`
and `AlgebraicGeometry.Scheme.size_congr` says the size of a scheme is an isomorphism
invariant.

## Main results

* `AlgebraicGeometry.Scheme.size_blowUp_le`: `size (blowUp ℐ) ≤ size X`.
* `Stacks.Blowup.size_relativeProj_reesSituation_le`: the same bound for the relative `Proj` of
  `Stacks.Blowup.reesSituation ℐ`.

## Implementation notes

No bound of this shape holds for the relative `Proj` of an arbitrary quasi-coherent graded
algebra `𝒜` on `X`: the degree-one piece `𝒜₁` may be a free module of arbitrarily large rank,
and the charts of the relative `Proj` are then `Proj` of a graded ring larger than any function
of `size X`.  What makes the Rees algebra different is that each of its homogeneous pieces
`ℐⁿ` is a *submodule of the structure sheaf*, which is what the affine charts
`Γ(X, U)[ℐ(U)/a] ⊆ Γ(X, U)_a` record.  So the bound is stated for the Rees algebra and not in
general.

No `@[stacks]` attribute is attached.  Tag 0804 is the identification of `b⁻¹(U)` with `Proj`
of the Rees algebra and its covering by the affine blowup charts, which is already carried in
`StacksFrontier/AlgebraicGeometry/Blowup/`; what is here is the cardinality count that covering
supports, which is no part of any tag.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public section

open AlgebraicGeometry Cardinal CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The coordinate ring of a standard affine chart of a blowup is small.** The affine blowup
algebra `Γ(X, U)[ℐ(U)/a]` is a subalgebra of the localization `Γ(X, U)_a`, and a localization
has cardinality at most `max ℵ₀ #Γ(X, U)`. -/
theorem mk_blowUpAffineChartRing_le (U : X.affineOpens) (a : I.ideal U) :
    #(blowUpAffineChartRing I U a) ≤ max ℵ₀ #Γ(X, U.1) :=
  (mk_le_of_injective Subtype.val_injective).trans
    (Cardinal.mk_le_of_isLocalization (Submonoid.powers (a : Γ(X, U.1)))
      (Localization.Away (a : Γ(X, U.1))))

/-- **Each standard affine chart of a blowup has size at most the size of the base.** By Stacks
000P the size of the spectrum is `max ℵ₀` of the cardinality of its ring, which
`AlgebraicGeometry.mk_blowUpAffineChartRing_le` bounds by `max ℵ₀ #Γ(X, U)`, and both of those
are at most `size X`. -/
theorem size_spec_blowUpAffineChartRing_le (U : X.affineOpens) (a : I.ideal U) :
    (Spec (CommRingCat.of (blowUpAffineChartRing I U a))).size ≤ X.size := by
  rw [Scheme.size_Spec]
  exact max_le X.aleph0_le_size ((mk_blowUpAffineChartRing_le I U a).trans
    (max_le X.aleph0_le_size (X.mk_sections_le_size U)))

/-- **The standard affine charts of a blowup are indexed by at most `size X` of them.** A chart
is a pair of an affine open `U` of `X` and a section of `ℐ(U)`; there are at most `size X`
affine opens, and `ℐ(U)` is a submodule of `Γ(X, U)`, which has at most `size X` elements. -/
theorem mk_sigma_ideal_le : #(Σ U : X.affineOpens, I.ideal U) ≤ X.size := by
  calc #(Σ U : X.affineOpens, I.ideal U)
      = Cardinal.sum (fun U : X.affineOpens => #(I.ideal U)) := mk_sigma _
    _ ≤ #X.affineOpens * ⨆ U : X.affineOpens, #(I.ideal U) := sum_le_mk_mul_iSup _
    _ ≤ X.size * X.size := mul_le_mul X.mk_affineOpens_le_size
        (ciSup_le' fun U => (mk_le_of_injective Subtype.val_injective).trans
          (X.mk_sections_le_size U)) (by positivity) (by positivity)
    _ = X.size := mul_eq_self X.aleph0_le_size

/-- **The blowup of a scheme in a quasi-coherent sheaf of ideals has size at most the size of
its base.** No hypothesis is placed on the centre `ℐ`; in particular it need not be of finite
type.

The standard affine charts of Stacks 0804 cover the blowup
(`AlgebraicGeometry.blowUpAffineChartCover`), there are at most `size X` of them
(`AlgebraicGeometry.mk_sigma_ideal_le`) and each has size at most `size X`
(`AlgebraicGeometry.size_spec_blowUpAffineChartRing_le`), so Stacks 000Q gives the bound. -/
theorem Scheme.size_blowUp_le : (blowUp I).size ≤ X.size := by
  have : Nonempty (Σ U : X.affineOpens, I.ideal U) :=
    ⟨⟨⟨⊥, isAffineOpen_bot X⟩, 0⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top
    (fun j : Σ U : X.affineOpens, I.ideal U => (blowUpAffineChart I j.1 j.2).opensRange)
    (blowUpAffineChartCover I).iSup_opensRange).trans
    (max_le (mk_sigma_ideal_le I) (ciSup_le' fun j => ?_))
  rw [← Scheme.size_congr (blowUpAffineChart I j.1 j.2).isoOpensRange]
  exact size_spec_blowUpAffineChartRing_le I j.1 j.2

end AlgebraicGeometry

namespace Stacks.Blowup

/-- **The relative `Proj` of the Rees algebra of a quasi-coherent sheaf of ideals has size at
most the size of its base.** This is `AlgebraicGeometry.Scheme.size_blowUp_le` transported along
`Stacks.Blowup.reesSituationBlowUpIso`, which identifies the relative `Proj` of the explicitly
built Rees algebra with `AlgebraicGeometry.blowUp`; the size of a scheme is an isomorphism
invariant by `AlgebraicGeometry.Scheme.size_congr`.

This is the form the size side conditions of Stacks 085Q ask for: each of the three relative
`Proj`s they name is the relative `Proj` of `Stacks.Blowup.reesSituation` of an ideal sheaf on a
scheme already belonging to the ambient site. -/
theorem size_relativeProj_reesSituation_le {X : Scheme.{u}} (ℐ : X.IdealSheafData) :
    (Stacks.Blowup.reesSituation ℐ).relativeProj.size ≤ X.size := by
  rw [Scheme.size_congr (reesSituationBlowUpIso ℐ)]
  exact Scheme.size_blowUp_le ℐ

end Stacks.Blowup

end
