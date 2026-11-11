module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpace

/-!
# The geometry of a hypersurface in projective space

Let `k` be a field, `F` a nonzero homogeneous polynomial of degree `d` in `n + 1` variables and
`Z ⊆ 𝐏ⁿ_k` the hypersurface it cuts out: the closed subscheme whose ideal sheaf is the zero
scheme of the section of `𝒪(d)` attached to `F`. This file records the basic geometry of `Z`
over `k`, with no hypothesis on the characteristic.

* `Z` is projective over `k`, as is every closed subscheme of `𝐏ⁿ_k`.
* `Z` is an effective Cartier divisor on the integral scheme `𝐏ⁿ_k`, and a relative effective
  Cartier divisor over `k` since everything is flat over a field; so for `n = m + 1` the
  structure morphism `Z ⟶ Spec k` has relative dimension `m` in the sense of [Stacks, Tag 02NJ].
* For `n ≥ 2` and `d > 0` the global functions of `Z` are one-dimensional over `k`: the sequence
  `0 ⟶ 𝒪(-d) ⟶ 𝒪 ⟶ 𝒪_Z ⟶ 0` gives `H⁰(Z, 𝒪_Z) ≅ H⁰(𝐏ⁿ_k, 𝒪) = k`, the twist `𝒪(-d)` having no
  `H⁰` and no `H¹`. In particular `Z` is nonempty, even when it has no `k`-rational point.

## Main results

* `Stacks.ProjectiveSpace.isProjective_comp_projToSpecCoeff`: a closed subscheme of `𝐏ⁿ_k` is
  projective over `k`.
* `Stacks.ProjectiveSpace.isEffectiveCartierDivisor_zeroScheme_degreeSection`: a hypersurface is
  an effective Cartier divisor.
* `Stacks.ProjectiveSpace.relativeDimension_zeroScheme_degreeSection`: a hypersurface in
  `𝐏^{m+1}_k` has relative dimension `m` over `k`.
* `Stacks.ProjectiveSpace.finrank_structureSheafCohomology_zero_zeroScheme_degreeSection`:
  `dim_k H⁰(Z, 𝒪_Z) = 1` for `n ≥ 2`, `d > 0`.
* `Stacks.ProjectiveSpace.nonempty_subscheme_zeroScheme_degreeSection`: such a hypersurface is
  nonempty.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheafModule degreeSection)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace

variable (k : Type u) [Field k]

/-- **A closed subscheme of `𝐏ⁿ_k` is projective over `k`**: a closed immersion followed by the
projective morphism `𝐏ⁿ_k ⟶ Spec k`. -/
theorem isProjective_comp_projToSpecCoeff (n : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ AlgebraicGeometry.Proj (polyGrading k n)) [IsClosedImmersion i] :
    IsProjective (i ≫ projToSpecCoeff k n) :=
  Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion i _
    inferInstance (Stacks.WeilDeRham.isProjective_projToSpecCoeff k n)

/-- `𝐏ⁿ_k ⟶ Spec k` is locally of finite type, being smooth. -/
instance locallyOfFiniteType_projToSpecCoeff (n : ℕ) :
    LocallyOfFiniteType (projToSpecCoeff k n) :=
  have := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff k n
  inferInstance

/-- Every morphism to the spectrum of a field is flat: the local rings of the target are fields. -/
theorem flat_of_to_spec_field {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Flat f :=
  AlgebraicGeometry.flat_of_isField_stalk f fun _ => AlgebraicGeometry.isField_stalk_Spec_field k _

/-- **A hypersurface is an effective Cartier divisor.** The zero scheme of the section of `𝒪(d)`
attached to a nonzero homogeneous polynomial is an effective Cartier divisor on the integral
scheme `𝐏ⁿ_k`. -/
theorem isEffectiveCartierDivisor_zeroScheme_degreeSection (n d : ℕ) (F : polyGrading k n d)
    (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
        (twistingSheafModule (polyGrading k n) (d : ℤ)) (degreeSection (polyGrading k n) d F)) := by
  have ht := Stacks.PresheafOfModules.sectionOfTop_val_top
    (twistingSheafModule (polyGrading k n) (d : ℤ)).val (degreeSection (polyGrading k n) d F)
  rw [← ht]
  exact Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero _ _ _
    (ht ▸ Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero k n d F hF)

/-- **A hypersurface in `𝐏^{m+1}_k` has relative dimension `m` over `k`** ([Stacks, Tag 02NJ]).
It is a relative effective Cartier divisor over `k` (flatness over a field being automatic) in
`𝐏^{m+1}_k`, which has relative dimension `m + 1`. -/
theorem relativeDimension_zeroScheme_degreeSection (m d : ℕ) (F : polyGrading k (m + 1) d)
    (hF : (F : MvPolynomial (Fin (m + 1 + 1)) k) ≠ 0) :
    RelativeDimension
      ((zeroScheme (AlgebraicGeometry.Proj (polyGrading k (m + 1)))
        (twistingSheafModule (polyGrading k (m + 1)) (d : ℤ))
        (degreeSection (polyGrading k (m + 1)) d F)).subschemeι ≫ projToSpecCoeff k (m + 1)) m :=
  relativeDimension_of_isRelativeEffectiveCartierDivisor (projToSpecCoeff k (m + 1)) m
    (Stacks.WeilDeRham.relativeDimension_projToSpecCoeff k (m + 1)) _
    ⟨isEffectiveCartierDivisor_zeroScheme_degreeSection k (m + 1) d F hF,
      flat_of_to_spec_field k _⟩

/-- **The global functions of a hypersurface of positive degree in `𝐏ⁿ_k`, `n ≥ 2`, are `k`**:
`dim_k H⁰(Z, 𝒪_Z) = 1`. The twist `𝒪(-d)` has no `H⁰` and no `H¹` ([Stacks, Tag 01XT]), so the
sequence `0 ⟶ 𝒪(-d) ⟶ 𝒪 ⟶ 𝒪_Z ⟶ 0` identifies `H⁰(Z, 𝒪_Z)` with `H⁰(𝐏ⁿ_k, 𝒪) = k`. -/
theorem finrank_structureSheafCohomology_zero_zeroScheme_degreeSection (n d : ℕ) (hn : 2 ≤ n)
    (hd : 0 < d) (F : polyGrading k n d) (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0) :
    Module.finrank k (structureSheafCohomology
      ((zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
        (twistingSheafModule (polyGrading k n) (d : ℤ))
        (degreeSection (polyGrading k n) d F)).subschemeι ≫ projToSpecCoeff k n) 0) = 1 := by
  obtain ⟨e⟩ := Cohomology.nonempty_structureSheafCohomologyIsoTwistCohomologyZero k n 0 d
    _ F hF (Scheme.IdealSheafData.ker_subschemeι _)
    (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology k n _ 0 (by omega))
    (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology k n _ 1 (by omega))
  exact ((e ≪≫ Stacks.ProjectiveSpace.Cohomology.twistCohomologyZeroIsoCoeff k n).toLinearEquiv
    ).finrank_eq.trans (Module.finrank_self k)

/-- **A hypersurface of positive degree in `𝐏ⁿ_k`, `n ≥ 2`, is nonempty.** Its global functions
are one-dimensional over `k`, while an empty scheme has zero global functions. No `k`-rational
point is needed. -/
theorem nonempty_subscheme_zeroScheme_degreeSection (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d)
    (F : polyGrading k n d) (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0) :
    Nonempty (zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
      (twistingSheafModule (polyGrading k n) (d : ℤ))
      (degreeSection (polyGrading k n) d F)).subscheme := by
  set J := zeroScheme (AlgebraicGeometry.Proj (polyGrading k n))
    (twistingSheafModule (polyGrading k n) (d : ℤ)) (degreeSection (polyGrading k n) d F)
  by_contra h
  rw [not_nonempty_iff] at h
  let : Algebra k Γ(J.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (J.subschemeι ≫ projToSpecCoeff k n).appTop).hom.toAlgebra
  have h2 : Module.finrank k (structureSheafCohomology (J.subschemeι ≫ projToSpecCoeff k n) 0) =
      Module.finrank k Γ(J.subscheme, ⊤) :=
    finrank_structureSheafCohomology_zero_eq_finrank_globalSections k _
  rw [finrank_structureSheafCohomology_zero_zeroScheme_degreeSection k n d hn hd F hF,
    Module.finrank_zero_of_subsingleton] at h2
  exact one_ne_zero h2

end Stacks.ProjectiveSpace

end
