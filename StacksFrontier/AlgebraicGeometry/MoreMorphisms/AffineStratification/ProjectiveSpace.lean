module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CohomologyVanishingProof
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CoverBound
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial

/-!
# The affine stratification number of projective space

Let `k` be a field and let `X = ℙⁿ_k` be `n`-dimensional projective space over `k`. The affine
stratification number of `X` is exactly `n`. The upper bound is the covering bound
[Stacks, Tag 0F2W] applied to the `n + 1` standard coordinate charts of [Stacks, Tag 01NG]. The
lower bound comes from the non-vanishing of `Hⁿ(ℙⁿ_k, 𝒪(-n-1))` ([Stacks, Tag 01XT]) against the
vanishing of [Stacks, Tag 0F2Y] above the affine stratification number.

## Main results

* `AlgebraicGeometry.affineStratificationNumber_proj_le`: the upper bound.
* `AlgebraicGeometry.le_affineStratificationNumber_proj`: the lower bound.
* `AlgebraicGeometry.affineStratificationNumber_proj`: the two together, the equality.

## Implementation notes

All three statements are unconditional: the vanishing above the affine stratification number is
taken from `AlgebraicGeometry.isZero_cohomology_of_affineStratificationNumber`, the form of
[Stacks, Tag 0F2Y] that assumes nothing beyond the hypotheses of that tag.

`Stacks.ProjectiveSpace.Cohomology.twistCohomology` reads the cohomology of a twist as a module
over the coefficient ring, while the vanishing above the affine stratification number is stated
for the abelian group `Hgroup`. The two are the same right derived functor read with and without
its module structure, and `AlgebraicGeometry.isZero_twistCohomology_iff_isZero_Hgroup` records
that they vanish together.

## References

* [Stacks Project, Tag 0F2Z](https://stacks.math.columbia.edu/tag/0F2Z)
* [Stacks Project, Tag 0F2W](https://stacks.math.columbia.edu/tag/0F2W)
* [Stacks Project, Tag 0F2Y](https://stacks.math.columbia.edu/tag/0F2Y)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveCohomology Stacks.ProjectiveSpace.Cohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-! ### Projective space is nonempty and quasi-compact -/

/-- **Projective `n`-space is quasi-compact.** The `n + 1` standard coordinate opens are affine,
hence quasi-compact, and they cover. -/
theorem compactSpace_proj (R : Type u) [CommRing R] (n : ℕ) :
    CompactSpace (Proj (polyGrading R n)) := by
  refine ⟨?_⟩
  have hcov := TopologicalSpace.IsOpenCover.iSup_set_eq_univ
    (u := fun i : Fin (n + 1) => Proj.basicOpen (polyGrading R n) (MvPolynomial.X i))
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n)
  rw [← hcov]
  exact isCompact_iUnion fun i =>
    (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R i) one_pos).isCompact

/-- **Projective `n`-space over a nontrivial ring is nonempty.** A standard coordinate chart is
the spectrum of a polynomial ring in `n` variables, which has a prime ideal. -/
theorem nonempty_proj (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) :
    Nonempty (Proj (polyGrading R n)) := by
  have : Nontrivial (Stacks.ProjectiveChart.ChartRing R n (0 : Fin (n + 1))) :=
    (Stacks.ProjectiveChart.chartRingEquiv R (0 : Fin (n + 1))).symm.toEquiv.nontrivial
  obtain ⟨x⟩ : Nonempty
      (PrimeSpectrum (Stacks.ProjectiveChart.ChartRing R n (0 : Fin (n + 1)))) := inferInstance
  exact ⟨((Proj.basicOpenIsoSpec (polyGrading R n) (MvPolynomial.X (0 : Fin (n + 1)))
    (Stacks.ProjectiveChart.X_mem_degree_one R 0) one_pos).inv.base x).1⟩

/-! ### The upper bound -/

/-- **[Stacks, Tag 0F2Z], the upper bound.** The affine stratification number of `ℙⁿ_k` is at
most `n`: projective space is separated and the `n + 1` standard coordinate charts are an affine
open covering. -/
@[stacks 0F2Z "the upper bound"]
theorem affineStratificationNumber_proj_le (k : Type u) [Field k] (n : ℕ) :
    affineStratificationNumber (Proj (polyGrading k n)) ≤ n :=
  affineStratificationNumber_le_of_isOpenCover _
    (fun i : Fin (n + 1) => Proj.basicOpen (polyGrading k n) (MvPolynomial.X i))
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top k n)
    fun i => Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X k i) one_pos

/-! ### Non-vanishing in the top degree -/

/-- The constant exponent vector `(-1, …, -1)` is a degree `-n-1` Laurent monomial with every
exponent negative. -/
private theorem neg_one_mem_negativeLaurentMonomials (n : ℕ) :
    (fun _ : Fin (n + 1) => (-1 : ℤ)) ∈ negativeLaurentMonomials n (-(n + 1 : ℤ)) := by
  refine ⟨?_, fun _ => by norm_num⟩
  simp

/-- The degree `-n-1` part of `(T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹]` is nonzero: it contains the
monomial `(T₀ ⋯ Tₙ)⁻¹`. -/
private theorem nontrivial_negativeTwistPart (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) :
    Nontrivial (negativeTwistPart R n (-(n + 1 : ℤ))) := by
  have hmem : (Finsupp.single (fun _ : Fin (n + 1) => (-1 : ℤ)) (1 : R)) ∈
      negativeTwistPart R n (-(n + 1 : ℤ)) := by
    change _ ∈ Finsupp.supported R R (negativeLaurentMonomials n (-(n + 1 : ℤ)))
    rw [Finsupp.mem_supported]
    intro x hx
    have hx' : x ∈ ({(fun _ : Fin (n + 1) => (-1 : ℤ))} : Finset (Fin (n + 1) → ℤ)) :=
      Finsupp.support_single_subset (Finset.mem_coe.mp hx)
    rw [Finset.mem_singleton] at hx'
    rw [hx']
    exact neg_one_mem_negativeLaurentMonomials n
  refine ⟨⟨⟨_, hmem⟩, 0, ?_⟩⟩
  simp only [ne_eq, Submodule.mk_eq_zero]
  exact Finsupp.single_ne_zero.2 one_ne_zero

/-- **`Hⁿ(ℙⁿ_k, 𝒪(-n-1))` is nonzero** for every field `k`: by [Stacks, Tag 01XT] it is the free
module on the degree `-n-1` Laurent monomials with every exponent negative, and `(T₀ ⋯ Tₙ)⁻¹` is
one of them. -/
theorem not_isZero_twistCohomology_top (k : Type u) [Field k] (n : ℕ) :
    ¬ IsZero (twistCohomology k n (-(n + 1 : ℤ)) n) := by
  intro h
  have hd : (-(n + 1 : ℤ)) < 0 := by omega
  have hz := (twistCohomologyIsoNegative k n (-(n + 1 : ℤ)) hd).isZero_iff.mp h
  have := nontrivial_negativeTwistPart k n
  exact not_subsingleton _ (ModuleCat.subsingleton_of_isZero hz)

/-! ### The two readings of the cohomology of a twist -/

/-- **The two readings of `H^q(ℙⁿ_R, 𝒪(d))` vanish together.**
`Stacks.ProjectiveSpace.Cohomology.twistCohomology` is the derived sections of the twisting
sheaf as a module over the coefficient ring, and `Hgroup` is the same derived functor with its
module structure forgotten. -/
theorem isZero_twistCohomology_iff_isZero_Hgroup (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (q : ℕ) :
    IsZero (twistCohomology R n d q) ↔
      IsZero (Hgroup (Proj (polyGrading R n)).ringCatSheaf ⊤ q
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) := by
  have e := (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
    (Proj (polyGrading R n)).ringCatSheaf (⊤ : (Proj (polyGrading R n)).Opens) q).app
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
  rw [← e.isZero_iff, ModuleCat.isZero_iff_subsingleton,
    AddCommGrpCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-! ### The lower bound and the equality -/

/-- **[Stacks, Tag 0F2Z], the lower bound.** The affine stratification number of `ℙⁿ_k` is at
least `n`: `Hⁿ(ℙⁿ_k, 𝒪(-n-1))` is nonzero, while [Stacks, Tag 0F2Y] makes the cohomology of a
quasi-coherent module vanish above the affine stratification number. -/
@[stacks 0F2Z "the lower bound"]
theorem le_affineStratificationNumber_proj (k : Type u) [Field k] (n : ℕ) :
    n ≤ affineStratificationNumber (Proj (polyGrading k n)) := by
  by_contra hlt
  rw [not_le] at hlt
  have hvanish := @isZero_cohomology_of_affineStratificationNumber
    (Proj (polyGrading k n)) (nonempty_proj k n) (compactSpace_proj k n) inferInstance
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) (-(n + 1 : ℤ)))
    (isQuasicoherent_twistingSheaf k n (-(n + 1 : ℤ))) n hlt
  exact not_isZero_twistCohomology_top k n
    ((isZero_twistCohomology_iff_isZero_Hgroup k n (-(n + 1 : ℤ)) n).2 hvanish)

/-- **[Stacks, Tag 0F2Z].** The affine stratification number of `n`-dimensional projective space
over a field is exactly `n`. -/
@[stacks 0F2Z "the equality"]
theorem affineStratificationNumber_proj (k : Type u) [Field k] (n : ℕ) :
    affineStratificationNumber (Proj (polyGrading k n)) = n :=
  le_antisymm (affineStratificationNumber_proj_le k n)
    (le_affineStratificationNumber_proj k n)

end AlgebraicGeometry

end
