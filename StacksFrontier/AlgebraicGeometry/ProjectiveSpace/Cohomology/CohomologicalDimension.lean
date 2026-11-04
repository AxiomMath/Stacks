module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomological dimension of projective space

The cohomology of a quasi-coherent module on projective `n`-space over an affine base vanishes
outside the degrees `0, …, n`:
$$ H^i(\mathbf{P}^n_S, \mathcal{F}) = 0 \qquad\text{unless } 0 \le i \le n. $$

## Main results

* `Stacks.ProjectiveSpace.Cohomology.isZero_cohomology_of_lt_zero_or_dim_lt`: the vanishing
  above, which is assertion (2) of [Stacks, Tag 01YS].

## Implementation notes

**Generality.** The source states the vanishing for a *coherent* module on `ℙⁿ_R` with `R`
Noetherian. Neither hypothesis is used: the affine cover has `n + 1` members over any affine
base, and the vanishing criterion needs only quasi-coherence. The statement is therefore made
for a quasi-coherent module over an arbitrary affine base scheme `S`; since
`AlgebraicGeometry.projectiveSpaceOverRing n R` is `AlgebraicGeometry.projectiveSpaceOver n`
at `Spec R`, which is affine, the source's statement is this one with `S = Spec R`.

**Cohomology.** `H^i(X, -)` is `Stacks.Cohomology.sectionsFunctor X ⊤`, sections valued in
`Γ(X, 𝒪_X)`-modules, right derived in the `ℤ`-indexed `Functor.rightDerivedPlus`. This is the
indexing the assertion needs, since it quantifies over all integers at once, and it is the
indexing [Stacks, Tag 01XK] is stated with in this library. Tag 01XI is stated in the
`ℕ`-indexed, abelian-group-valued model `Stacks.Cohomology.Hgroup`; the passage between the two
is `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` for the index and
`CategoryTheory.Functor.rightDerivedCompIso` along the exact forgetful functor
`ModuleCat Γ(X, 𝒪_X) ⥤ AddCommGrpCat` for the coefficients, a module being zero exactly when its
underlying group is.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Cohomology

universe u

namespace Stacks.ProjectiveSpace.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The cohomological dimension of projective space**: the cohomology of a quasi-coherent
module on projective `n`-space over an affine base vanishes in every degree outside `0, …, n`. -/
@[stacks 01YS "assertion (2)", ega "III 2.2.2" "(ii), P^n case"]
theorem isZero_cohomology_of_lt_zero_or_dim_lt (n : ℕ) (S : Scheme.{u}) [IsAffine S]
    (F : (projectiveSpaceOver n S).Modules) [F.IsQuasicoherent] (i : ℤ)
    (hi : i < 0 ∨ (n : ℤ) < i) :
    IsZero (((sectionsFunctor (projectiveSpaceOver n S) ⊤).rightDerivedPlus i).obj F) := by
  rcases hi with hi | hi
  · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ i hi F
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ i by omega)
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (sectionsFunctor (projectiveSpaceOver n S) ⊤) rfl F]
  have hAb : IsZero (((sectionsFunctor (projectiveSpaceOver n S) ⊤ ⋙
      forget₂ (ModuleCat.{u} Γ(projectiveSpaceOver n S, ⊤))
        AddCommGrpCat.{u}).rightDerived k).obj F) :=
    Stacks.Cohomology.AffineCover.isZero_cohomology_of_finite_affine_cover
      (projectiveSpaceOver n S) (AlgebraicGeometry.ProjectiveSpace.standardOpen n S)
      (AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen n S)
      (AlgebraicGeometry.ProjectiveSpace.iSup_standardOpen_eq_top n S) F k (by omega)
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    (hAb.of_iso (((sectionsFunctor (projectiveSpaceOver n S) ⊤).rightDerivedCompIso
      (forget₂ (ModuleCat.{u} Γ(projectiveSpaceOver n S, ⊤)) AddCommGrpCat.{u}) k).app F).symm))

end Stacks.ProjectiveSpace.Cohomology

end
