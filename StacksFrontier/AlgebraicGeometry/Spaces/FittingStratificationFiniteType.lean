module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartDiagramsOfModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStrata
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Fitting ideals of a finite type quasi-coherent module

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be
a quasi-coherent `𝒪_X`-module of finite type, the hypotheses Stacks 0CZ9 makes on its module.
The Fitting ideal sheaves of `G` are quasi-coherent, and they cut out a decreasing chain of
closed subspaces of `X` with empty intersection. If `G` is of finite presentation, the strata of
that chain assemble into an algebraic space over `S`, as in Stacks 0CZA.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_fittingIdeal_of_isFiniteTypeOnSite`: the
  Fitting ideal sheaves of a quasi-coherent module of finite type are quasi-coherent.
* `AlgebraicGeometry.Space.exists_fittingClosedSubspaces_of_isFiniteTypeOnSite`: clause (1) of
  Stacks 0CZ9 — the decreasing chain `X ⊇ Z_0 ⊇ Z_1 ⊇ …` cut out by the Fitting ideals of `G`
  exists and its intersection is the empty algebraic subspace.
* `AlgebraicGeometry.Space.exists_fittingRankStratification_of_isFinitePresentationOnSite`: for
  `G` of finite presentation, the Fitting rank strata are disjoint locally closed subspaces
  covering `X`, and their disjoint union is an algebraic space over `S`.

## References

* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-coherence of the Fitting ideal sheaves -/

/-- **The Fitting ideal sheaves of a quasi-coherent module of finite type are
quasi-coherent.** -/
theorem isQuasicoherentOnSite_fittingIdeal_of_isFiniteTypeOnSite
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGqc : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G) (r : ℕ) :
    (fittingIdeal B S hS X.1 X.2 G r).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_fittingIdeal G
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hGqc)
    (module_finite_sections_of_isFiniteTypeOnSite G hGqc hGft) r

/-! ### The chain of Fitting closed subspaces and clause (1) of Stacks 0CZ9 -/

/-- **Clause (1) of Stacks 0CZ9.** Let `X` be an algebraic space over `S` and let `G` be a
quasi-coherent `𝒪_X`-module of finite type. Then the Fitting ideals of `G` cut out a decreasing
chain `X ⊇ Z_0 ⊇ Z_1 ⊇ …` of closed subspaces of `X`, and the intersection of that chain is the
empty algebraic subspace. -/
theorem exists_fittingClosedSubspaces_of_isFiniteTypeOnSite
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGqc : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G) :
    ∃ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) ∧
        (Antitone fun r ↦ (Z r).1) ∧
          (⨅ r : ℕ, (Z r).1) = (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) := by
  obtain ⟨Z, hZ, hanti⟩ := exists_fittingClosedSubspaces B S hS X G
    fun r ↦ isQuasicoherentOnSite_fittingIdeal_of_isFiniteTypeOnSite B S hS X G hGqc hGft r
  exact ⟨Z, hZ, hanti, iInf_fittingClosedSubspace_eq_sheafify_bot B S hS X G Z hZ
    (module_finite_sections_of_isFiniteTypeOnSite G hGqc hGft)⟩

/-! ### The Fitting rank strata of a module of finite presentation -/

/-- **Part of Stacks 0CZA.** Let `X` be an algebraic space over `S` and let `G` be a quasi-coherent
`𝒪_X`-module of finite presentation. Then there is a decreasing chain `X ⊇ Z_0 ⊇ Z_1 ⊇ …` of closed
subspaces of `X` whose defining ideal sheaves are the Fitting ideals of `G` and whose intersection
is the empty algebraic subspace, the strata `X_r = Z_{r-1} \ Z_r` are pairwise disjoint locally
closed subspaces of `X`, every point of `X` lies in exactly one stratum, and the disjoint union
`X' = ∐_{r ≥ 0} X_r` is an algebraic space over `S` whose structural morphism restricts on the
`r`-th summand to the inclusion of `X_r`. -/
theorem exists_fittingRankStratification_of_isFinitePresentationOnSite
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G) :
    ∃ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) ∧
        (Antitone fun r ↦ (Z r).1) ∧
          (⨅ r : ℕ, (Z r).1) = (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) ∧
            (∀ r : ℕ, IsLocallyClosedSubspace B S hS (fittingRankStratum B S hS X Z r)) ∧
              (∀ r s : ℕ, r ≠ s →
                  fittingRankStratum B S hS X Z r ⊓ fittingRankStratum B S hS X Z s ≤
                    (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS)) ∧
                (∀ x : points B S hS X.1, ∃! r : ℕ,
                    x ∉ Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι) ∧
                      ∀ k < r, x ∈ Set.range
                        (pointsMap B S hS (Z k).1.toFunctor (Z k).1.ι)) ∧
                  IsAlgebraicSpace B S hS (fittingRankStratification B S hS X Z).obj ∧
                    ∀ r : ℕ, Sigma.ι (fun k : ℕ ↦ fittingRankStratumSpace B S hS X Z k) r ≫
                        fittingRankStratificationHom B S hS X Z =
                      fittingRankStratumHom B S hS X Z r := by
  have hGft : SheafOfModules.IsFiniteTypeOnSite G := inferInstance
  obtain ⟨Z, hZ, hanti, hinf⟩ :=
    exists_fittingClosedSubspaces_of_isFiniteTypeOnSite B S hS X G hGqc hGft
  have hfin := module_finite_sections_of_isFiniteTypeOnSite G hGqc hGft
  refine ⟨Z, hZ, hanti, hinf,
    (isLocallyClosedSubspace_and_disjoint_fittingRankStratum B S hS X G Z hZ).1,
    (isLocallyClosedSubspace_and_disjoint_fittingRankStratum B S hS X G Z hZ).2,
    existsUnique_fittingRankStratum_index B S hS X G Z hZ hfin,
    (isAlgebraicSpace_fittingRankStratification B S hS X Z).1,
    (isAlgebraicSpace_fittingRankStratification B S hS X Z).2⟩

end AlgebraicGeometry.Space

end
