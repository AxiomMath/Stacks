module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealZerothSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# The zeroth Fitting subspace of a finite type quasi-coherent module

Let `X` be an algebraic space over a scheme `S`, let `G` be a finite type, quasi-coherent
`𝒪_X`-module, let `Z₀ ⊆ X` be the closed subspace cut out by `Fit_0(G)` and let `Z ⊆ X` be the
scheme-theoretic support of `G`.  Then `Z ⊆ Z₀ ⊆ X` as closed subspaces,
`|Z| = |Z₀| = Supp(G)` as closed subsets of `|X|`, and `G` is the direct image of a finite type,
quasi-coherent `𝒪_{Z₀}`-module.  This is Stacks 0CZ6.

## Main results

* `AlgebraicGeometry.Space.fittingIdeal_zero_le_annihilatorIdealSheaf`: the zeroth Fitting ideal
  sheaf of `G` is contained in its annihilator ideal sheaf.
* `AlgebraicGeometry.Space.schemeTheoreticSupport_le_fittingClosedSubspace`: **Stacks 0CZ6,
  part (1).**
* `AlgebraicGeometry.Space.range_pointsMap_schemeTheoreticSupport_eq_supportOfSheaf`:
  **Stacks 0CZ6, part (2).**
* `AlgebraicGeometry.Space.exists_module_on_fittingClosedSubspace`: **Stacks 0CZ6, part (3).**

## Implementation notes

The closed subspace `Z₀` is any closed subspace whose defining ideal sheaf is `Fit_0(G)`; it
exists by `AlgebraicGeometry.Space.exists_fittingClosedSubspaces` and is unique by Stacks 03MB.
The scheme-theoretic support of Stacks 07U1 is the infimum of the closed subspaces of `X` whose
defining ideal sheaf annihilates `G`; for `G` quasi-coherent of finite type it is the closed
subspace cut out by the annihilator ideal sheaf
(`AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`).

Everything rests on the annihilation `Fit_0(G) · G = 0`
(`AlgebraicGeometry.Space.fittingIdeal_zero_smul_eq_zero`).  Part (1) reads it as membership of
`Z₀` in the family whose infimum is `Z`.  For part (2), the point set of a closed subspace is the
zero locus of its defining ideal sheaf, the support of `G` lies in the zero locus of its
annihilator, and `Fit_0(G) ⊆ Ann(G)` reverses to an inclusion of zero loci, so
`Supp(G) ⊆ |Z| ⊆ |Z₀| = Supp(G)`.  Part (3) reads the annihilation as `G` being a module over the
structure sheaf of `Z₀`, which the essential-image assertion of Stacks 04CJ part (3) for the
closed immersion `Z₀ → X` turns into the module, of finite type by Stacks 07U0 part (3).

The topology on `|X|` is the one of Stacks 03BY, `AlgebraicGeometry.Space.pointTopology`, and
the support is closed in it by Stacks 07TZ.

## References

* [Stacks Project, Tag 0CZ6](https://stacks.math.columbia.edu/tag/0CZ6)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

attribute [local instance] pointTopology

/-- **The zeroth Fitting ideal sheaf is contained in the annihilator ideal sheaf.**  A section of
`Fit_0(G)` over an étale chart restricts to a section of `Fit_0(G)` over every chart above it,
where it annihilates the sections of `G` by
`AlgebraicGeometry.Space.fittingIdeal_zero_smul_eq_zero`; that is the defining condition for
membership in the annihilator ideal. -/
theorem fittingIdeal_zero_le_annihilatorIdealSheaf
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCartesianOnAffineCharts G)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) :
    fittingIdeal B S hS X.1 X.2 G 0 ≤ annihilatorIdealSheaf B S hS X G := by
  intro U a ha W g t
  exact fittingIdeal_zero_smul_eq_zero B S hS X G hG hfin W.unop _
    ((fittingIdeal B S hS X.1 X.2 G 0).map_mem g ha) t

/-- The support of an `𝒪_X`-module lies in the zero locus of its annihilator ideal sheaf: over a
chart on which the annihilator is the unit ideal the module has only the zero section. -/
theorem supportOfSheaf_subset_idealZeroLocus_annihilatorIdealSheaf
    (G : Modules.{u, u} B S hS X.1 X.2) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) ⊆
      idealZeroLocus B S hS X (annihilatorIdealSheaf B S hS X G) :=
  supportOfSheaf_subset_idealZeroLocus_of_idealSmul_idealPow_top_eq_bot B S hS X G _ (n := 1)
    ((idealSmul_idealPow_top_eq_bot_iff B S hS X.1 X.2 _ G 1).2 fun W ↦ by
      rw [pow_one]
      exact le_bot_iff.1 (Submodule.smul_le.2 fun a ha z _ ↦ (Submodule.mem_bot _).2
        (smul_eq_zero_of_mem_annihilatorIdealAt B S hS X G (op W) a ha z)))

/-- **Stacks 0CZ6, part (1).**  Let `G` be a finite type, quasi-coherent `𝒪_X`-module, let `Z₀`
be the closed subspace of `X` cut out by `Fit_0(G)` and let `Z` be the scheme-theoretic support
of `G`.  Then `Z ⊆ Z₀ ⊆ X` as closed subspaces.

The scheme-theoretic support of Stacks 07U1 is a closed subspace by
`AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`.  It is the infimum of
the closed subspaces whose defining ideal sheaf annihilates `G`, and `Z₀` is one of them because
`Fit_0(G)` annihilates `G`. -/
@[stacks 0CZ6 "part (1)"]
theorem schemeTheoreticSupport_le_fittingClosedSubspace
    (G : Modules.{u, u} B S hS X.1 X.2) [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite G] (Z₀ : ClosedSubspaces B S hS X.1)
    (cutOut : definingIdealSheaf B S hS X Z₀ = fittingIdeal B S hS X.1 X.2 G 0) :
    IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X G) ∧
      schemeTheoreticSupport B S hS X G ≤ Z₀.1 := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G inferInstance
  have hfin := module_finite_sections_of_isFiniteTypeOnSite G inferInstance inferInstance
  obtain ⟨hZ, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X G inferInstance
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G inferInstance)
  exact ⟨hZ, sInf_le ⟨Z₀.2, (le_of_eq cutOut).trans
    (fittingIdeal_zero_le_annihilatorIdealSheaf B S hS X G hcart hfin)⟩⟩

/-- **Stacks 0CZ6, part (2).**  Let `G` be a finite type, quasi-coherent `𝒪_X`-module, let `Z₀`
be the closed subspace of `X` cut out by `Fit_0(G)` and let `Z` be the scheme-theoretic support
of `G`.  Then `|Z| = |Z₀| = Supp(G)` as closed subsets of `|X|`.

The point set of a closed subspace is the zero locus of its defining ideal sheaf
(`AlgebraicGeometry.Space.range_pointsMap_ι_eq_idealZeroLocus`); the defining ideal sheaves of
`Z` and `Z₀` are the annihilator and `Fit_0(G)`.  The support lies in the zero locus of the
annihilator, which lies in the zero locus of `Fit_0(G)` because `Fit_0(G) ⊆ Ann(G)`, and the
latter is the support by
`AlgebraicGeometry.Space.idealZeroLocus_fittingIdeal_zero_eq_supportOfSheaf`.  The support is
closed by Stacks 07TZ. -/
@[stacks 0CZ6 "part (2)", sga "7 VI 5.1" "more general"]
theorem range_pointsMap_schemeTheoreticSupport_eq_supportOfSheaf
    (G : Modules.{u, u} B S hS X.1 X.2) [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite G] (Z₀ : ClosedSubspaces B S hS X.1)
    (cutOut : definingIdealSheaf B S hS X Z₀ = fittingIdeal B S hS X.1 X.2 G 0) :
    Set.range (pointsMap B S hS (schemeTheoreticSupport B S hS X G).toFunctor
        (schemeTheoreticSupport B S hS X G).ι) =
        Set.range (pointsMap B S hS Z₀.1.toFunctor Z₀.1.ι) ∧
      Set.range (pointsMap B S hS Z₀.1.toFunctor Z₀.1.ι) =
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) ∧
      IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G)) := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G inferInstance
  have hfin := module_finite_sections_of_isFiniteTypeOnSite G inferInstance inferInstance
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X G inferInstance
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G inferInstance)
  have hZpts : Set.range (pointsMap B S hS (schemeTheoreticSupport B S hS X G).toFunctor
      (schemeTheoreticSupport B S hS X G).ι) =
        idealZeroLocus B S hS X (annihilatorIdealSheaf B S hS X G) := by
    rw [← hid]
    exact range_pointsMap_ι_eq_idealZeroLocus B S hS X ⟨_, hZ⟩
  have hZ₀pts : Set.range (pointsMap B S hS Z₀.1.toFunctor Z₀.1.ι) =
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) := by
    rw [range_pointsMap_ι_eq_idealZeroLocus B S hS X Z₀, cutOut]
    exact idealZeroLocus_fittingIdeal_zero_eq_supportOfSheaf B S hS X G hcart hfin inferInstance
  have hle : idealZeroLocus B S hS X (annihilatorIdealSheaf B S hS X G) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) := by
    rw [← hZ₀pts, range_pointsMap_ι_eq_idealZeroLocus B S hS X Z₀, cutOut]
    exact idealZeroLocus_antitone B S hS X
      (fittingIdeal_zero_le_annihilatorIdealSheaf B S hS X G hcart hfin)
  refine ⟨?_, hZ₀pts, isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 G⟩
  rw [hZpts, hZ₀pts]
  exact hle.antisymm (supportOfSheaf_subset_idealZeroLocus_annihilatorIdealSheaf B S hS X G)

/-- **Stacks 0CZ6, part (3).**  Let `G` be a finite type, quasi-coherent `𝒪_X`-module and let
`Z₀` be the closed subspace of `X` cut out by `Fit_0(G)`.  Then there is a finite type,
quasi-coherent `𝒪_{Z₀}`-module `G₀` with `(Z₀ → X)_* G₀ ≅ G`.

The ideal cutting out `Z₀` is `Fit_0(G)`, which annihilates `G`, so the essential-image assertion
of Stacks 04CJ part (3) for the closed immersion `Z₀ → X`,
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`, produces the
quasi-coherent module; it is of finite type by Stacks 07U0 part (3). -/
@[stacks 0CZ6 "part (3)"]
theorem exists_module_on_fittingClosedSubspace
    (G : Modules.{u, u} B S hS X.1 X.2) [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite G] (Z₀ : ClosedSubspaces B S hS X.1)
    (cutOut : definingIdealSheaf B S hS X Z₀ = fittingIdeal B S hS X.1 X.2 G 0) :
    ∃ G₀ : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z₀).1
        (closedSubspaceToSpace B S hS X Z₀).2,
      G₀.IsQuasicoherentOnSite ∧ SheafOfModules.IsFiniteTypeOnSite G₀ ∧
        Nonempty ((modulePushforward B S hS (closedSubspaceInclusion B S hS X Z₀)).obj G₀ ≅
          G) := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G inferInstance
  have hfin := module_finite_sections_of_isFiniteTypeOnSite G inferInstance inferInstance
  obtain ⟨G₀, hG₀, ⟨e⟩⟩ := isQuasicoherentEssImagePushforward_of_isClosedImmersion B S hS X
    (closedSubspaceInclusion B S hS X Z₀) Z₀.2.2 G inferInstance
    (annihilatedByKerIdeal_of_definingIdealSheaf_eq_fittingIdeal_zero B S hS X G hcart hfin Z₀
      cutOut)
  exact ⟨G₀, hG₀,
    isFiniteTypeOnSite_module_on_closedSubspace B S hS X G inferInstance Z₀ G₀ e, ⟨e⟩⟩

end AlgebraicGeometry.Space

end
