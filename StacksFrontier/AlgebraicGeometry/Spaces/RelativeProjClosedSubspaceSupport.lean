module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjChartSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A closed subspace of a relative Proj cut out in one degree, away from a quasi-compact open

Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space over `S` and `𝒜`
a quasi-coherent graded `𝒪_X`-algebra — the relative Proj situation of Stacks 0849 — and let
`π : P = Proj_X(𝒜) ⟶ X` be the relative Proj.  Stacks 085N refines Stacks 085M: for a closed
subspace `i : Z ⟶ P` of finite presentation and an open `U ⊆ |X|` which the image of `Z` misses,
the degree `d > 0` and the quasi-coherent finite type submodule `ℱ ⊆ 𝒜_d` with
`Z = Proj_X(𝒜/ℱ𝒜)` may be chosen so that the support of `𝒜_d/ℱ` is disjoint from `U`.

This file formalizes that refinement.  Its mathematical content is the **second** clause, the one
Stacks 085M does not have: the two steps by which the source transports "the support of
`𝒜_d/ℱ` misses `U`" from an affine étale chart of `X` to `X` itself; and Stacks 085N itself,
with clause (a) in the form Stacks 085M records it.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset_of_le`: **the source's step
  "`𝒜_d|_W/ℱ|_W` is a quotient of `𝒜_d|_W/ℱ'`"**, in the form this tree can state it.  Enlarging
  a submodule shrinks the support of the quotient: for `ℱ₀ ≤ ℱ` submodules of an `𝒪_X`-module
  `M`, the support of `M/ℱ` is contained in the support of `M/ℱ₀`.  Unconditional.
* `AlgebraicGeometry.Space.disjoint_supportOfSheaf_of_chart_surjective`: **the source's step
  "it suffices to check this after pulling back to `W`"**.  If an étale scheme chart `W` of `X`
  is surjective on points and the support of the restriction of a module to `W` misses the
  preimage of `U`, then the support of the module itself misses `U`.  Unconditional.
* `AlgebraicGeometry.Space.exists_finiteType_degreeSubmodule_disjoint_support`: **Stacks 085N**,
  with clause (a) as the structure
  `AlgebraicGeometry.Space.ClosedSubspaceDegreeQuotientPresentation`:
  `…RelativeProjSituation.exists_finiteType_degreeSubmodule_range_eq_quotientProj`, its range
  equality read through
  `…RelativeProjSituation.nonempty_closedSubspaceDegreeQuotientPresentation_of_range_eq`.

## Implementation notes

**The source's `i : Z \to X`.**  The statement of Stacks 085N introduces the closed subspace as
`i : Z \to X`, but its hypothesis (3) reads `|U| \cap |\pi|(|i|(|Z|)) = \emptyset`, which needs
`|i|` to land in `|P|`, and its conclusion `Z = \underline{\mathrm{Proj}}_X(\mathcal{A}/
\mathcal{F}\mathcal{A})` identifies `Z` with a closed subspace of `P`.  The standing setup of
Stacks 085L and the statement of Stacks 085M both read `i : Z \to P`.  The formalization below
reads it as `P`; with `X` in its place neither hypothesis (3) nor the conclusion is a statement.

**The support of `𝒜_d/ℱ`.**  The quotient is the categorical cokernel `cokernel ℱ.ι` of the
inclusion of the submodule, which is how the scheme case Stacks 0803,
`…RelativeProjGradedIdeal.exists_finiteType_presentation_supp_of_vanishingIdeal`, writes it as
well.  Its support is `AlgebraicGeometry.Space.supportOfSheaf` of the underlying abelian
sheaf, the support of Stacks 04KA: the set of points of `X` at which some geometric stalk is
nonzero.  This is **not** the Zariski support of a quasi-coherent module on a chart scheme, the
comparison of the two being Stacks 07TY.

**Why the first step is stated on `X` and not on the chart.**  The source argues that
`𝒜_d|_W/ℱ|_W` is a quotient of `𝒜_d|_W/ℱ'`, the two submodules living on the chart.  Stating that
here would need the restriction functor
`AlgebraicGeometry.Space.etaleModulePullback` to commute with cokernels, i.e. to be right exact;
it is `SheafOfModules.pushforward` along `AlgebraicGeometry.Space.smallEtalePostcomp`, a right
adjoint, and the cocontinuity of that functor — which is what would make it exact — is not in
this tree.  So the comparison of the two quotients is made on `X`, between a submodule `ℱ₀` of
`𝒜_d` and a larger one `ℱ`, `ℱ₀` being the submodule a chart-level argument produces.

## The statement of Stacks 085N

`AlgebraicGeometry.Space.exists_finiteType_degreeSubmodule_disjoint_support` is stated for the
relative Proj `P = Proj_X(𝒜)` itself (`…RelativeProjSituation.relativeProjFunctor`), with the
source's hypotheses: `X` quasi-compact and quasi-separated, `i : Z ⟶ P` a closed immersion of
finite presentation, `π` quasi-compact, `U` open and quasi-compact with `|U|` disjoint from the
image of `Z`, and every `𝒜_n` of finite type.  The degree `d`, the submodule `ℱ`, clause (a) and
clause (b) come from
`…RelativeProjSituation.exists_finiteType_degreeSubmodule_range_eq_quotientProj`; clause (a) is
then the structure `AlgebraicGeometry.Space.ClosedSubspaceDegreeQuotientPresentation`, its space
`Proj_X(𝒜/ℱ𝒜)` with its closed immersion `…quotientProjHom` into `P`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 085J](https://stacks.math.columbia.edu/tag/085J)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/- The abelian structure of the `𝒪_X`-modules at the universe of the schemes is Mathlib's
`SheafOfModules.instAbelian`.  `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` are global instances answering the same
goal at the enlarged module universe `max u v r w`, which cannot be the `u` of
`AlgebraicGeometry.Space.Modules.{u, u}`; left in place they are selected first and the
elaboration of the quotient `M/ℱ` dies on the universe constraint. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-! ### Enlarging a submodule shrinks the support of the quotient -/

section Quotient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Enlarging a submodule shrinks the support of the quotient.**  If `ℱ₀ ≤ ℱ` are submodules
of an `𝒪_X`-module `M`, then the support of `M/ℱ` is contained in the support of `M/ℱ₀`.

This is the step of the proof of Stacks 085N, inherited from Stacks 085M, which reads
"`𝒜_d|_W/ℱ|_W` is a quotient of `𝒜_d|_W/ℱ'`": the quotient map `M/ℱ₀ ⟶ M/ℱ` is an epimorphism,
hence locally surjective on the underlying abelian sheaves, and a surjection does not enlarge
the support by Stacks 04KB, part (5). -/
theorem supportOfSheaf_cokernel_subset_of_le {M : Modules.{u, u} B S hS X.1 X.2}
    {ℱ₀ ℱ : M.Submodule} (hle : ℱ₀ ≤ ℱ) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj (cokernel ℱ.ι)) ⊆
      supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj (cokernel ℱ₀.ι)) := by
  have hzero : ℱ₀.ι ≫ cokernel.π ℱ.ι = 0 := by
    rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_ι hle, Category.assoc,
      cokernel.condition, comp_zero]
  have hfac : cokernel.π ℱ₀.ι ≫ cokernel.desc ℱ₀.ι (cokernel.π ℱ.ι) hzero =
      cokernel.π ℱ.ι := cokernel.π_desc _ _ _
  have hcomp : Epi (cokernel.π ℱ₀.ι ≫ cokernel.desc ℱ₀.ι (cokernel.π ℱ.ι) hzero) := by
    rw [hfac]
    infer_instance
  have hepi : Epi (cokernel.desc ℱ₀.ι (cokernel.π ℱ.ι) hzero) :=
    epi_of_epi (cokernel.π ℱ₀.ι) _
  have hsurj : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map
        (cokernel.desc ℱ₀.ι (cokernel.π ℱ.ι) hzero)) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
      (cokernel.desc ℱ₀.ι (cokernel.π ℱ.ι) hzero)
  -- The local surjectivity is passed by hand: the topology carried by the structure ring sheaf
  -- is the one of the small étale ringed site, which instance search does not identify with
  -- `AlgebraicGeometry.Space.SmallEtale.topology` as the support statement spells it.
  exact @supportOfSheaf_subset_of_isLocallySurjective.{u, u} B S hS X.1 X.2 _ _
    ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map
      (cokernel.desc ℱ₀.ι (cokernel.π ℱ.ι) hzero)) hsurj

end Quotient

/-! ### Descent of a support statement along a surjective étale chart -/

section Descent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **A support statement descends along an étale scheme chart surjective on points.**  Let `W`
be an étale scheme chart of `X` whose structure morphism is surjective on points and let `U` be
a set of points of `X`.  If the support of the restriction of an `𝒪_X`-module `M` to `W` is
disjoint from the preimage of `U`, then the support of `M` is disjoint from `U`.

The support of the restriction is the preimage of the support by
`AlgebraicGeometry.Space.supportOfSheaf_chartToSpace`, so the hypothesis says that the preimage
of the intersection is empty; surjectivity turns that into emptiness of the intersection.

This is the step of the source's proof reading "`𝒜_d/ℱ` is supported on `X \ U` because
`𝒜_d|_W/ℱ|_W` is supported on `W \ U ×_X W`". -/
theorem disjoint_supportOfSheaf_of_chart_surjective (W : SmallEtale B S hS X.1)
    (hW : Function.Surjective (pointsMap B S hS (chartSpace B S hS X W).1
      (chartToSpace B S hS X W).hom))
    (M : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1))
    (hdisj : Disjoint
      (supportOfSheaf B S hS (chartSpace B S hS X W).1
        ((SheafOfModules.toSheaf
            (structureRingSheaf B S hS (chartSpace B S hS X W))).obj
          ((etaleModulePullback B S hS
            (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W)).obj M)))
      (pointsMap B S hS (chartSpace B S hS X W).1
        (chartToSpace B S hS X W).hom ⁻¹' U)) :
    Disjoint (supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj M)) U := by
  rw [Set.disjoint_left] at hdisj ⊢
  intro x hx hxU
  obtain ⟨y, rfl⟩ := hW x
  exact hdisj ((supportOfSheaf_chartToSpace B S hS X W M).symm.subset hx) hxU

end Descent

/-! ### Stacks 085N -/

section Main

variable (s : RelativeProjSituation.{u, u})

/-- **Stacks 085N.**  Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic
space over `S` and `𝒜` a quasi-coherent graded `𝒪_X`-algebra; let `π : P = Proj_X(𝒜) ⟶ X` be the
relative Proj (`…RelativeProjSituation.relativeProjFunctor`), let `i : Z ⟶ P` be a closed subspace
and let `U` be an open of `|X|`.  Assume (1) `π` quasi-compact, (2) `i` of finite presentation,
(3) `|U| ∩ |π|(|i|(|Z|)) = ∅`, (4) `U` quasi-compact and (5) every `𝒜_n` of finite type.  Then
there are a degree `d > 0` and a quasi-coherent finite type `𝒪_X`-submodule `ℱ ⊆ 𝒜_d` with
(a) `Z = Proj_X(𝒜/ℱ𝒜)` and (b) the support of `𝒜_d/ℱ` disjoint from `U`.

Clause (a) is the structure `AlgebraicGeometry.Space.ClosedSubspaceDegreeQuotientPresentation`,
the form in which Stacks 085M records the same assertion; clause (b) is disjointness from `U` of
the support of Stacks 04KA of the cokernel of `ℱ ⊆ 𝒜_d`.  This is
`…RelativeProjSituation.exists_finiteType_degreeSubmodule_range_eq_quotientProj`, whose clause (a)
is the equality of the ranges of `i` and of `Proj_X(𝒜/ℱ𝒜) ⟶ P`, read through
`…RelativeProjSituation.nonempty_closedSubspaceDegreeQuotientPresentation_of_range_eq`. -/
@[stacks 085N "the relative Proj P = Proj_X(𝒜) of Stacks 084A-084B; clause (a) as the data \
ClosedSubspaceDegreeQuotientPresentation (Z identified over P with Proj_X(𝒜/ℱ𝒜) and its closed \
immersion into P), clause (b) the disjointness from U of the support of 𝒜_d/ℱ; the closed \
subspace written i : Z → X in the source is i : Z ⟶ P, which condition (3) and clause (a) \
require"]
theorem exists_finiteType_degreeSubmodule_disjoint_support
    (hX : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase s.site.contains_terminal
      s.space.1)
    {Z : AlgebraicSpaces s.site s.base s.containsBase}
    (i : Z ⟶ (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (hfp : IsFinitePresentation s.site s.base s.containsBase i.hom)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.relativeProjFunctor s.relativeProjπ
        (pointsMap s.site s.base s.containsBase Z.1 i.hom z)))
    (hU : IsOpen U) (hUc : IsCompact U)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n)) :
    ∃ (d : ℕ) (hd : 0 < d) (ℱ : (s.algebra.piece (d : ℤ)).Submodule),
      ℱ.toSheafOfModules.IsQuasicoherentOnSite ∧
        SheafOfModules.IsFiniteType ℱ.toSheafOfModules ∧
          Nonempty (ClosedSubspaceDegreeQuotientPresentation i hd ℱ) ∧
            Disjoint (supportOfSheaf s.site s.base s.containsBase s.space.1
              ((SheafOfModules.toSheaf (structureRingSheaf s.site s.base s.containsBase
                s.space)).obj (cokernel ℱ.ι))) U := by
  obtain ⟨d, hd, ℱ, hℱ, hft, hrange, hdisj⟩ :=
    s.exists_finiteType_degreeSubmodule_range_eq_quotientProj hX hXqs i.hom hi hπ hfp hZU hU hUc hA
  exact ⟨d, hd, ℱ, hℱ, hft,
    s.nonempty_closedSubspaceDegreeQuotientPresentation_of_range_eq i hi hd ℱ hℱ hrange, hdisj⟩

end Main

end AlgebraicGeometry.Space

end
