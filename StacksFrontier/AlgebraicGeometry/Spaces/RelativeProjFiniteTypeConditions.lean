module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProj.DegreeZeroFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteOfCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjProper

/-!
# Stacks 084I on an algebraic space: the finite type conditions and properness

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra — Situation 0849.  Stacks 084I compares two ways of asking that `𝒜` be
finitely generated over the base,

1. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒜₀`-algebra;
2. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒪_X`-algebra,

asserts that they are equivalent, and asserts that under either one the structure morphism
`π : Proj_X(𝒜) ⟶ X` is proper.

## How the conditions are read

* "`𝒜₀` is a finite type `𝒪_X`-module" is `SheafOfModules.IsFiniteTypeOnSite` of the degree-zero
  piece `s.algebra.piece 0`, the library's finite type `𝒪_X`-module on the small étale site
  (Stacks 03DL (5)); no new predicate is introduced for it.
* "`𝒜` is of finite type as an `𝒜₀`-algebra", respectively "as an `𝒪_X`-algebra", are
  `AlgebraicGeometry.Space.RelativeProjSituation.IsFiniteTypeOverDegreeZero` and
  `AlgebraicGeometry.Space.RelativeProjSituation.IsFiniteTypeOverBase`: the predicates of the
  scheme case (Stacks 07ZX, 07ZY), read on the restriction `𝒜|_V` of
  `AlgebraicGeometry.Space.relativeProjChartSituation` at **every** étale scheme chart `V` of `X`.
  This is how finite type of a quasi-coherent algebra on an algebraic space is defined — étale
  locally — and it is the reading of `AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType` for
  ungraded algebras.  The library has no ungraded algebra sheaf attached to a graded
  `SheafOfModules.GradedAlgebra`, so the graded section rings of the charts are used directly.

For the degree-zero piece the chart reading is not a definition but a theorem:
`RelativeProjSituation.isFiniteTypeOnSite_iff_forall_isDegreeZeroFiniteType` identifies
`SheafOfModules.IsFiniteTypeOnSite` of `𝒜₀` with the scheme-level degree-zero condition of
Stacks 084I at every chart.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.properFiniteType_tfae_and_isProper`:
  **Stacks 084I**, both assertions in one statement, for Situation 0849.
* `AlgebraicGeometry.Space.RelativeProjSituation.properFiniteType_tfae`: the equivalence of the
  two conditions.
* `AlgebraicGeometry.Space.isProper_relativeProj_of_chart` and
  `AlgebraicGeometry.Space.isProper_relativeProj_of_chart_of_isFiniteTypeOverBase`: properness of
  `π` under condition (1), respectively (2).
* `RelativeProjSituation.isFiniteTypeOnSite_iff_forall_isDegreeZeroFiniteType`: the degree-zero
  condition read on the sheaf `𝒜₀` and read on the charts agree.

## Implementation notes

**The relative Proj enters through its chart presentation.**  Properness is stated for a
morphism `π : P ⟶ X` of algebraic spaces carrying an
`AlgebraicGeometry.Space.RelativeProjSituationChart`: a surjective étale scheme chart `V` of `X`
and the cartesian square of Stacks 084B identifying `P ×_X V` with the scheme-level relative Proj
of the restriction `𝒜|_V` — that restriction and no other.  This is the device Stacks 084E, 084F,
084G and 084H are stated with (`AlgebraicGeometry.Space.isSeparated_relativeProj_of_chart` and its
siblings), and the proof of the source uses exactly this square: it reduces properness to the case
of schemes along a surjective étale chart, Stacks 083R (4), then quotes the scheme case.  The
presentation does not occur in the conclusion.

**Properness** is separatedness, finite type and universal closedness together, which is
Stacks 03ZM.  Separatedness is Stacks 084E and needs no hypothesis on `𝒜`; finite type is
Stacks 084G, fed the finite type condition over `𝒪_X` that the equivalence supplies; universal
closedness is Stacks 084H, fed the integrality of `𝒪_X ⟶ 𝒜₀` that finiteness of `𝒜₀` supplies.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084I](https://stacks.math.columbia.edu/tag/084I)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 084G](https://stacks.math.columbia.edu/tag/084G)
* [Stacks Project, Tag 084H](https://stacks.math.columbia.edu/tag/084H)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-! ### The two algebra conditions, read on `𝒜` -/

/-- **`𝒜` is of finite type as an `𝒜₀`-algebra.**  Over every affine open of the scheme of every
étale chart `V` of `X`, the graded ring of sections of `𝒜|_V` is a finite type algebra over its
degree-zero piece.  This is the second conjunct of condition (1) of Stacks 084I. -/
def IsFiniteTypeOverDegreeZero : Prop :=
  ∀ V : SmallEtale s.site s.base s.containsBase s.space.1,
    (relativeProjChartSituationOfSituation s V).IsFiniteTypeOverDegreeZero

/-- **`𝒜` is of finite type as an `𝒪_X`-algebra.**  Over every affine open of the scheme of every
étale chart `V` of `X`, the graded ring of sections of `𝒜|_V` is a finite type algebra over the
functions on that open.  This is the second conjunct of condition (2) of Stacks 084I. -/
def IsFiniteTypeOverBase : Prop :=
  ∀ V : SmallEtale s.site s.base s.containsBase s.space.1,
    (relativeProjChartSituationOfSituation s V).IsFiniteTypeOverBase

/-! ### The degree-zero condition: on the sheaf `𝒜₀` and on the charts -/

/-- The degree-zero piece of the chart situation at `V` is the restriction of `𝒜₀` to the scheme
of `V`, read through `AlgebraicGeometry.Space.restrictToChart`. -/
theorem relativeProjChartSituation_piece_zero_eq
    (V : SmallEtale s.site s.base s.containsBase s.space.1) :
    (relativeProjChartSituationOfSituation s V).algebra.piece 0 =
      restrictToChart s.site s.base s.containsBase s.space.2 (s.algebra.piece 0) V :=
  (relativeProjChartSituationOfSituation_algebra_piece s V 0).trans
    (restrictToChart_eq_restrictToChartScheme _ _ _ _ _ _).symm

/-- **At one chart, the degree-zero condition of Stacks 084I is finite type of the restriction of
`𝒜₀`.**  For the quasi-coherent degree-zero piece of a scheme-level situation the affine-local
degree-zero condition is finite type of that piece,
`Stacks.RelativeProj.Situation.isDegreeZeroFiniteType_iff_isFiniteType`, and the degree-zero
piece of the chart situation is the restriction of `𝒜₀`,
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjChartSituation_piece_zero_eq`. -/
theorem isDegreeZeroFiniteType_chart_iff
    (V : SmallEtale s.site s.base s.containsBase s.space.1) :
    (relativeProjChartSituationOfSituation s V).IsDegreeZeroFiniteType ↔
      (restrictToChart s.site s.base s.containsBase s.space.2 (s.algebra.piece 0)
        V).IsFiniteType := by
  rw [Stacks.RelativeProj.Situation.isDegreeZeroFiniteType_iff_isFiniteType,
    relativeProjChartSituation_piece_zero_eq s V]
  exact Iff.rfl

/-- **`𝒜₀` is a finite type `𝒪_X`-module exactly when the degree-zero condition of Stacks 084I
holds at every étale chart.**  Finite type on the small étale site is finite type on charts for a
quasi-coherent module, `AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_isFiniteTypeOnCharts`, and
at each chart `AlgebraicGeometry.Space.RelativeProjSituation.isDegreeZeroFiniteType_chart_iff`
concludes. -/
theorem isFiniteTypeOnSite_iff_forall_isDegreeZeroFiniteType :
    SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0) ↔
      ∀ V : SmallEtale s.site s.base s.containsBase s.space.1,
        (relativeProjChartSituationOfSituation s V).IsDegreeZeroFiniteType :=
  (isFiniteTypeOnSite_iff_isFiniteTypeOnCharts s.site s.base s.containsBase s.space
    (s.algebra.piece 0) (s.isQuasicoherent 0)).trans
      (forall_congr' fun V => (isDegreeZeroFiniteType_chart_iff s V).symm)

/-! ### Stacks 084I, the equivalence -/

/-- **Stacks 084I, the equivalence.** For the quasi-coherent graded `𝒪_X`-algebra `𝒜` of
Situation 0849 on an algebraic space `X` the two finite type conditions are equivalent: that `𝒜₀`
is a finite type `𝒪_X`-module and `𝒜` is of finite type over `𝒜₀`, and that `𝒜₀` is a finite
type `𝒪_X`-module and `𝒜` is of finite type over `𝒪_X`.

At each étale chart this is the scheme-level `Stacks.RelativeProj.Situation.properFiniteType_tfae`:
over an affine open of the chart the implication either way is the transitivity of finite type
algebras along the tower `Γ(V, U) ⟶ 𝒜₀(U) ⟶ 𝒜(U)`. -/
theorem properFiniteType_tfae :
    List.TFAE
      [SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0) ∧ s.IsFiniteTypeOverDegreeZero,
        SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0) ∧ s.IsFiniteTypeOverBase] := by
  have hzero := (isFiniteTypeOnSite_iff_forall_isDegreeZeroFiniteType s).1
  tfae_have 1 ↔ 2 := and_congr_right fun h0 => forall_congr' fun V =>
    and_congr_right_iff.1 ((Stacks.RelativeProj.Situation.properFiniteType_tfae
      (relativeProjChartSituationOfSituation s V)).out 1 2) (hzero h0 V)
  tfae_finish

end RelativeProjSituation

/-! ### Stacks 084I, properness of the structure morphism -/

variable (s : RelativeProjSituation.{u, u})

/-- **Stacks 084I, properness under condition (1).**  In Situation 0849, if `𝒜₀` is a finite type
`𝒪_X`-module and `𝒜` is of finite type as an `𝒜₀`-algebra, the structure morphism
`π : Proj_X(𝒜) ⟶ X` is proper.

Properness is separatedness, finite type and universal closedness together, which is Stacks 03ZM:
separatedness is Stacks 084E and needs no hypothesis on `𝒜`; finite type is Stacks 084G, fed the
finite type condition over the structure sheaf that the equivalence supplies; universal closedness
is Stacks 084H, fed the integrality of `𝒪_X ⟶ 𝒜₀` that finiteness supplies.  Each is read on the
chart presentation whose chart-level situation is the restriction `𝒜|_V`. -/
theorem isProper_relativeProj_of_chart
    {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace s.site s.base s.containsBase P) (π : P ⟶ s.space.1)
    (c : RelativeProjSituationChart s π)
    (hzero : SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0))
    (hft : s.IsFiniteTypeOverDegreeZero) :
    IsProper s.site s.base s.containsBase π :=
  isProper_relativeProj s.site s.base s.containsBase hP s.space.2 π c.toChart
    ((RelativeProjSituation.isFiniteTypeOnSite_iff_forall_isDegreeZeroFiniteType s).1 hzero
      c.chart) (hft c.chart)

/-- **Stacks 084I, properness under condition (2).**  The second form of the finite type
hypothesis gives the first, by the equivalence, and then properness. -/
theorem isProper_relativeProj_of_chart_of_isFiniteTypeOverBase
    {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace s.site s.base s.containsBase P) (π : P ⟶ s.space.1)
    (c : RelativeProjSituationChart s π)
    (hzero : SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0))
    (hft : s.IsFiniteTypeOverBase) :
    IsProper s.site s.base s.containsBase π := by
  have hiff := (RelativeProjSituation.properFiniteType_tfae s).out 2 1
  exact isProper_relativeProj_of_chart s hP π c hzero (hiff.mp ⟨hzero, hft⟩).2

/-! ### Stacks 084I, the whole statement -/

namespace RelativeProjSituation

/-- **Stacks 084I.** In Situation 0849 — `X` an algebraic space over a scheme `S` and `𝒜` a
quasi-coherent graded `𝒪_X`-algebra — the following conditions are equivalent:

1. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒜₀`-algebra,
2. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒪_X`-algebra;

and if they hold, the structure morphism `π : Proj_X(𝒜) ⟶ X` is proper.

`𝒜₀` being of finite type is `SheafOfModules.IsFiniteTypeOnSite` of the degree-zero piece; the
two algebra conditions are read on the restriction of `𝒜` to every étale chart.  The relative Proj
`π : P ⟶ X` is any morphism of algebraic spaces presented, on a surjective étale chart, as the
relative Proj of the restriction of `𝒜` (Stacks 084B), which is how the source's proof reaches
the scheme case. -/
@[stacks 084I "both assertions for Situation 0849: the equivalence of the two finite-type \
conditions, with finite type of A_0 the finite type O_X-module condition on the small etale site \
and the two algebra conditions read on the restriction of A to every etale chart, and properness \
of the structure morphism of the relative Proj under them, the relative Proj entering through its \
Tag 084B chart presentation on the restriction of A"]
theorem properFiniteType_tfae_and_isProper :
    List.TFAE
        [SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0) ∧ s.IsFiniteTypeOverDegreeZero,
          SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0) ∧ s.IsFiniteTypeOverBase] ∧
      (SheafOfModules.IsFiniteTypeOnSite (s.algebra.piece 0) ∧ s.IsFiniteTypeOverDegreeZero →
        ∀ {P : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u},
          IsAlgebraicSpace s.site s.base s.containsBase P → ∀ (π : P ⟶ s.space.1),
            RelativeProjSituationChart s π → IsProper s.site s.base s.containsBase π) :=
  ⟨properFiniteType_tfae s, fun ⟨hzero, hft⟩ _ hP π c =>
    isProper_relativeProj_of_chart s hP π c hzero hft⟩

end RelativeProjSituation

end AlgebraicGeometry.Space

end
