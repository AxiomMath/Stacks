module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentGradedPiece
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The standard charts of projective space over a base scheme are affine over the base

Let `S` be a scheme and `n` a natural number. Projective `n`-space `ℙⁿ_S` over `S` is the base
change of the integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` along `S ⟶ Spec ℤ`, with structure
morphism the first projection and with `AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse`
the second.

A homogeneous `t` of positive degree in `ℤ[T₀, …, Tₙ]` cuts out the standard open `D₊(t)` of the
integral model, which is affine, and its preimage in `ℙⁿ_S` is the chart it determines there. The
open immersion of that chart into `ℙⁿ_S` is an affine morphism, and the chart is affine over `S`.

Taking `t` to be the product `∏_{i ∈ s} Tᵢ` of the variables indexed by a nonempty finite set `s`
gives the intersection of the coordinate charts indexed by `s`, so the two statements cover the
coordinate charts and all their nonempty finite intersections at once. The coordinate charts,
indexed by `Fin (n + 1)`, cover `ℙⁿ_S`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.standardOpen`: the standard open `D₊(t)` of the
  integral model of projective space.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.chart`: the chart of `ℙⁿ_S` determined by `t`,
  the preimage of `D₊(t)` under the projection to the integral model.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.coordChart`: the `i`-th coordinate chart, the
  locus where the `i`-th variable does not vanish.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.interChart`: the intersection of the coordinate
  charts indexed by a finite set, as the chart of the product of the corresponding variables.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.chartCover`: the open cover of `ℙⁿ_S` by the
  `n + 1` coordinate charts.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.isAffineHom_chart_ι`: the chart determined by a
  homogeneous `t` of positive degree is an affine open subscheme of `ℙⁿ_S`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.isAffineHom_chart_structureMorphism`: that chart
  is affine over `S`.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.isAffineHom_interChart_ι` and
  `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.isAffineHom_interChart_structureMorphism`: the
  same two statements for every nonempty finite intersection of coordinate charts.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.interChart_eq_iInf`: that chart really is the
  intersection of the coordinate charts it is named by.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceCharts.iSup_coordChart_eq_top`: the coordinate charts
  cover `ℙⁿ_S`.

## Implementation notes

`AlgebraicGeometry.projectiveSpaceAtUniverse` is a plain definition whose body is `Proj` of the
total-degree grading of `ULift ℤ[T₀, …, Tₙ]`, so a term about `Proj` of that grading is accepted
for a goal about the integral model only at default transparency, and instance search does not see
through it; `isSeparated_projectiveSpaceAtUniverse` transports Mathlib's separatedness of `Proj`
across that definition once, as a local instance.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.ProjectiveSpace.Cohomology (chartDenom)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceCharts

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Affine opens of a separated scheme -/

/-- A morphism from an affine scheme, composed with the map to the terminal scheme, is affine. -/
private theorem isAffineHom_comp_terminal_from {U X : Scheme.{u}} [IsAffine U] (f : U ⟶ X) :
    IsAffineHom (f ≫ terminal.from X) := by
  rw [show f ≫ terminal.from X = terminal.from U from terminal.hom_ext _ _]
  infer_instance

/-- **The inclusion of an affine open of a separated scheme is an affine morphism.** -/
@[sga "6 II 2.2.6"]
theorem isAffineHom_ι_of_isAffineOpen {X : Scheme.{u}} [X.IsSeparated] {U : X.Opens}
    (hU : IsAffineOpen U) : IsAffineHom U.ι := by
  have : IsAffine U.toScheme := hU
  refine MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated)
    U.ι (terminal.from X) inferInstance (isAffineHom_comp_terminal_from _)

/-! ### The standard opens of the integral model -/

/-- **The integral model of projective space is separated.** -/
theorem isSeparated_projectiveSpaceAtUniverse (n : ℕ) :
    Scheme.IsSeparated (projectiveSpaceAtUniverse.{u} n) :=
  inferInstanceAs
    (Scheme.IsSeparated (AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) n)))

attribute [local instance] isSeparated_projectiveSpaceAtUniverse

/-- The standard open `D₊(t)` of the integral model of projective `n`-space, the locus where the
homogeneous polynomial `t` does not vanish. -/
def standardOpen (n : ℕ) (t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :
    (projectiveSpaceAtUniverse.{u} n).Opens :=
  AlgebraicGeometry.Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) t

/-- **A standard open of the integral model of a homogeneous polynomial of positive degree is an
affine open.** -/
theorem isAffineOpen_standardOpen (n : ℕ) {t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)} {m : ℕ}
    (ht : t ∈ polyGrading (ULift.{u} ℤ) n m) (hm : 0 < m) :
    IsAffineOpen (standardOpen.{u} n t) :=
  AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ t ht hm

/-- **The inclusion of a standard open of the integral model is an affine morphism.** -/
theorem isAffineHom_standardOpen_ι (n : ℕ) {t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)} {m : ℕ}
    (ht : t ∈ polyGrading (ULift.{u} ℤ) n m) (hm : 0 < m) :
    IsAffineHom (standardOpen.{u} n t).ι :=
  isAffineHom_ι_of_isAffineOpen (isAffineOpen_standardOpen n ht hm)

/-- **A standard open of the integral model is affine over the terminal scheme.** -/
theorem isAffineHom_standardOpen_terminal (n : ℕ)
    {t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)} {m : ℕ}
    (ht : t ∈ polyGrading (ULift.{u} ℤ) n m) (hm : 0 < m) :
    IsAffineHom ((standardOpen.{u} n t).ι ≫ terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  have : IsAffine (standardOpen.{u} n t).toScheme := isAffineOpen_standardOpen n ht hm
  exact isAffineHom_comp_terminal_from _

/-- The standard open of a product of variables is the intersection of the standard opens of the
variables. -/
theorem standardOpen_prod (n : ℕ) (s : Finset (Fin (n + 1))) :
    standardOpen.{u} n (∏ i ∈ s, MvPolynomial.X i) =
      ⨅ i ∈ s, standardOpen.{u} n (MvPolynomial.X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₁ : standardOpen.{u} n (∏ i ∈ (∅ : Finset (Fin (n + 1))), MvPolynomial.X i) = ⊤ := by
      rw [Finset.prod_empty]
      exact AlgebraicGeometry.Proj.basicOpen_one _
    have h₂ : (⨅ i ∈ (∅ : Finset (Fin (n + 1))), standardOpen.{u} n (MvPolynomial.X i)) = ⊤ :=
      le_antisymm le_top (le_iInf fun i => le_iInf fun hi => by simp at hi)
    rw [h₁, h₂]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.iInf_insert, ← ih]
    exact AlgebraicGeometry.Proj.basicOpen_mul _ _ _

/-- The product `∏_{i ∈ s} Tᵢ` of the variables indexed by `s` is homogeneous of degree the
cardinality of `s`. -/
theorem chartDenom_mem (R : Type u) [CommRing R] (n : ℕ) (s : Finset (Fin (n + 1))) :
    chartDenom R n s ∈ polyGrading R n s.card := by
  have h : (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)).IsHomogeneous
      (∑ _i ∈ s, 1) :=
    MvPolynomial.IsHomogeneous.prod s _ _ fun i _ => MvPolynomial.isHomogeneous_X R i
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 h

/-! ### The charts of projective space over a base scheme -/

variable (n : ℕ) (S : Scheme.{u})

/-- The chart of `ℙⁿ_S` determined by a homogeneous polynomial `t`: the preimage of the standard
open `D₊(t)` of the integral model under the projection to the integral model. -/
def chart (t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) : (projectiveSpaceOver n S).Opens :=
  projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ standardOpen.{u} n t

/-- **A chart of `ℙⁿ_S` is the base change of the corresponding standard open of the integral
model.** -/
theorem isPullback_chart (t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :
    IsPullback (projectiveSpaceOver.toIntegralAtUniverse n S ∣_ standardOpen.{u} n t)
      (chart n S t).ι (standardOpen.{u} n t).ι
      (projectiveSpaceOver.toIntegralAtUniverse n S) :=
  isPullback_morphismRestrict _ _

/-- **A chart of `ℙⁿ_S`, over the base `S`, is the base change of the corresponding standard open
of the integral model over the terminal scheme.** -/
theorem isPullback_chart_structureMorphism (t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :
    IsPullback (projectiveSpaceOver.toIntegralAtUniverse n S ∣_ standardOpen.{u} n t)
      ((chart n S t).ι ≫ (projectiveSpaceOver n S ↘ S))
      ((standardOpen.{u} n t).ι ≫ terminal.from (projectiveSpaceAtUniverse.{u} n))
      (terminal.from S) :=
  (isPullback_chart n S t).paste_vert
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip

/-- **The open immersion of a chart of `ℙⁿ_S` into `ℙⁿ_S` is an affine morphism**, for the chart
determined by a homogeneous polynomial of positive degree. -/
theorem isAffineHom_chart_ι {t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)} {m : ℕ}
    (ht : t ∈ polyGrading (ULift.{u} ℤ) n m) (hm : 0 < m) :
    IsAffineHom (chart n S t).ι :=
  MorphismProperty.of_isPullback (isPullback_chart n S t)
    (isAffineHom_standardOpen_ι n ht hm)

/-- **A chart of `ℙⁿ_S` is affine over `S`**, for the chart determined by a homogeneous polynomial
of positive degree. -/
theorem isAffineHom_chart_structureMorphism {t : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)} {m : ℕ}
    (ht : t ∈ polyGrading (ULift.{u} ℤ) n m) (hm : 0 < m) :
    IsAffineHom ((chart n S t).ι ≫ (projectiveSpaceOver n S ↘ S)) :=
  MorphismProperty.of_isPullback (isPullback_chart_structureMorphism n S t)
    (isAffineHom_standardOpen_terminal n ht hm)

/-! ### The coordinate charts and their intersections -/

/-- The `i`-th coordinate chart of `ℙⁿ_S`: the locus where the `i`-th homogeneous coordinate does
not vanish. -/
def coordChart (i : Fin (n + 1)) : (projectiveSpaceOver n S).Opens :=
  chart n S (MvPolynomial.X i)

/-- The intersection of the coordinate charts of `ℙⁿ_S` indexed by a finite set `s`, presented as
the chart of the product `∏_{i ∈ s} Tᵢ` of the corresponding variables. -/
def interChart (s : Finset (Fin (n + 1))) : (projectiveSpaceOver n S).Opens :=
  chart n S (chartDenom (ULift.{u} ℤ) n s)

/-- Preimages commute with the intersection of a finite family of opens. -/
theorem preimage_iInf_finset {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (s : Finset ι)
    (U : ι → Y.Opens) : f ⁻¹ᵁ (⨅ i ∈ s, U i) = ⨅ i ∈ s, f ⁻¹ᵁ U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.iInf_insert, Finset.iInf_insert, ← ih]; rfl

/-- **The chart named by a finite set of indices is the intersection of the corresponding
coordinate charts.** -/
theorem interChart_eq_iInf (s : Finset (Fin (n + 1))) :
    interChart n S s = ⨅ i ∈ s, coordChart n S i := by
  rw [interChart, show chartDenom (ULift.{u} ℤ) n s = ∏ i ∈ s, MvPolynomial.X i from rfl,
    chart, standardOpen_prod, preimage_iInf_finset]
  rfl

/-- The coordinate chart of an index is the chart named by the corresponding singleton. -/
theorem coordChart_eq_interChart_singleton (i : Fin (n + 1)) :
    coordChart n S i = interChart n S {i} := by
  rw [coordChart, interChart, show chartDenom (ULift.{u} ℤ) n {i} =
    ∏ j ∈ ({i} : Finset (Fin (n + 1))), MvPolynomial.X j from rfl,
    Finset.prod_singleton]

/-- **The open immersion of a nonempty finite intersection of coordinate charts into `ℙⁿ_S` is an
affine morphism.** -/
theorem isAffineHom_interChart_ι {s : Finset (Fin (n + 1))} (hs : s.Nonempty) :
    IsAffineHom (interChart n S s).ι :=
  isAffineHom_chart_ι n S (chartDenom_mem (ULift.{u} ℤ) n s) (Finset.card_pos.2 hs)

/-- **A nonempty finite intersection of coordinate charts is affine over `S`.** -/
theorem isAffineHom_interChart_structureMorphism {s : Finset (Fin (n + 1))} (hs : s.Nonempty) :
    IsAffineHom ((interChart n S s).ι ≫ (projectiveSpaceOver n S ↘ S)) :=
  isAffineHom_chart_structureMorphism n S (chartDenom_mem (ULift.{u} ℤ) n s)
    (Finset.card_pos.2 hs)

/-- **The open immersion of a coordinate chart into `ℙⁿ_S` is an affine morphism.** -/
theorem isAffineHom_coordChart_ι (i : Fin (n + 1)) : IsAffineHom (coordChart n S i).ι :=
  isAffineHom_chart_ι n S (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one _ n i) Nat.one_pos

/-- **A coordinate chart is affine over `S`.** -/
theorem isAffineHom_coordChart_structureMorphism (i : Fin (n + 1)) :
    IsAffineHom ((coordChart n S i).ι ≫ (projectiveSpaceOver n S ↘ S)) :=
  isAffineHom_chart_structureMorphism n S
    (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one _ n i) Nat.one_pos

/-! ### The coordinate charts cover projective space -/

/-- **The coordinate charts cover `ℙⁿ_S`.** -/
theorem iSup_coordChart_eq_top : (⨆ i, coordChart n S i) = ⊤ :=
  (projectiveSpaceOver.toIntegralAtUniverse n S).iSup_preimage_eq_top
    (Stacks.AlgebraicGeometry.ProjPolyChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n)

/-! ### The coordinate charts as the standard opens of `ℙⁿ_S`

The coordinate chart `coordChart n S i` is, by unfolding, the standard open
`AlgebraicGeometry.ProjectiveSpace.standardOpen n S i`; the name `standardOpen` is taken in this
file by the standard open of the integral model, so the results about the imported one are named
`standardOpenOver`. -/

/-- **The `i`-th coordinate chart is the standard open
`AlgebraicGeometry.ProjectiveSpace.standardOpen n S i`.** -/
theorem coordChart_eq_standardOpen (i : Fin (n + 1)) :
    coordChart n S i = AlgebraicGeometry.ProjectiveSpace.standardOpen n S i :=
  rfl

/-- **The standard open of a variable is the intersection chart of the singleton.** -/
theorem standardOpenOver_eq_interChart_singleton (i : Fin (n + 1)) :
    AlgebraicGeometry.ProjectiveSpace.standardOpen n S i = interChart n S {i} :=
  coordChart_eq_interChart_singleton n S i

/-- **The inclusion of the standard open of a variable is affine**, with no affineness
hypothesis on the base. -/
theorem isAffineHom_standardOpenOver_ι (i : Fin (n + 1)) :
    IsAffineHom (AlgebraicGeometry.ProjectiveSpace.standardOpen n S i).ι :=
  isAffineHom_coordChart_ι n S i

/-- **The standard open of a variable is affine over `S`**, with no affineness hypothesis on the
base. -/
theorem isAffineHom_standardOpenOver_structureMorphism (i : Fin (n + 1)) :
    IsAffineHom ((AlgebraicGeometry.ProjectiveSpace.standardOpen n S i).ι ≫
      (projectiveSpaceOver n S ↘ S)) :=
  isAffineHom_coordChart_structureMorphism n S i

/-- **The open cover of `ℙⁿ_S` by its `n + 1` coordinate charts.** -/
def chartCover : (projectiveSpaceOver n S).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1)) (fun i => (coordChart n S i).toScheme)
    (fun i => (coordChart n S i).ι) fun x => by
      have hx : x ∈ ⨆ i, coordChart n S i := by rw [iSup_coordChart_eq_top]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (coordChart n S i)).ge hi
      exact ⟨i, y, hy⟩

/-- The index set of `chartCover n S` is `Fin (n + 1)`. -/
@[simp] theorem chartCover_I₀ : (chartCover n S).I₀ = Fin (n + 1) := rfl

/-- The `i`-th member of `chartCover n S` is the coordinate chart `coordChart n S i`. -/
@[simp] theorem chartCover_X (i : Fin (n + 1)) :
    (chartCover n S).X i = (coordChart n S i).toScheme := rfl

/-- The `i`-th map of `chartCover n S` is the open immersion `(coordChart n S i).ι`. -/
@[simp] theorem chartCover_f (i : Fin (n + 1)) :
    (chartCover n S).f i = (coordChart n S i).ι := rfl

end Stacks.AlgebraicGeometry.ProjectiveSpaceCharts

end
