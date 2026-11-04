module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Diagonal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The collinearity equations put the third point on the line through the first two

Let `V` be a vector space over a field `k`. A point `t` of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` lies in the
collinearity locus when every determinant section vanishes at it. This file turns that condition
into the linear-algebra statement the dimension theory of the incidence variety consumes:

the degree-one forms vanishing at the first two points of `t` all vanish at the third,

that is `lineSubmodule k V (pr₁ t) (pr₂ t) ≤ pointSubmodule k V (pr₃ t)`, as soon as neither of
the first two submodules of degree-one equations contains the other.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_basicOpen_chartRatio_iff`: a chart ratio
  `prᵢ^♯ (ι v / ι u)` is a unit at a point of the chart exactly when `v` is *not* a degree-one
  equation of the `i`-th projection of that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartResidue_chartRatio_eq_zero_iff`: **the chart
  dictionary.** The same, read as the vanishing of the residue of that ratio at the point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_inf_le_pointSubmodule_of_collinear`:
  **the core.** For a collinear triple whose first two submodules of degree-one equations are
  incomparable, the degree-one forms vanishing at the first two points vanish at the third.

The form for a triple whose first two points are closed points of `𝐏(V)` over an algebraically
closed field — where incomparability is just their being distinct, the two submodules being
hyperplanes — is where the dimension bound uses this, and it is carried out inside
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_collinearLocus_inter_le_one` of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreDimension`.

## Implementation notes

The chart dictionary is `AlgebraicGeometry.Scheme.Modules.mem_basicOpen_iff_of_smul_eq` — the
ratio `ι v / ι u` is a unit at a point of the chart exactly where `ι v / 1` is nonvanishing —
composed with `Stacks.SheafOfModules.nonvanishingLocus` of a pulled-back tautological section
being the preimage of the nonvanishing locus, and with
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_tautologicalSection_iff`, which
reads the latter as the standard open `D₊(ι v)`. The hypothesis of
`mem_basicOpen_iff_of_smul_eq` is the defining property
`Stacks.SheafOfModules.smul_divBySection` of the ratio, transported along
`AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_tautologicalPullbackSection`.

**No linearity of the chart coordinate is needed.** The determinant
`AlgebraicGeometry.ProjectiveSpaceOfModule.det_residue_chartMatrix_eq_zero` is evaluated at the
single triple of vectors `(a, b, v)`, where `a` is a degree-one equation of the first point and
not of the second, `b` the other way round, and `v` an equation of both. Four of the nine entries
of the residue matrix then vanish by the dictionary, the `3 × 3` expansion collapses to
`- (ι b / ι u₀)(ι a / ι u₁)(ι v / ι u₂)` and the first two factors are nonzero, so the third
vanishes — which by the dictionary again says that `v` is an equation of the third point. So the
chart coordinate is used only through the *vanishing* of its values, and neither its additivity
nor its homogeneity — which are not available in the `Stacks.SheafOfModules.divBySection`
spelling, see the implementation notes of
`StacksDraft.AlgebraicGeometry.IncidenceDistinctPairs.ChartFunctional` — is required.

Incomparability of the two submodules of degree-one equations, and not merely their being
distinct, is what the argument needs, and it is what the application has: over an algebraically
closed field the degree-one equations of a closed point form a hyperplane
(`AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_pointSubmodule`), two distinct
hyperplanes are incomparable, and distinctness of the submodules follows from distinctness of the
points by `AlgebraicGeometry.ProjectiveSpaceOfModule.eq_of_pointSubmodule_eq`. For non-closed
points it can genuinely fail — the generic point of a plane and the generic point of a conic in
it both have no degree-one equations at all — and then the conclusion fails with it, the fibre of
the collinearity locus over such a pair being the whole plane and not a line. That is why the
fibre bound of Tag 0B1R is taken over the *closed* points of the base, with
`AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton` restoring it everywhere.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The chart dictionary -/

/-- **A chart ratio is a unit at a point of the chart exactly when its numerator is not a
degree-one equation of the projected point.** -/
public theorem mem_basicOpen_chartRatio_iff
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {t : prodThree k V} (ht : t ∈ U) :
    t ∈ (prodThree k V).basicOpen (chartRatio k V f u v hU) ↔
      v ∉ pointSubmodule k V (f.base t) := by
  set M := (Scheme.Modules.pullback f).obj (tautologicalModule k V)
  have hfr : U ≤ nonvanishingOpen M (tautologicalPullbackSection k V f u) :=
    le_nonvanishingOpen_tautologicalPullbackSection k V f u hU
  have htop : ∀ v' : V, sectionsOfTop M
      ((tautologicalPullbackSection k V f v').eval (op ⊤)) =
      tautologicalPullbackSection k V f v' := fun v' => sectionsOfTop_eval_top_self _ _
  have hh : chartRatio k V f u v hU •
      (sectionsOfTop M ((tautologicalPullbackSection k V f u).eval (op ⊤))).eval (op U) =
      (sectionsOfTop M ((tautologicalPullbackSection k V f v).eval (op ⊤))).eval (op U) := by
    rw [htop u, htop v, ← divBySection_tautologicalPullbackSection k V f u v hU]
    exact smul_divBySection M (tautologicalPullbackSection k V f u) hfr
      ((tautologicalPullbackSection k V f v).eval (op U))
  have hb := Scheme.Modules.mem_basicOpen_iff_of_smul_eq M U
    ((tautologicalPullbackSection k V f v).eval (op ⊤))
    ((tautologicalPullbackSection k V f u).eval (op ⊤))
    (by rwa [htop u]) (chartRatio k V f u v hU) hh ht
  have hset : t ∈ nonvanishingOpen M (tautologicalPullbackSection k V f v) ↔
      f.base t ∈ nonvanishingLocus (X := (projectiveSpaceOfModule k V).toRingedSpace)
        (tautologicalModule k V) (tautologicalSection k V v) :=
    Iff.of_eq (congrArg (fun S : Set (prodThree k V) => t ∈ S)
      (nonvanishingLocus_tautologicalPullbackSection k V f v))
  rw [htop v] at hb
  rw [hb, hset, mem_nonvanishingLocus_tautologicalSection_iff, mem_pointSubmodule_iff]

/-- The residue map at a point of a chart: the germ there, followed by the residue of the local
ring. This is the ring homomorphism the chart description of the collinearity equations is read
through. -/
public def chartResidue {U : (prodThree k V).Opens} {t : prodThree k V} (ht : t ∈ U) :
    Γ(prodThree k V, U) →+* IsLocalRing.ResidueField ((prodThree k V).presheaf.stalk t) :=
  (IsLocalRing.residue ((prodThree k V).presheaf.stalk t)).comp
    ((prodThree k V).presheaf.germ U t ht).hom

/-- **The chart dictionary.** On a chart the residue at a point of the ratio `prᵢ^♯ (ι v / ι u)`
vanishes exactly when `v` is a degree-one equation of the `i`-th projection of that point. -/
public theorem chartResidue_chartRatio_eq_zero_iff
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {t : prodThree k V} (ht : t ∈ U) :
    chartResidue k V ht (chartRatio k V f u v hU) = 0 ↔
      v ∈ pointSubmodule k V (f.base t) := by
  rw [chartResidue, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← (prodThree k V).mem_basicOpen _ t ht,
    not_iff_comm, mem_basicOpen_chartRatio_iff k V f u v hU ht]

/-! ### The core -/

/-- **The degree-one forms vanishing at the first two points of a collinear triple vanish at the
third**, as soon as neither of the first two submodules of degree-one equations contains the
other. -/
@[sga "7 XVII 2.1" "partial"]
public theorem pointSubmodule_inf_le_pointSubmodule_of_collinear {t : prodThree k V}
    (ht : t ∈ collinearLocus k V)
    (ha : ∃ a ∈ pointSubmodule k V ((pr₁ k V).base t), a ∉ pointSubmodule k V ((pr₂ k V).base t))
    (hb : ∃ b ∈ pointSubmodule k V ((pr₂ k V).base t), b ∉ pointSubmodule k V ((pr₁ k V).base t)) :
    pointSubmodule k V ((pr₁ k V).base t) ⊓ pointSubmodule k V ((pr₂ k V).base t) ≤
      pointSubmodule k V ((pr₃ k V).base t) := by
  obtain ⟨a, ha₁, ha₂⟩ := ha
  obtain ⟨b, hb₂, hb₁⟩ := hb
  intro v hv
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.mp hv
  -- a chart around `t`: a vector outside the degree-one equations of each projection
  obtain ⟨u₀, hu₀⟩ := exists_ι_notMem k V ((pr₁ k V).base t)
  obtain ⟨u₁, hu₁⟩ := exists_ι_notMem k V ((pr₂ k V).base t)
  obtain ⟨u₂, hu₂⟩ := exists_ι_notMem k V ((pr₃ k V).base t)
  set u : Fin 3 → V := ![u₀, u₁, u₂]
  set D₁ : (prodThree k V).Opens :=
    pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 0))
  set D₂ : (prodThree k V).Opens :=
    pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 1))
  set D₃ : (prodThree k V).Opens :=
    pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 2))
  set U : (prodThree k V).Opens := D₁ ⊓ D₂ ⊓ D₃
  have h₁ : U ≤ D₁ := inf_le_left.trans inf_le_left
  have h₂ : U ≤ D₂ := inf_le_left.trans inf_le_right
  have h₃ : U ≤ D₃ := inf_le_right
  have hx : t ∈ U :=
    ⟨⟨(mem_nonvanishingLocus_tautologicalSection_iff k V u₀ _).mpr hu₀,
      (mem_nonvanishingLocus_tautologicalSection_iff k V u₁ _).mpr hu₁⟩,
      (mem_nonvanishingLocus_tautologicalSection_iff k V u₂ _).mpr hu₂⟩
  -- the determinant of the residue matrix at the triple of vectors `(a, b, v)`
  set w : Fin 3 → V := ![a, b, v]
  set M := (chartMatrix k V u w h₁ h₂ h₃).map (chartResidue k V hx)
  have hdet : M.det = 0 := det_residue_chartMatrix_eq_zero k V u w h₁ h₂ h₃ hx ht
  -- the dictionary at each of the six entries that matter
  have e00 : M 0 0 = 0 :=
    (chartResidue_chartRatio_eq_zero_iff k V (pr₁ k V) (u 0) (w 0) h₁ hx).mpr ha₁
  have e02 : M 0 2 = 0 :=
    (chartResidue_chartRatio_eq_zero_iff k V (pr₁ k V) (u 0) (w 2) h₁ hx).mpr hv₁
  have e11 : M 1 1 = 0 :=
    (chartResidue_chartRatio_eq_zero_iff k V (pr₂ k V) (u 1) (w 1) h₂ hx).mpr hb₂
  have e12 : M 1 2 = 0 :=
    (chartResidue_chartRatio_eq_zero_iff k V (pr₂ k V) (u 1) (w 2) h₂ hx).mpr hv₂
  have e01 : M 0 1 ≠ 0 := fun h =>
    hb₁ ((chartResidue_chartRatio_eq_zero_iff k V (pr₁ k V) (u 0) (w 1) h₁ hx).mp h)
  have e10 : M 1 0 ≠ 0 := fun h =>
    ha₂ ((chartResidue_chartRatio_eq_zero_iff k V (pr₂ k V) (u 1) (w 0) h₂ hx).mp h)
  -- the expansion collapses to the single product
  rw [Matrix.det_fin_three, e00, e02, e11, e12] at hdet
  have hprod : M 0 1 * M 1 0 * M 2 2 = 0 := by linear_combination -hdet
  exact (chartResidue_chartRatio_eq_zero_iff k V (pr₃ k V) (u 2) (w 2) h₃ hx).mp
    ((mul_eq_zero.mp hprod).resolve_left (mul_ne_zero e01 e10))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
