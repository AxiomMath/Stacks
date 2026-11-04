module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapChartwiseVanishing

/-!
# The finite-presentation clause of Stacks 083K

Let `S = \Spec(R)` be an affine scheme of a big fppf site, let `X` be an algebraic space over
`S` and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S`
(Stacks 0CWA).  Assume `ℱ` is of finite type with quasi-compact scheme theoretic support.
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_specQuotient` produces, out
of the vanishing of the base change of `u` to a test object `T`, a **finitely generated** ideal
`J ⊆ R` cutting out a closed subscheme `Z = \Spec(R/J) ⊆ S` which is of finite presentation over
`S` and through which `T ⟶ S` factors, and which kills the image of `u` over one fixed affine
chart `Z₀` of `X`.  What this file adds is the remaining clause, `u_Z = 0`.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineChartDiagramWith`: the property of an étale scheme chart of
  `X` of being the chart of `X` of a diagram of affine étale charts over a morphism `g : X ⟶ X'`
  whose chart of `X'` satisfies a prescribed condition.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.HandledChart`: the condition on a chart
  of `X` under which the two chartwise halves of the clause apply to the charts of `X ×_S Z`
  above it — a morphism to `Z₀`, or the vanishing of `u` on the sections over the chart and over
  every chart over it.

## Main results

* `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagramWith`: **the cover-density
  statement.**  If a condition on the étale charts of `X'` passes to charts over one and holds on
  a chart around every point of `X'`, then a sieve of a chart of `X` containing every morphism out
  of a chart carrying an affine chart diagram over `g` whose chart of `X'` satisfies the condition
  is a covering sieve of the small étale site of `X`.
  `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagramWith_onRange` asks the condition
  only at the points of `|X'|` in the image of `g` on points, which is all the proof uses and
  what a condition failing away from that image can supply.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_mem_smul_top`:
  **`u_Z = 0`** for an ideal killing the image of `u` over an affine chart whose image on points
  contains the support of `ℱ`.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_isZeroAt_specQuotient`:
  **the finite-presentation clause of Stacks 083K** — a finitely generated ideal whose closed
  subscheme `Z ⊆ S` is of finite presentation over `S`, through which the test object factors,
  and at which the base change of `u` vanishes.

## Implementation notes

**The cover-density argument.**  `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`
is the unconditional statement: the charts of `X` carrying an affine chart diagram over `g` are
cover-dense.  Its proof lifts a point of a chart `U` of `X` in three stages, and only the middle
one has to change here.  There the chart of `X'` is refined from a surjective atlas chart `U₀` to
an *affine open* of `U₀` around the image point; here it is refined to an affine étale chart over
`U₀` which, in addition, satisfies the prescribed condition.  That refinement is
`AlgebraicGeometry.Space.exists_affine_chart_over_with_at`: the condition supplies a chart `V` of
`X'` whose image contains the image point, `AlgebraicGeometry.Space.exists_common_chart` takes the
fibre product of `U₀` and `V` — again an étale chart of `X'`, carrying a point above both — and
`AlgebraicGeometry.Space.exists_affine_chart_at` cuts an affine open out of it around that point.
Both steps go down the condition, which is why it is asked to pass to charts over.

**Why the condition is a disjunction.**  The support hypothesis of the clause gives *one* affine
chart `Z₀` of `X` whose image on points contains the support of `ℱ`
(`AlgebraicGeometry.Space.isCompact_supportOfSheaf_of_compactSpace` and
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact`), and off the support there is no
single chart at all, only a chart around each point
(`AlgebraicGeometry.Space.exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf`).  So the
charts of `X` that the two chartwise halves of the clause cover are not the charts over a single
chart, and the condition cannot be "lies over `Z₀`"; it is the disjunction of that with the
vanishing of `u` on sections, and it is cover-dense because the support and its complement
exhaust the points of `X`.

The second disjunct is the vanishing of `u` on the sections over the chart *and over every chart
over it*, not `Subsingleton (ℱ(V))`: a restriction map of sections need not be surjective, so
`Subsingleton (ℱ(V))` does not pass to charts over `V`, whereas the vanishing statement quantified
over charts over `V` does, and it is exactly what
`AlgebraicGeometry.Space.exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf` provides
and what
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_val_app_eq_zero` consumes.

**The hypothesis on the test object.**  It is taken in the shape
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_specQuotient` consumes,
namely the vanishing of the extension of scalars `ℱ(Z₀) ⊗_R Γ(T, ⊤) → 𝒢(Z₀) ⊗_R Γ(T, ⊤)` of the
map on sections over an affine chart.  Reading the vanishing of the base change `u_T` on the
algebraic space `X ×_S T` as that ring statement is the content of the unconditional clause of
Stacks 083K and is not done here; the finite-presentation clause is proved from the ring form at
every affine chart, which is what the unconditional clause delivers.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Cover-density of the affine chart diagrams with a condition on the chart of the target -/

section CoverDensity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-- **An étale chart of `X` carrying an affine chart diagram over `g` whose chart of `X'`
satisfies `P`.**  This is `AlgebraicGeometry.Space.HasAffineChartDiagram` with the extra demand
`P` on the chart of `X'`. -/
def HasAffineChartDiagramWith (g : X ⟶ X') (P : SmallEtale B S hS X'.1 → Prop)
    (W : SmallEtale B S hS X.1) : Prop :=
  IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧
    ∃ (V : SmallEtale B S hS X'.1) (q : W.1.left ⟶ V.1.left),
      yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) ∧ P V

variable (P : SmallEtale B S hS X'.1 → Prop)

/-- Points of schemes of charts are carried along a composite of morphisms of charts step by
step. -/
private theorem map_comp_toOver_apply_eq {V₁ V₂ V₃ : SmallEtale B S hS X.1} (f : V₁ ⟶ V₂)
    (f' : V₂ ⟶ V₃) {y₁ : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V₁)}
    {y₂ : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V₂)}
    {y₃ : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V₃)}
    (h : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map f) y₁ = y₂)
    (h' : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map f') y₂ = y₃) :
    (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map (f ≫ f')) y₁ = y₃ := by
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, h, h']

/-- **An affine étale chart over a given one satisfying a cover-dense condition.**  Let `P` be a
condition on the étale charts of `X'` which passes to charts over one and which holds on a chart
whose image on points contains the image in `|X'|` of the prescribed point `y` of `U₀`.  Then `y`
lifts to an affine étale chart over `U₀` satisfying `P`.

The condition on `P` is asked at that *one* point of `|X'|`, not at every point: the proof uses
it there and nowhere else, and the consumers below only ever have it on the image of a
morphism.

The condition supplies a chart `V` whose image contains the image of the point in `|X'|`;
`AlgebraicGeometry.Space.exists_common_chart` produces the fibre product of `U₀` and `V`, an
étale chart of `X'` over `U₀` carrying a point above the prescribed one, and
`AlgebraicGeometry.Space.exists_affine_chart_at` cuts an affine open out of that around the
lifted point. -/
theorem exists_affine_chart_over_with_at
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (U₀ : SmallEtale B S hS X'.1)
    (y : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X'.1).obj U₀))
    (hPcov : ∀ p₀ : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj U₀)),
      pointsToScheme B S hS ((SmallEtale.toOver B S hS X'.1).obj U₀) p₀ = y →
      ∃ V : SmallEtale B S hS X'.1, P V ∧
        pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj U₀)) U₀.1.hom p₀ ∈
          Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom)) :
    ∃ (W : SmallEtale B S hS X'.1) (m : W ⟶ U₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧ P W ∧
      ∃ y' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X'.1).obj W),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X'.1).map m) y' = y := by
  obtain ⟨p₀, hp₀⟩ := surjective_pointsToScheme B S hS U₀.1.left y
  obtain ⟨V, hPV, v, hv⟩ := hPcov p₀ hp₀
  obtain ⟨W₁, a, b, r, hra, -⟩ := exists_common_chart B S hS X'.1 U₀ V p₀ v hv.symm
  have hW₁ : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X'.1).map a)
      (pointsToScheme B S hS W₁.1.left r) = y := by
    have h := pointsToScheme_pointsMap_yoneda B S hS a.hom.left r
    rw [hra, hp₀] at h
    exact h.symm
  obtain ⟨W, ι, hWaff, y', hy'⟩ :=
    exists_affine_chart_at B S hS X'.1 W₁ (pointsToScheme B S hS W₁.1.left r)
  refine ⟨W, ι ≫ a, hWaff, hPhom (ι ≫ b) hPV, y', ?_⟩
  exact map_comp_toOver_apply_eq B S hS ι a hy' hW₁

/-- **An affine étale chart over a given one satisfying a cover-dense condition.**  Let `P` be a
condition on the étale charts of `X'` which passes to charts over one and which holds on a chart
whose image on points contains any prescribed point.  Then every point of every étale chart `U₀`
of `X'` lifts to an affine étale chart over `U₀` satisfying `P`.

This reads `AlgebraicGeometry.Space.exists_affine_chart_over_with_at`, which asks the condition
only at the one point of `|X'|` the proof uses it at, with the condition at every point. -/
theorem exists_affine_chart_over_with
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, ∃ V : SmallEtale B S hS X'.1, P V ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U₀ : SmallEtale B S hS X'.1)
    (y : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X'.1).obj U₀)) :
    ∃ (W : SmallEtale B S hS X'.1) (m : W ⟶ U₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧ P W ∧
      ∃ y' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X'.1).obj W),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X'.1).map m) y' = y :=
  exists_affine_chart_over_with_at B S hS P hPhom U₀ y fun _p₀ _ => hPcov _

/-- The three-stage lift of `AlgebraicGeometry.Space.exists_hasAffineChartDiagramWith_onRange`,
with the surjective chart of `X'` that its first stage base changes taken as a parameter. -/
private theorem exists_hasAffineChartDiagramWith_aux_onRange (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, x ∈ Set.range (pointsMap B S hS X.1 g.hom) →
      ∃ V : SmallEtale B S hS X'.1, P V ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1) (U₀ : SmallEtale B S hS X'.1)
    (hU₀S : (MorphismProperty.inverseImage (@Surjective)
      (BigFppfOver.toScheme B S hS)).presheaf U₀.1.hom)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      HasAffineChartDiagramWith B S hS g P W ∧
      ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) z' = z := by
  obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ := exists_chart_over B S hS g U U₀ hU₀S z
  obtain ⟨w₀, hw₀⟩ := surjective_pointsToScheme B S hS V₁.1.left z₁
  have hPcov' : ∀ p₀ : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj U₀)),
      pointsToScheme B S hS ((SmallEtale.toOver B S hS X'.1).obj U₀) p₀ =
          (BigFppfOver.toScheme B S hS).map q₁ z₁ →
      ∃ V : SmallEtale B S hS X'.1, P V ∧
        pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj U₀)) U₀.1.hom p₀ ∈
          Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom) := by
    intro p₀ hp₀
    refine hPcov _ ⟨pointsMap B S hS (yoneda.obj V₁.1.left) V₁.1.hom w₀, ?_⟩
    have hp₀eq : p₀ = pointsMap B S hS (yoneda.obj V₁.1.left) (yoneda.map q₁) w₀ :=
      injective_pointsToScheme B S hS _
        (by
          rw [hp₀]
          exact ((pointsToScheme_pointsMap B S hS q₁ w₀).trans
            (congrArg ((BigFppfOver.toScheme B S hS).map q₁) hw₀)).symm)
    rw [hp₀eq, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hq₁]
  obtain ⟨U'', m, hU''aff, hPU'', y'', hy''⟩ :=
    exists_affine_chart_over_with_at B S hS P hPhom U₀
      ((BigFppfOver.toScheme B S hS).map q₁ z₁) hPcov'
  obtain ⟨T₂, π₂, p₂, hp₂, -, w₂, hw₂, -⟩ :=
    exists_chart_pullback B S hS g V₁ q₁ hq₁ m z₁ y'' hy''.symm
  obtain ⟨T₃, π₃, hT₃aff, w₃, hw₃⟩ := exists_affine_chart_at B S hS X.1 T₂ w₂
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁,
    ⟨hT₃aff, U'', (SmallEtale.toOver B S hS X.1).map π₃ ≫ p₂, ?_, hU''aff, hPU''⟩, w₃, ?_⟩
  · rw [Functor.map_comp, Category.assoc, hp₂, ← Category.assoc]
    exact congrArg (fun φ => φ ≫ g.hom) (CostructuredArrow.w (π₃.hom))
  · exact map_comp_toOver_apply_eq B S hS _ _ hw₃ (map_comp_toOver_apply_eq B S hS _ _ hw₂ hz₁)

/-- **Every point of a chart of `X` lifts to a chart carrying an affine chart diagram over `g`
whose chart of `X'` satisfies `P`.**  This is the geometric content of the cover-density
statement; `P` is asked to pass to charts over one and to hold on a chart around every point
of `X'` **in the image of `g` on points** — which is all the proof needs, the point it is used
at being the image of `z` under `U ⟶ X ⟶ X'`.

The first and third stages are those of
`AlgebraicGeometry.Space.exists_hasAffineChartDiagram`: a surjective atlas chart of `X'` is base
changed to a chart of `X` over `U` carrying a lift of the point, and an affine open is cut out of
the result at the end.  The middle stage is
`AlgebraicGeometry.Space.exists_affine_chart_over_with_at`, which refines the atlas chart to an
affine chart over it satisfying `P`. -/
theorem exists_hasAffineChartDiagramWith_onRange (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, x ∈ Set.range (pointsMap B S hS X.1 g.hom) →
      ∃ V : SmallEtale B S hS X'.1, P V ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      HasAffineChartDiagramWith B S hS g P W ∧
      ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) z' = z := by
  obtain ⟨A₀, g₀, hg₀S, hg₀E⟩ := X'.2.exists_atlas
  exact exists_hasAffineChartDiagramWith_aux_onRange B S hS P g hPhom hPcov U
    ⟨CostructuredArrow.mk g₀, hg₀E⟩ hg₀S z

/-- **Every point of a chart of `X` lifts to a chart carrying an affine chart diagram over `g`
whose chart of `X'` satisfies `P`.**  This is the geometric content of the cover-density
statement; `P` is asked to pass to charts over one and to hold on a chart around every point
of `X'`.

This reads `AlgebraicGeometry.Space.exists_hasAffineChartDiagramWith_onRange`, which asks the
condition only on the image of `g` on points, with the condition at every point. -/
theorem exists_hasAffineChartDiagramWith (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, ∃ V : SmallEtale B S hS X'.1, P V ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ U),
      HasAffineChartDiagramWith B S hS g P W ∧
      ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map a) z' = z :=
  exists_hasAffineChartDiagramWith_onRange B S hS P g hPhom (fun x _ => hPcov x) U z

/-- **The cover-density statement.**  Let `P` be a condition on the étale charts of `X'` which
passes to charts over one and which holds on a chart whose image on points contains any
prescribed point **in the image of `g` on points**.  Then a sieve of an étale chart `U` of `X`
containing every morphism to `U` whose source carries an affine chart diagram over `g` with `P`
on its chart of `X'` is a covering sieve of the small étale site of `X`.

Restricting the condition to the image of `g` is what makes the statement usable when `P` is a
property that fails away from that image — for instance when `P V` says that a meromorphic
section of a module on `X'` is an honest section over `V`, which holds near the image of the
canonical morphism from the spectrum of a local ring of `X'` and nowhere else in general.

A covering sieve of the small étale site is one whose arrows are jointly surjective on the scheme
points of the chart (`AlgebraicGeometry.Space.smallEtale_sieve_of_pointwise_covering`), and
`AlgebraicGeometry.Space.exists_hasAffineChartDiagramWith_onRange` supplies, above each point,
an arrow of the sieve. -/
theorem mem_topology_of_hasAffineChartDiagramWith_onRange (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, x ∈ Set.range (pointsMap B S hS X.1 g.hom) →
      ∃ V : SmallEtale B S hS X'.1, P V ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1) (R : Sieve U)
    (hR : ∀ ⦃W : SmallEtale B S hS X.1⦄ (a : W ⟶ U),
      HasAffineChartDiagramWith B S hS g P W → R a) :
    R ∈ SmallEtale.topology B S hS X.1 U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS X.1 U R fun z => ?_
  obtain ⟨W, a, hW, z', hz'⟩ :=
    exists_hasAffineChartDiagramWith_onRange B S hS P g hPhom hPcov U z
  exact ⟨W, a, hR a hW, z', hz'⟩

/-- **The cover-density statement.**  Let `P` be a condition on the étale charts of `X'` which
passes to charts over one and which holds on a chart whose image on points contains any
prescribed point.  Then a sieve of an étale chart `U` of `X` containing every morphism to `U`
whose source carries an affine chart diagram over `g` with `P` on its chart of `X'` is a covering
sieve of the small étale site of `X`.

This reads `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagramWith_onRange`, which
asks the condition only on the image of `g` on points, with the condition at every point. -/
theorem mem_topology_of_hasAffineChartDiagramWith (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, ∃ V : SmallEtale B S hS X'.1, P V ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1) (R : Sieve U)
    (hR : ∀ ⦃W : SmallEtale B S hS X.1⦄ (a : W ⟶ U),
      HasAffineChartDiagramWith B S hS g P W → R a) :
    R ∈ SmallEtale.topology B S hS X.1 U :=
  mem_topology_of_hasAffineChartDiagramWith_onRange B S hS P g hPhom (fun x _ => hPcov x) U R hR

/-- **The cover-density statement as a covering family.**  Every étale chart `U` of `X` carries a
covering family of the small étale site each of whose members carries an affine chart diagram over
`g` whose chart of `X'` satisfies `P`, the condition on `P` being asked only at the points of
`|X'|` in the image of `g`.

This is `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagramWith_onRange` applied to
the sieve generated by *all* the morphisms to `U` out of such charts; it is the shape in which
`AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows` consumes a covering. -/
theorem exists_ofArrows_hasAffineChartDiagramWith_onRange (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, x ∈ Set.range (pointsMap B S hS X.1 g.hom) →
      ∃ V : SmallEtale B S hS X'.1, P V ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS X.1) (π : ∀ j, Y j ⟶ U),
      Sieve.ofArrows Y π ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ j, HasAffineChartDiagramWith B S hS g P (Y j) := by
  refine ⟨Σ W : SmallEtale B S hS X.1, {a : W ⟶ U // HasAffineChartDiagramWith B S hS g P W},
    fun j => j.1, fun j => j.2.1, ?_, fun j => j.2.2⟩
  refine mem_topology_of_hasAffineChartDiagramWith_onRange B S hS P g hPhom hPcov U _ ?_
  intro W a hW
  exact Sieve.ofArrows_mk (fun j : Σ W : SmallEtale B S hS X.1,
      {a : W ⟶ U // HasAffineChartDiagramWith B S hS g P W} => j.1)
    (fun j => j.2.1) ⟨W, a, hW⟩

/-- **The cover-density statement as a covering family.**  Every étale chart `U` of `X` carries a
covering family of the small étale site each of whose members carries an affine chart diagram
over `g` whose chart of `X'` satisfies `P`.

This reads `AlgebraicGeometry.Space.exists_ofArrows_hasAffineChartDiagramWith_onRange`, which
asks the condition only at the points of `|X'|` in the image of `g`, with the condition at every
point; it is the shape in which `AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows` consumes a
covering. -/
theorem exists_ofArrows_hasAffineChartDiagramWith (g : X ⟶ X')
    (hPhom : ∀ {V V' : SmallEtale B S hS X'.1}, (V' ⟶ V) → P V → P V')
    (hPcov : ∀ x : points B S hS X'.1, ∃ V : SmallEtale B S hS X'.1, P V ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X'.1).obj V)) V.1.hom))
    (U : SmallEtale B S hS X.1) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS X.1) (π : ∀ j, Y j ⟶ U),
      Sieve.ofArrows Y π ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ j, HasAffineChartDiagramWith B S hS g P (Y j) :=
  exists_ofArrows_hasAffineChartDiagramWith_onRange B S hS P g hPhom (fun x _ => hPcov x) U

end CoverDensity

/-! ### The finite-presentation clause of Stacks 083K -/

namespace ModuleMapFlatTargetSituation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S]
    (D : ModuleMapFlatTargetSituation B S hS)

/-- **The charts of `X` on which the finite-presentation clause of Stacks 083K is settled.**  An
étale chart `V` of `X` is settled with respect to an affine chart `Z₀` when it admits a morphism
to `Z₀`, or when `u` vanishes on the sections over `V` and over every chart over `V`.

Above a settled chart the base change of `u` to `X ×_S Z` vanishes on the sections over every
affine chart: by
`ModuleMapFlatTargetSituation.modulePullback_map_val_app_specQuotient_eq_zero`
in the first case, by
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_val_app_eq_zero` in the second.

The second disjunct quantifies over the charts over `V` so that the condition passes to charts
over one, which is what the cover-density argument needs; `Subsingleton (ℱ(V))` does not, a
restriction map of sections not being surjective in general. -/
def HandledChart (Z₀ V : SmallEtale B S hS D.X.1) : Prop :=
  Nonempty (V ⟶ Z₀) ∨
    ∀ V' : SmallEtale B S hS D.X.1, (V' ⟶ V) → D.u.val.app (op V') = 0

/-- **Being settled passes to charts over.**  A morphism to `Z₀` is composed with, and the
vanishing of `u` over the charts over a chart is inherited by the charts over a chart over it. -/
theorem handledChart_of_hom {Z₀ V V' : SmallEtale B S hS D.X.1} (φ : V' ⟶ V)
    (h : D.HandledChart B S hS Z₀ V) : D.HandledChart B S hS Z₀ V' :=
  h.imp (fun hψ => ⟨φ ≫ hψ.some⟩) fun hv V'' ψ => hv V'' (ψ ≫ φ)

/-- **Being settled is cover-dense.**  Every point of `X` lies in the image of a settled chart:
the points of the support of `ℱ` lie in the image of `Z₀` by hypothesis, and off the support
`AlgebraicGeometry.Space.exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf` provides a
chart around the point on which, and on every chart over which, `u` vanishes on sections. -/
theorem exists_handledChart (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (Z₀ : SmallEtale B S hS D.X.1)
    (hsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj Z₀)) Z₀.1.hom))
    (x : points B S hS D.X.1) :
    ∃ V : SmallEtale B S hS D.X.1, D.HandledChart B S hS Z₀ V ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj V)) V.1.hom) := by
  by_cases hx : x ∈ supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F)
  · exact ⟨Z₀, Or.inl ⟨CategoryStruct.id Z₀⟩, hsupp hx⟩
  · obtain ⟨W, hWx, hWvan⟩ :=
      exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf B S hS D.X hFft D.u hx
    exact ⟨W, Or.inr hWvan, hWx⟩

/-- **An affine chart of `X` whose image contains the support of `ℱ`.**  This is the support
hypothesis of the finite-presentation clause of Stacks 083K: the support of a quasi-coherent
module of finite type with quasi-compact scheme theoretic support is a compact set of points
(`AlgebraicGeometry.Space.isCompact_supportOfSheaf_of_compactSpace`), and a compact set of points
lies in the image of an étale chart with affine underlying scheme
(`AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact`).

Only one finite type hypothesis on `ℱ` is asked for, as in the source: the categorical one,
which is all that `AlgebraicGeometry.Space.isCompact_supportOfSheaf_of_compactSpace` consumes. -/
theorem exists_affine_chart_supportOfSheaf_subset_range
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hcpt : CompactSpace (points B S hS (schemeTheoreticSupport B S hS D.X D.F).toFunctor)) :
    ∃ Z₀ : SmallEtale B S hS D.X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z₀.1.left) ∧
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
        Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj Z₀)) Z₀.1.hom) := by
  obtain ⟨Z, c, hZaff, hZE, hsub⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS D.X.1 D.X.2
      (isCompact_supportOfSheaf_of_compactSpace B S hS D.X D.F D.quasicoherent_F hFft hcpt)
  exact ⟨⟨CostructuredArrow.mk c, hZE⟩, hZaff, hsub⟩

/-- **The base change of `u` to `X ×_S Z` vanishes on the sections over a chart carrying an
affine chart diagram over the projection whose chart of `X` is settled.**  The two cases of
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.HandledChart` are the two chartwise halves
of the clause. -/
theorem modulePullback_map_val_app_specQuotient_eq_zero_of_handledChart (J : Ideal Γ(S, ⊤))
    {Z₀ : SmallEtale B S hS D.X.1}
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (hJ : letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
      ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u)))
    {W : SmallEtale B S hS ((D.toModuleMapSituation B S hS).baseChangeSpace
      (D.specQuotientTest B S hS J)).1}
    (hW : HasAffineChartDiagramWith B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.specQuotientTest B S hS J))
      (D.HandledChart B S hS Z₀) W) :
    ((modulePullback B S hS ((D.toModuleMapSituation B S hS).baseChangeProjection
        (D.specQuotientTest B S hS J))).map D.u).val.app (op W) = 0 := by
  obtain ⟨hWaff, V, q, hcomm, hVaff, hPV⟩ := hW
  rcases hPV with hφ | hvan
  · exact modulePullback_map_val_app_specQuotient_eq_zero B S hS D J hZ₀
      { U := W, V := V, g := q, comm := hcomm.symm } hWaff hVaff hφ.some hJ
  · exact modulePullback_map_val_app_eq_zero_of_val_app_eq_zero B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.specQuotientTest B S hS J))
      D.quasicoherent_F D.quasicoherent_G D.u
      { U := W, V := V, g := q, comm := hcomm.symm } hWaff hVaff
      (hvan V (CategoryStruct.id V))

/-- **`u_Z = 0`.**  Let `J` be an ideal of the functions on the affine base killing the image of
`u` over an affine chart `Z₀` of `X` whose image on points contains the support of `ℱ`.  Then the
base change of `u` to `X ×_S Z`, for `Z = \Spec(Γ(S, ⊤)/J)`, is zero.

Vanishing of a map of `𝒪`-modules is étale local
(`AlgebraicGeometry.Space.Modules.eq_zero_of_ofArrows`), the charts of `X ×_S Z` carrying an
affine chart diagram over the projection whose chart of `X` is settled are cover-dense
(`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagramWith`), and above a settled chart
the base change vanishes on sections. -/
theorem isZeroAt_specQuotient_of_mem_smul_top
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) (J : Ideal Γ(S, ⊤))
    (Z₀ : SmallEtale B S hS D.X.1)
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (hsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj Z₀)) Z₀.1.hom))
    (hJ : letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
      ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))) :
    (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.specQuotientTest B S hS J) := by
  refine Modules.eq_zero_of_ofArrows B S hS
    ((D.toModuleMapSituation B S hS).baseChangeHom (modulePullbackSystem B S hS)
      (D.specQuotientTest B S hS J)) fun U => ?_
  obtain ⟨I, Y, π, hcov, hgood⟩ :=
    exists_ofArrows_hasAffineChartDiagramWith B S hS (D.HandledChart B S hS Z₀)
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.specQuotientTest B S hS J))
      (fun φ h => D.handledChart_of_hom B S hS φ h)
      (D.exists_handledChart B S hS hFft Z₀ hsupp) U
  exact ⟨I, Y, π, hcov, fun j =>
    D.modulePullback_map_val_app_specQuotient_eq_zero_of_handledChart B S hS J hZ₀ hJ (hgood j)⟩

/-- **The finite-presentation clause of Stacks 083K, at a chart of `X` whose image contains the
support of `ℱ`.**

Granted the vanishing, over the affine chart `Z₀`, of the extension of scalars to the functions
on the test object of the map on sections of `u`, there is a finitely generated ideal `J` of the
functions on the affine base such that, for `Z = \Spec(Γ(S, ⊤)/J) ⊆ S`,

* `Z ⟶ S` is locally of finite presentation — and it is affine, hence quasi-compact and
  quasi-separated, so it is of finite presentation;
* the test object factors through `Z` over `S`;
* the base change `u_Z` is zero.

The ideal, its finite presentation and the factorisation are
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_specQuotient`; the
vanishing of `u_Z` is
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.isZeroAt_specQuotient_of_mem_smul_top`. -/
theorem exists_fg_ideal_isZeroAt_specQuotient_of_chart
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) (T : BigFppfOver B S hS)
    (Z₀ : SmallEtale B S hS D.X.1)
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (hsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS D.X.1).obj Z₀)) Z₀.1.hom)) :
    letI := chartBaseAlgebra B S hS D.X Z₀
    letI := testSchemeBaseAlgebra B S hS T
    letI : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    haveI := isScalarTower_chartRing_sections B S hS D.X D.F Z₀
    haveI := isScalarTower_chartRing_sections B S hS D.X D.G Z₀
    LinearMap.rTensor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        ((D.u.val.app (op Z₀)).hom.restrictScalars Γ(S, ⊤)) = 0 →
      ∃ J : Ideal Γ(S, ⊤), J.FG ∧
        LocallyOfFinitePresentation (specQuotientToBase S J) ∧
        Nonempty (T ⟶ specQuotientOver B S hS J) ∧
        (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
          (D.specQuotientTest B S hS J) := by
  let := chartBaseAlgebra B S hS D.X Z₀
  let := testSchemeBaseAlgebra B S hS T
  let : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  let : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  intro hzero
  obtain ⟨J, hJfg, hJfp, hJT, hJ⟩ :=
    exists_fg_ideal_specQuotient B S hS D hFft Z₀ hZ₀ T hzero
  exact ⟨J, hJfg, hJfp, hJT,
    isZeroAt_specQuotient_of_mem_smul_top B S hS D hFft J Z₀ hZ₀ hsupp hJ⟩

/-- **The finite-presentation clause of Stacks 083K.**

In the situation of Stacks 0CWA over an affine base, assume `ℱ` is of finite type and its scheme
theoretic support is quasi-compact, and let `T` be a test object over `S` whose base change `u_T`
vanishes — read, over each affine étale chart `Z₀` of `X`, as the vanishing of the extension of
scalars `ℱ(Z₀) ⊗_{Γ(S, ⊤)} Γ(T, ⊤) → 𝒢(Z₀) ⊗_{Γ(S, ⊤)} Γ(T, ⊤)` of the map on sections.  Then
there is a finitely generated ideal `J` of the functions on the base such that the closed
subscheme `Z = \Spec(Γ(S, ⊤)/J) ⊆ S` it cuts out satisfies

* `Z ⟶ S` is locally of finite presentation — and affine, hence quasi-compact and
  quasi-separated, so of finite presentation;
* `T ⟶ S` factors through `Z`;
* the base change `u_Z` is zero.

The affine chart around the support is
`ModuleMapFlatTargetSituation.exists_affine_chart_supportOfSheaf_subset_range`,
and the rest is
`ModuleMapFlatTargetSituation.exists_fg_ideal_isZeroAt_specQuotient_of_chart`.

**This carries no `@[stacks 083K]` attribute, deliberately.**  The hypothesis `hzero` is the
*chartwise ring-level reading* of `u_T = 0`, not the source's hypothesis `IsZeroAt` itself, so a
registration here would be a conditional one, which this project does not allow.  The implication
from the source's hypothesis is proved, for a quasi-compact test object, in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartMapQuasiCompactTest.lean`, and the attribute sits on
the statement that results,
`ModuleMapFlatTargetSituation.exists_fg_ideal_isZeroAt_specQuotient_of_quasiCompact`. -/
theorem exists_fg_ideal_isZeroAt_specQuotient
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hcpt : CompactSpace (points B S hS (schemeTheoreticSupport B S hS D.X D.F).toFunctor))
    (T : BigFppfOver B S hS)
    (hzero : ∀ (Z₀ : SmallEtale B S hS D.X.1),
      IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀) →
      letI := chartBaseAlgebra B S hS D.X Z₀
      letI := testSchemeBaseAlgebra B S hS T
      letI : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
      letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
        Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
      haveI := isScalarTower_chartRing_sections B S hS D.X D.F Z₀
      haveI := isScalarTower_chartRing_sections B S hS D.X D.G Z₀
      LinearMap.rTensor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        ((D.u.val.app (op Z₀)).hom.restrictScalars Γ(S, ⊤)) = 0) :
    ∃ J : Ideal Γ(S, ⊤), J.FG ∧
      LocallyOfFinitePresentation (specQuotientToBase S J) ∧
      Nonempty (T ⟶ specQuotientOver B S hS J) ∧
      (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
        (D.specQuotientTest B S hS J) := by
  obtain ⟨Z₀, hZ₀aff, hsupp⟩ :=
    exists_affine_chart_supportOfSheaf_subset_range B S hS D hFft hcpt
  exact exists_fg_ideal_isZeroAt_specQuotient_of_chart B S hS D hFft T Z₀ hZ₀aff hsupp
    (hzero Z₀ hZ₀aff)

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
