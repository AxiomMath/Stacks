module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceUndeformedTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceUndeformedTargetUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftComorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftReduction

/-!
# A solution of the lifting problem into an undeformed target is the comorphism of a lift

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `b : W ⟶ V`
be a morphism and let `c : X ⟶ W` be a morphism, so that `c` is a lift over `V` of its own
restriction `a = i ≫ c` to the thickening.  Call a morphism of sheaves of rings

`g : 𝒪_W ⟶ a_*(i^{-1}𝒪_X)`

on the small étale site of `W` a *solution of the lifting problem* when

* it agrees with the comorphism of `c` on the regular functions read from the base `V`, and
* its reduction along `i^{-1}𝒪_X ⟶ 𝒪_Z` is the comorphism of `a`.

This file proves that every solution is the comorphism, read through the thickening, of an
honest morphism `c' : X ⟶ W` over `V` restricting to `a`.

With the algebraic half — that the comorphism of `c` moved by the derivation Equation
[Stacks Project, Tag 0619] attaches to an `𝒪_Z`-linear map `θ : a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` is such a
solution, with descended difference `θ` from the comorphism of `c` — this closes the
**existence clause of [Stacks Project, Tag 04D0]** for the lifting problem of
[Stacks Project, Tag 061A] with an undeformed target: every `θ` is the difference from `c` of
some lift.  Together with the uniqueness half of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceUndeformedTargetUnique.lean`
that is the whole of Tag 04D0 in this situation.

It is unconditional, and in particular does not use Properties of Spaces, Theorem 04KL — the
full faithfulness of the functor from algebraic spaces to locally ringed topoi — which is what
recovering a morphism of algebraic spaces from an arbitrary comorphism would need.  The morphism
is built chart by chart, where a morphism into an affine scheme is determined by its map of
global sections, and the charts are glued by the sheaf property of the lifts.

## Main results

* `AlgebraicGeometry.Space.isChartLift_thickeningLiftChartHom_of_solution`: over an affine étale
  chart of `W` carrying an affine chart diagram over `b`, the morphism of charts attached to a
  solution is a lift of `a` over `V`.
* `AlgebraicGeometry.Space.exists_hom_structureSharpThroughThickeningAt_eq_of_solution`: **a
  solution is the comorphism of a lift.**  The chartwise morphisms amalgamate into a morphism
  `c' : X ⟶ W` over `V` restricting to `a`, whose comorphism read through the thickening is the
  solution.
* `AlgebraicGeometry.Space.exists_liftDifferenceData_solution_of_hom`: the comorphism of `c`
  moved by the derivation attached to an `𝒪_Z`-linear map `θ` is a solution, and its descended
  difference from the comorphism of `c` is `θ`.
* `AlgebraicGeometry.Space.exists_undeformedLiftDiff_eq`: **every `𝒪_Z`-linear map is the
  difference from `c` of some lift**, the existence half of [Stacks Project, Tag 04D0].
* `AlgebraicGeometry.Space.existsUnique_undeformedLiftDiff_eq`: **[Stacks Project, Tag 04D0]**
  for an undeformed target — exactly one lift has a prescribed difference from `c`.

## Implementation notes

**Why the solution is a hypothesis here and not constructed.**  The solution attached to `θ` is
`(AlgebraicGeometry.Space.liftDifferenceDataOfHom …).g`, and the two clauses above hold for it by
`AlgebraicGeometry.Space.comp_liftDifferenceDataOfHom_g_eq` — the derivation kills the functions
read from the base, which is the field `d_app` of Equation (0619) — and by
`AlgebraicGeometry.Space.liftDifferenceDataOfHom_g_comp_eq` together with
`AlgebraicGeometry.Space.app_reduction_squareZeroValuesAt_ι_eq_zero`, the reduction killing the
ideal of values.  Both are general lemmas already in the library.

Carrying the solution as a hypothesis in the two theorems above keeps the geometric content
independent of that algebra; the algebra is packaged separately, in
`AlgebraicGeometry.Space.exists_liftDifferenceData_solution_of_hom`, and the two are joined in
`AlgebraicGeometry.Space.exists_undeformedLiftDiff_eq`.

**The square-zero datum `E` is passed explicitly at every call.**  It is an implicit argument of
`AlgebraicGeometry.Space.liftDifferenceDataOfHom` and of every general lemma about it, and
solving `?E.ambient ≡ (i ≫ c)_*(i^{-1}𝒪_X)` for it is a higher-order unification problem which
at the size of these terms is a deterministic heartbeat timeout — not the terms themselves,
which elaborate in under a second once `E` is given.  Every application below therefore writes
`(E := squareZeroValuesAt …)`.

**The reduction hypothesis is what makes the chart morphisms restrict correctly.**  `hred` says
that the solution and the comorphism of `c` have the same reduction, which is exactly that the
solution still restricts to `a` on the thickening; without it the chartwise morphisms would lie
over `V` but need not agree with `a` on the part of a chart lying in `Z`.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- **The reduction kills the ideal of values**, at an arbitrary target space.  This is
`AlgebraicGeometry.Space.app_reduction_restrictedSquareZeroValues_ι_eq_zero` with the closed
subspace of the target replaced by an arbitrary algebraic space, which is the form the undeformed
target needs. -/
theorem app_reduction_squareZeroValuesAt_ι_eq_zero (T : AlgebraicSpaces B S hS)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T)
    (Vv : (SmallEtale B S hS T.1)ᵒᵖ)
    (m : ((modulePushforward B S hS e).obj (conormalModule B S hS X Z)).val.obj Vv) :
    (pullbackRingSheafMap (SmallEtale.topology B S hS T.1)
          (smallToposMorphismTypeU B S hS e).pushforward
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).hom.app Vv
        ((squareZeroValuesAt B S hS Z T e hZ).ι m) = 0 :=
  app_pullbackRingSheafMap_pullbackModuleMap_eq_zero
    (SmallEtale.topology B S hS T.1)
    (smallToposMorphismTypeU B S hS e).pushforward
    (conormalInverseImageι B S hS Z hZ)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) Vv
    (app_conormalInverseImageι_eq_zero B S hS Z hZ) m

variable (b : W ⟶ V) (c : X ⟶ W)
  (g : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
  (hbase : ∀ (Q : SmallEtale B S hS W.1)
      (s : ToType ((structureRingSheafInverseImage B S hS b).obj.obj (op Q))),
    g.hom.app (op Q) ((structureSharpRingInverseImage B S hS b).hom.app (op Q) s) =
      (structureSharpThroughThickening B S hS Z c).hom.app (op Q)
        ((structureSharpRingInverseImage B S hS b).hom.app (op Q) s))
  (hred : g ≫ thickeningLiftReduction B S hS Z c =
    structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))

include hbase hred in
/-- **The morphism of charts attached to a solution of the lifting problem is a lift.**

Let `g : 𝒪_W ⟶ a_*(i^{-1}𝒪_X)` be a solution of the lifting problem for the first order
thickening `Z ⊂ X` and the morphism `c : X ⟶ W`, that is a morphism of sheaves of rings which
agrees with the comorphism of `c` on the regular functions read from the base `V` (`hbase`) and
whose reduction is the comorphism of `a = i ≫ c` (`hred`).  Over an affine étale chart `Q` of `W`
carrying an affine chart diagram over `b`, the morphism of charts `g` attaches to an index `j` is
a lift of `a` over `V`: both clauses of `AlgebraicGeometry.Space.IsChartLift` hold.

It lies over `V` by `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq`, read at the
index the affine chart diagram names, which is where `hbase` is used; and it agrees with `a` on
the part of the chart lying in `Z` by
`AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_eq_restriction`, which is where `hred` is
used. -/
theorem isChartLift_thickeningLiftChartHom_of_solution (Q : SmallEtale B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj Q))]
    (j : StructuredArrow (op (chartBaseChange B S hS c Q)) (comparisonFunctor B S hS X).op)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj Q)
    (hQ : HasAffineChartDiagram B S hS b Q)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ.1 c g Q j) :
    IsChartLift B S hS (c ≫ b) b (subspaceInclusion B S hS X Z ≫ c).hom j.right.unop
      (yoneda.map ψ ≫ Q.1.hom) := by
  obtain ⟨-, V', qq, hqq, hV'aff⟩ := hQ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS V.1).obj V')) := hV'aff
  let idx := indexOfChartDiagram B S hS b (⟨Q, V', qq, hqq.symm⟩ :
    ChartDiagram B S hS W.1 V.1 b.hom)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj idx.right.unop)) :=
    (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj Q)))
  exact ⟨yoneda_map_comp_chart_hom_comp_eq B S hS Z hZ.1 c g b V' idx j
      (fun s => hbase _ s) ψ hψ,
    fun Ww k t hkt => yoneda_map_comp_chart_hom_eq_restriction B S hS Z hZ.1 c g hred Q j ψ hψ
      Ww k t hkt⟩

include hZ hbase hred in
/-- **A solution of the lifting problem is the comorphism of an honest lift.**

There is a morphism `c' : X ⟶ W` over `V` whose restriction to the thickening is `a = i ≫ c`,
whose restriction to any chart of `X` carrying an index over any affine chart of `W` is the
morphism of charts `g` induces, and whose comorphism read through the thickening is `g` itself.

This is the geometric half of the existence clause of [Stacks Project, Tag 04D0] for an
undeformed target: the chartwise morphisms amalgamate by
`AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom`, and the comorphism of the
amalgamated morphism is `g` by
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom`.

It is unconditional, and in particular does not use Properties of Spaces, Theorem 04KL: the
morphism is built chart by chart, where a morphism into an affine scheme is determined by its map
of global sections, and the charts are glued by the sheaf property of the lifts. -/
theorem exists_hom_structureSharpThroughThickeningAt_eq_of_solution :
    ∃ (c' : X ⟶ W) (hcc : subspaceInclusion B S hS X Z ≫ c' =
        subspaceInclusion B S hS X Z ≫ c),
      c' ≫ b = c ≫ b ∧
        structureSharpThroughThickeningAt B S hS Z c'
          (subspaceInclusion B S hS X Z ≫ c) hcc = g := by
  obtain ⟨ε, hover, hres, hchart⟩ := exists_hom_eq_thickeningLiftChartSiteHom B S hS Z hZ.1 c g b
    (fun Q s => hbase Q s) (c ≫ b) b (Zs := Z.1) (subspaceInclusion B S hS X Z ≫ c).hom
    fun Q _ j ψ hQ hψ =>
      isChartLift_thickeningLiftChartHom_of_solution B S hS Z hZ b c g hbase hred Q j ψ hQ hψ
  refine ⟨ObjectProperty.homMk ε, ObjectProperty.hom_ext _ hres,
    ObjectProperty.hom_ext _ hover, ?_⟩
  exact structureSharpThroughThickeningAt_eq_of_thickeningLiftChartHom B S hS Z hZ.1 c
    (ObjectProperty.homMk ε) (ObjectProperty.hom_ext _ hres) g hred b
    (fun Q s => hbase Q s) fun Q hQaff j ψ hψ => @hchart Q hQaff j ψ hψ


variable (θ : (modulePullback B S hS (subspaceInclusion B S hS X Z ≫ c)).obj
  (sheafOfDifferentials B S hS b) ⟶ conormalModule B S hS X Z)

/-- **The comorphism of `c` moved by the derivation attached to `θ` is a solution of the lifting
problem, and its descended difference from the comorphism of `c` is `θ`.**

This is the algebraic half of the existence clause of [Stacks Project, Tag 04D0] for an
undeformed target, packaged so that the geometric half above can consume it: the pair
`AlgebraicGeometry.Space.liftDifferenceDataOfHom` supplies the solution, its agreement with the
comorphism of `c` on the functions read from the base is
`AlgebraicGeometry.Space.comp_liftDifferenceDataOfHom_g_eq` — the derivation attached to `θ`
kills those functions, which is the field `d_app` of Equation [Stacks Project, Tag 0619] — its
reduction is computed by `AlgebraicGeometry.Space.liftDifferenceDataOfHom_g_comp_eq` together
with `AlgebraicGeometry.Space.app_reduction_squareZeroValuesAt_ι_eq_zero`, and the descended
difference is `θ` by
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom`. -/
theorem exists_liftDifferenceData_solution_of_hom :
    ∃ (L : Stacks.Sites.LiftDifferenceData (𝟙 (structureRingSheaf B S hS W))
        (squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ))
      (hz : ∀ (Vv : (SmallEtale B S hS W.1)ᵒᵖ)
        (s : (inverseImageStructureSheaf B S hS b).obj.obj Vv),
        L.toQuotientDerivation.descend
          ((structureSharpInverseImage B S hS b).hom.app Vv s) = 0),
      L.f = structureSharpThroughThickeningAt B S hS Z c
          (subspaceInclusion B S hS X Z ≫ c) rfl ∧
        structureSharpRingInverseImage B S hS b ≫ L.g =
          structureSharpRingInverseImage B S hS b ≫
            structureSharpThroughThickeningAt B S hS Z c
              (subspaceInclusion B S hS X Z ≫ c) rfl ∧
        L.g ≫ thickeningLiftReduction B S hS Z c =
          structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c) ∧
        liftDifferenceDifferentialsHom B S hS b
            (subspaceInclusion B S hS X Z ≫ c) (conormalModule B S hS X Z) L hz = θ := by
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  have hsmul := fun (V : (SmallEtale B S hS W.1)ᵒᵖ) x m => squareZeroValuesAt_ι_smul B S hS Z W
    (subspaceInclusion B S hS X Z ≫ c) hZ (𝟙 _)
    (structureSharpThroughThickeningAt B S hS Z c (subspaceInclusion B S hS X Z ≫ c) rfl)
    ((structureSharpThroughThickeningAt_comp_reduction B S hS Z c
      (subspaceInclusion B S hS X Z ≫ c) rfl).trans (Category.id_comp _).symm) (V := V) x m
  refine ⟨liftDifferenceDataOfHom B S hS b (subspaceInclusion B S hS X Z ≫ c)
      (conormalModule B S hS X Z)
      (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
      (structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl)
      hsmul θ,
    liftDifferenceDataOfHom_descend_eq_zero B S hS b (subspaceInclusion B S hS X Z ≫ c)
      (conormalModule B S hS X Z)
      (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
      (structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl)
      hsmul θ, rfl, ?_, ?_, ?_⟩
  · refine comp_liftDifferenceDataOfHom_g_eq B S hS b (subspaceInclusion B S hS X Z ≫ c)
      (conormalModule B S hS X Z)
      (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
      (structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl)
      hsmul θ
      (structureSharpRingInverseImage B S hS b) fun Vv x => ?_
    have hbridge : (structureSharpRingInverseImage B S hS b).hom.app Vv x =
        (structureSharpInverseImage B S hS b).hom.app Vv x := by
      rw [structureSharpRingInverseImage_eq_forget₂]
      rfl
    have hgoal := derivationFamilyOfHom_app B S hS b (subspaceInclusion B S hS X Z ≫ c)
      (conormalModule B S hS X Z) θ Vv x
    rw [← hbridge] at hgoal
    exact hgoal
  · refine (liftDifferenceDataOfHom_g_comp_eq B S hS b (subspaceInclusion B S hS X Z ≫ c)
      (conormalModule B S hS X Z)
      (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
      (structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl)
      hsmul θ
      (thickeningLiftReduction B S hS Z c)
      (app_reduction_squareZeroValuesAt_ι_eq_zero B S hS Z hZ W
        (subspaceInclusion B S hS X Z ≫ c))).trans ?_
    exact structureSharpThroughThickeningAt_comp_reduction B S hS Z c
      (subspaceInclusion B S hS X Z ≫ c) rfl
  · exact liftDifferenceDifferentialsHom_liftDifferenceDataOfHom B S hS b
      (subspaceInclusion B S hS X Z ≫ c) (conormalModule B S hS X Z)
      (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
      (structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl)
      hsmul θ

include hZ in
/-- **The existence half of [Stacks Project, Tag 04D0] for an undeformed target.**  Every
`𝒪_Z`-linear map `θ : a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` is the difference from `c` of some lift `c'` of
`a = i ≫ c` over `V`.

The comorphism of `c` moved by the derivation attached to `θ` is a solution of the lifting
problem whose descended difference from the comorphism of `c` is `θ`
(`AlgebraicGeometry.Space.exists_liftDifferenceData_solution_of_hom`); that solution is the
comorphism of an honest lift `c'`
(`AlgebraicGeometry.Space.exists_hom_structureSharpThroughThickeningAt_eq_of_solution`); and the
pair `(c, c')` then has the same two comorphisms as the pair `(c^♯, g)`, hence the same descended
difference, the comparison being made against the pair `(c', c')` whose descended difference
vanishes.

With `AlgebraicGeometry.Space.eq_of_undeformedLiftDiff_eq_zero` this is the whole of
[Stacks Project, Tag 04D0] in this situation, and it is unconditional. -/
@[stacks 04D0 "the existence half: every linear map is the difference from a given lift of some \
lift, for an UNDEFORMED target"]
theorem exists_undeformedLiftDiff_eq :
    ∃ (c' : X ⟶ W) (h' : subspaceInclusion B S hS X Z ≫ c' =
        subspaceInclusion B S hS X Z ≫ c) (hb : c ≫ b = c' ≫ b),
      undeformedLiftDiff B S hS Z hZ (subspaceInclusion B S hS X Z ≫ c) b c c' rfl h' hb = θ := by
  obtain ⟨L, hz, hf, hψ, hρ, hθ⟩ :=
    exists_liftDifferenceData_solution_of_hom B S hS Z hZ b c θ
  have hbase : ∀ (Q : SmallEtale B S hS W.1)
      (s : ToType ((structureRingSheafInverseImage B S hS b).obj.obj (op Q))),
      L.g.hom.app (op Q) ((structureSharpRingInverseImage B S hS b).hom.app (op Q) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op Q)
          ((structureSharpRingInverseImage B S hS b).hom.app (op Q) s) := by
    intro Q s
    rw [← structureSharpThroughThickeningAt_self B S hS Z c]
    exact ringSheafHom_congr_app_apply hψ (op Q) s
  obtain ⟨c', hcc, hover, hsharp⟩ :=
    exists_hom_structureSharpThroughThickeningAt_eq_of_solution B S hS Z hZ b c L.g hbase hρ
  refine ⟨c', hcc, hover.symm, ?_⟩
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  have hzero := liftDifferenceDifferentialsHom_eq_zero B S hS b
    (subspaceInclusion B S hS X Z ≫ c) (conormalModule B S hS X Z)
    (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
    (undeformedLiftDifferenceData B S hS Z hZ (subspaceInclusion B S hS X Z ≫ c) c' c' hcc hcc)
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ
      (subspaceInclusion B S hS X Z ≫ c) b c' c' hcc hcc rfl)
    ((undeformedLiftDifferenceData_f B S hS Z hZ
        (subspaceInclusion B S hS X Z ≫ c) c' c' hcc hcc).trans
      (undeformedLiftDifferenceData_g B S hS Z hZ
        (subspaceInclusion B S hS X Z ≫ c) c' c' hcc hcc).symm)
  have hadd := liftDifferenceDifferentialsHom_add B S hS b
    (subspaceInclusion B S hS X Z ≫ c) (conormalModule B S hS X Z)
    (E := squareZeroValuesAt B S hS Z W (subspaceInclusion B S hS X Z ≫ c) hZ)
    (undeformedLiftDifferenceData B S hS Z hZ (subspaceInclusion B S hS X Z ≫ c) c c' rfl hcc)
    (undeformedLiftDifferenceData B S hS Z hZ (subspaceInclusion B S hS X Z ≫ c) c' c' hcc hcc)
    L
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ
      (subspaceInclusion B S hS X Z ≫ c) b c c' rfl hcc hover.symm)
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ
      (subspaceInclusion B S hS X Z ≫ c) b c' c' hcc hcc rfl)
    hz
    ((undeformedLiftDifferenceData_g B S hS Z hZ
        (subspaceInclusion B S hS X Z ≫ c) c c' rfl hcc).trans
      (undeformedLiftDifferenceData_f B S hS Z hZ
        (subspaceInclusion B S hS X Z ≫ c) c' c' hcc hcc).symm)
    ((undeformedLiftDifferenceData_f B S hS Z hZ
        (subspaceInclusion B S hS X Z ≫ c) c c' rfl hcc).trans hf.symm)
    ((undeformedLiftDifferenceData_g B S hS Z hZ
        (subspaceInclusion B S hS X Z ≫ c) c' c' hcc hcc).trans hsharp)
  rw [undeformedLiftDiff_eq B S hS Z hZ (subspaceInclusion B S hS X Z ≫ c) b c c' rfl hcc
    hover.symm]
  rw [← hθ, ← hadd, hzero, add_zero]

include hZ in
/-- **[Stacks Project, Tag 04D0] for an undeformed target.**  For every `𝒪_Z`-linear map
`θ : a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` there is exactly one lift of `a = i ≫ c` over `V` whose difference
from `c` is `θ`.

Existence is `AlgebraicGeometry.Space.exists_undeformedLiftDiff_eq` and uniqueness is
`AlgebraicGeometry.Space.undeformedLiftDiff_injective`.  Together with the additivity of the
difference this is the simple transitivity of [Stacks Project, Tag 061C] over the ambient space
of the thickening, in the case where the target is not deformed. -/
@[stacks 04D0 "existence and uniqueness of the lift with a prescribed difference from a given \
lift, for an UNDEFORMED target"]
theorem existsUnique_undeformedLiftDiff_eq :
    ∃! p : {c' : X ⟶ W //
        (subspaceInclusion B S hS X Z ≫ c' = subspaceInclusion B S hS X Z ≫ c) ∧
          c ≫ b = c' ≫ b},
      undeformedLiftDiff B S hS Z hZ (subspaceInclusion B S hS X Z ≫ c) b c p.1 rfl
        p.2.1 p.2.2 = θ := by
  obtain ⟨c', h', hb, hd⟩ := exists_undeformedLiftDiff_eq B S hS Z hZ b c θ
  refine ⟨⟨c', h', hb⟩, hd, fun qq hq => ?_⟩
  exact Subtype.ext (undeformedLiftDiff_injective B S hS Z hZ
    (subspaceInclusion B S hS X Z ≫ c) b c qq.1 c' rfl qq.2.1 h' qq.2.2 hb
    (qq.2.2.symm.trans hb) (hq.trans hd.symm))

end AlgebraicGeometry.Space

end
