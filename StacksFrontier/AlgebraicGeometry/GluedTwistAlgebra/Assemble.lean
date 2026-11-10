module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.GluedTwistSectionMap.Global
public import StacksFrontier.AlgebraicGeometry.TwistGluedProduct.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistCocycle.Pointwise

/-!
# Tag 01NR's twist datum for the glued twists

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra — Situation 01NN. Tag 01NR asserts that the graded twists on the projective spectra
of the affine section rings of `A` glue to a sheaf of graded algebras on the relative Proj of `A`,
compatibly with the absolute twists on every affine chart and with a homogeneous-section map from
`A`. The assertion is the existence of a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`.

**This file produces one.** `StacksFrontier/AlgebraicGeometry/GluedTwistAlgebra/Basic.lean` stops at
the local multiplication and unit of the glued twists over a chart image; this file feeds them to
`Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedGradedAlgebra`, proves
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso` for the resulting chart data, and
hands both to `Stacks.AlgebraicGeometry.GluedTwistSectionMap.mkOfGradedAlgebra`, whose remaining
fields — the homogeneous-section map and its chart description — are already discharged there.

## Main definitions

* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.gluedTwistAlgebra`: **the sheaf of `ℤ`-graded
  algebras of the glued twists on a relative projective spectrum.** Its homogeneous pieces are
  the glued twists `Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` of Tag 01NO —
  `gluedTwistAlgebra_piece` is `rfl` — and its product and unit are the canonical product and
  unit of Tag 01MO on each affine chart.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistData`: **Tag 01NR's twist datum**, for a
  nested cocycle in every integer degree.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`: **the same with no
  hypothesis at all beyond the graded algebra `A`.**

## Main results

* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.isMultiplicativeCmpGen`: **the chart comparison is
  multiplicative**, unconditionally — `Stacks.AlgebraicGeometry.TwistGluedProduct.cmpGen_mul` and
  `cmpGen_one` packaged as the interface `Basic.lean` states its overlap lemmas against, so
  nothing below carries a multiplicativity hypothesis.
* `mulData_agree` and `oneData_agree`: the local products, respectively units, over two chart
  images agree on the overlaps.
* `mulData_heq_assoc`, `mulData_heq_one_mul` and `mulData_heq_mul_one`: the three algebra laws
  for the local data over one chart image.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.isGradedChartIso`: **the chart identifications of
  `gluedTwistAlgebra` carry the canonical product and unit of the absolute twists to its own**,
  in every pair of integer degrees and over every open of every chart.
* `restrictAppIso_chartSectionEquiv_symm` and `gluedMapSection_eq`: **the chart comparison of a
  glued module on sections, over an arbitrary open of a chart.**
  `Stacks.AlgebraicGeometry.GluedTwistSectionMap.restrictAppIso_chartSectionEquiv_top_symm` is
  this over the top open only, and `IsGradedChartIso` quantifies over every open.

## Implementation notes

**The kernel obstruction, and how it is avoided.** Feeding `mulData` and `oneData` to the
glueing directly fails with `(kernel) deterministic timeout`s. The cause is narrow: **the kernel
cannot delta-unfold
`mulData` or `oneData` underneath a projection.** Every ingredient is cheap — the generic
`congrLocalBilinear_app` and `congrLocalSection_app` of `Basic.lean` are `rfl`; the written-out
`(congrLocalBilinear (chartEquiv …) … (pushLocalBilinear …)).app V hV s t = ofChart … ((twistMul
…).app …)` is `rfl`; `chartEquiv`, `toChart`, `ofChart`, `chartProd` and `chartUnit` all reduce
freely; and a statement that merely *mentions* `(oneData A hcoc m).app V hV` type-checks at once.
It is
only the one delta step from `mulData A hcoc i j m` to its own body, taken under
`LocalBilinearMap.app`, that exhausts the kernel's budget, and `set_option` is unavailable to
raise it. Re-declaring the same body under a new name does not help; an inline lambda, whose
elimination is a *beta* step, does.

The resolution is therefore to take that delta **once, at the level of the data itself**, where
it is a syntactic match and costs nothing: `mulData_eq` and `oneData_eq` are equalities of the
local data, with no projection applied, and are `rfl`. Every value below is read off them by
`congrArg` — `mulData_app` and `oneData_app` — and `Basic.lean`'s `mulData` and `oneData` are
then passed to the glueing unchanged. Nothing here is restated at the glued twists and nothing in
`Basic.lean` is weakened.

The last step of `mulData_app` and `oneData_app` is the one place where the pointwise product of
local sections of the twists meets Tag 01MO's product: `mulData` pushes forward
`Stacks.AlgebraicGeometry.ProjConeTwist.twistMul`, which is given by its values in the fibres,
while `chartProd` is `absoluteTwistProduct`, which is given by a map out of the sheafified tensor
product. The two agree fibrewise and not on the nose, so each `_app` ends with one application of
`twistSection_ext` and `twistProd_val` rather than with `rfl`.

Each of the five obligations of the glueing is its own declaration for the same budget reason:
supplied as inline proofs of one `gluedGradedAlgebra` application they exceed it together, and the
unit law was the first to go.

`gluedTwistAlgebra_mul`, `gluedTwistAlgebra_one` and `gluedTwistAlgebra_piece` are the same
discipline one level up — the structure-level unfoldings of the glued algebra, each `rfl`, taken
before any projection is applied. The one place that could not be done this way is the unit in
`isGradedChartIso`: writing a *new* statement about `(gluedTwistAlgebra A hcoc).one.eval` makes
the **elaborator** resolve `.eval` by `whnf` through the algebra and exhaust its heartbeats, so
the substitution is made by `rw [gluedTwistAlgebra_one]` on the already-elaborated goal, where it
is syntactic. `ModuleBilinearGlue.gluedOne_eval` then needs its `piece` argument given by name:
it occurs only as `piece 0`, which no first-order unifier can solve.

The transport in `mapSection_eq` is along `chart ⁻¹ᵁ (chart ''ᵁ W) = W` and is carried in the
statement rather than simplified away. That is what makes the general open as cheap as the top
open: the `⊤` case of the tree's own lemma is `rfl` because morphisms of opens are unique there,
and keeping the `eqToHom` keeps the general case a `rfl` too.

## What is not done here

The registration is made here: `@[stacks 01NR …]` sits on `twistDataOfGradedAlgebra` below, which
states the whole
of the tag's existence assertion, and the attribute's note names the two declarations carrying
the tag's uniqueness assertions.

The module docstring of `StacksFrontier/AlgebraicGeometry/GluedTwistAlgebra/Basic.lean` is
**stale**: it advertises `isMultiplicativeCmpGen`,
`mulData_agree`, `oneData_agree` and `mulApp_heq_assoc`/`_heq_one_mul`/`_heq_mul_one` as its own
main results, and none of the six is in it. The first three are proved here; the last three are
`chartProd_heq_assoc`/`_heq_one_mul`/`_heq_mul_one` there, about the chart's product rather than
the glued one, and are consumed here through `heq_ofChart`.

`Stacks.AlgebraicGeometry.GluedTwistSectionMap.Global` still restates `cover`, `chartModule`,
`modelData_cmp` and `trans_app_cmpGen` verbatim from `GluedTwistAlgebra.Basic`; it does not restate
`chartSections`,
`chartSections_resLE` and `trans_chartSections`, but imports `GluedTwistAlgebra.Basic` and uses
those three from there. This file uses `GluedTwistAlgebra.Basic`'s copies throughout.

Quasi-coherence of the pieces and commutativity of the product are fields of `TwistData` and are
not addressed here: `Stacks.AlgebraicGeometry.TwistDataFromChart.mk` derives them from the chart
data and from `IsGradedChartIso`, by `RelativeProjTwistQcoh.isQuasicoherent_piece` and
`mul_comm_of_isGradedChartIso`, so proving the chart condition above is what supplies them.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.GluedTwistAlgebra

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **The chart comparison is multiplicative, unconditionally.** -/
public theorem isMultiplicativeCmpGen : IsMultiplicativeCmpGen A :=
  ⟨fun W U hW hU i j hci hcj hcij hpre V hV a b =>
      TwistGluedProduct.cmpGen_mul A W U hW hU hpre i j hci hcj hcij V hV a b,
   fun W U hW hU hc hpre V hV =>
      TwistGluedProduct.cmpGen_one A W U hW hU hpre hc V hV⟩

variable (hcoc : ∀ n : ℤ, IsNestedCocycle A n)

/-! ### Transport of a heterogeneous equation along the chart comparison -/

/-- **The inverse chart comparison carries a heterogeneous equation to one**, the two degrees
being variables. Proved by substituting the equality of degrees away, so that no motive is ever
elaborated at a compound index. -/
public theorem heq_ofChart (m : S.affineOpens) {V : (relativeProj A).scheme.Opens}
    (hV : V ≤ cover A m) {n n' : ℤ} (h : n = n')
    {a : (chartModule A n m).obj (op V)} {b : (chartModule A n' m).obj (op V)} (hab : HEq a b) :
    HEq (ofChart A n (hcoc n) m hV a) (ofChart A n' (hcoc n') m hV b) := by
  subst h
  exact heq_of_eq (congrArg (ofChart A n (hcoc n) m hV) (eq_of_heq hab))

/-! ### The overlap agreement -/

/-- **The local products over two chart images agree on the overlap.** -/
public theorem ofChart_chartProd_agree (i j : ℤ) (k l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hVk : V ≤ cover A k) (hVl : V ≤ cover A l)
    (s : (gluedTwist A i (hcoc i)).val.obj (op V))
    (t : (gluedTwist A j (hcoc j)).val.obj (op V)) :
    ofChart A (i + j) (hcoc (i + j)) k hVk
        (chartProd A i j k (toChart A i (hcoc i) k hVk s) (toChart A j (hcoc j) k hVk t))
      = ofChart A (i + j) (hcoc (i + j)) l hVl
        (chartProd A i j l (toChart A i (hcoc i) l hVl s) (toChart A j (hcoc j) l hVl t)) := by
  refine Eq.trans (ofChart_trans A (i + j) (hcoc (i + j)) k l hVk hVl _).symm ?_
  refine congrArg (ofChart A (i + j) (hcoc (i + j)) l hVl) ?_
  refine Eq.trans (trans_mul A hcoc (isMultiplicativeCmpGen A) i j k l hVk hVl _ _) ?_
  exact congrArg₂ (fun a b => chartProd A i j l (V := V) a b)
    (trans_toChart A i (hcoc i) k l hVk hVl s) (trans_toChart A j (hcoc j) k l hVk hVl t)

/-- **The local units over two chart images agree on the overlap.** -/
public theorem ofChart_chartUnit_agree (k l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hVk : V ≤ cover A k) (hVl : V ≤ cover A l) :
    ofChart A 0 (hcoc 0) k hVk (chartUnit A k)
      = ofChart A 0 (hcoc 0) l hVl (chartUnit A l) := by
  refine Eq.trans (ofChart_trans A 0 (hcoc 0) k l hVk hVl _).symm ?_
  exact congrArg (ofChart A 0 (hcoc 0) l hVl)
    (trans_one A hcoc (isMultiplicativeCmpGen A) k l hVk hVl)

/-! ### The three algebra laws over one chart image -/

/-- **Associativity of the local product over a chart image**, with the round trip through the
chart comparison between the two factors already present. -/
public theorem heq_ofChart_chartProd_assoc (i j k : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (x : (gluedTwist A i (hcoc i)).val.obj (op V))
    (y : (gluedTwist A j (hcoc j)).val.obj (op V))
    (z : (gluedTwist A k (hcoc k)).val.obj (op V)) :
    HEq
      (ofChart A (i + j + k) (hcoc (i + j + k)) m hV
        (chartProd A (i + j) k m
          (toChart A (i + j) (hcoc (i + j)) m hV
            (ofChart A (i + j) (hcoc (i + j)) m hV
              (chartProd A i j m (toChart A i (hcoc i) m hV x) (toChart A j (hcoc j) m hV y))))
          (toChart A k (hcoc k) m hV z)))
      (ofChart A (i + (j + k)) (hcoc (i + (j + k))) m hV
        (chartProd A i (j + k) m (toChart A i (hcoc i) m hV x)
          (toChart A (j + k) (hcoc (j + k)) m hV
            (ofChart A (j + k) (hcoc (j + k)) m hV
              (chartProd A j k m (toChart A j (hcoc j) m hV y)
                (toChart A k (hcoc k) m hV z)))))) := by
  simp only [toChart_ofChart]
  exact heq_ofChart A hcoc m hV (add_assoc i j k)
    (chartProd_heq_assoc A i j k m (toChart A i (hcoc i) m hV x)
      (toChart A j (hcoc j) m hV y) (toChart A k (hcoc k) m hV z))

/-- **The local unit is a left identity for the local product over a chart image.** -/
public theorem heq_ofChart_chartUnit_mul (i : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (x : (gluedTwist A i (hcoc i)).val.obj (op V)) :
    HEq
      (ofChart A (0 + i) (hcoc (0 + i)) m hV
        (chartProd A 0 i m
          (toChart A 0 (hcoc 0) m hV (ofChart A 0 (hcoc 0) m hV (chartUnit A m)))
          (toChart A i (hcoc i) m hV x))) x := by
  rw [toChart_ofChart]
  exact (heq_ofChart A hcoc m hV (zero_add i)
    (chartProd_heq_one_mul A i m (toChart A i (hcoc i) m hV x))).trans
    (heq_of_eq (ofChart_toChart A i (hcoc i) m hV x))

/-- **The local unit is a right identity for the local product over a chart image.** -/
public theorem heq_ofChart_mul_chartUnit (i : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (x : (gluedTwist A i (hcoc i)).val.obj (op V)) :
    HEq
      (ofChart A (i + 0) (hcoc (i + 0)) m hV
        (chartProd A i 0 m (toChart A i (hcoc i) m hV x)
          (toChart A 0 (hcoc 0) m hV (ofChart A 0 (hcoc 0) m hV (chartUnit A m))))) x := by
  rw [toChart_ofChart]
  exact (heq_ofChart A hcoc m hV (add_zero i)
    (chartProd_heq_mul_one A i m (toChart A i (hcoc i) m hV x))).trans
    (heq_of_eq (ofChart_toChart A i (hcoc i) m hV x))

/-! ### The local data of `GluedTwistAlgebra.Basic`, evaluated

`mulData` and `oneData` may not be unfolded underneath a projection: the kernel
exhausts its budget on the single delta step, and `set_option` is unavailable to raise it. They
are therefore unfolded **once, at the level of the data itself**, where the step is a syntactic
match and costs nothing; every value below is read off that equation by `congrArg`. -/

/-- The local product of `GluedTwistAlgebra.Basic`, unfolded at the level of the data. -/
public theorem mulData_eq (i j : ℤ) (m : S.affineOpens) :
    mulData A hcoc i j m
      = congrLocalBilinear (chartEquiv A i (hcoc i) m) (chartEquiv A j (hcoc j) m)
          (chartEquiv A (i + j) (hcoc (i + j)) m)
          (pushLocalBilinear ((relativeProj A).chart (m.1 : S.Opens) m.2)
            (TwistDataConstruction.twistMul (A.grading (m.1 : S.Opens)) i j) (cover A m)) :=
  rfl

/-- The local unit of `GluedTwistAlgebra.Basic`, unfolded at the level of the data. -/
public theorem oneData_eq (m : S.affineOpens) :
    oneData A hcoc m
      = congrLocalSection (chartEquiv A 0 (hcoc 0) m)
          (pushLocalSection ((relativeProj A).chart (m.1 : S.Opens) m.2)
            (TwistDataConstruction.twistOne (A.grading (m.1 : S.Opens))) (cover A m)) :=
  rfl

/-- **The local product is the chart's own product, read through the chart comparison.** -/
public theorem mulData_app (i j : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (s : (gluedTwist A i (hcoc i)).val.obj (op V))
    (t : (gluedTwist A j (hcoc j)).val.obj (op V)) :
    (mulData A hcoc i j m).app V hV s t
      = ofChart A (i + j) (hcoc (i + j)) m hV
          (chartProd A i j m (toChart A i (hcoc i) m hV s) (toChart A j (hcoc j) m hV t)) := by
  have key : (ProjConeTwist.twistMul (A.grading (m.1 : S.Opens)) i j).app
        (op ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V))
        (toChart A i (hcoc i) m hV s) (toChart A j (hcoc j) m hV t)
      = chartProd A i j m (toChart A i (hcoc i) m hV s) (toChart A j (hcoc j) m hV t) :=
    ProjConeTwist.twistSection_ext (A.grading (m.1 : S.Opens)) fun x =>
      (TwistDataConstruction.twistProd_val (A.grading (m.1 : S.Opens)) i j _ _ x).symm
  exact (congrArg (fun d => TopCat.Sheaf.LocalBilinearMap.app d V hV s t)
    (mulData_eq A hcoc i j m)).trans (congrArg (ofChart A (i + j) (hcoc (i + j)) m hV) key)

/-- **The local unit is the chart's own unit, read through the chart comparison.** -/
public theorem oneData_app (m : S.affineOpens) {V : (relativeProj A).scheme.Opens}
    (hV : V ≤ cover A m) :
    (oneData A hcoc m).app V hV = ofChart A 0 (hcoc 0) m hV (chartUnit A m) := by
  have key : (ProjConeTwist.twistOne (A.grading (m.1 : S.Opens))).eval
        (op ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V))
      = chartUnit A m (V := V) :=
    ProjConeTwist.twistSection_ext (A.grading (m.1 : S.Opens)) fun x =>
      (TwistDataConstruction.twistUnit_val (A.grading (m.1 : S.Opens)) x).symm
  exact (congrArg (fun d => TopCat.Sheaf.LocalSectionData.app d V hV)
    (oneData_eq A hcoc m)).trans (congrArg (ofChart A 0 (hcoc 0) m hV) key)

/-! ### The five obligations of the glueing -/

/-- **The local products over two chart images agree on the overlap.** -/
public theorem mulData_agree (i j : ℤ) (k l : S.affineOpens)
    (V : (relativeProj A).scheme.Opens) (hVk : V ≤ cover A k) (hVl : V ≤ cover A l) :
    (mulData A hcoc i j k).app V hVk = (mulData A hcoc i j l).app V hVl :=
  AddMonoidHom.ext fun s => AddMonoidHom.ext fun t =>
    ((mulData_app A hcoc i j k hVk s t).trans
        (ofChart_chartProd_agree A hcoc i j k l hVk hVl s t)).trans
      (mulData_app A hcoc i j l hVl s t).symm

/-- **The local units over two chart images agree on the overlap.** -/
public theorem oneData_agree (k l : S.affineOpens)
    (V : (relativeProj A).scheme.Opens) (hVk : V ≤ cover A k) (hVl : V ≤ cover A l) :
    (oneData A hcoc k).app V hVk = (oneData A hcoc l).app V hVl :=
  ((oneData_app A hcoc k hVk).trans (ofChart_chartUnit_agree A hcoc k l hVk hVl)).trans
    (oneData_app A hcoc l hVl).symm

/-- **The local product is associative over a chart image.** -/
public theorem mulData_heq_assoc (i j k : ℤ) (m : S.affineOpens)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ cover A m)
    (x : (gluedTwist A i (hcoc i)).val.obj (op V))
    (y : (gluedTwist A j (hcoc j)).val.obj (op V))
    (z : (gluedTwist A k (hcoc k)).val.obj (op V)) :
    HEq ((mulData A hcoc (i + j) k m).app V hV ((mulData A hcoc i j m).app V hV x y) z)
      ((mulData A hcoc i (j + k) m).app V hV x ((mulData A hcoc j k m).app V hV y z)) := by
  rw [mulData_app, mulData_app, mulData_app, mulData_app]
  exact heq_ofChart_chartProd_assoc A hcoc i j k m hV x y z

/-- **The local unit is a left identity over a chart image.** -/
public theorem mulData_heq_one_mul (i : ℤ) (m : S.affineOpens)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ cover A m)
    (x : (gluedTwist A i (hcoc i)).val.obj (op V)) :
    HEq ((mulData A hcoc 0 i m).app V hV ((oneData A hcoc m).app V hV) x) x := by
  rw [oneData_app, mulData_app]
  exact heq_ofChart_chartUnit_mul A hcoc i m hV x

/-- **The local unit is a right identity over a chart image.** -/
public theorem mulData_heq_mul_one (i : ℤ) (m : S.affineOpens)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ cover A m)
    (x : (gluedTwist A i (hcoc i)).val.obj (op V)) :
    HEq ((mulData A hcoc i 0 m).app V hV x ((oneData A hcoc m).app V hV)) x := by
  rw [oneData_app, mulData_app]
  exact heq_ofChart_mul_chartUnit A hcoc i m hV x

/-! ### The graded algebra -/

/-- **The sheaf of `\u2124`-graded algebras of the glued twists on a relative projective
spectrum.** Its homogeneous pieces are the glued twists of Tag 01NO, and its product and unit are
the canonical product and unit of Tag 01MO on each affine chart. -/
public def gluedTwistAlgebra : SchemeGradedAlgebra (relativeProj A).scheme :=
  ModuleBilinearGlue.gluedGradedAlgebra (piece := fun n => gluedTwist A n (hcoc n))
    (iSup_cover A) (mulData A hcoc) (mulData_agree A hcoc) (oneData A hcoc)
    (oneData_agree A hcoc) (mulData_heq_assoc A hcoc) (mulData_heq_one_mul A hcoc)
    (mulData_heq_mul_one A hcoc)

/-- The homogeneous pieces of `gluedTwistAlgebra` are the glued twists. -/
public theorem gluedTwistAlgebra_piece (n : ℤ) :
    (gluedTwistAlgebra A hcoc).piece n = gluedTwist A n (hcoc n) := rfl

/-- The identification of the pieces of `gluedTwistAlgebra` with the glued twists: the identity,
the pieces being the glued twists on the nose. -/
public def pieceIso (n : ℤ) : (gluedTwistAlgebra A hcoc).piece n ≅ gluedTwist A n (hcoc n) :=
  Iso.refl _

/-- The multiplication of `gluedTwistAlgebra`, unfolded at the level of the bilinear map. -/
public theorem gluedTwistAlgebra_mul (i j : ℤ) :
    (gluedTwistAlgebra A hcoc).mul i j
      = ModuleBilinearGlue.gluedMul (iSup_cover A) (mulData A hcoc) (mulData_agree A hcoc) i j :=
  rfl

/-- The unit of `gluedTwistAlgebra`, unfolded at the level of the global section. -/
public theorem gluedTwistAlgebra_one :
    (gluedTwistAlgebra A hcoc).one
      = ModuleBilinearGlue.gluedOne (iSup_cover A) (oneData A hcoc) (oneData_agree A hcoc) :=
  rfl

/-! ### The chart comparison of the chart data, on sections

The chart image of an open of a chart is below the chart image of the top open, which is the
member of the cover; so a section of a chart's absolute twist over an open `W` is a section of the
glued twist over the chart image of `W`, and the comparison is `ofChart` applied to the transport
along `chart ⁻¹ᵁ (chart ''ᵁ W) = W`. -/

/-- The chart image of an open of a chart is inside the chart image of the base's affine open. -/
public theorem chartImage_le_cover (m : S.affineOpens)
    (W : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens) :
    (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ W ≤ cover A m :=
  (((relativeProj A).chart (m.1 : S.Opens) m.2).image_mono le_top).trans
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le

/-- **The chart comparison of a glued module on sections, over an arbitrary open of the chart.**
`Stacks.AlgebraicGeometry.GluedTwistSectionMap.restrictAppIso_chartSectionEquiv_top_symm` is this
over the top open only, where the transport below degenerates to a restriction map; carrying the
transport along in the statement makes the general case the same `rfl`. -/
public theorem restrictAppIso_chartSectionEquiv_symm (n : ℤ) (hc : IsNestedCocycle A n)
    (m : S.affineOpens) (W : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
    (hW : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ W ≤ cover A m)
    (a : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op W)) :
    (Scheme.Modules.restrictAppIso ((relativeProj A).chart (m.1 : S.Opens) m.2)
          (gluedTwist A n hc) W).hom
        ((SchemeModuleGlue.chartSectionEquiv (modelData A n hc).toChartGlueData m
          (hom_isOpenImmersion := GluedTwistSectionMap.chartOI A m)
          (RelativeProjTwistGlue.chart_image_top (relativeProj A) (m.1 : S.Opens) m.2).le
          W).symm a)
      = ofChart A n hc m hW
          ((twistingSheaf (A.grading (m.1 : S.Opens)) n).val.restrictₛₗ
            (eqToHom (((relativeProj A).chart (m.1 : S.Opens) m.2).preimage_image_eq W)).op a) :=
  rfl

/-- **The chart comparison of the glued twist on sections, over an arbitrary open.** -/
public theorem gluedMapSection_eq (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens)
    (W : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
    (hW : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ W ≤ cover A m)
    (a : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op W)) :
    GluedTwistSectionMap.gluedMapSection n hc (m.1 : S.Opens) m.2 W a
      = ofChart A n hc m hW
          ((twistingSheaf (A.grading (m.1 : S.Opens)) n).val.restrictₛₗ
            (eqToHom (((relativeProj A).chart (m.1 : S.Opens) m.2).preimage_image_eq W)).op a) :=
  (congrArg (fun z => (Scheme.Modules.restrictAppIso
        ((relativeProj A).chart (m.1 : S.Opens) m.2) (gluedTwist A n hc) W).hom z)
    (GluedTwistSectionMap.gluedChartIso_inv_app n hc m W a)).trans
    (restrictAppIso_chartSectionEquiv_symm A n hc m W hW a)

/-- **The chart comparison of the chart data of `gluedTwistAlgebra`, on sections.** -/
public theorem mapSection_eq (n : ℤ) (m : S.affineOpens)
    (W : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
    (hW : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ W ≤ cover A m)
    (a : (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.obj (op W)) :
    (GluedTwistChartData.chartData hcoc (gluedTwistAlgebra A hcoc)
          (pieceIso A hcoc)).mapSection (m.1 : S.Opens) m.2 n W a
      = ofChart A n (hcoc n) m hW
          ((twistingSheaf (A.grading (m.1 : S.Opens)) n).val.restrictₛₗ
            (eqToHom (((relativeProj A).chart (m.1 : S.Opens) m.2).preimage_image_eq W)).op a) :=
  (GluedTwistSectionMap.chartData_mapSection hcoc (gluedTwistAlgebra A hcoc) (pieceIso A hcoc)
      (m.1 : S.Opens) m.2 n W a).trans
    (gluedMapSection_eq A n (hcoc n) m W hW a)

/-! ### The product and the unit of the glued algebra over a chart image -/

/-- **The product of `gluedTwistAlgebra` on two sections read off a chart** is the chart's own
product, read back. -/
public theorem mul_ofChart (i j : ℤ) (m : S.affineOpens)
    {V₀ : (relativeProj A).scheme.Opens} (hV₀ : V₀ ≤ cover A m)
    (u : (chartModule A i m).obj (op V₀)) (v : (chartModule A j m).obj (op V₀)) :
    ((gluedTwistAlgebra A hcoc).mul i j).app (op V₀)
        (ofChart A i (hcoc i) m hV₀ u) (ofChart A j (hcoc j) m hV₀ v)
      = ofChart A (i + j) (hcoc (i + j)) m hV₀ (chartProd A i j m u v) := by
  refine Eq.trans (congrArg (fun M => Stacks.BilinearMap.app M (op V₀)
      (ofChart A i (hcoc i) m hV₀ u) (ofChart A j (hcoc j) m hV₀ v))
    (gluedTwistAlgebra_mul A hcoc i j)) ?_
  refine Eq.trans (ModuleBilinearGlue.gluedMul_app (iSup_cover A) (mulData A hcoc)
    (mulData_agree A hcoc) i j m V₀ hV₀ _ _) ?_
  refine Eq.trans (mulData_app A hcoc i j m hV₀ _ _) ?_
  exact congrArg (ofChart A (i + j) (hcoc (i + j)) m hV₀)
    (congrArg₂ (fun z w => chartProd A i j m (V := V₀) z w)
      (toChart_ofChart A i (hcoc i) m hV₀ u) (toChart_ofChart A j (hcoc j) m hV₀ v))

/-! ### Tag 01NR's chart condition, and the twist datum -/

/-- **The chart identifications of `gluedTwistAlgebra` carry the canonical product and unit of
the absolute twists to its own**, in every pair of integer degrees and over every open of every
chart. This is the `isGradedChartIso` field of Tag 01NR's twist datum. -/
public theorem isGradedChartIso :
    IsGradedChartIso (GluedTwistChartData.chartData hcoc (gluedTwistAlgebra A hcoc)
      (pieceIso A hcoc)) := by
  refine ⟨fun U hU i j V a b => ?_, fun U hU V => ?_⟩
  · have hW := chartImage_le_cover A ⟨U, hU⟩ V
    refine Eq.trans (mapSection_eq A hcoc (i + j) ⟨U, hU⟩ V hW _) ?_
    refine Eq.trans (congrArg (ofChart A (i + j) (hcoc (i + j)) ⟨U, hU⟩ hW)
      (TwistDataConstruction.twistProd_naturality (A.grading U) i j
        (eqToHom (((relativeProj A).chart U hU).preimage_image_eq V)).op a b)) ?_
    refine Eq.trans (mul_ofChart A hcoc i j ⟨U, hU⟩ hW _ _).symm ?_
    exact congrArg₂ (fun z w => ((gluedTwistAlgebra A hcoc).mul i j).app
        (op ((relativeProj A).chart U hU ''ᵁ V)) z w)
      (mapSection_eq A hcoc i ⟨U, hU⟩ V hW a).symm (mapSection_eq A hcoc j ⟨U, hU⟩ V hW b).symm
  · have hW := chartImage_le_cover A ⟨U, hU⟩ V
    rw [gluedTwistAlgebra_one A hcoc]
    refine Eq.trans (mapSection_eq A hcoc 0 ⟨U, hU⟩ V hW _) ?_
    refine Eq.trans (congrArg (ofChart A 0 (hcoc 0) ⟨U, hU⟩ hW)
      (map_absoluteTwistUnit (A.grading U) _)) ?_
    exact ((ModuleBilinearGlue.gluedOne_eval (piece := fun n => gluedTwist A n (hcoc n))
      (iSup_cover A) (oneData A hcoc) (oneData_agree A hcoc) ⟨U, hU⟩
      ((relativeProj A).chart U hU ''ᵁ V) hW).trans (oneData_app A hcoc ⟨U, hU⟩ hW)).symm

/-- **Tag 01NR's twist datum for the glued twists on a relative projective spectrum.** -/
public def twistData : TwistData A :=
  GluedTwistSectionMap.mkOfGradedAlgebra hcoc (gluedTwistAlgebra A hcoc) (pieceIso A hcoc)
    (isGradedChartIso A hcoc)

/-- **The twists on the relative projective spectrum of a quasi-coherent graded algebra exist**,
on no hypothesis beyond the graded algebra itself: the nested cocycle of Tag 01MZ that the glued
twists are indexed by is discharged in every integer degree by
`Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle`. -/
@[stacks 01NR "the existence assertion: the graded twists and the homogeneous-section map, for a \
quasi-coherent graded algebra on any scheme, with no hypothesis beyond the algebra itself. The two \
uniqueness assertions are carried by `Stacks.AlgebraicGeometry.TwistExistence.isUniqueTwistData` \
and `Stacks.AlgebraicGeometry.TwistRigidity.determinesChartIso`, which were vacuous until this \
term existed"]
public def twistDataOfGradedAlgebra : TwistData A :=
  twistData A fun n => ProjTwistCocycle.isNestedCocycle A n

end Stacks.AlgebraicGeometry.GluedTwistAlgebra

end
