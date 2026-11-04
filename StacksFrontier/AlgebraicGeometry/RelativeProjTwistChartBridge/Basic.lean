module

public import StacksFrontier.AlgebraicGeometry.MorphismsIntoProj
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.Basic

/-!
# Over an affine base, the glued twists on a relative `Proj` are the absolute twists

Let `S` be a scheme with `⊤` affine and `A` a quasi-coherent graded `𝒪_S`-algebra. Tag 01NR
(`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`) equips the relative homogeneous
spectrum `Proj_S(A)` with a graded algebra whose pieces `𝒪(n)` restrict, along the chart over
each affine open `U` of the base, to the absolute twists `𝒪(n)` of `Proj Γ(U, A)`. Over an
affine base the chart over `⊤` is already an isomorphism
(`Stacks.VeryAmpleAffineBase.isIso_topChart`), so that single chart identification says
everything: the glued twist in degree `n` *is* the absolute twist of the graded ring of global
sections, and the two agree after inverse image along any morphism into either scheme.

This file records that in the two forms its consumers need. Both are stated in **every integer
degree `n`** and for an **arbitrary `TwistData`** — no genericity in the open, the degree or the
graded algebra is given up, and in particular nothing here is special to degree one or to a
symmetric algebra.

The identifications are infrastructure for two tags and prove no clause of either on their own:

* [Stacks, Tag 01O1] over an affine base, whose route through
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.existsUnique_hom_toDegreeOpen`
  produces a morphism into `U_d ⊆ Proj Γ(⊤, A)` together with an identification of the pullback
  of the *absolute* degree-`d` twist, and must hand back an identification of the pullback of
  the *relative* one.
* [Stacks, Tag 01O9] clause (1), whose chart-level algebraic half becomes a morphism of
  `𝒪`-modules only once the twists are pulled back along the chart.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTopChartPieceIso`: the chart
  identification at `U = ⊤`, in inverse-image form — the inverse image of the glued twist
  `𝒪(n)` along the chart over `⊤` is the absolute twist `𝒪(n)` of `Proj Γ(⊤, A)`.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.restrictTopChartPieceIso`: the same,
  in the `AlgebraicGeometry.Scheme.Modules.restrict` form the `ChartData` field is stated in.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pieceIsoPullbackTwist`: the glued
  twist itself, as the inverse image of the absolute twist along the inverse of the chart.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistIso`: **the
  absolute-to-relative bridge.** For a morphism `g` into `Proj Γ(⊤, A)`, the inverse image of
  the absolute twist `𝒪(n)` along `g` is the inverse image of the glued twist `𝒪(n)` along the
  corresponding morphism `g ≫ topChart` into `Proj_S(A)`.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackPieceIso`: the same bridge
  read from the relative side, for a morphism into `Proj_S(A)`.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistDegreeOpenIso`: the
  bridge at the spelling Tag 01O1 produces it in, for a morphism through the open `U_d` of
  `Stacks.AlgebraicGeometry.MorphismsIntoProj`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackTwistIso_over_base` and
  `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.pullbackPieceIso_over_base`: the two
  bridges change the morphism only over the base — the structure morphism to `S` is unchanged,
  which is what makes a morphism over `S` on one side a morphism over `S` on the other.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.restrict` needs the chart to be an open immersion, so the
`ChartData` field is stated under a `letI`. The inverse-image forms need no such hypothesis,
which is why they, and not the `restrict` form, are the shape everything downstream is built
from; `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` converts between them.

The shape of `pullbackTwistIso` is not new, only its vocabulary is. In the older glueing-data
formalisation of the relative homogeneous spectrum —
`Stacks.RelativeProj.Situation`, where the glued twist is `Situation.twistSheaf` rather than a
piece of a `TwistData` —
`Stacks.RelativeProj.Situation.twistSheafPullbackChartIso` of
`StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModulePullback` already
identifies the inverse image of the glued twist along a morphism factoring through a chart with
the inverse image of the absolute twist along the factor. It is more general in the open, which
is an arbitrary affine `W` rather than `⊤`, and it carries the factorisation as a hypothesis
instead of producing it; it is not stated for a `TwistData`, and no declaration connects the two
vocabularies. The bridges here are the `TwistData` analogues, with the factorisation supplied by
the chart over `⊤` being an isomorphism.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.VeryAmpleAffineBase

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (hS : IsAffineOpen (⊤ : S.Opens))

/-! ### The chart identification at the top open -/

/-- **The chart identification of the glued twists at `U = ⊤`**, in inverse-image form: the
inverse image of the degree-`n` glued twist along the chart over the whole of the base is the
absolute twist `𝒪(n)` of `Proj Γ(⊤, A)`.

This is `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chartIso` at `U = ⊤`, converted
from restriction to inverse image. It holds in every integer degree and for an arbitrary
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`. -/
def pullbackTopChartPieceIso (D : TwistData A) (n : ℤ) :
    (Scheme.Modules.pullback (topChart A hS)).obj (D.algebra.piece n) ≅
      twistingSheaf (A.grading (⊤ : S.Opens)) n :=
  letI := D.chartData.chart_isOpenImmersion (⊤ : S.Opens) hS
  ((Scheme.Modules.restrictFunctorIsoPullback (topChart A hS)).app (D.algebra.piece n)).symm ≪≫
    D.chartData.chartIso (⊤ : S.Opens) hS n

/-- The chart identification at `U = ⊤` in the restriction form the `ChartData` field is
stated in: a reusable name for `chartIso` specialised to the top open. -/
def restrictTopChartPieceIso (D : TwistData A) (n : ℤ) :
    letI := D.chartData.chart_isOpenImmersion (⊤ : S.Opens) hS
    Scheme.Modules.restrict (D.algebra.piece n) (topChart A hS) ≅
      twistingSheaf (A.grading (⊤ : S.Opens)) n :=
  D.chartData.chartIso (⊤ : S.Opens) hS n

/-- **The glued twist on a relative `Proj` over an affine base is an absolute twist.** In every
integer degree, the degree-`n` piece of the glued graded algebra is the inverse image of the
absolute twist `𝒪(n)` of `Proj Γ(⊤, A)` along the inverse of the chart over `⊤`. -/
def pieceIsoPullbackTwist (D : TwistData A) (n : ℤ) :
    D.algebra.piece n ≅
      (Scheme.Modules.pullback (inv (topChart A hS))).obj
        (twistingSheaf (A.grading (⊤ : S.Opens)) n) :=
  ((Scheme.Modules.pullbackId (relativeProj A).scheme).app (D.algebra.piece n)).symm ≪≫
    (Scheme.Modules.pullbackCongr
      (IsIso.inv_hom_id (topChart A hS)).symm).app (D.algebra.piece n) ≪≫
    ((Scheme.Modules.pullbackComp (inv (topChart A hS))
      (topChart A hS)).app (D.algebra.piece n)).symm ≪≫
    (Scheme.Modules.pullback (inv (topChart A hS))).mapIso
      (pullbackTopChartPieceIso hS D n)

/-! ### The absolute-to-relative twist bridge -/

variable {Y : Scheme.{u}}

/-- **The absolute-to-relative twist bridge.** Over an affine base, for any morphism `g` into
the absolute `Proj Γ(⊤, A)`, the inverse image along `g` of the absolute twist `𝒪(n)` is the
inverse image of the degree-`n` glued twist of `Proj_S(A)` along the corresponding morphism
`g ≫ topChart A hS`.

The degree generality is complete: this holds for every `n : ℤ`, and for an arbitrary
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`. -/
def pullbackTwistIso (D : TwistData A) (g : Y ⟶ AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens)))
    (n : ℤ) :
    (Scheme.Modules.pullback g).obj (twistingSheaf (A.grading (⊤ : S.Opens)) n) ≅
      (Scheme.Modules.pullback (g ≫ topChart A hS)).obj (D.algebra.piece n) :=
  ((Scheme.Modules.pullback g).mapIso (pullbackTopChartPieceIso hS D n)).symm ≪≫
    (Scheme.Modules.pullbackComp g (topChart A hS)).app (D.algebra.piece n)

/-- The morphism the bridge produces lies over the base: composing `g ≫ topChart A hS` with the
structure morphism of `Proj_S(A)` is composing `g` with the structure morphism
`Stacks.VeryAmpleAffineBase.projStructureHom` of the absolute `Proj`. -/
theorem pullbackTwistIso_over_base
    (g : Y ⟶ AlgebraicGeometry.Proj (A.grading (⊤ : S.Opens))) :
    (g ≫ topChart A hS) ≫ (relativeProj A).toBase = g ≫ projStructureHom A hS := by
  rw [Category.assoc, topChart_toBase]

/-- **The bridge read from the relative side.** For a morphism `h` into `Proj_S(A)` over an
affine base, the inverse image along `h` of the degree-`n` glued twist is the inverse image of
the absolute twist `𝒪(n)` of `Proj Γ(⊤, A)` along the corresponding morphism
`h ≫ inv (topChart A hS)`. -/
def pullbackPieceIso (D : TwistData A) (h : Y ⟶ (relativeProj A).scheme) (n : ℤ) :
    (Scheme.Modules.pullback h).obj (D.algebra.piece n) ≅
      (Scheme.Modules.pullback (h ≫ inv (topChart A hS))).obj
        (twistingSheaf (A.grading (⊤ : S.Opens)) n) :=
  (Scheme.Modules.pullbackCongr
      (show h = (h ≫ inv (topChart A hS)) ≫ topChart A hS by
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id])).app (D.algebra.piece n) ≪≫
    (pullbackTwistIso hS D (h ≫ inv (topChart A hS)) n).symm

/-- The morphism the relative-side bridge produces lies over the base. -/
theorem pullbackPieceIso_over_base (h : Y ⟶ (relativeProj A).scheme) :
    (h ≫ inv (topChart A hS)) ≫ projStructureHom A hS = h ≫ (relativeProj A).toBase := by
  rw [← topChart_toBase A hS, ← Category.assoc, Category.assoc h,
    IsIso.inv_hom_id, Category.comp_id]

/-! ### The bridge at the degree-`d` open of Tag 01O1 -/

/-- **The bridge at the spelling Tag 01O1 produces.** A morphism `φ` through the open
`U_d ⊆ Proj Γ(⊤, A)` of `Stacks.AlgebraicGeometry.MorphismsIntoProj.degreeOpen` has
`Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackTwist` for its pullback of the absolute
twist; this identifies that with the pullback of the degree-`n` glued twist along the
corresponding morphism into `Proj_S(A)`, for every `n : ℤ`. -/
def pullbackTwistDegreeOpenIso (D : TwistData A) {d : ℕ}
    (φ : Y ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme)
    (n : ℤ) :
    MorphismsIntoProj.pullbackTwist (A.grading (⊤ : S.Opens)) φ n ≅
      (Scheme.Modules.pullback
        (MorphismsIntoProj.toProj (A.grading (⊤ : S.Opens)) φ ≫ topChart A hS)).obj
          (D.algebra.piece n) :=
  pullbackTwistIso hS D (MorphismsIntoProj.toProj (A.grading (⊤ : S.Opens)) φ) n

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
