module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence

/-!
# The chart morphism attached to a comorphism through a thickening lies over a space under `W`

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `c : X ⟶ W`, let `r : W ⟶ W'` and let `a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a morphism of
sheaves of rings agreeing with the comorphism of `c` read through the thickening on the regular
functions read from `W'`.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartOverBase.lean` proves that
the morphism of charts attached to `a` then lies over `S`.

This file proves the sharper statement from which that one follows: the morphism of charts
attached to `a` **agrees with the one `c` itself induces after composition with the chart
morphism to the affine chart `V'` of `W'`.**  That is the equation
`AlgebraicGeometry.ext_of_isAffine` gives at `V'`, before it is composed with the structure
morphism of `V'`; and it says exactly that the attached morphism of charts is a morphism *over
`W'`*, not merely over `S`.

For `W' = X` and `r` a retraction of `c` — the situation of [Stacks Project, Tag 0CKE], where
`c` is a section of the source of a groupoid and `r` is that source — this is the first clause of
the lifting condition `AlgebraicGeometry.Space.IsChartLift`: the attached morphism of charts is a
**section of `r` over the chart of `X`**.

## Main results

* `AlgebraicGeometry.comp_eq_of_appTop_comp_eq_of_isAffine`: two morphisms into a scheme agree
  after a morphism into an affine scheme as soon as their maps of regular functions agree on the
  functions read from it.
* `AlgebraicGeometry.Space.appTop_comp_thickeningLiftChartHom_appTop_eq`: the attached map of
  regular functions agrees with the chartwise pullback on the functions pulled back from the
  target chart of a chart diagram.
* `AlgebraicGeometry.Space.thickeningLiftChartHom_comp_chartBaseChangeMap_eq_of_chartDiagram`
  and `AlgebraicGeometry.Space.thickeningLiftChartHom_comp_chartBaseChangeMap_eq`: **the
  attached morphism of charts agrees with the one `c` induces after the chart morphism to the
  affine chart of `W'`.**
* `AlgebraicGeometry.Space.comp_chartBaseChangeMap_eq_of_toScheme_map_eq`: the same for a
  morphism of the site lifting it, the functor to schemes being faithful.
* `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq`: **the attached morphism of
  charts, read as a section of `W` over the chart of `X`, lies over `W'`.**
* `AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq_of_index`: the same for a solution
  of the lifting problem indexed by a morphism out of the thickening.

## Implementation notes

The map of regular functions is compared exactly as in
`AlgebraicGeometry.Space.thickeningLiftChartHom_comp_structureHom`, whose proof contains this
comparison as an intermediate step; it is restated here on its own, because the conclusion
wanted is the equation at the affine factor rather than its composite with a morphism out of
that factor.

**No `@[stacks]` attribute is placed.**  As in the files this one extends, what is proved is a
comparison internal to this development of two readings of [Stacks Project, Tag 03G8].

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this step is an
  input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry

/-- **Two morphisms into a scheme agree after a morphism into an affine scheme, as soon as their
maps of regular functions agree on the functions read from that affine scheme.**  This is
`AlgebraicGeometry.ext_of_isAffine` at the affine scheme, and it is the equation
`AlgebraicGeometry.comp_eq_comp_of_appTop_comp_eq_of_isAffine` proves before composing with a
morphism out of that scheme. -/
theorem comp_eq_of_appTop_comp_eq_of_isAffine {V' V T : Scheme.{u}} [IsAffine T]
    (p : V ⟶ T) {ψ χ : V' ⟶ V}
    (h : p.appTop ≫ ψ.appTop = p.appTop ≫ χ.appTop) : ψ ≫ p = χ ≫ p :=
  ext_of_isAffine
    ((Scheme.Hom.comp_appTop ψ p).trans (h.trans (Scheme.Hom.comp_appTop χ p).symm))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The comparison of the maps of regular functions -/

/-- **The map of regular functions attached to `a` over an affine chart agrees with the
chartwise pullback on the functions read from an affine scheme `T`**, as soon as `a` agrees
there with the comorphism of `c` read through the thickening.

This is the intermediate step of
`AlgebraicGeometry.Space.thickeningLiftChartHom_comp_structureHom`, stated on its own. -/
theorem appTop_comp_thickeningLiftChartHom_appTop_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    {T : Scheme.{u}} [IsAffine T]
    (p : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V) ⟶ T)
    (hbase : ∀ y : Γ(T, (⊤ : T.Opens)),
      a.hom.app (op V) (p.appTop y) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op V) (p.appTop y)) :
    p.appTop ≫ (thickeningLiftChartHom B S hS Z hZ c a V j).appTop =
      p.appTop ≫
        ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c V j)).appTop := by
  refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
  refine ((congrArg (fun φ ↦ φ (p.appTop y))
    (thickeningLiftChartHom_appTop B S hS Z hZ c a V j)).trans ?_).trans
    (toScheme_map_chartBaseChangeMap_appTop B S hS c V j (p.appTop y)).symm
  refine (thickeningLiftChartAppTop_congr B S hS Z hZ c a
    (structureSharpThroughThickening B S hS Z c) V j (p.appTop y) (hbase y)).trans ?_
  exact congrArg (fun φ : ToType ((structureRingSheaf B S hS W).obj.obj (op V)) →+*
      ToType ((structureRingSheaf B S hS X).obj.obj j.right) ↦ φ (p.appTop y))
    (thickeningLiftChartAppTop_structureSharpThroughThickening B S hS Z hZ c V j)

/-! ### The attached morphism of charts lies over `W'` -/

/-- **The morphism of charts attached to `a` agrees with the one `c` induces after the chart
morphism to the affine chart of `W'`, with the condition read off a chart diagram.**  Both are
morphisms of schemes from the chart `j` of `X` to the affine chart `V'` of `W'`, so
`AlgebraicGeometry.ext_of_isAffine` applies there, and what has to be checked is agreement of
their maps of regular functions on the functions pulled back from `V'`. -/
theorem thickeningLiftChartHom_comp_chartBaseChangeMap_eq_of_chartDiagram
    (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ y : ToType ((structureRingSheaf B S hS W').obj.obj (op V')),
      a.hom.app (op m.right.unop) (chartPullbackRingHom B S hS r V' m y) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op m.right.unop)
          (chartPullbackRingHom B S hS r V' m y)) :
    thickeningLiftChartHom B S hS Z hZ c a m.right.unop j ≫
        (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m) =
      (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c m.right.unop j) ≫
        (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m) :=
  comp_eq_of_appTop_comp_eq_of_isAffine
    ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m))
    (appTop_comp_thickeningLiftChartHom_appTop_eq B S hS Z hZ c a m.right.unop j
      ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m)) hbase)

/-- **The morphism of charts attached to `a` agrees with the one `c` induces after the chart
morphism to the affine chart of `W'`.**  The regular functions on `V'` pull back to values of
`r^♯`, by
`AlgebraicGeometry.Space.exists_app_structureSharpRingInverseImage_eq_chartPullbackRingHom`. -/
theorem thickeningLiftChartHom_comp_chartBaseChangeMap_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj
        (op m.right.unop)),
      a.hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s)) :
    thickeningLiftChartHom B S hS Z hZ c a m.right.unop j ≫
        (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m) =
      (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS c m.right.unop j) ≫
        (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS r V' m) :=
  thickeningLiftChartHom_comp_chartBaseChangeMap_eq_of_chartDiagram B S hS Z hZ c a r V' m j
    fun y ↦ by
      obtain ⟨s, hs⟩ :=
        exists_app_structureSharpRingInverseImage_eq_chartPullbackRingHom B S hS r V' m y
      rw [← hs]
      exact hbase s

/-- **The same for a morphism of the site lifting the attached morphism of charts.**  The
functor from the big fppf category over `S` to schemes is faithful, so the equation of schemes
is an equation of the site. -/
theorem comp_chartBaseChangeMap_eq_of_toScheme_map_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj
        (op m.right.unop)),
      a.hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s))
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj m.right.unop)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c a m.right.unop j) :
    ψ ≫ chartBaseChangeMap B S hS r V' m =
      chartBaseChangeMap B S hS c m.right.unop j ≫ chartBaseChangeMap B S hS r V' m :=
  (BigFppfOver.toScheme B S hS).map_injective
    (((BigFppfOver.toScheme B S hS).map_comp ψ (chartBaseChangeMap B S hS r V' m)).trans
      (((congrArg (fun z ↦ z ≫ (BigFppfOver.toScheme B S hS).map
              (chartBaseChangeMap B S hS r V' m)) hψ).trans
          (thickeningLiftChartHom_comp_chartBaseChangeMap_eq B S hS Z hZ c a r V' m j
            hbase)).trans
        ((BigFppfOver.toScheme B S hS).map_comp
          (chartBaseChangeMap B S hS c m.right.unop j)
          (chartBaseChangeMap B S hS r V' m)).symm))

/-- **The attached morphism of charts, read as a section of `W` over the chart of `X`, lies over
`W'`.**  The section of `W` over the chart `j` of `X` given by the attached morphism of charts
followed by the chart `m ⟶ W` has the same composite with `r` as the chart `j ⟶ X` followed by
`c ≫ r`.

For `W' = X` and `r` a retraction of `c` this is the first clause of the lifting condition
`AlgebraicGeometry.Space.IsChartLift`. -/
theorem yoneda_map_comp_chart_hom_comp_eq (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W) (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj
        (op m.right.unop)),
      a.hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s) =
        (structureSharpThroughThickening B S hS Z c).hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s))
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj m.right.unop)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c a m.right.unop j) :
    (yoneda.map ψ ≫ m.right.unop.1.hom) ≫ r.hom =
      j.right.unop.1.hom ≫ c.hom ≫ r.hom := by
  have hm : yoneda.map (chartBaseChangeMap B S hS r V' m) ≫ V'.1.hom =
      m.right.unop.1.hom ≫ r.hom :=
    (chartBaseChangeMap_comm B S hS r m.right.unop V' m.hom.unop).symm
  have hj : yoneda.map (chartBaseChangeMap B S hS c m.right.unop j) ≫
      m.right.unop.1.hom = j.right.unop.1.hom ≫ c.hom :=
    (chartBaseChangeMap_comm B S hS c j.right.unop m.right.unop j.hom.unop).symm
  have hcomp := congrArg (fun z ↦ yoneda.map z ≫ V'.1.hom)
    (comp_chartBaseChangeMap_eq_of_toScheme_map_eq B S hS Z hZ c a r V' m j hbase ψ hψ)
  simp only [Functor.map_comp, Category.assoc, hm] at hcomp
  rw [Category.assoc]
  refine hcomp.trans ?_
  rw [← Category.assoc, hj, Category.assoc]

/-- **The same for a solution of the lifting problem read at the index `e`**, which is the
index `AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening` produces.  This is
`AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_comp_eq` with the index transported, exactly
as `AlgebraicGeometry.Space.exists_thickeningLiftChartSiteHom_of_index` transports it. -/
theorem yoneda_map_comp_chart_hom_comp_eq_of_index (hZ : IsThickening B S hS X Z.1)
    (c : X ⟶ W)
    (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (he : subspaceInclusion B S hS X Z ≫ c = e)
    (a : structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS e).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    {W' : AlgebraicSpaces B S hS} (r : W ⟶ W') (V' : SmallEtale B S hS W'.1)
    (m : StructuredArrow (op (chartBaseChange B S hS r V'))
      (comparisonFunctor B S hS W).op)
    (j : StructuredArrow (op (chartBaseChange B S hS c m.right.unop))
      (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.1).obj m.right.unop))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W'.1).obj V'))]
    (hbase : ∀ s : ToType ((structureRingSheafInverseImage B S hS r).obj.obj
        (op m.right.unop)),
      a.hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s) =
        (structureSharpThroughThickeningAt B S hS Z c e he).hom.app (op m.right.unop)
          ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s))
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj m.right.unop)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c (thickeningLiftOfIndex B S hS Z c e he a)
        m.right.unop j) :
    (yoneda.map ψ ≫ m.right.unop.1.hom) ≫ r.hom =
      j.right.unop.1.hom ≫ c.hom ≫ r.hom :=
  yoneda_map_comp_chart_hom_comp_eq B S hS Z hZ c
    (thickeningLiftOfIndex B S hS Z c e he a) r V' m j
    (fun s ↦ (app_thickeningLiftOfIndex_congr B S hS Z c e he a
          (structureSharpThroughThickeningAt B S hS Z c e he) (op m.right.unop) _
          (hbase s)).trans
      (congrArg (fun n : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c ↦
          n.hom.app (op m.right.unop)
            ((structureSharpRingInverseImage B S hS r).hom.app (op m.right.unop) s))
        (thickeningLiftOfIndex_structureSharpThroughThickeningAt B S hS Z c e he)))
    ψ hψ

end Space

end AlgebraicGeometry

end
