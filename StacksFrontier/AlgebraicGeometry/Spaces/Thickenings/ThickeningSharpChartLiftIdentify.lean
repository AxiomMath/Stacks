module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# A morphism of sheaves of rings is determined on a cover-dense class of charts

The identification of the glued section of [Stacks Project, Tag 0CKE] with the solution of the
lifting problem compares two morphisms of sheaves of rings on the small étale site of an
algebraic space, and the comparison is available only over the charts carrying an affine chart
diagram.  This file records that this is enough: a morphism of sheaves of rings is determined by
its values over a cover-dense class of étale charts, the target being a sheaf and the agreement
of two morphisms at a chart being inherited by every chart above it.

## Main results

* `AlgebraicGeometry.Space.ringSheafHom_ext_of_cover`: **two morphisms of sheaves of rings on the
  small étale site of an algebraic space which agree on the sections over every chart of a
  cover-dense class are equal.**

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this
  extensionality is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Two morphisms of sheaves of rings on the small étale site agreeing over a cover-dense class
of charts are equal.**

The hypothesis `hP` is cover-density of the class `Pp` in the form
`AlgebraicGeometry.Space.mem_topology_of_hasChartHomToAffineChartDiagram` and
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram` supply it: a sieve containing
every arrow whose source lies in the class is covering.

Agreement over a chart of the class is inherited by every chart below it, by naturality, so the
two sections of the target over an arbitrary chart agree on a covering sieve; the target is a
sheaf, hence a separated presheaf. -/
theorem ringSheafHom_ext_of_cover {X : AlgebraicSpaces B S hS}
    {F G : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (Pp : SmallEtale B S hS X.1 → Prop)
    (hP : ∀ (V : SmallEtale B S hS X.1) (R : Sieve V),
      (∀ ⦃K : SmallEtale B S hS X.1⦄ (n : K ⟶ V), Pp K → R.arrows n) →
        R ∈ SmallEtale.topology B S hS X.1 V)
    (a b : F ⟶ G)
    (h : ∀ (V : SmallEtale B S hS X.1), Pp V →
      ∀ x : ToType (F.obj.obj (op V)), a.hom.app (op V) x = b.hom.app (op V) x) :
    a = b := by
  have hGsep : Presheaf.IsSeparated (SmallEtale.topology B S hS X.1)
      (G.obj ⋙ CategoryTheory.forget RingCat.{u}) :=
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).obj G).property.isSeparated
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ RingCat.hom_ext (RingHom.ext fun x ↦ ?_)))
  refine hGsep V.unop (Sieve.generate fun (K : SmallEtale B S hS X.1) (_ : K ⟶ V.unop) ↦ Pp K)
    (hP V.unop _ fun {K} n hn ↦ ⟨K, 𝟙 K, n, hn, Category.id_comp n⟩) _ _ ?_
  rintro K n ⟨K', g, m, hm, rfl⟩
  have key : ∀ c : F ⟶ G,
      (G.obj ⋙ CategoryTheory.forget RingCat.{u}).map (g ≫ m).op (c.hom.app V x) =
        (G.obj ⋙ CategoryTheory.forget RingCat.{u}).map g.op
          (c.hom.app (op K') ((F.obj ⋙ CategoryTheory.forget RingCat.{u}).map m.op x)) := by
    intro c
    rw [← Stacks.Sites.map_map (F := G.obj ⋙ CategoryTheory.forget RingCat.{u}) m g
      (c.hom.app V x)]
    exact congrArg _ (congrArg (fun r : F.obj.obj V ⟶ G.obj.obj (op K') ↦ ConcreteCategory.hom r x)
      (c.hom.naturality m.op)).symm
  change (G.obj ⋙ CategoryTheory.forget RingCat.{u}).map (g ≫ m).op (a.hom.app V x) =
    (G.obj ⋙ CategoryTheory.forget RingCat.{u}).map (g ≫ m).op (b.hom.app V x)
  rw [key a, key b, h K' hm]

/-! ### The chart morphism of a solution agrees with that of `c` on the thickening -/

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The chart morphism attached to a solution of the lifting problem agrees with the chart
morphism of `c` on the part of the chart lying in `Z`, as a morphism into the chart `V`.**

This is `AlgebraicGeometry.Space.comp_rep_snd_eq_of_toScheme_map_eq` with the agreement moved
from the representable projection of `Z ×_X V'` onto the inclusion of the preimage subfunctor,
which is the spelling
`AlgebraicGeometry.Space.comp_chartBaseChangeMap_eq_of_thickeningRestriction_eq` asks for.  The
preimage is the range of the projection
(`AlgebraicGeometry.Space.preimage_eq_range_rep_snd`), and a morphism onto its range is an
epimorphism, so the projection cancels on the left.

Note that the agreement is genuinely at the level of the chart: the weaker statement
`AlgebraicGeometry.Space.yoneda_map_comp_chart_hom_eq_restriction`, which is the same agreement
composed with the structure morphism of `V`, could not give it — two sections of an étale
morphism agreeing over the base need not be equal. -/
theorem comp_preimage_ι_eq_chartBaseChangeMap (hZ : IsThickening B S hS X Z.1) (c : X ⟶ W)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj V))]
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj V)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ =
      thickeningLiftChartHom B S hS Z hZ c a V j) :
    (Z.1.preimage j.right.unop.1.hom).ι ≫ yoneda.map ψ =
      (Z.1.preimage j.right.unop.1.hom).ι ≫
        yoneda.map (chartBaseChangeMap B S hS c V j) := by
  have h : yoneda.map (Z.2.2.rep.snd j.right.unop.1.hom) ≫ yoneda.map ψ =
      yoneda.map (Z.2.2.rep.snd j.right.unop.1.hom) ≫
        yoneda.map (chartBaseChangeMap B S hS c V j) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      comp_rep_snd_eq_of_toScheme_map_eq B S hS Z hZ c a hred V j ψ hψ]
  rw [preimage_eq_range_rep_snd B S hS X Z _ j.right.unop.1.hom]
  exact (cancel_epi (Subfunctor.toRange
      (yoneda.map (Z.2.2.rep.snd j.right.unop.1.hom)))).1
    (by simpa only [← Category.assoc, Subfunctor.toRange_ι] using h)

end AlgebraicGeometry.Space

end
