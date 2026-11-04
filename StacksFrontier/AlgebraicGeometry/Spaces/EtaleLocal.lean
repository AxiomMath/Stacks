module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Lifting a surjective étale chart through a morphism of presheaves (Stacks 02X1)

Let `a : F ⟶ G` be a morphism of presheaves on the big fppf site of `S` whose source is an
algebraic space. Every surjective étale scheme chart of `G` is dominated by a surjective étale
scheme chart of `F`.

## Main results

* `AlgebraicGeometry.Space.exists_surjective_etale_chart_lift`: a surjective étale scheme chart
  of the target of a morphism out of an algebraic space is dominated by a surjective étale scheme
  chart of the source.
* `AlgebraicGeometry.Space.isStableUnderComposition_presheaf_inverseImage`: a multiplicative
  property of morphisms of schemes, tested on charts, is stable under composition.

## Implementation notes

A chart of a presheaf `F` is a morphism `yoneda.obj U ⟶ F` from a representable presheaf, and
its étaleness or surjectivity is the corresponding relative morphism property
`CategoryTheory.MorphismProperty.presheaf`, which carries representability with it. The
pullbacks of charts are therefore the represented pullbacks of
`CategoryTheory.Functor.relativelyRepresentable`, and the argument is carried out in the site
rather than in schemes: the relative property is stable under base change for any tested
property and under composition because `AlgebraicGeometry.Etale` and
`AlgebraicGeometry.Surjective` are.

One hypothesis of the source statement is not needed and is omitted: in
`AlgebraicGeometry.Space.exists_surjective_etale_chart_lift` the target need not be an
algebraic space, since the chart `q` of the target is assumed étale and hence representable.
The statement therefore covers the source one.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stability of the chart conditions under composition -/

/-- A multiplicative property of morphisms of schemes, tested on the charts of presheaves on the
big fppf site of `S`, is stable under composition. -/
theorem isStableUnderComposition_presheaf_inverseImage (Q : MorphismProperty Scheme.{u})
    [Q.IsMultiplicative] :
    MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf) :=
  have : Q.IsStableUnderComposition :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  MorphismProperty.relative_isStableUnderComposition (F := yoneda) _

/-! ### Lifting a chart of the target to a chart of the source -/

/-- Let `a : F ⟶ G` be a morphism of presheaves on the big fppf site of `S` with `F` an
algebraic space over `S`. Every surjective étale scheme chart `q : yoneda.obj V ⟶ G` is
dominated by a surjective étale scheme chart of `F`: there are an object `U` of the site, a
surjective étale chart `p : yoneda.obj U ⟶ F` and a morphism `α : U ⟶ V` making the square
commute. -/
@[stacks 02X1]
theorem exists_surjective_etale_chart_lift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (a : F ⟶ G) (V : BigFppfOver B S hS)
    (q : yoneda.obj V ⟶ G)
    (hq_surjective : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hq_etale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F) (α : U ⟶ V),
      p ≫ a = yoneda.map α ≫ q ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p := by
  obtain ⟨W, p₀, hp₀_surjective, hp₀_etale⟩ := hF.exists_atlas
  have key : ∀ (Q : MorphismProperty Scheme.{u}) [Q.IsMultiplicative] [Q.IsStableUnderBaseChange],
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf q →
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf p₀ →
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (hq_etale.rep.snd (p₀ ≫ a)) ≫ p₀) := by
    intro Q _ _ hq hp
    have := isStableUnderComposition_presheaf_inverseImage B S hS Q
    have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS))
    exact MorphismProperty.comp_mem _ _ _
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (hq_etale.rep.isPullback' (p₀ ≫ a)) hq) hp
  refine ⟨hq_etale.rep.pullback (p₀ ≫ a), yoneda.map (hq_etale.rep.snd (p₀ ≫ a)) ≫ p₀,
    hq_etale.rep.fst' (p₀ ≫ a), ?_, key _ hq_surjective hp₀_surjective,
    key _ hq_etale hp₀_etale⟩
  rw [Category.assoc]
  exact (hq_etale.rep.isPullback' (p₀ ≫ a)).w.symm

end AlgebraicGeometry.Space

end
