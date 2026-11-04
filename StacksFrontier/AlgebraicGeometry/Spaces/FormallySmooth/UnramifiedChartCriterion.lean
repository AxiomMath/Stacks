module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Factor
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion

/-!
# Formal unramifiedness is an étale-chart condition

A morphism of algebraic spaces over a scheme is formally unramified exactly when the morphism
of schemes underlying every commuting square of étale scheme charts is formally unramified, and
exactly when that holds for one such square whose two chart maps are surjective.

## Main results

* `AlgebraicGeometry.Space.formallyUnramified_of_surjectiveEtaleChart'`: formal unramifiedness
  descends from one square of étale charts whose source chart is surjective.  This is the
  hypothesis-weakening variant of
  `AlgebraicGeometry.Space.formallyUnramified_of_surjectiveEtaleChart`, which asks both charts
  to be surjective and takes its data as an existential.
* `AlgebraicGeometry.Space.formallyUnramified_iff_etaleCharts`: **Stacks 04G8**, the
  equivalence of (1) and (2).
* `AlgebraicGeometry.Space.formallyUnramified_iff_surjectiveEtaleChart`: **Stacks 04G8**, the
  equivalence of (1) and (3).

## Implementation notes

The implication from the algebraic-space side to the chart side is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_formallyUnramified`. The converse is the
descent half of Tag 04CY: given a surjective étale chart `a : yoneda.obj U ⟶ X` and an étale
chart `b : yoneda.obj V ⟶ Y` with `a ≫ f = yoneda.map ψ ≫ b`, the composite `a ≫ f` is
formally unramified because `yoneda.map ψ` and `b` are, and
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated` then transfers this to
`f`. That statement
asks for `X` to be a sheaf for the *étale* topology on the slice, which an algebraic space is
because the étale topology is contained in the fppf one — every selected étale covering family
is in particular a selected fppf covering family.

Passing from formal unramifiedness of the scheme morphism underlying `ψ` to formal
unramifiedness of `yoneda.map ψ` is immediate: a lift of a square against `yoneda.obj U` *is* a
morphism of the site, and `AlgebraicGeometry.FormallyUnramified.hom_ext` identifies two such
after applying `AlgebraicGeometry.BigFppfOver.toScheme`, which is faithful.

## References

* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over `S` is a sheaf for the étale topology on the slice. -/
public theorem isSheaf_etaleTopology_over_of_isAlgebraicSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) :
    Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) X :=
  hX.isSheaf.of_le (etaleTopologyOver_le_topology B S hS)

/-- **Stacks 04G8, (3) implies (1).** Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`, let `a : yoneda.obj U ⟶ X` be a surjective étale chart, let `b : yoneda.obj V ⟶ Y` be an
étale chart and let `ψ : U ⟶ V` make the square commute. If the morphism of schemes underlying
`ψ` is formally unramified, then `f` is formally unramified. -/
public theorem formallyUnramified_of_surjectiveEtaleChart'
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hdiag : a ≫ f = yoneda.map ψ ≫ b)
    (hψ : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallyUnramified f := by
  have hcomp : FormallyUnramified (a ≫ f) :=
    hdiag ▸ formallyUnramified_comp (yoneda.map ψ) b
      (formallyUnramified_yoneda_map_of_formallyUnramified_map B S hS ψ hψ)
      (formallyUnramified_of_etale B S hS b hb)
  exact formallyUnramified_of_comp_of_isSeparated
    { B := B, S := S, hS := hS, F := yoneda.obj U, G := X, H := Y, a := a, b := f
      representable_a := ha.1, surjective_a := haSurj, etale_a := ha }
    ((isSheaf_iff_isSheaf_of_type _ X).mp
      (isSheaf_etaleTopology_over_of_isAlgebraicSpace B S hS hX)).isSeparated hcomp

/-- **Stacks 04G8, the equivalence of (1) and (2).** A morphism of algebraic spaces over `S` is
formally unramified exactly when the morphism of schemes underlying every commuting square of
étale scheme charts is formally unramified. -/
@[stacks 04G8 "equivalence of (1) and (2)"]
public theorem formallyUnramified_iff_etaleCharts
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallyUnramified f ↔
      HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) f := by
  refine ⟨holdsOnEveryEtaleChart_of_formallyUnramified B S hS f, fun hall ↦ ?_⟩
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact formallyUnramified_of_surjectiveEtaleChart' B S hS hX f a b ψ haEtale hbEtale haSurj
    hdiag (hall U V a b ψ haEtale hbEtale hdiag.symm)

/-- **Stacks 04G8, the equivalence of (1) and (3).** A morphism of algebraic spaces over `S` is
formally unramified exactly when there is one commuting square of étale scheme charts, both
chart maps surjective, whose underlying morphism of schemes is formally unramified. -/
@[stacks 04G8 "equivalence of (1) and (3)"]
public theorem formallyUnramified_iff_surjectiveEtaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallyUnramified f ↔
      ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V),
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf b ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf b ∧
        yoneda.map ψ ≫ b = a ≫ f ∧
        _root_.AlgebraicGeometry.FormallyUnramified
          ((BigFppfOver.toScheme B S hS).map ψ) := by
  constructor
  · intro hf
    obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
    obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
    exact ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm,
      (formallyUnramified_iff_etaleCharts B S hS hX hY f).mp hf U V a b ψ haEtale hbEtale
        hdiag.symm⟩
  · rintro ⟨U, V, a, b, ψ, ha, hb, haSurj, -, hdiag, hψ⟩
    exact formallyUnramified_of_surjectiveEtaleChart' B S hS hX f a b ψ ha hb haSurj
      hdiag.symm hψ

end AlgebraicGeometry.Space

end
