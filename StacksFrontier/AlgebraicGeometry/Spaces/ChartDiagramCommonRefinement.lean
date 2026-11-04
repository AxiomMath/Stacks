module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleImageData

/-!
# Two commuting squares of étale charts over one chart of the source have a common refinement

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `d`, `d'` be commuting squares of étale scheme charts over `f`. If a chart `Z` of `X` maps to
both `d.U` and `d'.U`, there is a commuting square over `f` with chart `Z` of `X` whose chart of
`Y`, the fibre product `d.V ×_Y d'.V`, maps to both `d.V` and `d'.V` compatibly with the two
vertical morphisms.

## Main results

* `AlgebraicGeometry.Space.exists_dominating_chart`: a chart of `X` mapping to the charts of `X`
  of two squares over `f` carries a square whose chart of `Y` maps to both charts of `Y`,
  compatibly with the two vertical morphisms.
* `AlgebraicGeometry.Space.exists_dominating_chartSection`: the values of a linear map of
  sections along `f` at the two squares, restricted to that chart, are both values at the
  dominating square.

## References

* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- A morphism of charts of `X` into the chart `d.U` of a square over `f` gives a factorization of
the composite of the chart `Z` with `f` through the chart `d.V` of `Y`. -/
private theorem comp_hom_eq_of_map_chart_diagram (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {Z : SmallEtale B S hS X.1} (k : Z ⟶ d.U) :
    Z.1.hom ≫ f.hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map k ≫ d.g) ≫ d.V.1.hom := by
  have hk : yoneda.map ((SmallEtale.toOver B S hS X.1).map k) ≫ d.U.1.hom = Z.1.hom :=
    CostructuredArrow.w k.hom
  rw [Functor.map_comp, Category.assoc, ← d.comm, ← hk, Category.assoc]

/-- Two commuting squares of étale scheme charts over `f` whose charts of `X` both receive a chart
`Z` are dominated by a square with chart `Z` of `X`: its chart of `Y` maps to both charts of `Y`,
and its vertical morphism composed with these maps is the vertical morphism of the square through
`d`, respectively through `d'`, precomposed with the given morphism of charts of `X`. -/
theorem exists_dominating_chart (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    {Z : SmallEtale B S hS X.1} (k : Z ⟶ d.U) (i : Z ⟶ d'.U) :
    ∃ (W : SmallEtale B S hS Y.1)
      (g : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj W)
      (_ : Z.1.hom ≫ f.hom = yoneda.map g ≫ W.1.hom) (p : W ⟶ d.V) (q : W ⟶ d'.V),
      (SmallEtale.toOver B S hS X.1).map k ≫ d.g =
          g ≫ (SmallEtale.toOver B S hS Y.1).map p ∧
        (SmallEtale.toOver B S hS X.1).map i ≫ d'.g =
          g ≫ (SmallEtale.toOver B S hS Y.1).map q := by
  have hc := comp_hom_eq_of_map_chart_diagram B S hS f d k
  have hc' := comp_hom_eq_of_map_chart_diagram B S hS f d' i
  have hboth : yoneda.map ((SmallEtale.toOver B S hS X.1).map k ≫ d.g) ≫ d.V.1.hom =
      yoneda.map ((SmallEtale.toOver B S hS X.1).map i ≫ d'.g) ≫ d'.V.1.hom :=
    hc.symm.trans hc'
  refine ⟨SmallEtale.prodObj B S hS Y.1 d.V d'.V,
    d.V.property.rep.lift' ((SmallEtale.toOver B S hS X.1).map k ≫ d.g)
      ((SmallEtale.toOver B S hS X.1).map i ≫ d'.g) hboth, ?_,
    SmallEtale.prodFst B S hS Y.1 d.V d'.V, SmallEtale.prodSnd B S hS Y.1 d.V d'.V,
    (d.V.property.rep.lift'_fst _ _ hboth).symm,
    (d.V.property.rep.lift'_snd _ _ hboth).symm⟩
  have hp : yoneda.map ((SmallEtale.toOver B S hS Y.1).map
      (SmallEtale.prodFst B S hS Y.1 d.V d'.V)) ≫ d.V.1.hom =
      (SmallEtale.prodObj B S hS Y.1 d.V d'.V).1.hom :=
    CostructuredArrow.w (SmallEtale.prodFst B S hS Y.1 d.V d'.V).hom
  rw [hc, ← hp, ← Category.assoc]
  exact congrArg (· ≫ d.V.1.hom) ((yoneda.map_comp _ _).symm.trans
    (congrArg yoneda.map (d.V.property.rep.lift'_fst _ _ hboth))).symm

/-- Over a chart of `X` receiving the charts of `X` of two squares over `f`, the restrictions of
the values of a linear map of sections along `f` at the two squares are both values at one
square. -/
theorem exists_dominating_chartSection {N : Modules.{u, u} B S hS X.1 X.2}
    {M : Modules.{u, u} B S hS Y.1 Y.2} (ξ : ModuleFMap B S hS f N M)
    (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    {Z : SmallEtale B S hS X.1} (k : Z ⟶ d.U) (i : Z ⟶ d'.U)
    (s : M.val.obj (op d.V)) (s' : M.val.obj (op d'.V)) :
    ∃ (W : SmallEtale B S hS Y.1)
      (g : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj W)
      (hc : Z.1.hom ≫ f.hom = yoneda.map g ≫ W.1.hom) (p : W ⟶ d.V) (q : W ⟶ d'.V),
      ξ.app ⟨Z, W, g, hc⟩ (M.val.map p.op s) = N.val.map k.op (ξ.app d s) ∧
        ξ.app ⟨Z, W, g, hc⟩ (M.val.map q.op s') = N.val.map i.op (ξ.app d' s') := by
  obtain ⟨W, g, hc, p, q, hp, hq⟩ := exists_dominating_chart B S hS f d d' k i
  exact ⟨W, g, hc, p, q, ξ.naturality d ⟨Z, W, g, hc⟩ k p hp s,
    ξ.naturality d' ⟨Z, W, g, hc⟩ i q hq s'⟩

end AlgebraicGeometry.Space

end
