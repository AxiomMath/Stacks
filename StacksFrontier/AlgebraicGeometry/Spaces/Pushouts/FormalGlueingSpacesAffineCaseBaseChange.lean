module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# Global functions of a direct image along a base change

Let `P' = P ×_Q Q'` be a cartesian square of algebraic spaces with `g : P ⟶ Q` affine, and let
`k : Q ⟶ X` with `X` represented by a chart `Z₀`.  A section `x` of `k_*g_*𝒪_P` over `Z₀` is a
global function on `P`.  Pushing it through the unit of `h^* ⊣ h_*`, the composition comparisons
and the affine base change isomorphism of Stacks 07U8 gives a section of `(g' ≫ h ≫ k)_*𝒪_{P'}`
over `Z₀`, that is a global function on `P'`.  This file proves that it is the pullback of `x`
along `P' ⟶ P`.

## Main results

* `AlgebraicGeometry.Space.globalFunctions_ext_of_surjective`: global functions agreeing on a
  surjective étale chart agree.
* `AlgebraicGeometry.Space.globalFunctionsMap_apply_chart`: pullback of global functions,
  evaluated on a chart.
* `AlgebraicGeometry.Space.pushforwardUnitGlobal_baseChange`: the statement above.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Global functions agreeing on a surjective étale chart agree.** -/
theorem globalFunctions_ext_of_surjective (X : AlgebraicSpaces B S hS) (T : SmallEtale B S hS X.1)
    (hT : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) T.1.hom)
    {a b : globalFunctions B S hS X.1} (hab : a.1 (op T) = b.1 (op T)) : a = b := by
  apply Subtype.ext
  funext V
  let hrep := T.2.1
  let W := hrep.pullback V.unop.1.hom
  let i := hrep.fst' V.unop.1.hom
  let j := hrep.snd V.unop.1.hom
  let hp := hrep.isPullback' V.unop.1.hom
  have hjEtale := T.2.property V.unop.1.hom (yoneda.map i) j hp
  let WC := chartFromEtaleHom B S hS X W (yoneda.map j ≫ V.unop.1.hom)
    (chart_preimage_etale B S hS X V.unop.1.hom V.unop.2 j hjEtale)
  let iC : WC ⟶ T := ObjectProperty.homMk (CostructuredArrow.homMk i hp.w)
  let jC : WC ⟶ V.unop := ObjectProperty.homMk (CostructuredArrow.homMk j rfl)
  have hw : a.1 (op WC) = b.1 (op WC) := by
    rw [← a.2 iC.op, ← b.2 iC.op]
    exact congrArg _ hab
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    hT.property V.unop.1.hom (yoneda.map i) j hp
  have _ : Etale ((BigFppfOver.toScheme B S hS).map j) := hjEtale
  exact Scheme.Hom.appTop_injective_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map j) ((a.2 jC.op).trans (hw.trans (b.2 jC.op).symm))

/-- **Pullback of global functions, evaluated on a chart** factoring through a chart of the
target. -/
theorem globalFunctionsMap_apply_chart {P P' : AlgebraicSpaces B S hS} (q : P' ⟶ P)
    (s : globalFunctions B S hS P.1) (E : SmallEtale B S hS P'.1) (W : SmallEtale B S hS P.1)
    (t : (SmallEtale.toOver B S hS P'.1).obj E ⟶ (SmallEtale.toOver B S hS P.1).obj W)
    (ht : E.1.hom ≫ q.hom = yoneda.map t ≫ W.1.hom) :
    (globalFunctionsMap B S hS q s).1 (op E) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op (s.1 (op W)) := by
  have h1 := congrArg (fun z => z.1 (op E))
    ((globalFunctionsChartEquiv B S hS P').2 (globalFunctionsMap B S hS q s))
  have h2 := congrArg (fun z => z.1 (op W)) ((globalFunctionsChartEquiv B S hS P).2 s)
  have h3 := congrArg (fun z => z.1 (op ((SmallEtale.inclusion B S hS P'.1).obj E)))
    (globalFunctionsMap_chart B S hS q s)
  let m : (CostructuredArrow.map q.hom).obj ((SmallEtale.inclusion B S hS P'.1).obj E) ⟶
      (SmallEtale.inclusion B S hS P.1).obj W := CostructuredArrow.homMk t ht.symm
  have h4 := ((globalFunctionsChartEquiv B S hS P).1 s).2 m.op
  exact h1.symm.trans (h3.trans (h4.symm.trans (congrArg _ h2)))

/-- The identification `g^*𝒪_Y ≅ 𝒪_X` of Stacks 03LU carries the unit section of a regular
function to its pullback. -/
theorem modulePullbackUnitIso_hom_unitSection {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (r : chartRing B S hS Y.1 Y.2 d.V) :
    (modulePullbackUnitIso B S hS f).hom.val.app (op d.U)
        (modulePullbackUnitSection B S hS f (SheafOfModules.unit (structureRingSheaf B S hS Y))
          d r) =
      chartDiagramRestrict B S hS f d r := by
  have h1 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f
    (SheafOfModules.unit (structureRingSheaf B S hS Y)) d r
  have h2 := modulePullbackChartSection_unit B S hS f d r
  have h3 : (modulePullbackUnitIso B S hS f).hom.val.app (op d.U)
      ((modulePullbackUnitIso B S hS f).inv.val.app (op d.U)
        (1 : (structureRingSheaf B S hS X).obj.obj (op d.U))) =
        (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)) :=
    congrArg (fun m : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ _ =>
      m.val.app (op d.U) (1 : (structureRingSheaf B S hS X).obj.obj (op d.U)))
      (modulePullbackUnitIso B S hS f).inv_hom_id
  refine (congrArg ((modulePullbackUnitIso B S hS f).hom.val.app (op d.U)).hom
    (h1.trans h2)).trans ?_
  refine (((modulePullbackUnitIso B S hS f).hom.val.app (op d.U)).hom.map_smul _ _).trans ?_
  exact (congrArg (fun z => chartDiagramRestrict B S hS f d r • z) h3).trans
    ((unitModule_smul_eq_mul' B S hS X d.U _ _).trans (mul_one _))

end AlgebraicGeometry.Space
