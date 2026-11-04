module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence

/-!
# Endomorphisms of the structure sheaf and their inverse images

For an algebraic space `X` the endomorphisms of `𝒪_X` as an `𝒪_X`-module are the global
functions, acting by multiplication.  This file records the two facts about that identification
which a computation with matrices of functions needs:

* evaluating an endomorphism at the unit function over an étale chart `U` is a ring map
  `End(𝒪_X) → 𝒪_X(U)` (`AlgebraicGeometry.Space.unitEndValue_comp`), and for the algebraic space
  of a scheme `T` its value at the identity chart is a bijection with `Γ(T, 𝒪_T)`
  (`AlgebraicGeometry.Space.unitEndValue_bijective`);
* the inverse image of Stacks 03LU, read on endomorphisms through `g^*𝒪 ≅ 𝒪`, is pullback of
  functions: over a commutative diagram of étale charts its value is the pullback of the value
  along the vertical morphism of schemes (`AlgebraicGeometry.Space.unitEndValue_pullEnd`).

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure sheaf of an algebraic space as a module over itself, as an object of the
modules of the small étale ringed topos.  The structure ring is spelled through the small étale
ringed site, as in `AlgebraicGeometry.Space.modulePullbackUnitIso`, so that the statements about
that identification apply to it verbatim. -/
abbrev unitS (X : AlgebraicSpaces B S hS) : toposModules B S hS X :=
  SheafOfModules.unit (structureRingSheaf B S hS X)

/-- The endomorphisms of the structure sheaf of an algebraic space. -/
abbrev UnitEnd (X : AlgebraicSpaces B S hS) : Type (u + 1) := unitS X ⟶ unitS X

/-- The inverse image of the structure sheaf is the structure sheaf
(`AlgebraicGeometry.Space.modulePullbackUnitIso`), as an isomorphism of modules of the small étale
ringed topos. -/
abbrev modulePullbackUnitIsoS {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    @Iso (toposModules B S hS X) _
      (((toposModulePullbackData B S hS).pull f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y)))
      (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  modulePullbackUnitIso B S hS f

/-- **The value of an endomorphism of `𝒪_X` over an étale chart**: its value on the unit
function. -/
abbrev unitEndValue {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1) (s : UnitEnd X) :
    (structureRingSheaf B S hS X).obj.obj (op U) :=
  s.val.app (op U) (1 : (structureRingSheaf B S hS X).obj.obj (op U))

/-- An endomorphism of `𝒪_X` is multiplication by its value. -/
theorem unitEnd_val_app {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1) (s : UnitEnd X)
    (x : (structureRingSheaf B S hS X).obj.obj (op U)) :
    s.val.app (op U) x = x * unitEndValue U s := by
  let one : (SheafOfModules.unit (structureRingSheaf B S hS X)).val.obj (op U) :=
    (1 : (structureRingSheaf B S hS X).obj.obj (op U))
  have h : x • one = x := mul_one x
  refine (congrArg (fun z => s.val.app (op U) z) h.symm).trans ?_
  exact (s.val.app (op U)).hom.map_smul x one

/-- **Evaluation at the unit function is multiplicative.** -/
theorem unitEndValue_comp {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
    (s t : UnitEnd X) : unitEndValue U (s ≫ t) = unitEndValue U s * unitEndValue U t :=
  unitEnd_val_app U t (unitEndValue U s)

/-- Evaluation at the unit function carries the identity to `1`. -/
theorem unitEndValue_id {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1) :
    unitEndValue U (𝟙 (unitS X)) = 1 :=
  rfl

/-- Evaluation at the unit function is additive. -/
theorem unitEndValue_add {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
    (s t : UnitEnd X) : unitEndValue U (s + t) = unitEndValue U s + unitEndValue U t :=
  rfl

/-- Evaluation at the unit function carries `0` to `0`. -/
theorem unitEndValue_zero {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1) :
    unitEndValue U (0 : UnitEnd X) = 0 :=
  rfl

/-- The value over a smaller chart is the restriction of the value. -/
theorem unitEndValue_map {X : AlgebraicSpaces B S hS} {U V : SmallEtale B S hS X.1} (g : V ⟶ U)
    (s : UnitEnd X) :
    unitEndValue V s =
      ((structureRingSheaf B S hS X).obj.map g.op).hom (unitEndValue U s) := by
  have h := congrArg (fun m => m.hom (1 : (structureRingSheaf B S hS X).obj.obj (op U)))
    (s.val.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  exact (congrArg (s.val.app (op V))
    (map_one ((structureRingSheaf B S hS X).obj.map g.op).hom).symm).trans h

/-- **The inverse image of an endomorphism of the structure sheaf**, read through `g^*𝒪 ≅ 𝒪`. -/
def pullEnd {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (s : UnitEnd Y) : UnitEnd X :=
  (modulePullbackUnitIsoS f).inv ≫ ((toposModulePullbackData B S hS).pull f).map s ≫
    (modulePullbackUnitIsoS f).hom

/-- **The inverse image of an endomorphism of `𝒪_Y` is pullback of its values.**  Over a
commutative diagram `d` of étale charts, the value of the inverse image at the chart of `X` is the
pullback along the vertical morphism of schemes of the value at the chart of `Y`. -/
theorem unitEndValue_pullEnd {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (s : UnitEnd Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    unitEndValue d.U (pullEnd f s) = chartDiagramRestrict B S hS f d (unitEndValue d.V s) := by
  let r : (structureRingSheaf B S hS Y).obj.obj (op d.V) := unitEndValue d.V s
  let x1 : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj (op d.V) :=
    (1 : (structureRingSheaf B S hS Y).obj.obj (op d.V))
  have h1 := modulePullbackUnitIso_inv_val_app_one B S hS f d
  have h2 := modulePullbackChartSection_map B S hS f (SheafOfModules.unit _) s d x1
  have h3 : s.val.app (op d.V) x1 = r • x1 := (mul_one r).symm
  have h4 := modulePullbackChartSection_smul B S hS f (SheafOfModules.unit _) d r x1
  have h5 := modulePullbackUnitIso_hom_val_app_modulePullbackChartSection B S hS f d
  refine (congrArg (fun z => (modulePullbackUnitIso B S hS f).hom.val.app (op d.U)
    (((modulePullback B S hS f).map s).val.app (op d.U) z)) h1).trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso B S hS f).hom.val.app (op d.U) z) h2).trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso B S hS f).hom.val.app (op d.U)
    (modulePullbackChartSection B S hS f _ d z)) h3).trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso B S hS f).hom.val.app (op d.U) z) h4).trans ?_
  refine ((((modulePullbackUnitIso B S hS f).hom.val.app (op d.U))).hom.map_smul _ _).trans ?_
  refine (congrArg (fun z => chartDiagramRestrict B S hS f d r • z) h5).trans ?_
  exact mul_one (chartDiagramRestrict B S hS f d r)

/-- The morphism from an étale chart of the algebraic space of a scheme `T` to its identity
chart. -/
def toYonedaEtaleChart (T : BigFppfOver B S hS) (V : SmallEtale B S hS (yoneda.obj T)) :
    V ⟶ yonedaEtaleChart B S hS T :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (yoneda.preimage (V.1.hom : yoneda.obj V.1.left ⟶ yoneda.obj T))
    ((congrArg (· ≫ 𝟙 (yoneda.obj T)) (Functor.map_preimage yoneda _)).trans
      (Category.comp_id _)))

/-- **The endomorphisms of the structure sheaf of the algebraic space of a scheme `T` are the
functions on `T`**: evaluation at the unit function over the identity chart is a bijection
`End(𝒪_T) ≃ Γ(T, 𝒪_T)`. -/
theorem unitEndValue_bijective (T : BigFppfOver B S hS) :
    Function.Bijective (unitEndValue (X := schemeSpace T) (yonedaEtaleChart B S hS T)) := by
  constructor
  · intro s t h
    refine (SheafOfModules.unitHomEquiv (SheafOfModules.unit
      (structureRingSheaf B S hS (schemeSpace T)))).injective (Subtype.ext (funext fun V => ?_))
    show unitEndValue V.unop s = unitEndValue V.unop t
    rw [unitEndValue_map (toYonedaEtaleChart T V.unop) s,
      unitEndValue_map (toYonedaEtaleChart T V.unop) t, h]
  · intro a
    let σ := yonedaGlobalFunctions B S hS T a
    let sec : (SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace T))).sections :=
      ⟨σ.1, σ.2⟩
    refine ⟨(SheafOfModules.unitHomEquiv (SheafOfModules.unit
      (structureRingSheaf B S hS (schemeSpace T)))).symm sec, ?_⟩
    exact (CategoryTheory.Sheaf.unitHomEquiv_symm_val_app_one _ sec _).trans
      (globalFunctionsChartRestriction_yonedaGlobalFunctions B S hS T a)

end AlgebraicGeometry.Space

end
