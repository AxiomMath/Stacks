module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartBase

/-!
# The chart thickenings of a square-zero extension over the base scheme

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
over `S`, as an algebra over `f⁻¹𝒪_Y` for `f : X ⟶ Y` (the data of Stacks 05ZT). Composing the
algebra structure with the structure map of `g : Y ⟶ Z` makes `E` an algebra over
`(f ≫ g)⁻¹𝒪_Z`. For `Z` the base `S` itself, the chart thickening `U'` of every étale chart `U`
of `X` maps to `S` extending the structure morphism of `U`, compatibly with the morphisms
`V' ⟶ U'`. These are the structure morphisms making `U'` a scheme over `S`, which the proof of
Stacks 05ZT needs in order to form the quotient `U'/R'` over `S`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.compToBase`: `E` as an algebra over `(f ≫ g)⁻¹𝒪_Z`.
* `AlgebraicGeometry.Space.baseAlgebraicSpace`: the base `S` as an algebraic space over itself.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeToBaseScheme`: `U' ⟶ S`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartInclusion_comp_chartRealizedSchemeToBaseScheme`
* `Space.SquareZeroExtension.chartRealizedSchemeMap_comp_chartRealizedSchemeToBaseScheme`

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The base `S`, as an algebraic space over itself: the final object. -/
abbrev baseAlgebraicSpace : AlgebraicSpaces B S hS :=
  schemeSpace (BigFppfOver.terminalObj B S hS)

/-- The structure morphism of an algebraic space over `S`. -/
noncomputable def toBaseAlgebraicSpace (X : AlgebraicSpaces B S hS) :
    X ⟶ baseAlgebraicSpace B S hS :=
  ObjectProperty.homMk ((isTerminal_yoneda_obj_base B S hS).from X.1)

variable (B S hS) in
/-- The base `S`, as an étale chart of itself. -/
abbrev baseChart : SmallEtale B S hS (baseAlgebraicSpace B S hS).1 :=
  idEtaleChart B S hS (BigFppfOver.terminalObj B S hS)

/-- The chart diagram of an étale chart `U` of `X` over the base chart: the structure morphism
of `U`. -/
noncomputable def baseSpaceChartDiagram {X : AlgebraicSpaces B S hS}
    (h : X ⟶ baseAlgebraicSpace B S hS) (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 (baseAlgebraicSpace B S hS).1 h.hom where
  U := U
  V := baseChart B S hS
  g := Over.homMk U.obj.left.hom
  comm := (isTerminal_yoneda_obj_base B S hS).hom_ext _ _

namespace SquareZeroExtension

variable {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **The algebra structure over `(f ≫ g)⁻¹𝒪_Z`**: the algebra structure of the extension
composed with the inverse image along `f` of the structure map `g⁻¹𝒪_Z ⟶ 𝒪_Y` of `g`. -/
noncomputable def compToBase (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Z).O ⟶ E.A :=
  (smallEtaleRingedToposHom_compInverseImageRingIso B S hS f g).inv.app _ ≫
    (smallEtaleInverseImageRing B S hS f).map
      (smallEtaleRingedToposHom B S hS g).fSharpInverseImage ≫ E.toBase

/-- The composed algebra structure lifts the structure map of `f ≫ g`. -/
theorem compToBase_π (g : Y ⟶ Z) :
    E.compToBase g ≫ E.π = (smallEtaleRingedToposHom B S hS (f ≫ g)).fSharpInverseImage := by
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) E.toBase_π))).trans ?_)
  exact (congrArg (_ ≫ ·)
    (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS f g).symm).trans
    (Iso.inv_hom_id_app_assoc _ _ _)

/-- **The structure morphism `U' ⟶ S` of the chart thickening of an étale chart `U`**: the
morphism to the base chart given by the composed algebra structure over `S`. -/
noncomputable def chartRealizedSchemeToBaseScheme (U : SmallEtale B S hS X.1) :
    E.chartRealizedScheme U ⟶ chartScheme (baseChart B S hS) :=
  E.chartRealizedSchemeToBase (E.compToBase (toBaseAlgebraicSpace Y))
    (E.compToBase_π (toBaseAlgebraicSpace Y)) (baseSpaceChartDiagram _ U)

/-- `U' ⟶ S` extends the structure morphism of `U`. -/
theorem chartInclusion_comp_chartRealizedSchemeToBaseScheme (U : SmallEtale B S hS X.1) :
    E.chartInclusion U ≫ E.chartRealizedSchemeToBaseScheme U =
      (baseSpaceChartDiagram (f ≫ toBaseAlgebraicSpace Y) U).schemeMap :=
  E.chartInclusion_comp_chartRealizedSchemeToBase _ _ (baseSpaceChartDiagram _ U)

/-- The morphisms `V' ⟶ U'` are morphisms over `S`. -/
theorem chartRealizedSchemeMap_comp_chartRealizedSchemeToBaseScheme {U V : SmallEtale B S hS X.1}
    (i : V ⟶ U) :
    E.chartRealizedSchemeMap i ≫ E.chartRealizedSchemeToBaseScheme U =
      E.chartRealizedSchemeToBaseScheme V := by
  have h : (SmallEtale.toOver B S hS X.1).map i ≫ (baseSpaceChartDiagram (f ≫ toBaseAlgebraicSpace
      Y) U).g =
      (baseSpaceChartDiagram (f ≫ toBaseAlgebraicSpace Y) V).g ≫
        (SmallEtale.toOver B S hS (baseAlgebraicSpace B S hS).1).map (𝟙 (baseChart B S hS)) :=
    Over.mkIdTerminal.hom_ext _ _
  exact (E.chartRealizedSchemeMap_comp_chartRealizedSchemeToBase _ _ (baseSpaceChartDiagram _ U)
    (baseSpaceChartDiagram _ V) i (𝟙 _) h).trans (Category.comp_id _)

end SquareZeroExtension

end AlgebraicGeometry.Space

end
