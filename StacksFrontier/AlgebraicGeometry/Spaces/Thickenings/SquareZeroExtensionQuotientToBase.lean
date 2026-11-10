module

public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartBaseIndep
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientImmersion

/-!
# The thickened quotient maps to the base space

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension of the small
étale structure sheaf of `X`, as an algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT). Let `P` be
a presentation `X = U/R` mapping to a presentation `Y = V/R_Y` over `f`, and suppose the site
contains the chart thickenings `U'`, `R'`, so that the thickening `X' = U'/R'` is defined. The
morphisms `U' ⟶ V` and `R' ⟶ R_Y` given by the algebra structure are morphisms over `S`, they
are compatible with the projections of the two relations, and so `U' ⟶ V ⟶ Y` descends to
`X' ⟶ Y`. Its composite with `X ⟶ X'` is `f`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.thickeningQuotientToBase`: `X' ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.thickeningImmersion_comp_thickeningQuotientToBase`:
  `X ⟶ X' ⟶ Y` is `f`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (P : Presentation B S hS X.obj X.property) (Q : Presentation B S hS Y.obj Y.property)
  (gU : P.U ⟶ Q.U) (hgU : P.toSpace ≫ f.hom = yoneda.map gU ≫ Q.toSpace)
  (gR : P.R ⟶ Q.R) (hgt : gR ≫ Q.target = P.target ≫ gU) (hgs : gR ≫ Q.source = P.source ≫ gU)

/-- The chart diagram `U ⟶ V` of the presenting schemes over `f`. -/
def thickeningChartDiagram : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := presentationChart P
  V := presentationChart Q
  g := gU
  comm := hgU

include hgs in
/-- The chart diagram `R ⟶ R_Y` of the relation schemes over `f`. -/
def thickeningRelationChartDiagram : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := presentationRelationChart P
  V := presentationRelationChart Q
  g := gR
  comm := by
    change (yoneda.map P.source ≫ P.toSpace) ≫ f.hom =
      yoneda.map gR ≫ yoneda.map Q.source ≫ Q.toSpace
    rw [Category.assoc, hgU, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hgs]

variable (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- **`U' ⟶ V` over `S`**: the morphism from the thickening of the presenting scheme of `X` to
the presenting scheme of `Y` given by the algebra structure. -/
abbrev thickeningChartToBase : E.chartRealizedSchemeOver hS (presentationChart P) hU ⟶ Q.U :=
  E.chartRealizedSchemeOverToBase (thickeningChartDiagram P Q gU hgU) hU

/-- The underlying morphism of schemes of `thickeningChartToBase` is the morphism `U' ⟶ V`
given by the algebra structure. -/
theorem toScheme_map_thickeningChartToBase :
    (BigFppfOver.toScheme B S hS).map (E.thickeningChartToBase P Q gU hgU hU) =
      E.chartRealizedSchemeToBase E.toBase E.toBase_π (thickeningChartDiagram P Q gU hgU) :=
  rfl

/-- **`R' ⟶ R_Y` over `S`.** -/
abbrev thickeningRelationChartToBase :
    E.chartRealizedSchemeOver hS (presentationRelationChart P) hR ⟶ Q.R :=
  E.chartRealizedSchemeOverToBase (thickeningRelationChartDiagram P Q gU hgU gR hgs) hR

/-- The underlying morphism of schemes of `thickeningRelationChartToBase` is the morphism
`R' ⟶ R_Y` given by the algebra structure. -/
theorem toScheme_map_thickeningRelationChartToBase :
    (BigFppfOver.toScheme B S hS).map (E.thickeningRelationChartToBase P Q gU hgU gR hgs hR) =
      E.chartRealizedSchemeToBase E.toBase E.toBase_π
        (thickeningRelationChartDiagram P Q gU hgU gR hgs) :=
  rfl

/-- Compatibility of `R' ⟶ R_Y` and `U' ⟶ V` with a pair of projections of the relations. -/
private theorem thickeningRelationChartToBase_comp_eq
    (i : presentationRelationChart P ⟶ presentationChart P)
    (j : presentationRelationChart Q ⟶ presentationChart Q) (s : Q.R ⟶ Q.U)
    (hs : (BigFppfOver.toScheme B S hS).map s = chartSchemeMap j)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ (thickeningChartDiagram P Q gU hgU).g =
      (thickeningRelationChartDiagram P Q gU hgU gR hgs).g ≫
        (SmallEtale.toOver B S hS Y.1).map j) :
    E.thickeningRelationChartToBase P Q gU hgU gR hgs hR ≫ s =
      E.chartRealizedSchemeOverMap hS i hU hR ≫ E.thickeningChartToBase P Q gU hgU hU :=
  BigFppfOver.map_toScheme_injective B S hS (by
    change (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_thickeningChartToBase,
      toScheme_map_thickeningRelationChartToBase, toScheme_map_chartRealizedSchemeOverMap, hs]
    exact (E.chartRealizedSchemeMap_comp_chartRealizedSchemeToBase E.toBase E.toBase_π
      (thickeningChartDiagram P Q gU hgU) (thickeningRelationChartDiagram P Q gU hgU gR hgs)
      i j h).symm)

include hgt in
/-- The morphisms `R' ⟶ R_Y` and `U' ⟶ V` commute with the target projections of the two
relations. -/
theorem thickeningRelationChartToBase_target :
    E.thickeningRelationChartToBase P Q gU hgU gR hgs hR ≫ Q.target =
      E.chartRealizedSchemeOverMap hS (presentationRelationTargetHom P) hU hR ≫
        E.thickeningChartToBase P Q gU hgU hU :=
  E.thickeningRelationChartToBase_comp_eq P Q gU hgU gR hgs hU hR _
    (presentationRelationTargetHom Q) _ rfl hgt.symm

/-- The morphisms `R' ⟶ R_Y` and `U' ⟶ V` commute with the source projections of the two
relations. -/
theorem thickeningRelationChartToBase_source :
    E.thickeningRelationChartToBase P Q gU hgU gR hgs hR ≫ Q.source =
      E.chartRealizedSchemeOverMap hS (presentationRelationSourceHom P) hU hR ≫
        E.thickeningChartToBase P Q gU hgU hU :=
  E.thickeningRelationChartToBase_comp_eq P Q gU hgU gR hgs hU hR _
    (presentationRelationSourceHom Q) _ rfl hgs.symm

include hgt hgs in
/-- `U' ⟶ V ⟶ Y` agrees on the two projections of `R'`. -/
theorem thickeningChartToBase_comp_toSpace_eq :
    yoneda.map (E.thickeningQuotientPresentation hS P hU hR).target ≫
        yoneda.map (E.thickeningChartToBase P Q gU hgU hU) ≫ Q.toSpace =
      yoneda.map (E.thickeningQuotientPresentation hS P hU hR).source ≫
        yoneda.map (E.thickeningChartToBase P Q gU hgU hU) ≫ Q.toSpace := by
  change yoneda.map (E.chartRealizedSchemeOverMap hS (presentationRelationTargetHom P) hU hR) ≫ _ =
    yoneda.map (E.chartRealizedSchemeOverMap hS (presentationRelationSourceHom P) hU hR) ≫ _
  have h1 := E.thickeningRelationChartToBase_target P Q gU hgU gR hgt hgs hU hR
  have h2 := E.thickeningRelationChartToBase_source P Q gU hgU gR hgs hU hR
  exact (yoneda.map_comp_assoc _ _ Q.toSpace).symm.trans
    ((congrArg (fun m ↦ yoneda.map m ≫ Q.toSpace) h1.symm).trans
    ((yoneda.map_comp_assoc _ Q.target Q.toSpace).trans
    ((congrArg (yoneda.map (E.thickeningRelationChartToBase P Q gU hgU gR hgs hR) ≫ ·)
      Q.isPullback.w).trans
    ((yoneda.map_comp_assoc _ Q.source Q.toSpace).symm.trans
    ((congrArg (fun m ↦ yoneda.map m ≫ Q.toSpace) h2).trans
    (yoneda.map_comp_assoc _ _ Q.toSpace))))))

include hgt hgs in
/-- **The morphism `X' ⟶ Y`**: `U' ⟶ V ⟶ Y` descended along the quotient map `U' ⟶ X'`. -/
def thickeningQuotientToBase : E.thickeningQuotient hS P hU hR ⟶ Y :=
  ObjectProperty.homMk (quotientDescOfPresentation (E.thickeningQuotientPresentation hS P hU hR)
    Y.property.isSheaf (yoneda.map (E.thickeningChartToBase P Q gU hgU hU) ≫ Q.toSpace)
    (E.thickeningChartToBase_comp_toSpace_eq P Q gU hgU gR hgt hgs hU hR))

/-- `U' ⟶ X' ⟶ Y` is `U' ⟶ V ⟶ Y`. -/
theorem thickeningQuotientMap_comp_thickeningQuotientToBase :
    E.thickeningQuotientMap P hU hR ≫ (E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR).hom =
      yoneda.map (E.thickeningChartToBase P Q gU hgU hU) ≫ Q.toSpace :=
  toSpace_quotientDescOfPresentation (E.thickeningQuotientPresentation hS P hU hR)
    Y.property.isSheaf _ (E.thickeningChartToBase_comp_toSpace_eq P Q gU hgU gR hgt hgs hU hR)

/-- **`X ⟶ X' ⟶ Y` is `f`.** -/
theorem thickeningImmersion_comp_thickeningQuotientToBase :
    E.thickeningImmersion P hU hR ≫ E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR = f := by
  apply ObjectProperty.hom_ext
  refine presentation_toSpace_hom_ext P Y.property.isSheaf ?_
  change P.toSpace ≫ (E.thickeningImmersion P hU hR).hom ≫
    (E.thickeningQuotientToBase P Q gU hgU gR hgt hgs hU hR).hom = _
  rw [← Category.assoc, (E.isPullback_thickeningImmersion P hU hR).w, Category.assoc,
    thickeningQuotientMap_comp_thickeningQuotientToBase, hgU, ← Category.assoc]
  refine congrArg (· ≫ Q.toSpace) ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ?_))
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  change (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
  exact ((BigFppfOver.toScheme B S hS).map_comp (E.chartInclusionOver (presentationChart P) hU)
    (E.thickeningChartToBase P Q gU hgU hU)).trans
    ((congrArg₂ (· ≫ ·) (E.toScheme_map_chartInclusionOver _ hU)
      (E.toScheme_map_thickeningChartToBase P Q gU hgU hU)).trans
      (E.chartInclusion_comp_chartRealizedSchemeToBase _ _ (thickeningChartDiagram P Q gU hgU)))

end AlgebraicGeometry.Space.SquareZeroExtension

end
