module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartBaseComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotient

/-!
# The maps from chart thickenings to the base space do not depend on the chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension of the small
étale structure sheaf of `X`, as an algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT). For an étale
chart `U` of `X` whose thickening `U'` lies in the site and a chart diagram `U ⟶ V` over `f`,
the algebra structure gives a morphism `U' ⟶ V` over `S`
(`AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeOverToBase`). Its composite with
`V ⟶ Y` does not depend on the chart diagram: two chart diagrams `U ⟶ V₁`, `U ⟶ V₂` factor
through the chart `V₁ ×_Y V₂` of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.chartPairProduct`: the étale chart `V₁ ×_F V₂` of a presheaf.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeOverToBase`: `U' ⟶ V` over `S`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeOverToBase_toSpace_eq`: the
  independence.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PairProduct

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V₁ V₂ : SmallEtale B S hS F)

/-- The étale structure morphism of an étale chart. -/
theorem SmallEtale.etale_hom (V : SmallEtale B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) V.obj.hom :=
  V.property

/-- **The étale chart `V₁ ×_F V₂`** of a presheaf, for two étale charts `V₁`, `V₂`. -/
def chartPairProduct : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk (yoneda.map ((SmallEtale.etale_hom V₂).rep.snd V₁.obj.hom) ≫ V₁.obj.hom),
    etale_comp_of_scheme B S hS _ _
      ((SmallEtale.etale_hom V₂).property V₁.obj.hom
        (yoneda.map ((SmallEtale.etale_hom V₂).rep.fst' V₁.obj.hom))
        ((SmallEtale.etale_hom V₂).rep.snd V₁.obj.hom)
        ((SmallEtale.etale_hom V₂).rep.isPullback' V₁.obj.hom))
      (SmallEtale.etale_hom V₁)⟩

/-- The projection `V₁ ×_F V₂ ⟶ V₁`. -/
def chartPairProductFst : chartPairProduct V₁ V₂ ⟶ V₁ :=
  ObjectProperty.homMk (CostructuredArrow.homMk ((SmallEtale.etale_hom V₂).rep.snd V₁.obj.hom) rfl)

/-- The projection `V₁ ×_F V₂ ⟶ V₂`. -/
def chartPairProductSnd : chartPairProduct V₁ V₂ ⟶ V₂ :=
  ObjectProperty.homMk (CostructuredArrow.homMk ((SmallEtale.etale_hom V₂).rep.fst' V₁.obj.hom)
    ((SmallEtale.etale_hom V₂).rep.isPullback' V₁.obj.hom).w)

/-- The map into `V₁ ×_F V₂` of a pair of maps agreeing over `F`. -/
def chartPairProductLift {T : BigFppfOver B S hS} (a₁ : T ⟶ V₁.obj.left) (a₂ : T ⟶ V₂.obj.left)
    (h : yoneda.map a₁ ≫ V₁.obj.hom = yoneda.map a₂ ≫ V₂.obj.hom) :
    T ⟶ (chartPairProduct V₁ V₂).obj.left :=
  (SmallEtale.etale_hom V₂).rep.lift' a₂ a₁ h.symm

/-- The lift into `V₁ ×_F V₂` followed by the first projection is `a₁`. -/
theorem chartPairProductLift_fst {T : BigFppfOver B S hS} (a₁ : T ⟶ V₁.obj.left)
    (a₂ : T ⟶ V₂.obj.left) (h : yoneda.map a₁ ≫ V₁.obj.hom = yoneda.map a₂ ≫ V₂.obj.hom) :
    chartPairProductLift V₁ V₂ a₁ a₂ h ≫
        (SmallEtale.toOver B S hS F).map (chartPairProductFst V₁ V₂) =
      a₁ :=
  (SmallEtale.etale_hom V₂).rep.lift'_snd a₂ a₁ h.symm

/-- The lift into `V₁ ×_F V₂` followed by the second projection is `a₂`. -/
theorem chartPairProductLift_snd {T : BigFppfOver B S hS} (a₁ : T ⟶ V₁.obj.left)
    (a₂ : T ⟶ V₂.obj.left) (h : yoneda.map a₁ ≫ V₁.obj.hom = yoneda.map a₂ ≫ V₂.obj.hom) :
    chartPairProductLift V₁ V₂ a₁ a₂ h ≫
        (SmallEtale.toOver B S hS F).map (chartPairProductSnd V₁ V₂) =
      a₂ :=
  (SmallEtale.etale_hom V₂).rep.lift'_fst a₂ a₁ h.symm

/-- The two projections of `V₁ ×_F V₂` agree over `F`. -/
theorem chartPairProduct_w :
    yoneda.map ((SmallEtale.toOver B S hS F).map (chartPairProductFst V₁ V₂)) ≫ V₁.obj.hom =
      yoneda.map ((SmallEtale.toOver B S hS F).map (chartPairProductSnd V₁ V₂)) ≫ V₂.obj.hom :=
  ((SmallEtale.etale_hom V₂).rep.isPullback' V₁.obj.hom).w.symm

end PairProduct

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **`U' ⟶ V` over `S`**, for a chart diagram `U ⟶ V` over `f`: the morphism from the chart
thickening `U'` to the chart `V` of `Y` given by the algebra structure, as a morphism of the big
fppf site. -/
def chartRealizedSchemeOverToBase (d : ChartDiagram B S hS X.1 Y.1 f.hom) (hU : B.Contains
    (E.chartRealizedScheme d.U)) : E.chartRealizedSchemeOver hS d.U hU ⟶ d.V.obj.left :=
  Over.homMk (ObjectProperty.homMk (E.chartRealizedSchemeToBase E.toBase E.toBase_π d)) (by
    apply ObjectProperty.hom_ext
    exact E.chartRealizedSchemeToBase_comp_toBase (U := d.U) (V := d.V) d.g d.comm)

/-- The morphism of schemes underlying `U' ⟶ V` is `chartRealizedSchemeToBase`. -/
theorem toScheme_map_chartRealizedSchemeOverToBase (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : B.Contains (E.chartRealizedScheme d.U)) :
    (BigFppfOver.toScheme B S hS).map (E.chartRealizedSchemeOverToBase d hU) =
      E.chartRealizedSchemeToBase E.toBase E.toBase_π d :=
  rfl

/-- `U' ⟶ V' ⟶ V` is `U' ⟶ V` for chart diagrams `U ⟶ V' ⟶ V`. -/
theorem chartRealizedSchemeOverToBase_comp_of_comm {U : SmallEtale B S hS X.1}
    {V V' : SmallEtale B S hS Y.1}
    (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V')
    (c : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom) (c' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V'.1.hom)
    (j : V' ⟶ V) (h : g' ≫ (SmallEtale.toOver B S hS Y.1).map j = g)
    (hU : B.Contains (E.chartRealizedScheme U)) :
    E.chartRealizedSchemeOverToBase ⟨U, V', g', c'⟩ hU ≫ (SmallEtale.toOver B S hS Y.1).map j =
      E.chartRealizedSchemeOverToBase ⟨U, V, g, c⟩ hU := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  show (BigFppfOver.toScheme B S hS).map _ = (BigFppfOver.toScheme B S hS).map _
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
  refine (E.chartRealizedSchemeMap_comp_chartRealizedSchemeToBase E.toBase E.toBase_π
    ⟨U, V, g, c⟩ ⟨U, V', g', c'⟩ (𝟙 U) j
    (((congrArg (· ≫ g) ((SmallEtale.toOver B S hS X.1).map_id U)).trans
      (Category.id_comp g)).trans h.symm)).symm.trans ?_
  exact (congrArg (· ≫ _) (E.chartRealizedSchemeMap_id U)).trans (Category.id_comp _)

/-- **`U' ⟶ V ⟶ Y` does not depend on the chart diagram `U ⟶ V`.** -/
theorem chartRealizedSchemeOverToBase_toSpace_eq {U : SmallEtale B S hS X.1}
    {V₁ V₂ : SmallEtale B S hS Y.1}
    (g₁ : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V₁)
    (g₂ : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V₂)
    (c₁ : U.1.hom ≫ f.hom = yoneda.map g₁ ≫ V₁.1.hom)
    (c₂ : U.1.hom ≫ f.hom = yoneda.map g₂ ≫ V₂.1.hom) (hU : B.Contains (E.chartRealizedScheme U)) :
    yoneda.map (E.chartRealizedSchemeOverToBase ⟨U, V₁, g₁, c₁⟩ hU) ≫ V₁.obj.hom =
      yoneda.map (E.chartRealizedSchemeOverToBase ⟨U, V₂, g₂, c₂⟩ hU) ≫ V₂.obj.hom := by
  have hw : yoneda.map g₁ ≫ V₁.obj.hom = yoneda.map g₂ ≫ V₂.obj.hom := c₁.symm.trans c₂
  have cW : U.1.hom ≫ f.hom = yoneda.map (chartPairProductLift V₁ V₂ g₁ g₂ hw) ≫
      (chartPairProduct V₁ V₂).obj.hom := by
    refine c₁.trans ((congrArg (fun m ↦ yoneda.map m ≫ V₁.obj.hom)
      (chartPairProductLift_fst V₁ V₂ g₁ g₂ hw).symm).trans ?_)
    exact (yoneda.map_comp_assoc _ _ _)
  rw [← E.chartRealizedSchemeOverToBase_comp_of_comm (V' := chartPairProduct V₁ V₂) g₁ _ c₁ cW
      (chartPairProductFst V₁ V₂) (chartPairProductLift_fst V₁ V₂ g₁ g₂ hw) hU,
    ← E.chartRealizedSchemeOverToBase_comp_of_comm (V' := chartPairProduct V₁ V₂) g₂ _ c₂ cW
      (chartPairProductSnd V₁ V₂) (chartPairProductLift_snd V₁ V₂ g₁ g₂ hw) hU,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, chartPairProduct_w]

end SquareZeroExtension

end AlgebraicGeometry.Space

end
