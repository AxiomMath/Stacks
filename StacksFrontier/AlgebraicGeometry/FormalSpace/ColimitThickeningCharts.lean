module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleExtensionAffine

/-!
# Transporting an étale chart along a system of thickenings of algebraic spaces

Let `E : Λ ⥤ FppfSheaf B S hS` be a diagram of algebraic spaces over `S` indexed by a preorder
with least element `o`, whose transition morphisms are representable thickenings, and let
`u₀ : h_{U₀} ⟶ E o` be étale, representably by schemes. In the proof of **Stacks 0AIU** the chart
`u₀` is transported to every stage by the topological invariance of the étale site
(**Stacks 05ZH**). Here the transported charts are the pushforwards of `u₀` along the transitions
`E o ⟶ E j` (`CategoryTheory.monoPushforwardDiagram`), assembled into a diagram of fppf sheaves
over `E`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.thickeningChart`: the diagram `j ↦ (E o ⟶ E j)_* h_{U₀}` of
  fppf sheaves, with its projection `AlgebraicGeometry.FormalSpace.thickeningChartπ` to `E`.

## Main results

* `AlgebraicGeometry.FormalSpace.thickeningChartπ_equifibered`: the transported charts form an
  equifibered diagram over `E`.
* `AlgebraicGeometry.FormalSpace.hasSchemePropertyULift_etale_thickeningChartπ_app`: each
  transported chart is étale over its stage, representably by schemes.
* `AlgebraicGeometry.FormalSpace.exists_isAffine_iso_thickeningChart_obj`: if `U₀` is affine, each
  transported chart is represented by an affine object of the site (Stacks 07VT, thickening
  case).

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ : Type*} [Preorder Λ] (E : Λ ⥤ FppfSheaf B S hS)
  (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
  (o : Λ) (ho : ∀ j, o ≤ j) {C₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (u₀ : C₀ ⟶ (E.obj o).obj)

include hthick in
/-- The transitions of a system of representable thickenings are monomorphisms of presheaves. -/
theorem mono_map_hom_of_isRepresentableThickeningULift ⦃i j : Λ⦄ (g : i ⟶ j) :
    Mono (E.map g).hom :=
  mono_of_isRepresentableThickeningULift B S hS (hthick g)

include hthick in
/-- The transitions of a system of representable thickenings, as presheaves. -/
theorem mono_comp_sheafToPresheaf_map ⦃i j : Λ⦄ (g : i ⟶ j) :
    Mono ((E ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map g) :=
  mono_map_hom_of_isRepresentableThickeningULift B S hS E hthick g

/-- The transported charts as a diagram of presheaves: the pushforward of `u₀` along each
transition `E o ⟶ E j`. -/
abbrev thickeningChartPresheaf : Λ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  monoPushforwardDiagram (E ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) o ho
    (mono_comp_sheafToPresheaf_map B S hS E hthick) u₀

include hthick in
/-- **Each transported chart is an algebraic space**, when the stages are algebraic spaces and
`u₀` is étale representably by schemes. -/
theorem isAlgebraicSpaceULift_thickeningChartPresheaf_obj
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) (j : Λ) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      ((thickeningChartPresheaf B S hS E hthick o ho u₀).obj j) := by
  have := mono_map_hom_of_isRepresentableThickeningULift B S hS E hthick (homOfLE (ho j))
  exact Space.isAlgebraicSpaceULift_monoPushforward B S hS (E.map (homOfLE (ho j))).hom
    (hthick _) (halg j) u₀ hu₀

/-- **The transported charts as a diagram of fppf sheaves.** -/
def thickeningChart
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    Λ ⥤ FppfSheaf B S hS :=
  ObjectProperty.lift (Presheaf.IsSheaf (BigFppfOver.topology B S hS) (A := Type (u + 1)))
    (thickeningChartPresheaf B S hS E hthick o ho u₀)
    (fun j ↦ (isAlgebraicSpaceULift_thickeningChartPresheaf_obj B S hS E hthick o ho u₀
      halg hu₀ j).isSheaf)

/-- The projection of the transported charts to the stages. -/
def thickeningChartπ
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    thickeningChart B S hS E hthick o ho u₀ halg hu₀ ⟶ E where
  app j := ObjectProperty.homMk ((monoPushforwardDiagramπ
    (E ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) o ho
    (mono_comp_sheafToPresheaf_map B S hS E hthick) u₀).app j)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((monoPushforwardDiagramπ (E ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      o ho (mono_comp_sheafToPresheaf_map B S hS E hthick) u₀).naturality f)

/-- The component of `thickeningChartπ` at `j` is the projection of the pushforward of `u₀` along
`E o ⟶ E j`. -/
theorem thickeningChartπ_app_hom
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) (j : Λ) :
    ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j).hom =
      monoPushforward.π (E.map (homOfLE (ho j))).hom u₀ := rfl

/-- **The transported charts form an equifibered diagram over the stages**: the transition
squares of `CategoryTheory.monoPushforwardDiagram` are cartesian among presheaves, and the
forgetful functor from sheaves reflects them. -/
theorem thickeningChartπ_equifibered
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) :
    (thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).Equifibered := by
  intro j j' f
  have hpre := monoPushforwardDiagram_equifibered
    (E ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) o ho
    (mono_comp_sheafToPresheaf_map B S hS E hthick) u₀ f
  refine IsPullback.of_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).naturality f) ?_
  exact hpre

include hthick in
/-- **Each transported chart is étale over its stage**, representably by schemes (Stacks 05ZH at
a thickening of arbitrary order). -/
theorem hasSchemePropertyULift_etale_thickeningChartπ_app
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) (j : Λ) :
    Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale)
      ((thickeningChartπ B S hS E hthick o ho u₀ halg hu₀).app j).hom := by
  rw [thickeningChartπ_app_hom]
  have := mono_map_hom_of_isRepresentableThickeningULift B S hS E hthick (homOfLE (ho j))
  exact Space.hasSchemePropertyULift_etale_monoPushforward_π B S hS _ (hthick _) u₀ hu₀

/-- **A transported affine chart is affine**: if `U₀` is affine, every stage of the transported
chart is represented by an affine object of the site. -/
theorem exists_isAffine_iso_thickeningChart_obj
    (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)
    {U₀ : BigFppfOver B S hS} (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (u₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ (E.obj o).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) (j : Λ) :
    ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (((thickeningChart B S hS E hthick o ho u₀ halg hu₀).obj j).obj ≅
        uliftYoneda.{u + 1}.obj T) := by
  have := mono_map_hom_of_isRepresentableThickeningULift B S hS E hthick (homOfLE (ho j))
  exact Space.exists_isAffine_iso_uliftYoneda_monoPushforward B S hS
    (E.map (homOfLE (ho j))).hom (hthick _) (halg j) U₀ hU₀ u₀ hu₀

end AlgebraicGeometry.FormalSpace

end
