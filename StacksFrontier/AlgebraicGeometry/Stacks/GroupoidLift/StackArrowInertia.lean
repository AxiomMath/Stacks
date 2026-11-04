module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackArrowFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartPairIso
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.InertiaFibre

/-!
# The space of arrows of a chart is locally of finite presentation when the inertia is

Let `𝒳` be an algebraic stack over `S` whose inertia `ℐ_𝒳 ⟶ 𝒳` is locally of finite
presentation, in the relative form of Stacks 06Q2 at the relative inertia of the structure
morphism `𝒳 ⟶ S` of Stacks 050D. For an object `x` of `𝒳` over a scheme `V`, the base change
of the inertia along `x` is the automorphism presheaf `Aut(x) = Isom(x, x)` on the big fppf site
of `V` (`CategoryTheory.TwoFibreProductOver.InertiaFibre.equivalenceOver`), so `Aut(x)` is
locally of finite presentation over `V`. If two objects `x₀`, `x₁` over `V` are isomorphic,
`Isom(x₀, x₁)` is isomorphic to `Aut(x₀)`, hence locally of finite presentation as well.

Applied to the two objects `ξ v₀`, `ξ vₗ` over `Spec (P ⊗ P)` of a chart, this gives the finiteness
of the space of arrows that
`GroupoidLift.exists_arrowChart_finitePresentation_of_isLocallyOfFinitePresentation` needs, with no
finiteness assumption on `𝒳 ⟶ S`.

## Main results

* `isLocallyOfFinitePresentation_autPresheaf_of_inertia`: `Aut(x)` is locally of finite
  presentation over `V`.
* `isLocallyOfFinitePresentation_isomPresheaf_of_inertia`: `Isom(x₀, x₁)` is locally of finite
  presentation over `V` when `x₀ ≅ x₁`.
* `GroupoidLift.StackChart.isLocallyOfFinitePresentation_arrSpace_of_inertia`: the space of
  arrows of a chart whose two objects over `Spec (P ⊗ P)` are isomorphic.
* `GroupoidLift.arrowSpacesLocallyOfFinitePresentation_of_inertia`: the hypothesis of the lifting
  lemmas `exists_hom_of_cover_of_arrSpace` and `exists_lift_of_cover_of_arrSpace`, from the
  inertia.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Aut

variable {B S hS} {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The projection of `𝒳` to `BigFppfOver B S hS` is a fibered category. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- On an algebraic stack, `Isom(x₀, x₁)` is an algebraic space over `V`. -/
private theorem isAlgebraicSpace_isomPresheaf_of_isAlgebraicStack
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (V : BigFppfOver B S hS) (x₀ x₁ : 𝒳.val.p.Fiber V) :
    IsAlgebraicSpace B V.left.1 V.left.2
      ((Over.iteratedSliceBackward V).op ⋙ 𝒳.val.p.isomPresheaf x₀ x₁) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp
    (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳 h𝒳) V x₀ x₁
  exact isAlgebraicSpace_of_iso B V.left.1 V.left.2
    (((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u, u}).whiskeringRight _).preimageIso
      e).symm hF

/-- For an algebraic space `G` over `V`, being locally of finite presentation over `V` is the
same as its structure map being locally of finite presentation over `S` in the relative sense. -/
private theorem spaceProperty_algebraicSpaceMap_iff_terminal
    (V : BigFppfOver B S hS) (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G) :
    spaceProperty B S hS
        (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g :
          MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
        (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) ↔
      Space.IsLocallyOfFinitePresentation B V.left.1 V.left.2 (terminal.from G) := by
  have hri : (spaceProperty B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g :
        MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (prop_algebraicSpaceMap_iff B S hS _ V G hG).trans ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B V.left.1 S V.left.2 hS V.hom
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) G).trans ?_
  exact ⟨fun h => Space.holdsOnEveryEtaleChart_of_isTerminal B V.left.1 V.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ h,
    fun h => Space.holdsOnEveryEtaleChart_of_isTerminal B V.left.1 V.left.2
      terminalIsTerminal (Over.mkIdTerminal.isTerminalObj yoneda _) _ _ h⟩

/-- **The automorphism presheaf of a scheme-valued point is locally of finite presentation when
the inertia is.** For an algebraic stack `𝒳` whose inertia projection is locally of finite
presentation and an object `x` of `𝒳` over `V`, the presheaf `Aut(x) = Isom(x, x)` on the big
fppf site of `V` is locally of finite presentation over `V`: it is the base change of the
inertia along `x`. -/
theorem isLocallyOfFinitePresentation_autPresheaf_of_inertia
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (hI : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (relativeInertiaProjection B S hS (structureMorphism B S hS ⟨𝒳, h𝒳⟩)))
    (V : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber V) :
    Space.IsLocallyOfFinitePresentation B V.left.1 V.left.2
      (terminal.from ((Over.iteratedSliceBackward V).op ⋙ 𝒳.val.p.isomPresheaf x x)) := by
  let g := structureMorphism B S hS ⟨𝒳, h𝒳⟩
  let Plfp : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g
  have hP := Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  have hrep :
      IsRepresentableByAlgebraicSpaces B S hS (relativeInertiaProjection B S hS g).hom.hom :=
    isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack.{u, u, u + 1, t}
      B S hS 𝒳 _
      g.hom h𝒳 (isAlgebraicStack_schemeFibredCategory.{u, t} B S hS _)
  have hsome := (hasPropertyOnEverySmoothDiagram_iff_some.{u, t} B S hS Plfp hP
    (relativeInertiaStack B S hS g).property h𝒳 _).1 hI
  have hrel := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, t, u + 1} B S hS Plfp hP
    (relativeInertiaStack B S hS g).property h𝒳 _ hrep).1 hsome
  have hp := 𝒳.isFiberedInGroupoids
  let Y := Over.iteratedSliceBackward V ⋙ Functor.pullbackSliceFunctor 𝒳.val.p x
  have hY : Y ⋙ 𝒳.val.p = Over.map V.hom := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p V x
  let G := (Over.iteratedSliceBackward V).op ⋙ 𝒳.val.p.isomPresheaf x x
  have hG : IsAlgebraicSpace B V.left.1 V.left.2 G :=
    isAlgebraicSpace_isomPresheaf_of_isAlgebraicStack h𝒳 V x x
  have : (schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS)))).val.p.Faithful :=
    inferInstanceAs (Over.forget _).Faithful
  let e₁ := TwoFibreProductOver.InertiaFibre.equivalenceOver hp g.hom.hom.w hY
  obtain ⟨e₂⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff
    (TwoFibreProductOver.InertiaFibre.autPresheaf hp hY) G).2
    ⟨Functor.isoWhiskerRight (Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p V x x hp) _⟩
  have h := hrel V Y hY G hG ⟨e₁.trans e₂⟩
  exact (spaceProperty_algebraicSpaceMap_iff_terminal V G hG).mp h

/-- **`Isom(x₀, x₁)` is locally of finite presentation when the inertia is and `x₀ ≅ x₁`.**
Composition with an isomorphism `θ : x₁ ≅ x₀` identifies `Isom(x₀, x₁)` with `Aut(x₀)`. -/
theorem isLocallyOfFinitePresentation_isomPresheaf_of_inertia
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (hI : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (relativeInertiaProjection B S hS (structureMorphism B S hS ⟨𝒳, h𝒳⟩)))
    (V : BigFppfOver B S hS) {x₀ x₁ : 𝒳.val.p.Fiber V} (θ : x₁ ≅ x₀) :
    Space.IsLocallyOfFinitePresentation B V.left.1 V.left.2
      (terminal.from ((Over.iteratedSliceBackward V).op ⋙ 𝒳.val.p.isomPresheaf x₀ x₁)) := by
  have hp := 𝒳.isFiberedInGroupoids
  let c : 𝒳.val.p.isomPresheaf x₀ x₀ ≅ 𝒳.val.p.isomPresheaf x₀ x₁ :=
    isomPresheafIsoMorPresheaf 𝒳.val.p hp x₀ x₀ ≪≫
      (Functor.morPresheafFiberIso 𝒳.val.p (Iso.refl x₀) θ).symm ≪≫
      (isomPresheafIsoMorPresheaf 𝒳.val.p hp x₀ x₁).symm
  exact isLocallyOfFinitePresentation_terminal_of_iso B V.left.1 V.left.2
    (Functor.isoWhiskerLeft (Over.iteratedSliceBackward V).op c)
    (isLocallyOfFinitePresentation_autPresheaf_of_inertia h𝒳 hI V x₀)

end Aut

namespace GroupoidLift

open AlgebraicGeometry.Space.ChartDescent

variable {B S hS} {T' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- The projection of `𝒳` to `BigFppfOver B S hS` is a fibered category. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- **The space of arrows of the groupoid of a chart is locally of finite presentation over
`Spec (P ⊗ P)`, from the inertia.** If the inertia of `𝒳` is locally of finite presentation and
the two objects `ξ v₀`, `ξ vₗ` over `Spec (P ⊗ P)` are isomorphic, the space of arrows, the
coproduct presheaf of `Isom(ξ v₀, ξ vₗ)`, is locally of finite presentation over `Spec (P ⊗ P)`. -/
theorem isLocallyOfFinitePresentation_arrSpace_of_inertia
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (hI : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (relativeInertiaProjection B S hS (structureMorphism B S hS ⟨𝒳, h𝒳⟩)))
    (θ : pairObj₁ a ι ≅ pairObj₀ a ι) :
    Space.IsLocallyOfFinitePresentation B S hS (OverShriek.presheafToYoneda (pairIsom a ι)) := by
  set V := specOver (pairAlg P)
  let G' := (Over.iteratedSliceBackward V).op ⋙ pairIsom a ι
  have hG' : Space.IsLocallyOfFinitePresentation B V.left.1 V.left.2 (terminal.from G') :=
    isLocallyOfFinitePresentation_isomPresheaf_of_inertia h𝒳 hI V θ
  have hG'alg : IsAlgebraicSpace B V.left.1 V.left.2 G' :=
    isAlgebraicSpace_isomPresheaf_of_isAlgebraicStack h𝒳 V (pairObj₀ a ι) (pairObj₁ a ι)
  have h3 := (spaceProperty_algebraicSpaceMap_iff_terminal V G' hG'alg).mpr hG'
  let E := (Over.iteratedSliceEquiv V).op.congrLeft (E := Type u)
  let e'' : E.inverse.obj G' ≅ pairIsom a ι := (E.unitIso.app _).symm
  have hcomp : OverShriek.presheafToYoneda (E.inverse.obj G') =
      (OverShriek.presheafFunctor.map e''.hom) ≫ OverShriek.presheafToYoneda (pairIsom a ι) := by
    ext W x
    rfl
  have hri₀ : MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  have h4 : Space.IsLocallyOfFinitePresentation B S hS
      (OverShriek.presheafToYoneda (E.inverse.obj G')) := h3
  rw [hcomp] at h4
  exact (MorphismProperty.cancel_left_of_respectsIso _
    (OverShriek.presheafFunctor.mapIso e'').hom _).mp h4

end StackChart

/-- **When the inertia of `𝒳` is locally of finite presentation, so are the spaces of arrows of
its charts with isomorphic chart objects.** -/
theorem arrowSpacesLocallyOfFinitePresentation_of_inertia
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (hI : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (relativeInertiaProjection B S hS (structureMorphism B S hS ⟨𝒳, h𝒳⟩))) :
    ArrowSpacesLocallyOfFinitePresentation B S hS 𝒳 := by
  unfold ArrowSpacesLocallyOfFinitePresentation
  intro _ _ _ a _ ι ⟨θ⟩
  exact StackChart.isLocallyOfFinitePresentation_arrSpace_of_inertia a ι h𝒳 hI θ

end GroupoidLift

end AlgebraicGeometry.Stack

end
