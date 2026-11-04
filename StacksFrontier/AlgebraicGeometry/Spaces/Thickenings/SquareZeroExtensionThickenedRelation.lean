module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPresentation

/-!
# The thickened relation of a square-zero extension is an étale equivalence relation

Let `E` be a square-zero extension of a morphism of algebraic spaces and `C` a charted
presentation. The étale charts of the presentation lift to the thickening, and the thickened
source and target legs of the relation chart form an equivalence relation on the thickened
presenting chart in the category of schemes over `S`.

## Main definitions

* `thickU`: The thickened presenting chart, as a scheme over `S`.
* `thickR`: The thickened relation chart, as a scheme over `S`.
* `thickSource`, `thickTarget`: The thickened source and target legs `thickR ⟶ thickU`.
* `thickD`: The thickened double chart, as a scheme over `S`.
* `thickEquivalenceRelation`: The thickened legs as an internal equivalence relation on
  `thickU`.

## Main results

* `jointlyMono₂_thick`: The thickened target and source legs are jointly monic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)

/-- The thickened presenting chart, as a scheme over `S`. -/
abbrev thickU : Over S := Over.mk (presentationThickeningToBase E C)

/-- The thickened relation chart, as a scheme over `S`. -/
abbrev thickR : Over S := Over.mk (relationThickeningToBase E C)

/-- The thickened source leg. -/
def thickSource : thickR E C ⟶ thickU E C :=
  Over.homMk (chartThickeningMap B S hS E (presentationRelationSourceHom C.P)) rfl

/-- The thickened target leg. -/
def thickTarget : thickR E C ⟶ thickU E C :=
  Over.homMk (chartThickeningMap B S hS E (presentationRelationTargetHom C.P))
    (target_comp_presentationThickeningToBase E C)

/-- Two morphisms into the relation chart of `C.P` are equal if they agree after composing with
the structure morphism of `C.P.R`, with the source leg and with the target leg. -/
theorem presentationRelation_eq {Z : Scheme.{u}}
    (a b : Z ⟶ chartScheme (presentationRelationChart C.P))
    (hp : a ≫ B.inclusion.map C.P.R.hom = b ≫ B.inclusion.map C.P.R.hom)
    (hs : a ≫ chartSchemeMap (presentationRelationSourceHom C.P) =
      b ≫ chartSchemeMap (presentationRelationSourceHom C.P))
    (ht : a ≫ chartSchemeMap (presentationRelationTargetHom C.P) =
      b ≫ chartSchemeMap (presentationRelationTargetHom C.P)) : a = b := by
  have := (presentationEquivalenceRelation C.P).right_cancellation
    (Over.homMk (U := Over.mk (a ≫ B.inclusion.map C.P.R.hom)) a rfl)
    (Over.homMk (U := Over.mk (a ≫ B.inclusion.map C.P.R.hom)) b hp.symm)
    (Over.OverMorphism.ext ht) (Over.OverMorphism.ext hs)
  exact congrArg CommaMorphism.left this

/-- **The two thickened legs are jointly monic.** -/
theorem jointlyMono₂_thick : JointlyMono₂ (thickTarget E C) (thickSource E C) := by
  refine ⟨fun Z a b ht hs => Over.OverMorphism.ext ?_⟩
  have := etale_chartThickeningMap B S hS E (presentationRelationSourceHom C.P)
  refine eq_of_isPullback_thickening (chartImmersion B S hS E (presentationChart C.P))
    (chartImmersion B S hS E (presentationRelationChart C.P))
    (chartSchemeMap (presentationRelationSourceHom C.P))
    (chartSchemeMap (presentationRelationTargetHom C.P))
    (chartThickeningMap B S hS E (presentationRelationSourceHom C.P))
    (chartThickeningMap B S hS E (presentationRelationTargetHom C.P))
    (relationThickeningToBase E C)
    (isPullback_chartImmersion_chartThickeningMap B S hS E (presentationRelationSourceHom C.P))
    (chartImmersion_comp_chartThickeningMap B S hS E (presentationRelationTargetHom C.P))
    (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P)) ?_ a.left b.left
    (a.w.trans b.w.symm) (congrArg CommaMorphism.left hs) (congrArg CommaMorphism.left ht)
  intro Z a₀ b₀ hp hs₀ ht₀
  refine presentationRelation_eq C a₀ b₀ ?_ hs₀ ht₀
  rwa [chartImmersion_comp_relationThickeningToBase] at hp

section SiteEquations

variable (P : Presentation B S hS X.1 X.2)

/-- Morphisms in the small étale site of `X.1` are equal if their images over `X.1` are equal. -/
theorem smallEtale_hom_ext {A A' : SmallEtale B S hS X.1} {a b : A ⟶ A'}
    (h : (SmallEtale.toOver B S hS X.1).map a = (SmallEtale.toOver B S hS X.1).map b) : a = b :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h)

/-- The diagonal of the relation chart composed with the source leg is the identity. -/
theorem diagHom_comp_sourceHom :
    presentationRelationDiagHom P ≫ presentationRelationSourceHom P = 𝟙 _ :=
  smallEtale_hom_ext (presentationDiag_comp_source P)

/-- The diagonal of the relation chart composed with the target leg is the identity. -/
theorem diagHom_comp_targetHom :
    presentationRelationDiagHom P ≫ presentationRelationTargetHom P = 𝟙 _ :=
  smallEtale_hom_ext (presentationDiag_comp_target P)

/-- The symmetry of the relation chart composed with the target leg is the source leg. -/
theorem symHom_comp_targetHom :
    presentationRelationSymHom P ≫ presentationRelationTargetHom P =
      presentationRelationSourceHom P :=
  smallEtale_hom_ext (presentationSym_comp_target P)

/-- The symmetry of the relation chart composed with the source leg is the target leg. -/
theorem symHom_comp_sourceHom :
    presentationRelationSymHom P ≫ presentationRelationSourceHom P =
      presentationRelationTargetHom P :=
  smallEtale_hom_ext (presentationSym_comp_source P)

/-- The double chart is a commutative square: its first projection followed by the source leg
equals its second projection followed by the target leg. -/
theorem doubleFstHom_comp_sourceHom :
    presentationDoubleFstHom P ≫ presentationRelationSourceHom P =
      presentationDoubleSndHom P ≫ presentationRelationTargetHom P :=
  smallEtale_hom_ext (presentationDoubleFst_comp_source P)

/-- The composition of the relation chart followed by the target leg equals the first projection
of the double chart followed by the target leg. -/
theorem compHom_comp_targetHom :
    presentationCompHom P ≫ presentationRelationTargetHom P =
      presentationDoubleFstHom P ≫ presentationRelationTargetHom P :=
  smallEtale_hom_ext (presentationComp_comp_target P)

/-- The composition of the relation chart followed by the source leg equals the second
projection of the double chart followed by the source leg. -/
theorem compHom_comp_sourceHom :
    presentationCompHom P ≫ presentationRelationSourceHom P =
      presentationDoubleSndHom P ≫ presentationRelationSourceHom P :=
  smallEtale_hom_ext (presentationComp_comp_source P)

end SiteEquations

/-- If `a ≫ b = c` in the small étale site, then the thickenings of `a` and `b` compose to the
thickening of `c`. -/
theorem thick_map_comp_eq {A A' A'' : SmallEtale B S hS X.1} {a : A ⟶ A'} {b : A' ⟶ A''}
    {c : A ⟶ A''} (h : a ≫ b = c) :
    chartThickeningMap B S hS E a ≫ chartThickeningMap B S hS E b =
      chartThickeningMap B S hS E c := by
  rw [← chartThickeningMap_comp, h]

/-- The thickened double chart, as a scheme over `S`. -/
abbrev thickD : Over S :=
  Over.mk (chartThickeningMap B S hS E (presentationDoubleFstHom C.P) ≫
    relationThickeningToBase E C)

/-- The thickened source leg followed by the structure morphism of the thickened presenting chart
is the structure morphism of the thickened relation chart. -/
theorem source_comp_relationThickeningToBase :
    chartThickeningMap B S hS E (presentationRelationSourceHom C.P) ≫
      presentationThickeningToBase E C = relationThickeningToBase E C := rfl

/-- The two thickened projections of the double chart agree after composing with the structure
morphism of the thickened relation chart. -/
theorem doubleSnd_comp_relationThickeningToBase :
    chartThickeningMap B S hS E (presentationDoubleSndHom C.P) ≫ relationThickeningToBase E C =
      chartThickeningMap B S hS E (presentationDoubleFstHom C.P) ≫
        relationThickeningToBase E C := by
  calc _ = chartThickeningMap B S hS E (presentationDoubleSndHom C.P) ≫
        (chartThickeningMap B S hS E (presentationRelationTargetHom C.P) ≫
          presentationThickeningToBase E C) := by rw [target_comp_presentationThickeningToBase]
    _ = (chartThickeningMap B S hS E (presentationDoubleSndHom C.P) ≫
        chartThickeningMap B S hS E (presentationRelationTargetHom C.P)) ≫
          presentationThickeningToBase E C := (Category.assoc _ _ _).symm
    _ = (chartThickeningMap B S hS E (presentationDoubleFstHom C.P) ≫
        chartThickeningMap B S hS E (presentationRelationSourceHom C.P)) ≫
          presentationThickeningToBase E C := by
      rw [thick_map_comp_eq E (doubleFstHom_comp_sourceHom C.P).symm,
        thick_map_comp_eq E rfl]
    _ = _ := Category.assoc _ _ _

/-- **The thickened legs form an internal equivalence relation** on the thickened presenting
chart, in the category of schemes over `S`. -/
def thickEquivalenceRelation : EquivalenceRelation (thickTarget E C) (thickSource E C) where
  toJointlyMono₂ := jointlyMono₂_thick E C
  r := Over.homMk (chartThickeningMap B S hS E (presentationRelationDiagHom C.P)) (by
    change _ ≫ chartThickeningMap B S hS E (presentationRelationSourceHom C.P) ≫ _ = _
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [thick_map_comp_eq E (diagHom_comp_sourceHom C.P), chartThickeningMap_id]
    exact Category.id_comp _)
  reflexivity₁ := Over.OverMorphism.ext (thick_map_comp_eq E (diagHom_comp_targetHom C.P) |>.trans
    (chartThickeningMap_id B S hS E _))
  reflexivity₂ := Over.OverMorphism.ext (thick_map_comp_eq E (diagHom_comp_sourceHom C.P) |>.trans
    (chartThickeningMap_id B S hS E _))
  s := Over.homMk (chartThickeningMap B S hS E (presentationRelationSymHom C.P)) (by
    change _ ≫ chartThickeningMap B S hS E (presentationRelationSourceHom C.P) ≫ _ = _
    rw [← Category.assoc, thick_map_comp_eq E (symHom_comp_sourceHom C.P)]
    exact target_comp_presentationThickeningToBase E C)
  symmetry₁ := Over.OverMorphism.ext (thick_map_comp_eq E (symHom_comp_targetHom C.P))
  symmetry₂ := Over.OverMorphism.ext (thick_map_comp_eq E (symHom_comp_sourceHom C.P))
  c := PullbackCone.mk (W := thickD E C)
    (Over.homMk (chartThickeningMap B S hS E (presentationDoubleFstHom C.P)) rfl)
    (Over.homMk (chartThickeningMap B S hS E (presentationDoubleSndHom C.P))
      (doubleSnd_comp_relationThickeningToBase E C))
    (Over.OverMorphism.ext (thick_map_comp_eq E (doubleFstHom_comp_sourceHom C.P) |>.trans
      (chartThickeningMap_comp B S hS E _ _)))
  isLimit := by
    have H := isPullback_chartThickeningMap_of_toScheme B S hS E (doubleFstHom_comp_sourceHom C.P)
      (isPullback_toScheme_map_presentationDouble C.P)
    let a : thickD E C ⟶ thickR E C :=
      Over.homMk (chartThickeningMap B S hS E (presentationDoubleFstHom C.P)) rfl
    let b : thickD E C ⟶ thickR E C :=
      Over.homMk (chartThickeningMap B S hS E (presentationDoubleSndHom C.P))
        (doubleSnd_comp_relationThickeningToBase E C)
    exact (IsPullback.of_map_of_faithful (Over.forget S) (f := a) (g := b)
      (h := thickSource E C) (i := thickTarget E C) H).isLimit
  t := Over.homMk (chartThickeningMap B S hS E (presentationCompHom C.P)) (by
    change _ ≫ chartThickeningMap B S hS E (presentationRelationSourceHom C.P) ≫ _ =
      chartThickeningMap B S hS E (presentationDoubleFstHom C.P) ≫ relationThickeningToBase E C
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [thick_map_comp_eq E (compHom_comp_sourceHom C.P), chartThickeningMap_comp,
      Category.assoc, source_comp_relationThickeningToBase,
      doubleSnd_comp_relationThickeningToBase])
  transitivity₁ := Over.OverMorphism.ext ((thick_map_comp_eq E (compHom_comp_targetHom C.P)).trans
    (chartThickeningMap_comp B S hS E _ _))
  transitivity₂ := Over.OverMorphism.ext ((thick_map_comp_eq E (compHom_comp_sourceHom C.P)).trans
    (chartThickeningMap_comp B S hS E _ _))

end SquareZeroExtension

end AlgebraicGeometry.Space

end
