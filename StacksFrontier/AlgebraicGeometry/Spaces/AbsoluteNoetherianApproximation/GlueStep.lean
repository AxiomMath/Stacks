module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.LimitApprox.DescendOpen
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Assemble
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.RelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Absolute Noetherian approximation: the gluing step

The gluing step of the proof of Stacks 07SU: from a system `U_j` with limit the open `U ⊆ X`, a
system `V_j` with limit the étale neighbourhood `V` of the closed complement of `U`, and
compatible opens `W_j ⊆ V_j` étale over `U_j` with limit `W = V ×_X U`, the glued relations
`R_j = V_j ⊔_{W_j} W_j ×_{U_j} W_j` (`AlgebraicGeometry.Space.GluedRelationSystemData`) present a
Noetherian approximation of `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **The gluing step of the proof of Stacks 07SU.** Let `X` be an algebraic space covered by an
open `U` and a closed `Z`, and `f : V ⟶ X` an étale surjection from a scheme which is an
isomorphism over `Z`. Given, over a common directed index, a system `U_j` with limit `U`, a system
`V_j` of schemes with limit `V`, and compatible opens `W_j ⊆ V_j` étale over `U_j` with limit
`W = V ×_X U`, the quotients `V_j / R_j` of the glued relations form a Noetherian approximation of
`X` in the sense of `HasConventionalNoetherianApproximation`. -/
theorem hasConventionalNoetherianApproximation_of_gluing
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (_hXqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X)
    (U : Subfunctor X) (hU : IsOpenSubspace B (⊤_ Scheme.{u}) hZ U)
    (Z : Subfunctor X) (hZc : IsClosedSubspace B (⊤_ Scheme.{u}) hZ Z)
    (hcover : ∀ x : points B (⊤_ Scheme.{u}) hZ X,
      x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ U.toFunctor U.ι) ∨
        x ∈ Set.range (pointsMap B (⊤_ Scheme.{u}) hZ Z.toFunctor Z.ι))
    (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (f : yoneda.obj V ⟶ X)
    (_hVc : CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
    (_hVs : Scheme.IsSeparated ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V))
    (hfs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf f)
    (hfe : IsEtale B (⊤_ Scheme.{u}) hZ f) (hfZ : IsIso (pullback.fst Z.ι f))
    -- the approximation of the open `U`
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
    (hD : ∀ j, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj j))
    (hDqs : ∀ j, IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (D.obj j))
    (uπ : (Functor.const Jᵒᵖ).obj U.toFunctor ⟶ D) (huπ : IsLimit (Cone.mk _ uπ))
    -- the approximation of `V`
    (Vs : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ) (vπ : (Functor.const Jᵒᵖ).obj V ⟶ Vs)
    (hvπ : IsLimit ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapCone (Cone.mk V vπ)))
    (hVsc : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j)))
    (hVsft : ∀ j, LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Vs.obj j))))
    (hVsaff : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'),
      _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (Vs.map e)))
    -- the compatible open subschemes `W_j ⊆ V_j`, étale over the stages `U_j`
    (Ws : Jᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ) (ι : Ws ⟶ Vs)
    (hι : ∀ j, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (ι.app j)))
    (hιcart : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'), IsPullback (Ws.map e) (ι.app j) (ι.app j') (Vs.map e))
    (g : Ws ⋙ yoneda ⟶ D) (hge : ∀ j, IsEtale B (⊤_ Scheme.{u}) hZ (g.app j))
    (hgcart : ∀ {j j' : Jᵒᵖ} (e : j ⟶ j'),
      IsPullback (yoneda.map (Ws.map e)) (g.app j) (g.app j') (D.map e))
    (hWsc : ∀ j, CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj (Ws.obj j)))
    -- the open `W = f⁻¹(U)` of `V`, and its compatibility with the systems
    (W : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ιW : W ⟶ V) (gW : yoneda.obj W ⟶ U.toFunctor)
    (hW : IsPullback (yoneda.map ιW) gW f U.ι)
    (wπ : (Functor.const Jᵒᵖ).obj W ⟶ Ws)
    (hwcart : ∀ j, IsPullback (wπ.app j) ιW (ι.app j) (vπ.app j))
    (hwg : ∀ j, yoneda.map (wπ.app j) ≫ g.app j = gW ≫ uπ.app j) :
    HasConventionalNoetherianApproximation B hZ X := by
  let G : GluedRelationSystemData B (⊤_ Scheme.{u}) hZ Jᵒᵖ := ⟨D, hD, Vs, Ws, ι, hι, g, hge⟩
  have := G.isEtaleEquivalenceRelation
  exact hasConventionalNoetherianApproximation_of_relationSystem hX U hU Z hZc hcover V f hfs
    (presheaf_etale_of_isEtale B (⊤_ Scheme.{u}) hZ hfe) hfe hfZ D hD uπ huπ Vs Ws G.P G.R vπ hvπ
    hVsc hVsft
    (fun j => quasiSeparatedSpace_of_locallyOfFiniteType_terminal _) hVsaff ι hι g W ιW gW hW wπ
    hwcart hwg G.p₁ G.p₂ G.isPullback_p G.δ (fun j => inferInstance) G.a G.b G.s G.t G.isPushout
    (fun j => by rw [← NatTrans.comp_app, G.a_s, NatTrans.id_app])
    (fun j => by rw [← NatTrans.comp_app, G.a_t, NatTrans.id_app])
    (fun j => by rw [← NatTrans.comp_app, G.b_s, NatTrans.comp_app])
    (fun j => by rw [← NatTrans.comp_app, G.b_t, NatTrans.comp_app])
    (G.isPullback_R_map hιcart hgcart)
    (fun j =>
      (G.etale_and_isEquivalenceRelation j).2.2.nonempty_equivalenceRelation.some.toJointlyMono₂)
    (G.quasiCompact_s hZ hDqs hVsc hWsc hVsft)

end AlgebraicGeometry.Space

end
