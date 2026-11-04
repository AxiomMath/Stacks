module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Limits.DescendingMorphismPropertiesSiteConvention
import all StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Limits.DescendingMorphismPropertiesSiteConvention

namespace AlgebraicGeometry.Space.MorphismDescentSituation.C1573
end AlgebraicGeometry.Space.MorphismDescentSituation.C1573

/-!
# Isomorphism under the site convention

The declarations below accompany
`StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism`: they state its results
under the chapter's standing convention of Section 70.2 (tag 07SD) on the size of the site, in the
form the absolute Noetherian approximation of Stacks 07SU consumes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Criterion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end Criterion

namespace MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

end MorphismDescentSystem

/-! ### The situation of Stacks 084W

The same results for `AlgebraicGeometry.Space.MorphismDescentSituation`, which imposes no
condition on the size of the index; the descent of isomorphisms then takes the explicit
hypothesis `hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D.base`, the
chapter's convention of Section 70.2 (tag 07SD), and is also stated under
`hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`, which implies it. -/

namespace MorphismDescentSituation

open _root_.AlgebraicGeometry.Space.MorphismDescentSituation.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-- The descent of isomorphisms for a situation whose affine charts at the distinguished stage
have their limits inside the site. -/
private theorem exists_isIso_mapAt_of_limitBridges
    (hL : ∀ (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
      (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀), Nonempty C.LimitBridge)
    (hf : IsIso D.mapLimit) (hfp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsIso (D.mapAt i hi) := by
  have _ := hf
  have hEt : IsEtale B S hS D.mapLimit := isEtale_of_iso B S hS (asIso D.mapLimit)
  have hUI : UniversallyInjective B S hS D.mapLimit := universallyInjective_of_isIso B S hS _
  have hSurj : IsSurjective B S hS D.mapLimit := by
    intro y
    refine ⟨pointsMap B S hS D.targetLimit (inv D.mapLimit) y, ?_⟩
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]
  obtain ⟨i₁, hi₁, hEt₁⟩ := exists_isEtale_mapAt_of_limitBridges D hL hEt hfp
  obtain ⟨i₂, hi₂, hUI₂⟩ := exists_universallyInjective_mapAt_of_limitBridges D hL hUI
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp)
  obtain ⟨i₃, hi₃, hSurj₃⟩ := exists_isSurjective_mapAt_of_limitBridges D hL hSurj hfp
  obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
  obtain ⟨j, hjk, hj₃⟩ := directed_of (· ≤ ·) k i₃
  refine ⟨j, hi₁.trans (hk₁.trans hjk), ?_⟩
  exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
    (D.sourceAt_isAlgebraicSpace j _) (D.targetAt_isAlgebraicSpace j _) _
    (D.isEtale_mapAt_of_le hi₁ (hk₁.trans hjk) hEt₁)
    (D.universallyInjective_mapAt_of_le hi₂ (hk₂.trans hjk) hUI₂)
    (D.isSurjective_mapAt_of_le hi₃ hj₃ hSurj₃)

/-- **Stacks 0852**, and **Stacks 084S**, with bounded base changes. In the situation of
Stacks 084W, with the base changes of the stages along the affine points of the distinguished
stage bounded below the site's cutoff (`AlgebraicGeometry.Space.HasBoundedBaseChanges`), if the
base change `f` of `f₀` to the limit `B` is an isomorphism and `f₀` is locally of finite
presentation, then the base change `f_i` of `f₀` to some stage `B_i` is an isomorphism.

This is the form the proof of Stacks 07SQ consumes, for an index of any size below a singular
cutoff whose transition morphisms do not enlarge affine schemes; see
`exists_isIso_mapAt_of_siteContainsBaseChangeLimits` for the statement under the chapter's
convention. -/
theorem C1573.exists_isIso_mapAt_of_hasBoundedBaseChanges
    (hb : HasBoundedBaseChanges B S hS (op D.initial) D.base) (hf : IsIso D.mapLimit)
    (hfp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (hi : D.initial ≤ i), IsIso (D.mapAt i hi) :=
  D.exists_isIso_mapAt_of_limitBridges (limitBridges_of_hasBoundedBaseChanges D hb) hf hfp

end MorphismDescentSituation

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Space.MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

end AlgebraicGeometry.Space.MorphismDescentSystem

end
