module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionThickenedRelation

/-!
# The ambient algebraic space of a square-zero extension

WIP
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)
  (hcU : B.Contains (chartThickening B S hS E (presentationChart C.P)))
  (hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P)))

/-- The thickened presenting chart, as an object of the big fppf site over `S`. -/
def ambU : BigFppfOver B S hS := BigFppfOver.mk B S hS hcU (presentationThickeningToBase E C)

/-- The thickened relation chart, as an object of the big fppf site over `S`. -/
def ambR : BigFppfOver B S hS := BigFppfOver.mk B S hS hcR (relationThickeningToBase E C)

/-- The thickened source leg, as a morphism of the big fppf site over `S`. -/
def ambSource : ambR E C hcR ⟶ ambU E C hcU :=
  BigFppfOver.homMk B S hS hcU _ (chartThickeningMap B S hS E (presentationRelationSourceHom C.P))
    rfl

/-- The thickened target leg, as a morphism of the big fppf site over `S`. -/
def ambTarget : ambR E C hcR ⟶ ambU E C hcU :=
  BigFppfOver.homMk B S hS hcU _ (chartThickeningMap B S hS E (presentationRelationTargetHom C.P))
    (target_comp_presentationThickeningToBase E C)

attribute [local instance] hasSheafify_bigFppfOver

/-- **The thickened legs form an étale equivalence relation** on the thickened presenting chart. -/
instance isEtaleEquivalenceRelation_amb :
    IsEtaleEquivalenceRelation
      (relation B S hS (ambSource E C hcU hcR) (ambTarget E C hcU hcR)) := by
  have htarget : (relation B S hS (ambSource E C hcU hcR) (ambTarget E C hcU hcR)).target =
      (Over.post B.inclusion).map (ambTarget E C hcU hcR) := prod.lift_fst _ _
  have hsource : (relation B S hS (ambSource E C hcU hcR) (ambTarget E C hcU hcR)).source =
      (Over.post B.inclusion).map (ambSource E C hcU hcR) := prod.lift_snd _ _
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [htarget, hsource]
    exact (thickEquivalenceRelation E C).isEquivalenceRelation
  · rw [hsource]
    exact etale_chartThickeningMap B S hS E (presentationRelationSourceHom C.P)
  · rw [htarget]
    exact etale_chartThickeningMap B S hS E (presentationRelationTargetHom C.P)

/-- **The ambient space `X'`**: the quotient of the thickened presenting chart by the thickened
relation, an algebraic space over `S` by [Stacks Project, Tag 02WW]. -/
def ambient : AlgebraicSpaces B S hS :=
  ⟨(quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (relation B S hS (ambSource E C hcU hcR) (ambTarget E C hcU hcR))).obj,
    isAlgebraicSpace_quotient_unconditional B S hS _ _⟩

end SquareZeroExtension

end AlgebraicGeometry.Space

end
