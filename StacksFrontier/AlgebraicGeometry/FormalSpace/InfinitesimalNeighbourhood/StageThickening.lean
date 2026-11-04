module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.StageCriterion
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction

/-!
# The stages of a formal spectrum are representable thickenings

Each stage `Spec(A/J) ⟶ Spf A` of the formal spectrum of a weakly admissible topological ring is a
representable thickening (Stacks 0AI9), read for the universe-lifted Yoneda embedding.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_stageIncl`: each stage is a
  representable thickening.

## References

* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- A stage `Spec(A/J) ⟶ Spf A` of a formal spectrum is a representable thickening, for the
universe-lifted Yoneda embedding. -/
theorem isRepresentableThickeningULift_stageIncl (hA : IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (L : { I : Ideal A // IsWeakIdealOfDefinition I }) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (stageIncl D L).hom := by
  classical
  let I₀ := { I : Ideal A // IsWeakIdealOfDefinition I }
  let I := ULift.{u + 1} (OrderDual I₀)
  let eOrder : OrderDual I₀ ≃o I := { toEquiv := Equiv.ulift.symm, map_rel_iff' := Iff.rfl }
  let eI : OrderDual I₀ ≌ I := eOrder.equivalence
  have : Nonempty I := ⟨ULift.up ⟨hA.1.choose, hA.1.choose_spec⟩⟩
  have : IsDirected I (· ≤ ·) := ⟨fun i j => by
    refine ⟨ULift.up ⟨i.down.1 ⊓ j.down.1,
      ⟨i.down.2.1.inter j.down.2.1, fun x hx => i.down.2.2 x hx.1⟩⟩, ?_, ?_⟩
    · exact (inf_le_left : i.down.1 ⊓ j.down.1 ≤ i.down.1)
    · exact (inf_le_right : i.down.1 ⊓ j.down.1 ≤ j.down.1)⟩
  let E' : I ⥤ BigAffineFppf B S hS := eI.inverse ⋙ D.diagram
  have hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E'.map g)) :=
    fun _ _ g => D.isThickening_map_diagram (eI.inverse.map g)
  let p := colimit.pre (formalSpectrumDiagram D) eI.inverse
  have hp : IsIso p := inferInstance
  have h := isThickening_colimitι B S hS E' hD (formalSpectrum D) (@asIso _ _ _ _ p hp)
    (ULift.up (OrderDual.toDual L))
  have hι : colimit.ι (E' ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (ULift.up (OrderDual.toDual L)) ≫
        (@asIso _ _ _ _ p hp).hom = stageIncl D L := by
    change colimit.ι (eI.inverse ⋙ formalSpectrumDiagram D) _ ≫ p = _
    exact colimit.ι_pre _ _ _
  replace h := hι ▸ h
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  exact relative_uliftYoneda_of_sheafifiedYoneda B S hS P h

end AlgebraicGeometry.FormalSpace

end
