module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.Iso
public import StacksFrontier.AlgebraicGeometry.TwistBaseChange.DegreewiseIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartHypothesisBaseChange

/-!
# The graded ring map of sections of a base change, and its twist comparisons

For a quasi-coherent graded `𝒪_S`-algebra `A`, a morphism `g : S' ⟶ S` and affine opens
`U' ⊆ g⁻¹U`, `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange` is the graded
ring map `Γ(U, A) ⟶ Γ(U', g^*A)`. This file computes it on homogeneous sections and proves that
Tag 01MY's comparison maps on the twists of `Proj` along it are isomorphisms.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange_of`: a homogeneous
  section goes to the restriction of its pullback.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.isIso_twistMap_sectionBaseChange`:
  **the comparison map on every twist is an isomorphism.**

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjPresentation

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- **The graded ring map of sections on a homogeneous section**: a section of `A` of degree `k`
over `U` goes to the restriction to `U'` of its pullback, in degree `k`. -/
theorem sectionBaseChange_of (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) (k : ℕ) (a : A.sectionPieces U.toOpens k) :
    sectionBaseChange A g U U' h (DirectSum.of (A.sectionPieces U.toOpens) k a) =
      DirectSum.of ((A.pullback g).sectionPieces U'.toOpens) k
        (Scheme.Modules.pullbackSection g (A.piece (k : ℤ)) U.toOpens U'.toOpens h a) := by
  have e1 := situationSectionRingEquiv_of (algebra A) (isCommutative A)
    (vanishesInNegativeDegrees A) A.isQuasicoherent U.toOpens k a
  have e2 := Stacks.RelativeProj.Situation.sectionRingBaseChange_of (s := situation A)
    (s' := situation (A.pullback g)) g (pullbackHom A g) U.toOpens U'.toOpens h k a
  have e3 := situationSectionRingEquiv_symm_of (algebra (A.pullback g))
    (isCommutative (A.pullback g)) (vanishesInNegativeDegrees (A.pullback g))
    (A.pullback g).isQuasicoherent U'.toOpens k
    (Scheme.Modules.pullbackSection g (A.piece (k : ℤ)) U.toOpens U'.toOpens h a)
  exact (congrArg (situationSectionRingEquiv (algebra (A.pullback g))
    (isCommutative (A.pullback g)) (vanishesInNegativeDegrees (A.pullback g))
    (A.pullback g).isQuasicoherent U'.toOpens).symm
      ((congrArg (Stacks.RelativeProj.Situation.sectionRingBaseChange (s := situation A)
        (s' := situation (A.pullback g)) g (pullbackHom A g) U.toOpens U'.toOpens h) e1).trans
        e2)).trans e3

/-- **Tag 01MY's comparison map on the `n`-th twist for `Γ(U, A) ⟶ Γ(U', g^*A)` is an
isomorphism**, for every `n : ℤ`, with the ring and grading instances written out. -/
theorem isIso_twistMap_sectionBaseChangeComp (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) (n : ℤ) :
    IsIso (@Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap (A.sectionRing U.toOpens)
      ((A.pullback g).sectionRing U'.toOpens) _ _
      (inferInstance : CommRing (A.sectionRing U.toOpens))
      (inferInstance : CommRing ((A.pullback g).sectionRing U'.toOpens))
      (inferInstance : SetLike (AddSubgroup (A.sectionRing U.toOpens)) (A.sectionRing U.toOpens))
      (inferInstance :
        AddSubgroupClass (AddSubgroup (A.sectionRing U.toOpens)) (A.sectionRing U.toOpens))
      (inferInstance : SetLike (AddSubgroup ((A.pullback g).sectionRing U'.toOpens))
        ((A.pullback g).sectionRing U'.toOpens))
      (inferInstance : AddSubgroupClass (AddSubgroup ((A.pullback g).sectionRing U'.toOpens))
        ((A.pullback g).sectionRing U'.toOpens))
      (A.grading U.toOpens) ((A.pullback g).grading U'.toOpens)
      (inferInstance : GradedRing (A.grading U.toOpens))
      (inferInstance : GradedRing ((A.pullback g).grading U'.toOpens))
      (sectionBaseChangeComp A g U U' h) n) := by
  have : GradedRing (A.grading U.toOpens) := inferInstance
  have : GradedRing ((A.pullback g).grading U'.toOpens) := inferInstance
  let := (sectionBaseChangeComp A g U U' h).gradedZeroRingHom.toAlgebra
  let := (Stacks.RelativeProj.Situation.gradedBaseChange (s := situation A)
    (s' := situation (A.pullback g)) g (pullbackHom A g) U.toOpens U'.toOpens
      h).gradedZeroRingHom.toAlgebra
  exact Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_of_isBaseChange
    (sectionBaseChangeComp A g U U' h) (fun _ => rfl)
    (Stacks.AlgebraicGeometry.TwistBaseChange.isBaseChange_pieceMap_comp_of_isIso
      (chartHom A U) (chartInv A U)
      (chartInv_comp_chartHom A U) (chartHom_comp_chartInv A U)
      (chartInv (A.pullback g) U') (chartHom (A.pullback g) U')
      (chartHom_comp_chartInv (A.pullback g) U') (chartInv_comp_chartHom (A.pullback g) U')
      (Stacks.RelativeProj.Situation.gradedBaseChange (s := situation A)
        (s' := situation (A.pullback g)) g (pullbackHom A g) U.toOpens U'.toOpens h)
      (fun _ => rfl)
      (fun m => Stacks.RelativeProj.Situation.isBaseChange_pieceMap_gradedBaseChange
        (s := situation A) (s' := situation (A.pullback g)) g
        (pullbackHom A g) m (isAffineOpen_toOpens U) (isAffineOpen_toOpens U') h
        (isIso_pullbackHom_app A g) (fun _ => rfl) (fun _ => rfl))
      (fun _ => rfl)) n

/-- **Tag 01MY's comparison map on the `n`-th twist for `Γ(U, A) ⟶ Γ(U', g^*A)` is an
isomorphism**, at the canonical gradings. -/
theorem isIso_twistMap_sectionBaseChange (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) (n : ℤ) :
    IsIso (Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap (A.grading U.toOpens)
      ((A.pullback g).grading U'.toOpens) (sectionBaseChange A g U U' h) n) :=
  isIso_twistMap_sectionBaseChangeComp A g U U' h n

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
