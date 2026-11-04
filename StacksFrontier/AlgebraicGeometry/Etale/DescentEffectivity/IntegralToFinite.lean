module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.LimitEffective
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralAffineLimit09YZ

/-!
# Integral descent over an affine base reduces to finite descent

An integral morphism to an affine scheme is the limit of a directed inverse system of morphisms
finite and of finite presentation to that scheme
(`AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine`, the affine case of
[Stacks, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)). Feeding that presentation into
`AlgebraicGeometry.LimitDatum.qcSepEtaleEffective_of_forall_stage` reduces the effectivity of
quasi-compact separated étale descent along a surjective integral morphism with affine base to
the same statement for morphisms that are finite, of finite presentation and surjective.

The index category of the presentation is the opposite of a directed preorder, hence cofiltered
and connected; the base system is constant, so its limit cone is the constant cone and every one
of its stages is the affine base itself; and every stage of the source system is finite over an
affine scheme, hence affine. Surjectivity passes to the stages because the given morphism factors
through each of them.

## Main results

* `AlgebraicGeometry.qcSepEtaleEffective_of_forall_isFinite_finitePresentation`: **effectivity of
  quasi-compact separated étale descent along a surjective integral morphism with affine base
  follows from effectivity along the finite, finitely presented, surjective morphisms to that
  base.**

## References

* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **Effectivity of quasi-compact separated étale descent along a surjective integral morphism
with affine base reduces to the finite, finitely presented case.** -/
theorem qcSepEtaleEffective_of_forall_isFinite_finitePresentation {S X : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [Surjective f] [IsIntegralHom f]
    (H : ∀ (X' : Scheme.{u}) (g : X' ⟶ S), IsFinite g → FinitePresentation g → Surjective g →
      QcSepEtaleEffective g) :
    QcSepEtaleEffective f := by
  obtain ⟨P⟩ := nonempty_integralLimitPresentation_of_isAffine f
  let := P.indexPreorder
  let := P.indexNonempty
  let := P.indexDirected
  have hfin (i : P.indexTypeᵒᵖ) : IsFinite (P.structureMap.app i) := P.stageFinite i
  have haffS (i : P.indexTypeᵒᵖ) :
      IsAffine (((Functor.const P.indexTypeᵒᵖ).obj S).obj i) := inferInstanceAs (IsAffine S)
  have haffX (i : P.indexTypeᵒᵖ) : IsAffine (P.diagram.obj i) := by
    have := hfin i
    have := haffS i
    exact isAffine_of_isAffineHom (P.structureMap.app i)
  have hconn : IsConnected P.indexTypeᵒᵖ := IsCofiltered.isConnected P.indexTypeᵒᵖ
  have hf : ∀ i, (Cone.mk X P.limitCone).π.app i ≫ P.structureMap.app i =
      f ≫ (constCone P.indexTypeᵒᵖ S).π.app i := fun i ↦ by
    simpa using (P.compatible i).symm
  have hsurj (i : P.indexTypeᵒᵖ) : Surjective (P.structureMap.app i) := by
    have : Surjective (P.limitCone.app i ≫ P.structureMap.app i) := by
      rw [← P.compatible i]; infer_instance
    exact Surjective.of_comp (f := P.limitCone.app i) (g := P.structureMap.app i)
  exact LimitDatum.qcSepEtaleEffective_of_forall_stage (cX := Cone.mk X P.limitCone)
    (cS := constCone P.indexTypeᵒᵖ S) P.structureMap f hf P.isLimit
    (isLimitConstCone P.indexTypeᵒᵖ S)
    fun i ↦ H _ _ (hfin i) (P.stageFinitePresentation i) (hsurj i)

end AlgebraicGeometry

end
