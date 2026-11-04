module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SectionRingBaseChange

/-!
# The base change of graded section rings is functorial in both opens

`Stacks.RelativeProj.Situation.gradedBaseChange g Φ W W' h` depends on a *pair* of opens,
`W ⊆ S` and `W' ⊆ g⁻¹W ⊆ S'`, and it is functorial in each: shrinking `W` before
base-changing is base-changing from the smaller `W`, and base-changing and then restricting to a
smaller `W'` is base-changing to that smaller `W'` directly.

## Main results

* `Stacks.RelativeProj.Situation.pieceSectionHom_target_le` and
  `pieceSectionHom_source_le`: the degreewise components are functorial in `W` and in `W'`.
* `Stacks.RelativeProj.Situation.sectionRingBaseChange_sectionRingRestrict` and
  `sectionRingRestrict_sectionRingBaseChange`: the same on the section rings.
* `Stacks.RelativeProj.Situation.gradedBaseChange_comp_gradedRestrict`: **functoriality in `W`.**
  `𝒜(W₂) ⟶ 𝒜(W₁) ⟶ 𝒜'(W')` is `𝒜(W₂) ⟶ 𝒜'(W')`.
* `Stacks.RelativeProj.Situation.gradedRestrict_comp_gradedBaseChange`: **functoriality in `W'`.**
  `𝒜(W) ⟶ 𝒜'(W₂') ⟶ 𝒜'(W₁')` is `𝒜(W) ⟶ 𝒜'(W₁')`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum

universe u

namespace Stacks.RelativeProj.Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)

/-! ### The degreewise components are functorial in each open -/

/-- **The degreewise components are functorial in the open of `S`.** Restricting a homogeneous
section from `W₂` to `W₁` and then base-changing to `W'` is base-changing from `W₂` directly. -/
public theorem pieceSectionHom_target_le (n : ℕ) {W₁ W₂ : s.base.Opens} (h₁₂ : W₁ ≤ W₂)
    (W' : s'.base.Opens) (h₁ : W' ≤ g ⁻¹ᵁ W₁) (h₂ : W' ≤ g ⁻¹ᵁ W₂)
    (a : s.sectionPieces W₂ n) :
    pieceSectionHom g Φ n W₁ W' h₁
        ((s.algebra.piece (n : ℤ)).val.map (homOfLE h₁₂).op a)
      = pieceSectionHom g Φ n W₂ W' h₂ a :=
  (pieceSectionHom_apply g Φ n W₁ W' h₁ _).trans
    ((congrArg (fun z => (Φ.app (n : ℤ)).val.app (op W') z)
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le g
          (s.algebra.piece (n : ℤ)) h₁₂ W' h₂ h₁ a)).trans
      (pieceSectionHom_apply g Φ n W₂ W' h₂ a).symm)

/-- **The degreewise components are functorial in the open of `S'`.** Base-changing to `W₂'` and
then restricting to `W₁'` is base-changing to `W₁'` directly. -/
public theorem pieceSectionHom_source_le (n : ℕ) (W : s.base.Opens)
    {W₁' W₂' : s'.base.Opens} (h' : W₁' ≤ W₂') (h₂ : W₂' ≤ g ⁻¹ᵁ W) (h₁ : W₁' ≤ g ⁻¹ᵁ W)
    (a : s.sectionPieces W n) :
    (s'.algebra.piece (n : ℤ)).val.map (homOfLE h').op (pieceSectionHom g Φ n W W₂' h₂ a)
      = pieceSectionHom g Φ n W W₁' h₁ a := by
  refine Eq.trans ?_ (pieceSectionHom_apply g Φ n W W₁' h₁ a).symm
  refine Eq.trans (congrArg ((s'.algebra.piece (n : ℤ)).val.map (homOfLE h').op)
    (pieceSectionHom_apply g Φ n W W₂' h₂ a)) ?_
  refine ((PresheafOfModules.naturality_apply (Φ.app (n : ℤ)).val (homOfLE h').op
    (Scheme.Modules.pullbackSection g (s.algebra.piece (n : ℤ)) W W₂' h₂ a)).symm).trans ?_
  exact congrArg (fun z => (Φ.app (n : ℤ)).val.app (op W₁') z)
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g
      (s.algebra.piece (n : ℤ)) W W₂' W₁' h₂ h' h₁ a)

/-! ### Functoriality of the base change of section rings -/

/-- **Functoriality in the open of `S`, on the section rings.** -/
public theorem sectionRingBaseChange_sectionRingRestrict {W₁ W₂ : s.base.Opens} (h₁₂ : W₁ ≤ W₂)
    (W' : s'.base.Opens) (h₁ : W' ≤ g ⁻¹ᵁ W₁) (h₂ : W' ≤ g ⁻¹ᵁ W₂) (x : s.sectionRing W₂) :
    sectionRingBaseChange g Φ W₁ W' h₁ (sectionRingRestrict s W₁ W₂ h₁₂ x)
      = sectionRingBaseChange g Φ W₂ W' h₂ x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n a =>
      exact (congrArg (fun z : s.sectionRing W₁ => sectionRingBaseChange g Φ W₁ W' h₁ z)
          ((sectionRingStructure s).restrict_of W₁ W₂ h₁₂ n a)).trans
        ((sectionRingBaseChange_of g Φ W₁ W' h₁ n _).trans
          ((congrArg (DirectSum.of (s'.sectionPieces W') n)
              (pieceSectionHom_target_le g Φ n h₁₂ W' h₁ h₂ a)).trans
            (sectionRingBaseChange_of g Φ W₂ W' h₂ n a).symm))
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **Functoriality in the open of `S'`, on the section rings.** -/
public theorem sectionRingRestrict_sectionRingBaseChange (W : s.base.Opens)
    {W₁' W₂' : s'.base.Opens} (h' : W₁' ≤ W₂') (h₂ : W₂' ≤ g ⁻¹ᵁ W) (h₁ : W₁' ≤ g ⁻¹ᵁ W)
    (x : s.sectionRing W) :
    sectionRingRestrict s' W₁' W₂' h' (sectionRingBaseChange g Φ W W₂' h₂ x)
      = sectionRingBaseChange g Φ W W₁' h₁ x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of n a =>
      exact (congrArg (fun z : s'.sectionRing W₂' => sectionRingRestrict s' W₁' W₂' h' z)
          (sectionRingBaseChange_of g Φ W W₂' h₂ n a)).trans
        (((sectionRingStructure s').restrict_of W₁' W₂' h' n _).trans
          ((congrArg (DirectSum.of (s'.sectionPieces W₁') n)
              (pieceSectionHom_source_le g Φ n W h' h₂ h₁ a)).trans
            (sectionRingBaseChange_of g Φ W W₁' h₁ n a).symm))
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-! ### Functoriality of the base change of graded rings -/

/-- **Functoriality in the open of `S`.** Restricting the graded section ring from `W₂` to `W₁`
and then base-changing to `W'` is base-changing from `W₂` directly. -/
public theorem gradedBaseChange_comp_gradedRestrict {W₁ W₂ : s.base.Opens} (h₁₂ : W₁ ≤ W₂)
    (W' : s'.base.Opens) (h₁ : W' ≤ g ⁻¹ᵁ W₁) (h₂ : W' ≤ g ⁻¹ᵁ W₂) :
    (gradedBaseChange g Φ W₁ W' h₁).comp (s.gradedRestrict h₁₂)
      = gradedBaseChange g Φ W₂ W' h₂ :=
  DFunLike.ext _ _ fun x =>
    sectionRingBaseChange_sectionRingRestrict g Φ h₁₂ W' h₁ h₂ x

/-- **Functoriality in the open of `S'`.** Base-changing to `W₂'` and then restricting the graded
section ring to `W₁'` is base-changing to `W₁'` directly. -/
public theorem gradedRestrict_comp_gradedBaseChange (W : s.base.Opens)
    {W₁' W₂' : s'.base.Opens} (h' : W₁' ≤ W₂') (h₂ : W₂' ≤ g ⁻¹ᵁ W) (h₁ : W₁' ≤ g ⁻¹ᵁ W) :
    (s'.gradedRestrict h').comp (gradedBaseChange g Φ W W₂' h₂)
      = gradedBaseChange g Φ W W₁' h₁ :=
  DFunLike.ext _ _ fun x =>
    sectionRingRestrict_sectionRingBaseChange g Φ W h' h₂ h₁ x

end Stacks.RelativeProj.Situation

end
