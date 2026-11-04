module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Graph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose
public import StacksCore.Tactic.StacksAttribute

/-!
# The transpose of the graph of a morphism

The transposed graph `Γ_fᵗ ⊆ Y ×_S X` of a morphism `f : Y ⟶ X` over `S` is the image of the
graph `Γ_f ⊆ X ×_S Y` under the factor switch. Transposing the cycle of the graph produces the
cycle of the transposed graph, and the same holds for the associated rational correspondences:
`[Γ_f]ᵗ = [Γ_fᵗ]`.

The ingredient is that the cycle of a closed subscheme transports along an isomorphism of the
ambient scheme over the base: proper pushforward along the isomorphism carries `[Z]_k` to
`[Z]_k` computed for the transported closed immersion, and the cycle of a closed subscheme
depends only on the subscheme, not on the presentation of its closed immersion.

## Main definitions

* `Stacks.WeilCohomology.transposedGraph`: the transposed graph `Γ_fᵗ ⊆ Y ×_S X`.

## Main results

* `Stacks.Chow.componentMultiplicity_comp_closedImmersion`: multiplicity is unchanged by
  composing a closed immersion with a further closed immersion.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isIso`: pushforward along
  an isomorphism over the base carries the cycle of a closed subscheme to the cycle of its
  image.
* `Stacks.WeilCohomology.cycleTranspose_graph` and `Stacks.WeilCohomology.transpose_graph`:
  `[Γ_f]ᵗ = [Γ_fᵗ]`, on cycles and on rational correspondences.

## Implementation notes

Neither statement uses smoothness, projectivity or a base field: they hold for any morphism of
schemes locally of finite type over a base situation in the sense of Stacks 02QL. Proper
pushforward on Chow groups is taken along an isomorphism, so, as in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose`, no instance of
Stacks 02S2 is required.

## References

* [Stacks Project, Tag 0FG4](https://stacks.math.columbia.edu/tag/0FG4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Multiplicity is unchanged by composing a closed immersion with a further closed immersion. -/
theorem componentMultiplicity_comp_closedImmersion {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (i : Z ⟶ Y) [IsClosedImmersion i] (ξ : genericPoints Z) :
    componentMultiplicity (i ≫ f) ξ = componentMultiplicity i ξ := by
  unfold componentMultiplicity
  let A := X.presheaf.stalk ((i ≫ f) ξ.1)
  let B := Y.presheaf.stalk (i ξ.1)
  let M := Z.presheaf.stalk ξ.1
  let _ : Algebra B M := ((i.stalkMap ξ.1).hom).toAlgebra
  let _ : Algebra A M := (((i ≫ f).stalkMap ξ.1).hom).toAlgebra
  have hA : Module.length A M = Module.length M M :=
    Module.length_eq_of_surjective (S := A) ((i ≫ f).stalkMap_surjective ξ.1)
  have hB : Module.length B M = Module.length M M :=
    Module.length_eq_of_surjective (S := B) (i.stalkMap_surjective ξ.1)
  exact congrArg (fun n : ENat => (n.toNat : ℤ)) (hA.trans hB.symm)

/-- Proper pushforward along an isomorphism over the base carries the cycle of a closed
subscheme `i : Z ⟶ X` to the cycle of the transported closed immersion `i ≫ e.hom`. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_of_isIso (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (e : X ≅ Y) (he : e.hom ≫ sY = sX) (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) :
    properPushforward C sX sY e.hom he k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToClosedSubscheme C sY (i ≫ e.hom) k := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ : ∃ x : X, e.hom x = y := ⟨e.inv y, by simp⟩
  have hpre : e.hom.base ⁻¹' ({e.hom x} : Set Y) = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hz ↦ e.hom.isClosedEmbedding.injective hz, fun hz ↦ hz ▸ rfl⟩
  have hdim : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (e.hom x) := by
    rw [← he]
    exact relativeDimension_comp_closedImmersion C.dimensionFunction e.hom sY x
  have hcoeff : (cycleAssociatedToClosedSubscheme C sX i k).1 x =
      (cycleAssociatedToClosedSubscheme C sY (i ≫ e.hom) k).1 (e.hom x) := by
    show closedSubschemeCycleCoeff C sX i k x =
      closedSubschemeCycleCoeff C sY (i ≫ e.hom) k (e.hom x)
    unfold closedSubschemeCycleCoeff
    have hexists :
        (∃ ξ : genericPoints Z, i ξ.1 = x ∧
            relativeDimension C.dimensionFunction sX x = k) ↔
          (∃ ξ : genericPoints Z, (i ≫ e.hom) ξ.1 = e.hom x ∧
            relativeDimension C.dimensionFunction sY (e.hom x) = k) := by
      constructor
      · rintro ⟨ξ, hξ, hξdim⟩
        exact ⟨ξ, by simp [hξ], hdim.symm.trans hξdim⟩
      · rintro ⟨ξ, hξ, hξdim⟩
        exact ⟨ξ, e.hom.isClosedEmbedding.injective
          (by simpa [Scheme.Hom.comp_apply] using hξ), hdim.trans hξdim⟩
    by_cases hL : ∃ ξ : genericPoints Z,
        i ξ.1 = x ∧ relativeDimension C.dimensionFunction sX x = k
    · have hR := hexists.mp hL
      rw [dite_eq_left hL, dite_eq_left hR]
      have hchoose : Classical.choose hR = Classical.choose hL := by
        refine Subtype.ext (i.isClosedEmbedding.injective
          (e.hom.isClosedEmbedding.injective ?_))
        calc
          e.hom (i (Classical.choose hR).1) = (i ≫ e.hom) (Classical.choose hR).1 :=
            (Scheme.Hom.comp_apply i e.hom _).symm
          _ = e.hom x := (Classical.choose_spec hR).1
          _ = e.hom (i (Classical.choose hL).1) :=
            congrArg e.hom (Classical.choose_spec hL).1.symm
      rw [hchoose]
      exact (componentMultiplicity_comp_closedImmersion e.hom i (Classical.choose hL)).symm
    · rw [dite_eq_right hL, dite_eq_right fun h ↦ hL (hexists.mpr h)]
  rw [properPushforward_apply, hpre]
  simpa [hdim, residueDegree_eq_one_of_isClosedImmersion e.hom x] using hcoeff

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

variable {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) (f : Y ⟶ X) (hf : f ≫ sX = sY)

/-- The transposed graph `Γ_fᵗ ⊆ Y ×_S X` of a morphism `f : Y ⟶ X` over `S`: the image of the
graph `Γ_f ⊆ X ×_S Y` under the factor switch. -/
abbrev transposedGraph : Scheme.{u} :=
  (graphMorphism sX sY f hf ≫ (pullbackSymmetry sX sY).hom).image

/-- The factor switch identifies the graph with the transposed graph as closed subschemes. -/
theorem imageIsoOfIsIso_graphMorphism_hom_imageι :
    (Scheme.Hom.imageIsoOfIsIso (graphMorphism sX sY f hf)
          (pullbackSymmetry sX sY).hom).hom ≫
        (graphMorphism sX sY f hf ≫ (pullbackSymmetry sX sY).hom).imageι =
      (graphMorphism sX sY f hf).imageι ≫ (pullbackSymmetry sX sY).hom := by
  simp

variable (C : Stacks.Chow.ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]

/-- **Stacks Project, Tag 0FG4.** Transposing the cycle of the graph of `f : Y ⟶ X` gives the
cycle of the transposed graph. -/
@[stacks 0FG4 "transpose_graph"]
theorem cycleTranspose_graph (f : Y ⟶ X) (hf : f ≫ sX = sY) (k : ℤ) :
    cycleTranspose C sX sY k
        (cycleAssociatedToClosedSubscheme C (pullback.fst sX sY ≫ sX)
          (graphMorphism sX sY f hf).imageι k) =
      cycleAssociatedToClosedSubscheme C (pullback.fst sY sX ≫ sY)
        (graphMorphism sX sY f hf ≫ (pullbackSymmetry sX sY).hom).imageι k :=
  (properPushforward_cycleAssociatedToClosedSubscheme_of_isIso C (pullback.fst sX sY ≫ sX)
      (pullback.fst sY sX ≫ sY) (pullbackSymmetry sX sY) (pullbackSymmetry_hom_comp_base sX sY)
      (graphMorphism sX sY f hf).imageι k).trans
    (cycleAssociatedToClosedSubscheme_eq_of_iso C (pullback.fst sY sX ≫ sY) _ _
      (Scheme.Hom.imageIsoOfIsIso (graphMorphism sX sY f hf) (pullbackSymmetry sX sY).hom)
      (imageIsoOfIsIso_graphMorphism_hom_imageι sX sY f hf) k)

/-- **Stacks Project, Tag 0FG4.** The transpose of the rational correspondence of the graph of
`f : Y ⟶ X` is the rational correspondence of the transposed graph: `[Γ_f]ᵗ = [Γ_fᵗ]`. -/
@[stacks 0FG4 "transpose_graph"]
theorem transpose_graph (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e r : ℤ) (q : ℚ) :
    transpose C sX sY d e r (q ⊗ₜ[ℤ] QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C (pullback.fst sX sY ≫ sX)
          (graphMorphism sX sY f hf).imageι (e - r))) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
        (show e - r = d - (d - e + r) by omega)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C (pullback.fst sY sX ≫ sY)
          (graphMorphism sX sY f hf ≫ (pullbackSymmetry sX sY).hom).imageι (e - r))) := by
  rw [transpose_tmul]
  exact congrArg (fun α ↦ q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sY sX ≫ sY)
    (show e - r = d - (d - e + r) by omega) α)
    (congrArg QuotientAddGroup.mk (cycleTranspose_graph C sX sY f hf (e - r)))

end Stacks.WeilCohomology

end
