module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCoverSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A connected smooth scheme over a field has a relative dimension

A connected scheme `X` smooth over a field `k` is smooth of pure relative dimension: there is a
single `d` such that `X ⟶ Spec k` is smooth of relative dimension `d`.

## Main results

* `AlgebraicGeometry.exists_smoothOfRelativeDimension_of_connectedSpace`: a connected scheme smooth
  over a field is smooth of pure relative dimension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A connected scheme smooth over a field is smooth of pure relative dimension**: there is
`d` with `X ⟶ Spec k` smooth of relative dimension `d`. -/
@[sga "4½ Th_finitude 2.2" "Clause (a), special case"]
theorem exists_smoothOfRelativeDimension_of_connectedSpace {k : Type u} [Field k]
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k)) [Smooth f] :
    ∃ d : ℕ, SmoothOfRelativeDimension d f := by
  let : ∀ n, IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) := fun n =>
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} n)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  choose V hxV n hn using Smooth.exists_smoothOfRelativeDimension_nbhd f
  have key : ∀ x y, y ∈ V x → n y = n x := by
    intro x y hy
    let W : X.Opens := V x ⊓ V y
    have : Nonempty W := ⟨⟨y, hy, hxV y⟩⟩
    have dim_eq : ∀ z, W ≤ V z → topologicalKrullDim W = (n z : WithBot ℕ∞) := fun z hz => by
      have : SmoothOfRelativeDimension (n z) (W.ι ≫ f) := by
        rw [← X.homOfLE_ι hz, Category.assoc]
        exact IsZariskiLocalAtSource.comp (hn z) _
      exact topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (n z) (W.ι ≫ f)
    exact_mod_cast (dim_eq y inf_le_right).symm.trans (dim_eq x inf_le_left)
  have hloc : IsLocallyConstant n := IsLocallyConstant.iff_exists_open _ |>.2 fun y =>
    ⟨V y, (V y).2, hxV y, fun z hz => key y z hz⟩
  have hall : ∀ y, n y = n x₀ := fun y => hloc.apply_eq_of_preconnectedSpace y x₀
  exact ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top V
    (top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxV y⟩) fun i => hall i ▸ hn i⟩

end AlgebraicGeometry

end
