module

public import StacksFrontier.AlgebraicGeometry.Modules.PullbackVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice

/-!
# Vanishing of a homomorphism of modules along an open immersion, and near every point

## Main results

* `AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_eq_zero_of_pullback`: a homomorphism of
  modules whose inverse image along an open immersion vanishes has vanishing restriction along it.
* `AlgebraicGeometry.Scheme.Modules.app_eq_zero_of_le_opensRange`: a homomorphism of modules whose
  restriction along an open immersion vanishes kills every section over every open contained in
  the image.
* `AlgebraicGeometry.Scheme.Modules.app_eq_zero_of_forall_exists_le`: the image of a *section*
  under a homomorphism of modules vanishes as soon as it vanishes near every point.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X Y : Scheme.{u}}

/-- A homomorphism of modules whose inverse image along an open immersion vanishes also has
vanishing restriction along that open immersion. -/
theorem restrictFunctor_map_eq_zero_of_pullback {M N : X.Modules} (j : Y ⟶ X)
    [IsOpenImmersion j] (φ : M ⟶ N) (h : (Scheme.Modules.pullback j).map φ = 0) :
    (Scheme.Modules.restrictFunctor j).map φ = 0 := by
  set α := Scheme.Modules.restrictFunctorIsoPullback j with hα
  have hn := α.hom.naturality φ
  rw [h] at hn
  exact (cancel_mono (α.hom.app N)).1 (by simpa using hn)

/-- A homomorphism of modules whose restriction along an open immersion vanishes kills every
section over every open contained in the image of that open immersion. -/
theorem app_eq_zero_of_le_opensRange {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (φ : M ⟶ N) (h : (Scheme.Modules.restrictFunctor j).map φ = 0) {V : X.Opens}
    (hV : V ≤ j.opensRange) (x : Γ(M, V)) : φ.app V x = 0 := by
  have hV' : j ''ᵁ (j ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hV
  have hcomp := congrArg (fun g => g.app (j ⁻¹ᵁ V)) h
  change φ.app (j ''ᵁ (j ⁻¹ᵁ V)) = 0 at hcomp
  rw [hV'] at hcomp
  exact congrArg (fun q => q x) hcomp

/-- The image of a section under a homomorphism of modules vanishes as soon as it vanishes near
every point. -/
theorem app_eq_zero_of_forall_exists_le {M N : X.Modules} (φ : M ⟶ N) {V : X.Opens}
    (x : Γ(M, V))
    (h : ∀ y ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), y ∈ W ∧
      φ.app W (M.presheaf.map (homOfLE hW).op x) = 0) :
    φ.app V x = 0 := by
  refine Stacks.SheafOfModules.eq_zero_of_locally_zero' N _ fun y hy => ?_
  obtain ⟨W, hW, hyW, hz⟩ := h y hy
  exact ⟨W, homOfLE hW, hyW,
    (PresheafOfModules.naturality_apply φ.val (homOfLE hW).op x).symm.trans hz⟩

end AlgebraicGeometry.Scheme.Modules

end
