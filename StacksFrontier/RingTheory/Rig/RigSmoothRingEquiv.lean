module

public import StacksFrontier.RingTheory.Restricted.RigEtale
public import StacksFrontier.RingTheory.Rig.RigEtaleRingEquiv

/-!
# Rig-smoothness is invariant under isomorphisms of Noetherian adic rings

A rig-étale arrow of `WAdm^{Noeth}` is rig-smooth (Stacks 0GB1 read on the target of the arrow),
so an isomorphism of Noetherian adic topological rings, continuous in both directions, is
rig-smooth by `RingHom.isRigEtale_ringEquiv`. Together with the stability of rig-smoothness
under composition (**Stacks 0GCM**) this makes rig-smoothness of an arrow of `WAdm^{Noeth}`
depend only on the arrow up to isomorphism of its source and target, which is what lets the
rig-smooth chart condition of a morphism of formal algebraic spaces be read off any one
presentation of the chart map. This is the rig-smooth counterpart of
`StacksFrontier.RingTheory.Rig.RigEtaleRingEquiv`.

## Main results

* `RingHom.IsRigEtale.isRigSmooth`: a rig-étale homomorphism of Noetherian adic rings is
  rig-smooth.
* `RingHom.isRigSmooth_ringEquiv`: an isomorphism of Noetherian adic topological rings is
  rig-smooth.
* `RingHom.isRigSmoothArrow_of_comp_ringEquiv`: if `g ∘ α = β ∘ g₀` with `α`, `β` isomorphisms
  of Noetherian adic topological rings and `g₀` rig-smooth, then `g` is rig-smooth.

## References

* [Stacks Project, Tag 0GB1](https://stacks.math.columbia.edu/tag/0GB1)
* [Stacks Project, Tag 0GCJ](https://stacks.math.columbia.edu/tag/0GCJ)
* [Stacks Project, Tag 0GCM](https://stacks.math.columbia.edu/tag/0GCM)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public section

universe u v

namespace RingHom

/-- **A rig-étale arrow is rig-smooth.** A rig-étale homomorphism of Noetherian adic topological
rings in the sense of Stacks 0GCV is rig-smooth in the sense of Stacks 0GCJ: over the ideal of
definition at which its target is rig-étale, the target is rig-smooth by Stacks 0GB1. -/
theorem IsRigEtale.isRigSmooth {A : Type u} {C : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C] {φ : A →+* C} (hφ : IsRigEtale φ) : IsRigSmooth φ := by
  obtain ⟨hft, I, hI, hc, hfin, hre⟩ := hφ
  refine ⟨hft, I, hI, ?_⟩
  let _ : Algebra A C := φ.toAlgebra
  let _ : Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := hfin
  have heq : Rig.adicFiniteTypeAlgebra φ hft I hI =
      Rig.AdicFiniteTypeAlgebra.of (I := I) C hc := rfl
  rw [heq]
  exact Rig.isRigSmooth_of_isRigEtale _ hre

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing C]

/-- **An isomorphism of Noetherian adic topological rings is rig-smooth.** -/
theorem isRigSmooth_ringEquiv (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm) :
    IsRigSmooth (e : A →+* C) :=
  (isRigEtale_ringEquiv hA hC e he he').isRigSmooth

omit [IsLinearTopology A A] [IsNoetherianRing A] [IsLinearTopology C C] [IsNoetherianRing C] in
/-- **Rig-smoothness depends on an arrow only up to isomorphism of source and target.** If
`g ∘ α = β ∘ g₀` for isomorphisms `α`, `β` of Noetherian adic topological rings, continuous in
both directions, and `g₀` is a continuous rig-smooth homomorphism, then so is `g`: it is the
composite `β ∘ g₀ ∘ α⁻¹` of three rig-smooth arrows, and rig-smoothness is stable under
composition by Stacks 0GCM. -/
theorem isRigSmoothArrow_of_comp_ringEquiv {A₀ C₀ : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [IsNoetherianRing A₀]
    [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀]
    [IsNoetherianRing C₀]
    (hA₀ : TopologicalRing.IsAdic A₀) (hC₀ : TopologicalRing.IsAdic C₀)
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (g₀ : A₀ →+* C₀) (g : A →+* C)
    (α : A₀ ≃+* A) (hα : Continuous α) (hα' : Continuous α.symm)
    (β : C₀ ≃+* C) (hβ : Continuous β) (hβ' : Continuous β.symm)
    (hsq : g.comp (α : A₀ →+* A) = (β : C₀ →+* C).comp g₀) (h₀ : IsRigSmoothArrow g₀) :
    IsRigSmoothArrow g := by
  have he : g = ((β : C₀ →+* C).comp g₀).comp (α.symm : A →+* A₀) := by
    rw [← hsq, RingHom.comp_assoc]
    ext x
    simp
  obtain ⟨hg₀, -⟩ := h₀
  have hβg₀ : IsRigSmoothArrow ((β : C₀ →+* C).comp g₀) :=
    Rig.rigSmooth_comp ⟨hC, inferInstance⟩ ⟨hC₀, inferInstance⟩ ⟨hA₀, inferInstance⟩
      (β : C₀ →+* C) g₀ hβ hg₀ ⟨hβ, isRigSmooth_ringEquiv hC₀ hC β hβ hβ'⟩ h₀
  have hα's : IsRigSmoothArrow (α.symm : A →+* A₀) :=
    ⟨hα', isRigSmooth_ringEquiv hA hA₀ α.symm hα' (by simpa using hα)⟩
  rw [he]
  intro _ _ _ _
  exact Rig.rigSmooth_comp ⟨hC, inferInstance⟩ ⟨hA₀, inferInstance⟩ ⟨hA, inferInstance⟩
    _ (α.symm : A →+* A₀) (hβ.comp hg₀) hα' hβg₀ hα's

end RingHom

end
