module

public import StacksFrontier.RingTheory.Rig.RigEtaleArrowAlgebraization
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothTower
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# Rig-étaleness is invariant under isomorphisms of Noetherian adic rings

An isomorphism of topological rings between Noetherian adic rings — a ring equivalence which is
continuous in both directions — is rig-étale in the sense of **Stacks 0GCV**. Together with the
stability of rig-étaleness under composition (**Stacks 0GCX**) this makes rig-étaleness of an
arrow of `WAdm^{Noeth}` depend only on the arrow up to isomorphism of its source and target, which
is what lets a property of the chart map of a morphism of formal algebraic spaces be read off any
one presentation of that chart map.

## Main results

* `RingHom.isRigEtale_ringEquiv`: an isomorphism of Noetherian adic topological rings is
  rig-étale.
* `RingHom.isRigEtale_of_comp_ringEquiv`: if `g ∘ α = β ∘ g₀` with `α`, `β` isomorphisms of
  Noetherian adic topological rings and `g₀` rig-étale, then `g` is rig-étale.

## Implementation notes

The isomorphism `e : A ≃ C` is adic of topologically finite type by condition (3) of Stacks 0GBW:
the image of an ideal of definition defines the topology of `C`, and the reduction is
surjective. Its target is then, as an `A`-algebra through `e`, its own `I`-adic completion, and
`C` is étale over `A`; the bridge `RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv` of part (1)
of Stacks 0ALQ concludes.

## References

* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
* [Stacks Project, Tag 0GCX](https://stacks.math.columbia.edu/tag/0GCX)
* [Stacks Project, Tag 0GCY](https://stacks.math.columbia.edu/tag/0GCY)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
-/

@[expose] public section

universe u

namespace RingHom

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing C]

/-- An isomorphism of Noetherian adic topological rings, continuous in both directions, is
adic of topologically finite type: condition (6) of Stacks 0GBW. -/
theorem finiteTypeAdicAlgebraForEveryIdeal_ringEquiv (hA : TopologicalRing.IsAdic A)
    (hC : TopologicalRing.IsAdic C) (e : A ≃+* C) (he : Continuous e)
    (he' : Continuous e.symm) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal (e : A →+* C) := by
  obtain ⟨I, hI, hIadic⟩ := hA.1
  have h3 : Rig.FiniteTypeModuloSomeIdealOfDefinition (e : A →+* C) :=
    ⟨⟨I, hI, TopologicalRing.isAdic_map_of_ringEquiv e he he' hIadic⟩,
      ⟨I, hI, RingHom.FiniteType.of_surjective _
        (Ideal.quotientMap_surjective (fun c ↦ ⟨e.symm c, by simp⟩))⟩⟩
  exact ((Rig.adicFiniteType_tfae (e : A →+* C) he hA hC
    (Rig.exists_idealOfDefinition_fg hA inferInstance)
    (Rig.exists_idealOfDefinition_fg hC inferInstance)).out 3 6).mp h3

/-- **An isomorphism of Noetherian adic topological rings is rig-étale.** -/
theorem isRigEtale_ringEquiv (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm) :
    IsRigEtale (e : A →+* C) := by
  have hft := finiteTypeAdicAlgebraForEveryIdeal_ringEquiv hA hC e he he'
  obtain ⟨I, hI, -⟩ := hA.1
  let : Algebra A C := (e : A →+* C).toAlgebra
  let eA : A ≃ₐ[A] C := { e with commutes' := fun _ ↦ rfl }
  have : Algebra.Etale A C := Algebra.Etale.of_equiv eA
  have : Algebra.FiniteType A C := Algebra.FiniteType.equiv inferInstance eA
  have : IsAdicComplete (I.map (algebraMap A C)) C := (hft I hI).2.1
  refine isRigEtale_of_isEtaleOutside_of_ringEquiv (e : A →+* C) hft I hI (C₀ := C)
    (AdicCompletion.ofAlgEquiv (I.map (algebraMap A C))).toRingEquiv (fun a ↦ rfl) ?_
  intro p _
  rw [(Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := C)).mpr inferInstance]
  trivial

/-- **Rig-étaleness depends on an arrow only up to isomorphism of source and target.** If
`g ∘ α = β ∘ g₀` for isomorphisms `α`, `β` of Noetherian adic topological rings, continuous in
both directions, and `g₀` is a continuous rig-étale homomorphism, then so is `g`. -/
theorem isRigEtale_of_comp_ringEquiv {A₀ C₀ : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [IsNoetherianRing A₀]
    [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀]
    [IsNoetherianRing C₀]
    (hA₀ : TopologicalRing.IsAdic A₀) (hC₀ : TopologicalRing.IsAdic C₀)
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (g₀ : A₀ →+* C₀) (g : A →+* C) (hg₀ : Continuous g₀) (hg : Continuous g)
    (α : A₀ ≃+* A) (hα : Continuous α) (hα' : Continuous α.symm)
    (β : C₀ ≃+* C) (hβ : Continuous β) (hβ' : Continuous β.symm)
    (hsq : g.comp (α : A₀ →+* A) = (β : C₀ →+* C).comp g₀) (h₀ : IsRigEtale g₀) :
    IsRigEtale g := by
  have hcomp : IsRigEtale ((β : C₀ →+* C).comp g₀) :=
    Rig.rigEtale_comp hC hC₀ hA₀ (β : C₀ →+* C) g₀ hβ hg₀
      (isRigEtale_ringEquiv hC₀ hC β hβ hβ') h₀
  rw [← hsq] at hcomp
  exact Rig.rigEtale_cancel hC hA hA₀ g (α : A₀ →+* A) hg hα
    (isRigEtale_ringEquiv hA₀ hA α hα hα') hcomp

omit [IsLinearTopology A A] [IsNoetherianRing A] [IsLinearTopology C C] [IsNoetherianRing C] in
/-- `RingHom.IsRigEtaleArrow`, the form of rig-étaleness consumed by the chart conditions of
formal algebraic spaces, depends on an arrow only up to isomorphism of its source and target. -/
theorem isRigEtaleArrow_of_comp_ringEquiv {A₀ C₀ : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [IsNoetherianRing A₀]
    [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀]
    [IsNoetherianRing C₀]
    (hA₀ : TopologicalRing.IsAdic A₀) (hC₀ : TopologicalRing.IsAdic C₀)
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (g₀ : A₀ →+* C₀) (g : A →+* C)
    (α : A₀ ≃+* A) (hα : Continuous α) (hα' : Continuous α.symm)
    (β : C₀ ≃+* C) (hβ : Continuous β) (hβ' : Continuous β.symm)
    (hsq : g.comp (α : A₀ →+* A) = (β : C₀ →+* C).comp g₀) (h₀ : IsRigEtaleArrow g₀) :
    IsRigEtaleArrow g := by
  intro _ _ _ _
  obtain ⟨hg₀, h₀⟩ := h₀
  have hg : Continuous g := by
    have he : g = ((β : C₀ →+* C).comp g₀).comp (α.symm : A →+* A₀) := by
      rw [← hsq, RingHom.comp_assoc]
      ext x
      simp
    rw [he]
    exact (hβ.comp hg₀).comp hα'
  exact ⟨hg, isRigEtale_of_comp_ringEquiv hA₀ hC₀ hA hC g₀ g hg₀ hg α hα hα' β hβ hβ' hsq h₀⟩

end RingHom

end
