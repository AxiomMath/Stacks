module

public import StacksFrontier.RingTheory.Rig.RigEtaleIsLocal
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# Rig-étale arrows and isomorphisms of topological rings

A continuous ring isomorphism with continuous inverse between Noetherian adic topological rings
is rig-étale (Stacks 0GCV, `Rig.isRigEtale_ringEquiv`), and rig-étaleness of an arrow of
`WAdm^Noeth` is therefore invariant under composing on either side with such isomorphisms
(Stacks 0GCX).

## Main results

* `Rig.isRigEtale_of_ringEquiv`: rig-étaleness transports along homeomorphic ring isomorphisms
  of source and target.
* `Rig.isRigEtaleArrow_of_isRigEtaleArrow_of_ringEquiv`: rig-étaleness of arrows transports
  along homeomorphic ring isomorphisms of source and target.
-/

@[expose] public noncomputable section

open TopologicalRing

namespace Rig

universe u

/-- Recovering an arrow from its conjugate: if `φ' ∘ e₀ = e ∘ φ` then `φ' = e ∘ φ ∘ e₀⁻¹`. -/
private theorem eq_comp_comp_symm_of_comp_eq {A B A' B' : Type*}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (e₀ : A ≃+* A') (e : B ≃+* B') (φ' : A' →+* B')
    (hcomm : φ'.comp (e₀ : A →+* A') = (e : B →+* B').comp φ) :
    φ' = ((e : B →+* B').comp φ).comp (e₀.symm : A' →+* A) := by
  rw [← hcomm, RingHom.comp_assoc]
  ext x
  simp

/-- **Rig-étaleness of arrows transports along homeomorphic ring isomorphisms.** If
`φ' ∘ e₀ = e ∘ φ` for homeomorphic ring isomorphisms `e₀` of the sources and `e` of the
targets, all four rings Noetherian and adic, and `φ` is rig-étale, then so is `φ'`: it is the
composite `e ∘ φ ∘ e₀⁻¹` of rig-étale arrows (Stacks 0GCX). -/
public theorem isRigEtale_of_ringEquiv {A B A' B' : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    [IsNoetherianRing A']
    [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
    [IsNoetherianRing B']
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (φ : A →+* B) (hφc : Continuous φ) (hφ : RingHom.IsRigEtale φ)
    (e₀ : A ≃+* A') (he₀ : Continuous e₀) (he₀' : Continuous e₀.symm)
    (e : B ≃+* B') (he : Continuous e) (he' : Continuous e.symm)
    (φ' : A' →+* B') (hcomm : φ'.comp (e₀ : A →+* A') = (e : B →+* B').comp φ) :
    RingHom.IsRigEtale φ' := by
  have hA' : TopologicalRing.IsAdic A' := isAdic_of_ringEquiv e₀ he₀ he₀' hA
  have hB' : TopologicalRing.IsAdic B' := isAdic_of_ringEquiv e he he' hB
  have hφ' := eq_comp_comp_symm_of_comp_eq φ e₀ e φ' hcomm
  have h₁ : RingHom.IsRigEtale ((e : B →+* B').comp φ) :=
    rigEtale_comp hB' hB hA (e : B →+* B') φ he hφc (isRigEtale_ringEquiv hB hB' e he he') hφ
  rw [hφ']
  exact rigEtale_comp hB' hA hA' _ (e₀.symm : A' →+* A) (he.comp hφc) he₀' h₁
    (isRigEtale_ringEquiv hA' hA e₀.symm he₀' (by simpa using he₀))

/-- `Rig.isRigEtale_of_ringEquiv` for `RingHom.IsRigEtaleArrow`. The Noetherian and
linear-topology instances of the primed rings are those of the arrow `φ'`; those of the
unprimed rings are given. -/
public theorem isRigEtaleArrow_of_isRigEtaleArrow_of_ringEquiv {A B A' B' : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing B]
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B']
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (φ : A →+* B) (hφ : RingHom.IsRigEtaleArrow φ)
    (e₀ : A ≃+* A') (he₀ : Continuous e₀) (he₀' : Continuous e₀.symm)
    (e : B ≃+* B') (he : Continuous e) (he' : Continuous e.symm)
    (φ' : A' →+* B') (hcomm : φ'.comp (e₀ : A →+* A') = (e : B →+* B').comp φ) :
    RingHom.IsRigEtaleArrow φ' := by
  intro _ _ _ _
  obtain ⟨hφc, hφr⟩ := hφ
  have hcont : Continuous φ' := by
    rw [eq_comp_comp_symm_of_comp_eq φ e₀ e φ' hcomm]
    exact (he.comp hφc).comp he₀'
  exact ⟨hcont, isRigEtale_of_ringEquiv hA hB φ hφc hφr e₀ he₀ he₀' e he he' φ' hcomm⟩

end Rig

end
