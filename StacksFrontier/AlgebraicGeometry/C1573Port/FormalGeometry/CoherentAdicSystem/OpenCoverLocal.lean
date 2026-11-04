module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Cokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated

namespace Stacks.Coherent.C1573
end Stacks.Coherent.C1573

/-!
# Being a coherent adic system is local on an open cover

An inverse system `(F_n)` of `𝒪_X`-modules on a locally Noetherian scheme is a coherent adic system
along `ℐ` as soon as its restriction to each member of an open cover is a coherent adic system
along the restricted ideal (`Stacks.Coherent.C1573.isCoherentAdicSystem_of_restrict`). Coherence
and annihilation are local; for the quotient clause, the transition `F_{n+1} ⟶ F_n` kills
`ℐⁿ⁺¹F_{n+1}`, and the induced map from the quotient is an isomorphism because it is one after
restriction to each member of the cover, where it is the quotient isomorphism of the restricted
system read through `Stacks.Algebraization.restrictIdealPowerQuotientIso`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

open _root_.Stacks.Coherent.C1573

/-- **Being a coherent adic system is local on an open cover.** -/
theorem C1573.isCoherentAdicSystem_of_restrict {X : Scheme.{u}} [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (F : ℕᵒᵖ ⥤ X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤)
    (h : ∀ i, IsCoherentAdicSystem (J.comap (U i).ι)
      (F ⋙ Scheme.Modules.restrictFunctor (U i).ι)) :
    IsCoherentAdicSystem J F := by
  have hcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (F.obj (op n)) := fun n =>
    AlgebraicGeometry.Modules.isCoherent_of_restrict (F.obj (op n)) U hU fun i => (h i).1 n
  have hann : ∀ n, idealPowerMultiple J (n + 1) (F.obj (op n)) = ⊥ := fun n =>
    idealPowerMultiple_eq_bot_of_restrict J (n + 1) (F.obj (op n)) U hU fun i => (h i).2.1 n
  refine ⟨hcoh, hann, fun n => ?_⟩
  have : (F.obj (op (n + 1))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  let g := F.map (homOfLE (Nat.le_succ n)).op
  have hz :=
    idealPowerMultiple_ι_comp_eq_zero_of_app_smul J (n + 1) g fun V a ha y => by
      rw [Scheme.Modules.Hom.app_smul]
      exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot (hann n) V ha _
  let q := cokernel.desc _ g hz
  have hcov : ∀ x : X, ∃ i, ∃ y : (U i).toScheme, (U i).ι y = x := fun x => by
    have hx : x ∈ iSup U := hU ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  have hq : IsIso q := by
    refine Stacks.Duality.QcqsGeneration.isIso_of_isIso_restrictFunctor q (fun i => (U i).ι)
      hcov fun i => ?_
    obtain ⟨e, he⟩ := (h i).2.2 n
    have key : (restrictIdealPowerQuotientIso (U i).ι J (n + 1) (F.obj (op (n + 1)))).hom ≫
        (Scheme.Modules.restrictFunctor (U i).ι).map q = e.hom := by
      refine coequalizer.hom_ext ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ (Scheme.Modules.restrictFunctor (U i).ι).map q)
          (cokernel_π_comp_restrictIdealPowerQuotientIso (U i).ι J (n + 1)
            (F.obj (op (n + 1))))).trans
        (((Scheme.Modules.restrictFunctor (U i).ι).map_comp _ _).symm.trans
          ((congrArg (Scheme.Modules.restrictFunctor (U i).ι).map
            (cokernel.π_desc _ _ _)).trans he.symm))
    rw [(Iso.eq_inv_comp _).2 key]
    infer_instance
  exact ⟨asIso q, cokernel.π_desc _ _ _⟩

end Stacks.Coherent

end
