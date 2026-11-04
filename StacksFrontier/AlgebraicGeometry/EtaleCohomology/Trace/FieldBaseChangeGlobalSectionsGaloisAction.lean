module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportAction

/-!
# The Galois action on `Γ(Y_k̄, G|_{Y_k̄})`

Let `Y` be a scheme over a field `k`, `k̄` an extension field and `G` a sheaf of `Λ`-modules on
`Y_étale`. A `k`-automorphism `σ` of `k̄` acts on `Γ(Y_k̄, G|_{Y_k̄})`: `s_σ = id_Y × Spec σ` is an
automorphism of `Y_k̄` over `Y`, so the restriction `G|_{Y_k̄}` carries the canonical map
`G|_{Y_k̄} ⟶ (s_σ)_*(G|_{Y_k̄})` (the twist `Stacks.EtaleCohomology.selfMapTwist`), and
`Γ(Y_k̄, (s_σ)_* -) = Γ(Y_k̄, -)`. This is the degree-zero case of
`Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`, on sheaves rather than complexes.

## Main definitions

* `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction` — the action of `σ` on
  `Γ(Y_k̄, G|_{Y_k̄})`.

## Main results

* `Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction_naturality` — it is natural
  in `G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The action of `σ ∈ Aut_k(k̄)` on `Γ(Y_k̄, G|_{Y_k̄})`**: global sections of the twist
`G|_{Y_k̄} ⟶ (s_σ)_*(G|_{Y_k̄})`, followed by `Γ(Y_k̄, (s_σ)_* -) = Γ(Y_k̄, -)`. -/
def fieldBaseChangeGlobalSectionsGaloisAction (G : EtaleModules.{u, r} Λ Y.left) :
    (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj G) ⟶
      (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj G) :=
  (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
      ((selfMapTwist.{u, r} Λ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
        (galoisBaseChange_comp_fst Y kbar σ)).app G) ≫
    (etaleModuleGlobalSectionsDirectImageIso (galoisBaseChange Y kbar σ) Λ).hom.app
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj G)

/-- **The action of `σ` on `Γ(Y_k̄, G|_{Y_k̄})` is natural in `G`.** -/
theorem fieldBaseChangeGlobalSectionsGaloisAction_naturality
    {G G' : EtaleModules.{u, r} Λ Y.left} (v : G ⟶ G') :
    fieldBaseChangeGlobalSectionsGaloisAction.{u, r} Λ Y kbar σ G ≫
        (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map v) =
      (etaleModuleGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map v) ≫
        fieldBaseChangeGlobalSectionsGaloisAction.{u, r} Λ Y kbar σ G' := by
  have h₁ := (selfMapTwist.{u, r} Λ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
    (galoisBaseChange_comp_fst Y kbar σ)).naturality v
  have h₂ := (etaleModuleGlobalSectionsDirectImageIso (galoisBaseChange Y kbar σ) Λ).hom.naturality
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map v)
  simp only [Functor.comp_map] at h₁ h₂
  rw [fieldBaseChangeGlobalSectionsGaloisAction, fieldBaseChangeGlobalSectionsGaloisAction,
    Category.assoc, ← h₂, ← Functor.map_comp_assoc, ← h₁, Functor.map_comp_assoc]

end Stacks.EtaleCohomology

end
