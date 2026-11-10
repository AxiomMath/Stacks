module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartFormalFunctionsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentAdicAffineSectionTower
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# A coherent adic system on an algebraic space, read on an affine chart

Let `Y` be an algebraic space with locally Noetherian étale charts, `𝒥 ⊆ 𝒪_Y` a quasi-coherent
sheaf of ideals and `(𝒢_n)` a coherent `𝒥`-adic system.  Over an affine étale chart `V` of `Y`
whose ring of functions is Noetherian, the sections `𝒢_n(V)` form a tower of finite modules with
surjective transitions of kernel `𝒥(V)ⁿ⁺¹ 𝒢_{n+1}(V)`, so the associated sheaves on the affine
scheme of `V` form a coherent `𝒥(V)~`-adic system there
(`AlgebraicGeometry.Space.C1573.chartTildeSystem`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

open _root_.CategoryTheory.C1573
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Y : AlgebraicSpaces B S hS}
  (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)] [IsNoetherianRing Γ(chartScheme V, ⊤)]
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)

omit [IsAffine (chartScheme V)] [IsNoetherianRing Γ(chartScheme V, ⊤)] in
/-- Membership in `I ^ k • ⊤` is the same over the functions on a chart and over the global
functions of its scheme. -/
theorem C1573.mem_chartTopIdeal_pow_smul_top_iff (M : Modules.{u, u} B S hS Y.1 Y.2) (k : ℕ)
    (x : M.val.obj (op V)) :
    x ∈ chartTopIdeal B S hS V J ^ k •
        (⊤ : Submodule Γ(chartScheme V, ⊤) ((chartSectionsTop B S hS V).obj M)) ↔
      x ∈ chartSectionIdeal B S hS Y.1 Y.2 J V ^ k •
        (⊤ : Submodule (chartRing B S hS Y.1 Y.2 V) (M.val.obj (op V))) := by
  have e : Ideal.map (chartRingOfTop B S hS V) (chartTopIdeal B S hS V J) =
      chartSectionIdeal B S hS Y.1 Y.2 J V := Ideal.map_id _
  constructor
  · intro hx
    have h := Stacks.Submodule.mem_map_pow_smul_top_of_mem_pow_smul_top (chartRingOfTop B S hS V)
      (show (chartSectionsTop B S hS V).obj M →+ M.val.obj (op V) from AddMonoidHom.id _)
      (fun _ _ => rfl) (chartTopIdeal B S hS V J) k hx
    rwa [e] at h
  · intro hx
    refine Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top (chartRingOfTop B S hS V)
      Function.surjective_id
      (show (chartSectionsTop B S hS V).obj M ≃+ M.val.obj (op V) from AddEquiv.refl _)
      (fun _ _ => rfl) (chartTopIdeal B S hS V J) k ?_
    rwa [e]

variable (hJ : J.toSheafOfModules.IsQuasicoherentOnSite)
  (G : CoherentAdicSystems B S hS Y.1 Y.2 J)

include hJ in
omit [IsNoetherianRing Γ(chartScheme V, ⊤)] in
/-- The sections of a coherent adic system over an affine chart, with the transitions read over
the global functions of the chart scheme. -/
theorem C1573.surjective_and_ker_chartSectionsTop_transition (n : ℕ) :
    Function.Surjective ((chartSectionsTop B S hS V).map
        (G.obj.map (homOfLE (Nat.le_succ n)).op)).hom ∧
      LinearMap.ker ((chartSectionsTop B S hS V).map (G.obj.map (homOfLE (Nat.le_succ n)).op)).hom =
        chartTopIdeal B S hS V J ^ (n + 1) • ⊤ := by
  obtain ⟨h1, h2⟩ := surjective_and_ker_transition_of_isCoherentAdicSystem hJ G.property
    (V := V) ‹IsAffine (chartScheme V)› n
  refine ⟨h1, ?_⟩
  ext x
  exact (SetLike.ext_iff.mp h2 x).trans
    (mem_chartTopIdeal_pow_smul_top_iff B S hS V J _ (n + 1) x).symm

/-- **The coherent `𝒥(V)~`-adic system on the affine scheme of `V` given by the sections of a
coherent `𝒥`-adic system over `V`.** -/
def C1573.chartTildeSystem :
    Stacks.Coherent.CoherentAdicSystems
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J)) :=
  ⟨G.obj ⋙ chartSectionsTop B S hS V ⋙ Stacks.Coherent.affineTilde (chartScheme V), by
    refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
    · have := moduleFinite_sections_of_isCoherent B S hS Y.1 Y.2 _ (G.property.1 n)
        (V := V) ‹IsAffine (chartScheme V)›
      have : Module.Finite Γ(chartScheme V, ⊤)
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))) :=
        this
      exact Stacks.Coherent.affineTilde_coherent (chartScheme V) _
    · have : SheafOfModules.IsQuasicoherent
          ((G.obj ⋙ chartSectionsTop B S hS V ⋙ Stacks.Coherent.affineTilde (chartScheme V)).obj
            (op n)) := Stacks.Coherent.affineTilde_quasicoherent (chartScheme V)
        ((chartSectionsTop B S hS V).obj (G.obj.obj (op n)))
      apply Stacks.Coherent.affine_idealPowerMultiple_eq_bot
      apply Stacks.Coherent.affineTilde_power_annihilates
      refine le_antisymm (Submodule.smul_le.2 fun r hr x _ => ?_) bot_le
      have h := (idealPowerMultiple_eq_bot_iff B S hS Y.1 Y.2 J (n + 1) _).1 (G.property.2.1 n)
      exact (h V r hr x).symm ▸ Submodule.zero_mem _
    · obtain ⟨h1, h2⟩ := surjective_and_ker_chartSectionsTop_transition B S hS V J hJ G n
      obtain ⟨e, he⟩ := Stacks.Coherent.affineTildeQuotientIso (chartScheme V) _ (n + 1) _ h1 h2
      exact ⟨e, he⟩⟩

end AlgebraicGeometry.Space

end
