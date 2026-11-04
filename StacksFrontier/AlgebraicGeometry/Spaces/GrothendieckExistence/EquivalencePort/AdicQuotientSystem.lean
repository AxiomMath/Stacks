module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AdicQuotientKernelBound

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Reducing a coherent adic system modulo a power of a second ideal

For a coherent `𝓘`-adic system `(F_n)` and a quasi-coherent sheaf of ideals `𝓚`, the system
`(F_n / 𝓚^e F_n)_n` is again a coherent `𝓘`-adic system
(`AlgebraicGeometry.Space.C1573.isCoherentAdicSystem_quotientSystem`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- The quotient `M ↦ M / 𝓚^e M`, as a functor. -/
def C1573.smallEtaleAdicQuotientFunctor (e : ℕ) :
    Modules.{u, u} B S hS F hF ⥤ Modules.{u, u} B S hS F hF where
  obj M := smallEtaleAdicQuotient B S hS F hF 𝓚 e M
  map φ := smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e φ
  map_id M := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M)).1 ?_
    simp
  map_comp φ ψ := by
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)).1 ?_
    simp

/-- The projection `M ⟶ M / 𝓚^e M` is natural in `M`: composing it with the map induced by
`φ : M ⟶ N` equals `φ` followed by the projection `N ⟶ N / 𝓚^e N`. -/
@[reassoc (attr := simp)]
theorem C1573.smallEtaleAdicQuotientProjection_functor_map (e : ℕ)
    {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) :
    smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M ≫
        (smallEtaleAdicQuotientFunctor B S hS F hF 𝓚 e).map φ =
      φ ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e N :=
  smallEtaleAdicQuotientProjection_mapOfHom B S hS F hF 𝓚 e φ

/-- The transition maps `M / 𝓚^(e+1) ⟶ M / 𝓚^e` are natural. -/
theorem C1573.smallEtaleAdicQuotientTransition_naturality (e : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) :
    (smallEtaleAdicQuotientFunctor B S hS F hF 𝓚 (e + 1)).map φ ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e N =
      smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e M ≫
        (smallEtaleAdicQuotientFunctor B S hS F hF 𝓚 e).map φ := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 (e + 1) M)).1 ?_
  show smallEtaleAdicQuotientProjection B S hS F hF 𝓚 (e + 1) M ≫
      smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 (e + 1) φ ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e N =
    smallEtaleAdicQuotientProjection B S hS F hF 𝓚 (e + 1) M ≫
      smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e M ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e φ
  simp only [← Category.assoc, smallEtaleAdicQuotientProjection_mapOfHom,
    smallEtaleAdicQuotientProjection_comp_transition]
  simp only [Category.assoc, smallEtaleAdicQuotientProjection_comp_transition]

/-- The system `(F_n / 𝓚^e F_n)_n`. -/
abbrev C1573.quotientSystem (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (e : ℕ) :
    ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF :=
  E ⋙ smallEtaleAdicQuotientFunctor B S hS F hF 𝓚 e

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]

/-- **`(F_n / 𝓚^e F_n)_n` is a coherent `𝓘`-adic system.** -/
theorem C1573.isCoherentAdicSystem_quotientSystem (hK : 𝓚.toSheafOfModules.IsQuasicoherentOnSite)
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (e : ℕ) :
    IsCoherentAdicSystem B S hS F hF 𝓘 (quotientSystem B S hS F hF 𝓚 E e) := by
  refine ⟨fun n => isCoherent_idealPowerQuotient B S hS F hF 𝓚 hK _ (hE.1 n) e, fun n => ?_,
    fun n => ?_⟩
  · rw [idealPowerMultiple_eq_bot_iff]
    exact @isPowAnnihilated_of_epi B S hS F hF 𝓘 (n + 1) _ _
      (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e (E.obj (op n)))
      (show Epi (cokernel.π (idealPowerSubsheaf B S hS F hF 𝓚 e (E.obj (op n))).ι) from
        inferInstance)
      ((idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 _ _).1 (hE.2.1 n))
  · obtain ⟨en, hen⟩ := hE.2.2 n
    refine ⟨adicQuotientCommIso B S hS F hF 𝓘 𝓚 e (n + 1) (E.obj (op (n + 1))) ≪≫
      (smallEtaleAdicQuotientFunctor B S hS F hF 𝓚 e).mapIso en, ?_⟩
    have : Epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e (E.obj (op (n + 1)))) :=
      inferInstanceAs (Epi (cokernel.π _))
    refine (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _)).1 ?_
    show smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _ ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) _ ≫
          adicQuotientCommHom B S hS F hF 𝓘 𝓚 e (n + 1) (E.obj (op (n + 1))) ≫
            smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e en.hom =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e _ ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e (E.map (homOfLE (Nat.le_succ n)).op)
    have h1 := adicQuotientCommHom_spec B S hS F hF 𝓘 𝓚 e (n + 1) (E.obj (op (n + 1)))
    simp only [← Category.assoc] at h1 ⊢
    rw [h1]
    have h2 := smallEtaleAdicQuotientProjection_mapOfHom B S hS F hF 𝓚 e en.hom
    have h3 := congrArg (· ≫ smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e (E.obj (op n))) hen
    have h4 := smallEtaleAdicQuotientProjection_mapOfHom B S hS F hF 𝓚 e
      (E.map (homOfLE (Nat.le_succ n)).op)
    simp only [Category.assoc] at h3 ⊢
    exact ((congrArg (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) _ ≫ ·) h2).trans
      h3).trans h4.symm

end AlgebraicGeometry.Space

end
