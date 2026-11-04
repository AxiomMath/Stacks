module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealTorsionSystem

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Completion commutes with reduction modulo a power of a second ideal

For a coherent `𝒪_X`-module `M` and a quasi-coherent sheaf of ideals `𝓚`, the completion of
`M / 𝓚^e M` along `𝓘` is the reduction modulo `𝓚^e` of the completion of `M`
(`AlgebraicGeometry.Space.C1573.completionQuotientIso`).
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

/-- Morphisms out of `(M / 𝓚^e) / 𝓘^m` agree if they agree after the projections from `M`. -/
private theorem adicQuotient_quotient_hom_ext {e m : ℕ} {M : Modules.{u, u} B S hS F hF}
    {T : Modules.{u, u} B S hS F hF}
    {f g : smallEtaleAdicQuotient B S hS F hF 𝓘 m (smallEtaleAdicQuotient B S hS F hF 𝓚 e M) ⟶ T}
    (h : smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m _ ≫ f =
      smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M ≫
        smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m _ ≫ g) : f = g :=
  (cancel_epi (smallEtaleAdicQuotientProjection B S hS F hF 𝓚 e M ≫
    smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m _)).1 h

/-- The commutation isomorphism is compatible with the transition maps of the `𝓘`-adic towers. -/
theorem C1573.adicQuotientCommHom_naturality (e n : ℕ) (M : Modules.{u, u} B S hS F hF) :
    adicQuotientCommHom B S hS F hF 𝓘 𝓚 e (n + 1) M ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 n M) =
      smallEtaleAdicQuotientTransition B S hS F hF 𝓘 n (smallEtaleAdicQuotient B S hS F hF 𝓚 e M) ≫
        adicQuotientCommHom B S hS F hF 𝓘 𝓚 e n M := by
  refine adicQuotient_quotient_hom_ext B S hS F hF 𝓘 𝓚 ?_
  simp [reassoc_of% (smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓘 n M),
    reassoc_of% (smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓘 n
      (smallEtaleAdicQuotient B S hS F hF 𝓚 e M))]

/-- The transition map from stage `n + 1` to stage `n` of the `𝓘`-adic system of `M` is the
transition map `smallEtaleAdicQuotientTransition` between the corresponding quotients of `M`. -/
theorem C1573.adicQuotientSystem_map_succ (M : Modules.{u, u} B S hS F hF) (n : ℕ) :
    (adicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE (Nat.le_add_right n 1)).op =
      smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) M :=
  (adicQuotientSystem_map B S hS F hF 𝓘 M _).trans
    (smallEtaleAdicQuotientTransition_eq B S hS F hF 𝓘 M n).symm

/-- **The completion of `M / 𝓚^e M` is the reduction modulo `𝓚^e` of the completion of `M`.** -/
def C1573.completionQuotientIso (e : ℕ) (M : Modules.{u, u} B S hS F hF) :
    adicQuotientSystem B S hS F hF 𝓘 (smallEtaleAdicQuotient B S hS F hF 𝓚 e M) ≅
      quotientSystem B S hS F hF 𝓚 (adicQuotientSystem B S hS F hF 𝓘 M) e where
  hom := NatTrans.ofOpSequence (fun n => adicQuotientCommHom B S hS F hF 𝓘 𝓚 e (n + 1) M)
    fun n => by
      rw [adicQuotientSystem_map_succ]
      change _ = _ ≫ smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e
        ((adicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE (Nat.le_add_right n 1)).op)
      rw [adicQuotientSystem_map_succ]
      exact (adicQuotientCommHom_naturality B S hS F hF 𝓘 𝓚 e (n + 1) M).symm
  inv := NatTrans.ofOpSequence (fun n => adicQuotientCommHom B S hS F hF 𝓚 𝓘 (n + 1) e M)
    fun n => by
      rw [adicQuotientSystem_map_succ]
      change smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e
        ((adicQuotientSystem B S hS F hF 𝓘 M).map (homOfLE (Nat.le_add_right n 1)).op) ≫ _ = _
      rw [adicQuotientSystem_map_succ]
      have h := adicQuotientCommHom_naturality B S hS F hF 𝓘 𝓚 e (n + 1) M
      change _ ≫ (adicQuotientCommIso B S hS F hF 𝓘 𝓚 e (n + 1) M).inv =
        (adicQuotientCommIso B S hS F hF 𝓘 𝓚 e (n + 1 + 1) M).inv ≫ _
      exact (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 h).trans (Category.assoc _ _ _).symm)
  hom_inv_id := by
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨n⟩ := n
    exact (adicQuotientCommIso B S hS F hF 𝓘 𝓚 e (n + 1) M).hom_inv_id
  inv_hom_id := by
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨n⟩ := n
    exact (adicQuotientCommIso B S hS F hF 𝓘 𝓚 e (n + 1) M).inv_hom_id

section Natural

variable (e m : ℕ)

/-- The commutation map is natural in the module. -/
theorem C1573.adicQuotientCommHom_natural {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) :
    adicQuotientCommHom B S hS F hF 𝓘 𝓚 e m M ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e
          (smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 m φ) =
      smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 m
          (smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓚 e φ) ≫
        adicQuotientCommHom B S hS F hF 𝓘 𝓚 e m N := by
  refine adicQuotient_quotient_hom_ext B S hS F hF 𝓘 𝓚 ?_
  simp only [adicQuotientCommHom_spec_assoc,
    smallEtaleAdicQuotientProjection_mapOfHom_assoc, adicQuotientCommHom_spec,
    smallEtaleAdicQuotientProjection_mapOfHom]

/-- The commutation map is compatible with the transition maps in the second ideal. -/
theorem C1573.adicQuotientCommHom_transition (M : Modules.{u, u} B S hS F hF) :
    adicQuotientCommHom B S hS F hF 𝓘 𝓚 (e + 1) m M ≫
        smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e
          (smallEtaleAdicQuotient B S hS F hF 𝓘 m M) =
      smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 m
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓚 e M) ≫
        adicQuotientCommHom B S hS F hF 𝓘 𝓚 e m M := by
  refine adicQuotient_quotient_hom_ext B S hS F hF 𝓘 𝓚 ?_
  have h1 := smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓚 e
    (smallEtaleAdicQuotient B S hS F hF 𝓘 m M)
  have h2 := smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓚 e M
  simp only [adicQuotientCommHom_spec_assoc,
    smallEtaleAdicQuotientProjection_mapOfHom_assoc, reassoc_of% h2, adicQuotientCommHom_spec]
  exact congrArg (smallEtaleAdicQuotientProjection B S hS F hF 𝓘 m M ≫ ·) h1

end Natural

end AlgebraicGeometry.Space

end
