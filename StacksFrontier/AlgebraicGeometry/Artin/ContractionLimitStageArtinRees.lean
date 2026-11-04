module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageInputs

/-!
# The Artin–Rees estimate along the descended system

The Artin–Rees input of `AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom` for the
descended system of a stage witness in the proof of Stacks 0GI5.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I}
  [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  (W : StageWitness c κ ξ w k₀) [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}
  (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
    ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
      (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))

/-- **Artin–Rees for `A ⟶ C × A'`** from Artin–Rees for `α : A ⟶ C` and the injectivity of
`α' : A' ⟶ C'` on a power of `I'`, for a commutative square `α' ∘ r = t ∘ α`. -/
theorem exists_artinRees_of_comp {A A' C C' : Type*} [CommRing A] [CommRing A'] [CommRing C]
    [CommRing C'] (α : A →+* C) (α' : A' →+* C') (r : A →+* A') (t : C →+* C')
    (h : ∀ x, α' (r x) = t (α x)) {IA : Ideal A} {I' : Ideal A'}
    (hr : ∀ (n : ℕ), ∀ x ∈ IA ^ n, r x ∈ I' ^ n)
    (P : ℕ → C → Prop) (hK : ∃ K : ℕ, ∀ (n : ℕ) (x : A), P (n + K) (α x) →
      ∃ x' ∈ IA ^ n, α x' = α x)
    (hn : ∃ n₁ : ℕ, ∀ y : A', α' y = 0 → y ∈ I' ^ n₁ → y = 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : A), P (n + c) (α x) → r x ∈ I' ^ (n + c) →
      ∃ y ∈ IA ^ n, α (x - y) = 0 ∧ r (x - y) = 0 := by
  obtain ⟨K, hK⟩ := hK
  obtain ⟨n₁, hn₁⟩ := hn
  refine ⟨n₁ + K, fun n x hxC hxA => ?_⟩
  rw [← Nat.add_assoc] at hxC
  obtain ⟨x', hx'mem, hx'α⟩ := hK (n + n₁) x hxC
  have hα : α (x - x') = 0 := by rw [map_sub, hx'α, sub_self]
  refine ⟨x', Ideal.pow_le_pow_right (Nat.le_add_right n n₁) hx'mem, hα, hn₁ _ ?_ ?_⟩
  · rw [h, hα, map_zero]
  · rw [map_sub]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) hxA)
      (Ideal.pow_le_pow_right (by omega) (hr _ _ hx'mem))

/-- **The Artin–Rees estimate for `A_k^∧ ⟶ A^∧ × C_k^∧`** (the `hAR` input of
`AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom`). -/
theorem exists_stage_artinRees (k : Over k₀) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : AdicCompletion (stageIdeal I₀ k)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)),
      stageAlpha W hZI₀ k x ∈ towerFiltration (stageIdeal I₀ k) (stageQ W k) (n + c) →
        cresL I₀ κ k x ∈ (limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion
              (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))) ^
            (n + c) →
          ∃ y ∈ (stageIdeal I₀ k).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k)
              Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))) ^ n,
            stageAlpha W hZI₀ k (x - y) = 0 ∧ cresL I₀ κ k (x - y) = 0 :=
  exists_artinRees_of_comp
    (A := AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (A' := AdicCompletion (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))
    (C := towerRing (stageIdeal I₀ k) (stageQ W k))
    (C' := towerRing (limitIdeal (κ := κ) I₀) (limitP w))
    (IA := (stageIdeal I₀ k).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))))
    (I' := (limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion
      (limitIdeal (κ := κ) I₀) Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))))
    (stageAlpha W hZI₀ k) (limitAlpha W hZI₀) (cresL I₀ κ k)
    (towerRingMap (limitMap κ k) (stageIdeal_map_limit I₀ k).le (stageQ W k) (limitP w)
      (stageA W k) (stageA_q W k))
    (limitAlpha_completionRingHom_apply W hZI₀ k)
    (fun _ _ hx => completionRingHom_mem_map_pow (f := resL κ k) (stageIdeal_map_resL I₀ k).le hx)
    (fun n c => c ∈ towerFiltration (stageIdeal I₀ k) (stageQ W k) n)
    (exists_alpha_eq_of_mem_towerFiltration (stageQ W k) (isProper_stageQ W k)
      (stage_hZI hZI₀ k) (stage_hqc W k))
    ((limit_torsion W hZI₀).elim fun Nl hNl =>
      exists_eq_zero_of_alpha_eq_zero_of_mem (V := κ.pt.obj) (I := limitIdeal (κ := κ) I₀)
        (X := limitSpace w) (Z := ξ.Z) (limitP w) w.isProper_p (limit_hZI hZI₀)
        (limit_hqc (I₀ := I₀) (w := w)) (N := Nl) hNl.1)

end AlgebraicGeometry.Artin.LimitStages

end
