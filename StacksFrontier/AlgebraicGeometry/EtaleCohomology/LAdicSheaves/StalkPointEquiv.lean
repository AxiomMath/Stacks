module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkPointChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkFrobeniusCharpoly

/-!
# The ℓ-adic stalks along a morphism of geometric points

A morphism `θ : s ⟶ t` of geometric points of `X` induces isomorphisms of the finite-level stalks
of an ℓ-adic sheaf `F` at `t` and at `s` ([Stacks, Tag 04FN]), compatible with the transitions, so
an isomorphism `F_t ≅ F_s` of ℓ-adic stalks. It is natural in `F` and, when `θ` carries an
endomorphism `a` of `s` to an endomorphism `b` of `t`, intertwines their actions. Hence for an
endomorphism `ψ` of `F`, `Tr(ψ ∘ a | F_s ⊗ ℚ_ℓ) = Tr(ψ ∘ b | F_t ⊗ ℚ_ℓ)`: the twisted form of
`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkEnd_eq_of_comm`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.stalkPointEquiv`

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkEnd_eq_of_comm`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- Endomorphisms intertwined by a linear equivalence have the same trace. -/
public theorem trace_eq_of_linearEquiv_comm {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (L : V ≃ₗ[K] W) (φ : V →ₗ[K] V) (ψ : W →ₗ[K] W)
    (h : L.toLinearMap ∘ₗ φ = ψ ∘ₗ L.toLinearMap) :
    LinearMap.trace K V φ = LinearMap.trace K W ψ := by
  rw [← LinearMap.trace_conj' φ L]
  congr 1
  refine LinearMap.ext fun w => ?_
  rw [LinearEquiv.conj_apply_apply]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun h (L.symm w)

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable (F : LAdicSheaf B X ℓ) {s t : GeometricPoint X.1} (θ : GeometricPoint.Hom s t)

/-- **The ℓ-adic stalks `F_t ≅ F_s` along a morphism `θ : s ⟶ t` of geometric points.** -/
public def LAdicSheaf.stalkPointEquiv :
    LAdicSheaf.stalk B X ℓ F t ≃ₗ[ℤ_[ℓ]] LAdicSheaf.stalk B X ℓ F s where
  toFun v := ⟨fun n => (finiteLevelStalkPointIso B X ℓ F θ n).hom (v.1 n), fun n => by
    have h := congrArg (fun g => g.hom (v.1 (n + 1)))
      (finiteLevelStalkPointIso_transition B ℓ X F θ n)
    change LAdicSheaf.stalkTransition B X ℓ F s n _ =
      (finiteLevelStalkPointIso B X ℓ F θ n).hom
        (LAdicSheaf.stalkTransition B X ℓ F t n (v.1 (n + 1))) at h
    exact h.trans (congrArg (finiteLevelStalkPointIso B X ℓ F θ n).hom (v.2 n))⟩
  invFun v := ⟨fun n => (finiteLevelStalkPointIso B X ℓ F θ n).inv (v.1 n), fun n => by
    apply (finiteLevelStalkPointIso B X ℓ F θ n).toLinearEquiv.injective
    change (finiteLevelStalkPointIso B X ℓ F θ n).hom (LAdicSheaf.stalkTransition B X ℓ F t n
        ((finiteLevelStalkPointIso B X ℓ F θ (n + 1)).inv (v.1 (n + 1)))) =
      (finiteLevelStalkPointIso B X ℓ F θ n).hom
        ((finiteLevelStalkPointIso B X ℓ F θ n).inv (v.1 n))
    have h := congrArg
      (fun g => g.hom ((finiteLevelStalkPointIso B X ℓ F θ (n + 1)).inv (v.1 (n + 1))))
      (finiteLevelStalkPointIso_transition B ℓ X F θ n)
    change LAdicSheaf.stalkTransition B X ℓ F s n ((finiteLevelStalkPointIso B X ℓ F θ (n + 1)).hom
        ((finiteLevelStalkPointIso B X ℓ F θ (n + 1)).inv (v.1 (n + 1)))) =
      (finiteLevelStalkPointIso B X ℓ F θ n).hom (LAdicSheaf.stalkTransition B X ℓ F t n
        ((finiteLevelStalkPointIso B X ℓ F θ (n + 1)).inv (v.1 (n + 1)))) at h
    rw [← h, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
    exact v.2 n⟩
  left_inv v := Subtype.ext (funext fun n => Iso.hom_inv_id_apply _ _)
  right_inv v := Subtype.ext (funext fun n => Iso.inv_hom_id_apply _ _)
  map_add' v w := Subtype.ext (funext fun n => map_add _ _ _)
  map_smul' c v := Subtype.ext (funext fun n =>
    map_smul (finiteLevelStalkPointIso B X ℓ F θ n).hom.hom (PadicInt.toZModPow (n + 1) c) (v.1 n))

/-- **The stalk isomorphism along `θ` intertwines endomorphisms related by `θ`.** -/
public theorem LAdicSheaf.stalkPointEquiv_stalkEnd (a : GeometricPoint.Hom s s)
    (b : GeometricPoint.Hom t t) (h : θ.comp b = a.comp θ) (v : LAdicSheaf.stalk B X ℓ F t) :
    LAdicSheaf.stalkPointEquiv B X ℓ F θ (LAdicSheaf.stalkEnd B X ℓ F b v) =
      LAdicSheaf.stalkEnd B X ℓ F a (LAdicSheaf.stalkPointEquiv B X ℓ F θ v) :=
  Subtype.ext (funext fun n => congrArg (fun g => g.hom (v.1 n))
    (finiteLevelStalkEnd_comp_finiteLevelStalkPointIso B X ℓ F θ a b h n))

variable {F} in
/-- **The stalk isomorphism along `θ` is natural in the sheaf.** -/
public theorem LAdicSheaf.stalkPointEquiv_stalkMap {G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (v : LAdicSheaf.stalk B X ℓ F t) :
    LAdicSheaf.stalkPointEquiv B X ℓ G θ (LAdicSheaf.stalkMap φ t v) =
      LAdicSheaf.stalkMap φ s (LAdicSheaf.stalkPointEquiv B X ℓ F θ v) :=
  Subtype.ext (funext fun n => congrArg (fun g => g.hom (v.1 n))
    ((geometricPointStalkMap B X.1 X.property θ
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).naturality (φ.app n).hom))

/-- **Twisted traces are invariant under a change of geometric point**: if `θ : s ⟶ t` carries
`a : s ⟶ s` to `b : t ⟶ t`, then `Tr(ψ ∘ a | F_s ⊗ ℚ_ℓ) = Tr(ψ ∘ b | F_t ⊗ ℚ_ℓ)` for every
endomorphism `ψ` of `F`. -/
public theorem LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkEnd_eq_of_comm (ψ : F ⟶ F)
    (a : GeometricPoint.Hom s s) (b : GeometricPoint.Hom t t) (h : θ.comp b = a.comp θ) (k : ℕ) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkMap ψ s ∘ₗ
        LAdicSheaf.rationalStalkEnd B X ℓ F a ^ k) =
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkMap ψ t ∘ₗ
        LAdicSheaf.rationalStalkEnd B X ℓ F b ^ k) := by
  let e := LAdicSheaf.stalkPointEquiv B X ℓ F θ
  have hEk := (Function.Semiconj.iterate_right
    (LAdicSheaf.stalkPointEquiv_stalkEnd B X ℓ F θ a b h) k)
  have hcomm : e.toLinearMap ∘ₗ (LAdicSheaf.stalkMap ψ t ∘ₗ LAdicSheaf.stalkEnd B X ℓ F b ^ k) =
      (LAdicSheaf.stalkMap ψ s ∘ₗ LAdicSheaf.stalkEnd B X ℓ F a ^ k) ∘ₗ e.toLinearMap :=
    LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.pow_apply]
      rw [LAdicSheaf.stalkPointEquiv_stalkMap B X ℓ θ ψ, hEk v]
  have hbase (u : GeometricPoint X.1) (c : GeometricPoint.Hom u u) :
      LAdicSheaf.rationalStalkMap ψ u ∘ₗ LAdicSheaf.rationalStalkEnd B X ℓ F c ^ k =
      (LAdicSheaf.stalkMap ψ u ∘ₗ LAdicSheaf.stalkEnd B X ℓ F c ^ k).baseChange ℚ_[ℓ] := by
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_pow]
    rfl
  rw [hbase t b, hbase s a]
  refine (trace_eq_of_linearEquiv_comm (e.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _) _ _ ?_).symm
  rw [LinearEquiv.coe_baseChange, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomm]

end Stacks.EtaleCohomology

end
