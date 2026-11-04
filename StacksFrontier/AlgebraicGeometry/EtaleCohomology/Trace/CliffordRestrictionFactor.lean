module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CliffordSemisimple
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteIndexSemisimpleIndexInvertible

/-!
# Semisimplicity of a restriction through a normal subgroup on which the action factors

Let `ρ : Γ → End(V)` be a finite-dimensional semisimple representation over a field `K`, and
`φ : G' → Γ` a group homomorphism. In general `ρ ∘ φ` need not be semisimple. It is when the
following holds:

* there is a normal subgroup `N` of `Γ` on which `ρ` only depends on the image under a
  homomorphism `π : Γ → P`;
* `π ∘ φ = ι ∘ π'` with `π' : G' → P'` surjective and the range of `ι : P' → P` normal;
* the index of `φ⁻¹(N)` in `G'` is finite and invertible in `K`.

## Main results

* `Stacks.EtaleCohomology.exists_isCompl_of_map_normal`: Clifford for a subgroup whose image is
  normalized by the image of a larger one.
* `Stacks.EtaleCohomology.exists_isCompl_comp_of_normal_factor`: under the conditions above,
  `ρ ∘ φ` is semisimple.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Γ : Type*} [Group Γ]

omit [FiniteDimensional K V] in
/-- Stability under the image of a subgroup, as a set of units. -/
theorem isStableUnder_map_toHomUnits_iff (ρ : Γ →* Module.End K V) (T : Subgroup Γ)
    (W : Submodule K V) :
    IsStableUnder (Units.val '' ((T.map ρ.toHomUnits : Subgroup (Module.End K V)ˣ) :
      Set (Module.End K V)ˣ)) W ↔ ∀ t ∈ T, W ≤ W.comap (ρ t) := by
  refine ⟨fun h t ht => h _ ⟨ρ.toHomUnits t, ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
  rintro h _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  exact h t ht

/-- **Clifford, for images**: if `S ≤ T` are subgroups of `Γ`, the image of `S` is normalized by
the image of `T` (for `t ∈ T`, `s ∈ S`, `ρ(t s t⁻¹) = ρ(s')` for some `s' ∈ S`), and every
`T`-stable subspace has a `T`-stable complement, then every `S`-stable subspace has an
`S`-stable complement. -/
theorem exists_isCompl_of_map_normal (ρ : Γ →* Module.End K V) (T S : Subgroup Γ) (hST : S ≤ T)
    (hnorm : ∀ t ∈ T, ∀ s ∈ S, ∃ s' ∈ S, ρ (t * s * t⁻¹) = ρ s')
    (hss : ∀ W : Submodule K V, (∀ t ∈ T, W ≤ W.comap (ρ t)) →
      ∃ W', IsCompl W W' ∧ ∀ t ∈ T, W' ≤ W'.comap (ρ t))
    (W : Submodule K V) (hW : ∀ s ∈ S, W ≤ W.comap (ρ s)) :
    ∃ W', IsCompl W W' ∧ ∀ s ∈ S, W' ≤ W'.comap (ρ s) := by
  have hN := exists_isCompl_of_normal (T.map ρ.toHomUnits) (S.map ρ.toHomUnits)
    (Subgroup.map_mono hST) ?_ ?_ ((isStableUnder_map_toHomUnits_iff ρ S W).2 hW)
  · exact hN.imp fun _ => And.imp_right (isStableUnder_map_toHomUnits_iff ρ S _).1
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
    obtain ⟨s', hs', he⟩ := hnorm t ht s hs
    refine ⟨s', hs', Units.ext ?_⟩
    simp only [MonoidHom.coe_toHomUnits, ← he, map_mul, Units.val_mul]
    rfl
  · intro W₀ hW₀
    exact (hss W₀ ((isStableUnder_map_toHomUnits_iff ρ T W₀).1 hW₀)).imp fun _ =>
      And.imp_right (isStableUnder_map_toHomUnits_iff ρ T _).2

variable {G' P P' : Type*} [Group G'] [Group P] [Group P']

/-- **Semisimplicity of a restriction through a normal subgroup on which the action factors.**
Let `ρ : Γ → End(V)` be semisimple, `φ : G' → Γ`, `π : Γ → P`, `π' : G' → P'` surjective and
`ι : P' → P` with normal range and `π ∘ φ = ι ∘ π'`. If `N ◁ Γ` is such that `ρ` restricted to
`N` only depends on `π`, and `φ⁻¹(N)` has finite index invertible in `K`, then `ρ ∘ φ` is
semisimple. -/
theorem exists_isCompl_comp_of_normal_factor (ρ : Γ →* Module.End K V) (φ : G' →* Γ)
    (π : Γ →* P) (π' : G' →* P') (hπ' : Function.Surjective π') (ι : P' →* P) [ι.range.Normal]
    (hcomm : ∀ g, π (φ g) = ι (π' g)) (N : Subgroup Γ) [N.Normal]
    (hfac : ∀ n₁ ∈ N, ∀ n₂ ∈ N, π n₁ = π n₂ → ρ n₁ = ρ n₂) [(N.comap φ).FiniteIndex]
    (hidx : ((N.comap φ).index : K) ≠ 0)
    (hss : ∀ W : Submodule K V, (∀ g, W ≤ W.comap (ρ g)) →
      ∃ W', IsCompl W W' ∧ ∀ g, W' ≤ W'.comap (ρ g))
    (W : Submodule K V) (hW : ∀ g, W ≤ W.comap (ρ (φ g))) :
    ∃ W', IsCompl W W' ∧ ∀ g, W' ≤ W'.comap (ρ (φ g)) := by
  let N₃ : Subgroup Γ := N ⊓ ι.range.comap π
  have hss₃ := exists_isCompl_of_map_normal ρ ⊤ N₃ le_top
    (fun t _ s hs => ⟨t * s * t⁻¹, (inferInstance : N₃.Normal).conj_mem s hs t, rfl⟩)
    (fun W₀ hW₀ => (hss W₀ fun g => hW₀ g (Subgroup.mem_top g)).imp fun _ =>
      And.imp_right fun h t _ => h t)
  let H₀ : Subgroup G' := N.comap φ
  let S₄ : Subgroup Γ := H₀.map φ
  have hS₄ : S₄ ≤ N₃ := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨hh, ⟨π' h, (hcomm h).symm⟩⟩
  have hss₄ := exists_isCompl_of_map_normal ρ N₃ S₄ hS₄ ?_ hss₃
  · refine exists_isCompl_of_normal_index_ne_zero (ρ.comp φ) H₀ hidx ?_ W hW
    intro W₀ hW₀
    exact (hss₄ W₀ (by rintro _ ⟨h, hh, rfl⟩; exact hW₀ h hh)).imp fun _ =>
      And.imp_right fun h g hg => h (φ g) ⟨g, hg, rfl⟩
  · rintro t ⟨htN, p', hp'⟩ _ ⟨h, hh, rfl⟩
    obtain ⟨g, rfl⟩ := hπ' p'
    have hghg : g * h * g⁻¹ ∈ H₀ := (inferInstance : H₀.Normal).conj_mem h hh g
    refine ⟨φ (g * h * g⁻¹), ⟨_, hghg, rfl⟩, hfac _ ?_ _ hghg ?_⟩
    · exact (inferInstance : N.Normal).conj_mem _ hh t
    · simp only [map_mul, map_inv, ← hp', hcomm]

end Stacks.EtaleCohomology

end
