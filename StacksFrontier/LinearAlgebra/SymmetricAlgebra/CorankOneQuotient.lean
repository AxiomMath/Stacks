module

public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# Quotients by a free line and the symmetric algebra

A fact used to show that the vector bundle of a quotient of a module by a free line is an
effective Cartier divisor in the vector bundle of the module: a short exact sequence
`0 ⟶ R e ⟶ F ⟶ N ⟶ 0` with `R e` free on `e` and `N` free splits, `F ≅ N ⊕ R` compatibly with the
projection and with `e ↦ (0, 1)`. In particular there is a linear functional `l` with `l e = 1`,
which is what makes `e` a nonzerodivisor of `Sym_R(F)`
(`Stacks.Chow.GenuineChern.isRegular_ι_of_eq_one`).

The algebra map of symmetric algebras induced by a surjective linear map is surjective; that is
`SymPow.symAlgMap_surjective` of
`StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension`.

## Main results

* `SymmetricAlgebra.exists_splitLine`, `SymmetricAlgebra.exists_apply_eq_one_of_splitLine` — the
  splitting and the functional.
-/

@[expose] public section

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R] {F N : Type*} [AddCommGroup F] [Module R F] [AddCommGroup N]
  [Module R N]

/-- **A short exact sequence `0 ⟶ R e ⟶ F ⟶ N ⟶ 0` with `R e` free on `e` and `N` free splits**
as `F ≅ N ⊕ R` compatibly with the projection and with `e ↦ (0, 1)`. -/
theorem exists_splitLine {ι : Type*} (π : F →ₗ[R] N) (hπ : Function.Surjective π) (e : F)
    (hex : ∀ x, π x = 0 ↔ ∃ r : R, r • e = x) (hfree : ∀ r : R, r • e = 0 → r = 0)
    (b : Module.Basis ι R N) :
    ∃ φ : (N × R) ≃ₗ[R] F, (∀ x, π (φ x) = x.1) ∧ φ (0, 1) = e := by
  have := Module.Projective.of_basis b
  obtain ⟨σ, hσ⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  have hπσ : ∀ n, π (σ n) = n := LinearMap.congr_fun hσ
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : N × R →ₗ[R] F, ∀ x, φ₀ x = σ x.1 + x.2 • e :=
    ⟨σ.coprod (LinearMap.toSpanSingleton R F e), fun _ => rfl⟩
  have hπφ : ∀ x, π (φ₀ x) = x.1 := fun x => by simp [hφ₀, hπσ, (hex e).mpr ⟨1, one_smul R e⟩]
  refine ⟨LinearEquiv.ofBijective φ₀ ⟨fun x y hxy => ?_, fun z => ?_⟩, hπφ, ?_⟩
  · have h₁ : x.1 = y.1 := by rw [← hπφ x, ← hπφ y, hxy]
    rw [hφ₀, hφ₀, h₁] at hxy
    exact Prod.ext h₁ (sub_eq_zero.mp (hfree _ (by rw [sub_smul, add_left_cancel hxy, sub_self])))
  · obtain ⟨r, hr⟩ := (hex (z - σ (π z))).mp (by rw [map_sub, hπσ, sub_self])
    exact ⟨(π z, r), by rw [hφ₀, hr, add_sub_cancel]⟩
  · exact (hφ₀ (0, 1)).trans (by simp)

/-- In the situation of `SymmetricAlgebra.exists_splitLine`, a linear functional takes the value
`1` on the line. -/
theorem exists_apply_eq_one_of_splitLine {ι : Type*} (π : F →ₗ[R] N)
    (hπ : Function.Surjective π) (e : F) (hex : ∀ x, π x = 0 ↔ ∃ r : R, r • e = x)
    (hfree : ∀ r : R, r • e = 0 → r = 0) (b : Module.Basis ι R N) :
    ∃ l : F →ₗ[R] R, l e = 1 := by
  obtain ⟨φ, -, hφe⟩ := exists_splitLine π hπ e hex hfree b
  exact ⟨(LinearMap.snd R N R).comp φ.symm.toLinearMap, by simp [← hφe]⟩

end SymmetricAlgebra

end
