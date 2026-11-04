module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PrincipalDivisorAbelian

/-!
# Vanishing of `R^q h_*` for `q ≥ 2` along the complement of a smooth principal divisor, over
any field

Let `k` be a field and `φ : Y ⟶ 𝐀¹_k` a smooth morphism, and let `h : Y₀ ⟶ Y` be the base change
of `j : 𝐆_m ⟶ 𝐀¹_k` along `φ`. For an abelian sheaf `G` on `𝐆_m` killed by an integer `n`
invertible in `k`, smooth base change (Stacks 0EYU) identifies `R^q h_*(φ₀⁻¹ G)` with
`φ⁻¹ R^q j_* G`. Hence `R^q h_*(φ₀⁻¹ G) = 0` for `q ≥ 2` as soon as `R^q j_* G = 0` for `q ≥ 2`
on `𝐀¹_k`.

That vanishing on `𝐀¹_k`, over an arbitrary field, is stated here as the proposition
`Stacks.EtaleCohomology.Purity.AffineLineTorsionVanishing k`, the input to the computation of the
cohomology of `𝐆_m ⊆ 𝐀¹_k` over any field; this file proves the transport
(`Stacks.EtaleCohomology.Purity.isZero_rightDerived_of_isPullback_affineLine`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.AffineLineTorsionVanishing`.

## Main results

* `Stacks.EtaleCohomology.Purity.isZero_rightDerived_of_isPullback_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

/-- **`R^q j_* G = 0` for `q ≥ 2` along `j : 𝐆_m ⟶ 𝐀¹_k`, for `G` killed by an integer
invertible in `k`**, as a proposition about the field `k`. -/
def AffineLineTorsionVanishing (k : Type u) [Field k] : Prop :=
  ∀ (G : Sheaf (smallEtaleTopology (punctured k).toScheme) Ab.{u + 1}) (n : ℕ), 0 < n →
    IsUnit (n : k) → n • 𝟙 G = 0 → ∀ q : ℕ, 2 ≤ q →
      IsZero (((smallEtalePushforwardAb (punctured k).ι).rightDerived q).obj G)

/-- A sheaf whose identity is killed by `n` has stalks killed by `n`. -/
theorem nsmul_eq_zero_stalk_of_nsmul_id {T : Scheme.{u}}
    {G : Sheaf (smallEtaleTopology T) Ab.{u + 1}} {n : ℕ} (hG : n • 𝟙 G = 0)
    (t : GeometricPoint T) (a : (smallEtaleStalkAb t.hom).obj G) : n • a = 0 := by
  have := congrArg (fun f => ((smallEtaleStalkAb t.hom).map f) a) hG
  simpa [Functor.map_nsmul] using this

variable {k : Type u} [Field k]

/-- **Transport of the vanishing of `R^q j_*` along a smooth `φ : Y ⟶ 𝐀¹_k`.** For a cartesian
square `h : Y₀ ⟶ Y`, `φ₀ : Y₀ ⟶ 𝐆_m` over `φ` and `j : 𝐆_m ⟶ 𝐀¹_k`, and `G` on `𝐆_m` killed by
`n` invertible in `k`, `R^q h_*(φ₀⁻¹ G) = 0` for `q ≥ 2` given
`Stacks.EtaleCohomology.Purity.AffineLineTorsionVanishing k`: smooth base change (Stacks 0EYU)
identifies it with `φ⁻¹ R^q j_* G`. -/
theorem isZero_rightDerived_of_isPullback_affineLine (hA : AffineLineTorsionVanishing k)
    {Y Y₀ : Scheme.{u}} (φ : Y ⟶ affineLine k) [Smooth φ] (h : Y₀ ⟶ Y)
    (φ₀ : Y₀ ⟶ (punctured k).toScheme) (sq : IsPullback h φ₀ φ (punctured k).ι)
    (G : Sheaf (smallEtaleTopology (punctured k).toScheme) Ab.{u + 1}) (n : ℕ) (hn : 0 < n)
    (hnk : IsUnit (n : k)) (hG : n • 𝟙 G = 0) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((smallEtalePushforwardAb h).rightDerived q).obj
      ((smallEtalePullbackAb φ₀).obj G)) := by
  have : IsSeparated (punctured k).ι := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated (punctured k).ι := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  have hn' : IsUnit ((n : ℤ) : Γ(affineLine k, ⊤)) := by
    have := isUnit_natCast_globalSections_of_over (ℓ := n) (affineLine k ↘ Spec (.of k)) hnk
    exact_mod_cast this
  have := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth φ h φ₀ (punctured k).ι sq
    G (fun t a => ⟨n, hn, hn', nsmul_eq_zero_stalk_of_nsmul_id hG t a⟩) q
  exact (Functor.map_isZero (smallEtalePullbackAb φ) (hA G n hn hnk hG q hq)).of_iso
    (asIso ((higherBaseChangeMapAb φ (punctured k).ι h φ₀ sq.w q).app G)).symm

end Stacks.EtaleCohomology.Purity

end
