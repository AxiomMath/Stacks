module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerSectionTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineKummerGeneratorProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineChartVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule

/-!
# The Kummer generator on a smooth chart over the affine line

Let `φ : V ⟶ 𝔸¹_k` be smooth over a field `k`, `j : V₀ ⟶ V` the pullback of the punctured line
`𝐆_m ⊆ 𝔸¹_k`, `t = φ^*(coordinate)` and `N` invertible in `k`. The Kummer class `∂ t` of `t`
gives `σ_{∂ t} : ℤ/N ⟶ R¹ j_* μ_N`, and it is invertible on the stalks at the geometric points
of `V` outside `V₀`
(`Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine`):
the germ of `∂ t` generates the stalk of `R¹ j_* μ_N` freely over `ℤ/N` at every geometric point
of the divisor `t = 0`.

This is the case `V = 𝔸¹_k` (`Stacks.EtaleCohomology.Purity.affineLineKummerGenerator`) carried
along `φ`: smooth base change (Stacks 0EYU) makes the degree-one base change map
`φ⁻¹ R¹ j_* μ_N ⟶ R¹ j_* μ_N` an isomorphism, and it carries `σ_{∂ coordinate}` to `σ_{∂ t}`
(`Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_localKummerClass_comp`).
It applies to the charts `φ = π ≫ (𝔸¹_W ⟶ 𝔸¹_k)` of a smooth relative curve over a smooth `W`
(`Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`) and to their base changes along
`W' ⟶ W` with `W'` smooth over another field `k'`, through `𝔸¹_{W'} ⟶ 𝔸¹_{k'}`.

## Main results

* `Stacks.EtaleCohomology.Purity.isUnit_puncturedFunction_coordinate`.
* `Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k]

/-- **The coordinate of `𝔸¹_k` is invertible on the punctured line.** -/
theorem isUnit_puncturedFunction_coordinate :
    IsUnit (puncturedFunction (punctured k).ι ⊤ (coordinate k)) :=
  isUnit_puncturedFunction (punctured k).ι (i := origin k) (range_punctured_ι k).le (by
    intro x hx
    have h2 := hx.2
    rw [range_origin] at h2
    simpa using h2)

variable {k}

/-- The points of `V` over the punctured line are the points of `V₀`, for `V₀` the pullback of the
punctured line along `φ`. -/
theorem mem_range_iff_of_isPullback_punctured {V V₀ : Scheme.{u}} (φ : V ⟶ affineLine k)
    (j : V₀ ⟶ V) (φ₀ : V₀ ⟶ (punctured k).toScheme) (sq : IsPullback j φ₀ φ (punctured k).ι)
    (v : V) : v ∈ Set.range j.base ↔ φ.base v ∈ (punctured k : Set (affineLine k)) := by
  have hj : Set.range j.base = φ.base ⁻¹' Set.range (punctured k).ι.base := by
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      ← Scheme.Pullback.range_fst]
    exact Function.Surjective.range_comp (Scheme.homeoOfIso sq.isoPullback).surjective _
  rw [hj, Scheme.Opens.range_ι]
  rfl

/-- **The Kummer generator on a smooth chart.** Let `φ : V ⟶ 𝔸¹_k` be smooth, `V₀ ⊆ V` the
pullback of the punctured line, and `N` invertible in `k`. Then the morphism
`σ_{∂ t} : ℤ/N ⟶ R¹ j_* μ_N` of the Kummer class of `t = φ^*(coordinate)` is invertible on the
stalks at every geometric point of `V` outside `V₀`: smooth base change (Stacks 0EYU) carries
`R¹ j_* μ_N` on `𝔸¹_k` to `R¹ j_* μ_N` on `V`, and the generator `σ_{∂ coordinate}` of
`𝔸¹_k` (`Stacks.EtaleCohomology.Purity.affineLineKummerGenerator`) to `σ_{∂ t}`
(`Stacks.EtaleCohomology.Purity.pullback_map_torsionSectionSheafHom_localKummerClass_comp`). -/
theorem isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine {V V₀ : Scheme.{u}}
    (φ : V ⟶ affineLine k) [Smooth φ] (j : V₀ ⟶ V) (φ₀ : V₀ ⟶ (punctured k).toScheme)
    (sq : IsPullback j φ₀ φ (punctured k).ι) {N : ℕ} [NeZero N] (hN : IsUnit (N : k))
    (hNY : IsUnit ((N : ℕ) : Γ(V₀, ⊤)))
    (ht : IsUnit (puncturedFunction j ⊤ (φ.appTop (coordinate k)))) :
    IsIsoStalksOver (Set.range j.base)ᶜ
      (torsionSectionSheafHom (localKummerClass j (NeZero.ne N) hNY ⊤ (φ.appTop (coordinate k)) ht)
        (nsmul_localKummerClass j (NeZero.ne N) hNY ⊤ (φ.appTop (coordinate k)) ht)) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have : IsSeparated (punctured k).ι := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated (punctured k).ι := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  have hNT : IsUnit ((N : ℕ) : Γ((punctured k).toScheme, ⊤)) :=
    isUnit_natCast_globalSections_of_over ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k))) hN
  have hNS : IsUnit ((N : ℤ) : Γ(affineLine k, ⊤)) := by
    have := isUnit_natCast_globalSections_of_over (ℓ := N) (affineLine k ↘ Spec (.of k)) hN
    exact_mod_cast this
  have ht0 := isUnit_puncturedFunction_coordinate k
  have h3b := pullback_map_torsionSectionSheafHom_localKummerClass_comp φ (punctured k).ι j φ₀
    sq.w hN0 hNT hNY (coordinate k) ht0 ht
  have hBC := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth φ j φ₀ (punctured k).ι
    sq (kummerSequence.{u, 0} (punctured k).toScheme N).X₁
    (fun t a => ⟨N, Nat.pos_of_ne_zero hN0, hNS,
      nsmul_eq_zero_stalk_of_nsmul_id (nsmul_id_rootsOfUnitySheaf_univ _ N) t a⟩) (0 + 1)
  have : IsIso (rootsOfUnityInverseImageComparison.{u, 0} φ₀ N) :=
    isIso_rootsOfUnityInverseImageComparison φ₀ N hNT
  have : IsIso (kummerSequencePullbackMap φ₀ N).τ₁ := by
    show IsIso (((smallEtalePullbackAbIsoEtaleAbelianInverseImage φ₀).hom.app _) ≫
      rootsOfUnityInverseImageComparison.{u, 0} φ₀ N)
    infer_instance
  have : IsIso (kummerBaseChangeMap φ (punctured k).ι j φ₀ sq.w N) := by
    unfold kummerBaseChangeMap
    infer_instance
  have hσ : IsIsoStalksOver ((punctured k : Set (affineLine k)))ᶜ
      (torsionSectionSheafHom (localKummerClass (punctured k).ι hN0 hNT ⊤ (coordinate k) ht0)
        (nsmul_localKummerClass (punctured k).ι hN0 hNT ⊤ (coordinate k) ht0)) := by
    intro Ω _ _ x hx
    exact isIsoStalksOver_affineLine_of_affineLineKummerGenerator k (affineLineKummerGenerator k)
      N hN0 hNT ht0 x hx
  have he : IsIsoStalksOver (Set.range j.base)ᶜ
      ((smallEtalePullbackAbConstantIso φ).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))) := by
    intro Ω _ _ x _
    infer_instance
  have hβ : IsIsoStalksOver (Set.range j.base)ᶜ
      (kummerBaseChangeMap φ (punctured k).ι j φ₀ sq.w N) := by
    intro Ω _ _ x _
    infer_instance
  have hT : φ.base '' (Set.range j.base)ᶜ ⊆ ((punctured k : Set (affineLine k)))ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    exact fun h => hv ((mem_range_iff_of_isPullback_punctured φ j φ₀ sq v).2 h)
  intro Ω _ _ x hx
  exact IsIsoStalksOver.of_pullback φ hT _ _ h3b hσ he hβ x hx

end Stacks.EtaleCohomology.Purity

end
