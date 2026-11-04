module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.FieldTranslates

/-!
# `Pic⁰` of a smooth proper curve with a rational point is a smooth group scheme

This file assembles `Stacks.RigidifiedPicard.exists_grp_iso_functorZero` for a proper smooth
geometrically irreducible curve `X` over a field `k` with a rational point `σ`, discharging every
input of it which this library proves: the Zariski local triviality ([Stacks, Tag 0B9U]), both
halves of [Stacks, Tag 0B91], the degree-`g` class `θ`, the Hilbert scheme and its smoothness
([Stacks, Tag 0B9H]), and condition (2)(c) of [Stacks, Tag 0B9Q] from [Stacks, Tag 0B9Y]. What
remains as hypotheses is the claim in the proof of [Stacks, Tag 0B9X] (`hexists`, `huniq`) and
[Stacks, Tag 0B9Y] in its degree-zero/degree-`g` form (`h0B9Y`).

## Main results

* `Stacks.RigidifiedPicard.exists_smooth_grp_iso_functorZero` — `Pic⁰_{X/k,σ}` is represented by a
  smooth group scheme over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdimX : topologicalKrullDim X ≤ 1)
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

include hdimX in
/-- **`Pic⁰_{X/k,σ}` of a proper smooth curve with a rational point is a smooth group scheme**,
granted the claim of [Stacks, Tag 0B9X] and [Stacks, Tag 0B9Y]. -/
theorem exists_smooth_grp_iso_functorZero (θ : Stacks.Picard.ofScheme X)
    (hθ : invertibleCurveDegreeHom k f hdimX θ = genus f) (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d)
    (hexists : ∀ (T : Over (Spec (.of k))) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f))
          (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over (Spec (.of k)))
      (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z')
    (h0B9Y : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      invertibleCurveDegreeHom K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (topologicalKrullDim_bc_fieldExtensionPoint_le f hdimX K) c = 0 →
      ∃ c₀ : Stacks.Picard.ofScheme X, invertibleCurveDegreeHom k f hdimX c₀ = 0 ∧
        Module.finrank K (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀ +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) θ)).obj 0) = 1 ∧
        IsZero (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀ +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) θ)).obj 1)) :
    ∃ A : Grp (Over (Spec (.of k))), Nonempty (yonedaGrp.obj A ≅ functorZero f hdim σ hσ) ∧
      Smooth A.X.hom := by
  have : IsIntegral X := isIntegral_of_smooth_geometricallyIrreducible f
  have hθ' : ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = genus f := fun s => by
    rw [relativeInvertibleDegreeHomAt_spec f hdimX hdim s θ, hθ]
  obtain ⟨A, ⟨e⟩, hP⟩ := exists_grp_iso_functorZero f hdim σ hσ (isIso_bcProj_c f σ hσ)
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward θ hθ' (hH (genus f)) hexists huniq
    (exists_translate_mem_cohomologySubfunctorZero f hdimX hdim σ hσ θ h0B9Y)
  let : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  exact ⟨A, ⟨e⟩, hP @Smooth (smooth_of_represents f H hH (genus f))⟩

end Stacks.RigidifiedPicard

end
