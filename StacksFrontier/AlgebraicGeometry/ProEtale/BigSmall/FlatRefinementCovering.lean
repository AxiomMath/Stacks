module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.WeaklyEtaleAffineRefinement

/-!
# The pro-étale covering produced by a flat refinement

Let `T` be affine, let `a : U ⟶ T` be weakly étale with `U` affine, let `b : W ⟶ T` be flat and
*surjective* with `W` affine, and let `φ : W ⟶ U` be a morphism over `T`. The refinement
`AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_surjective_pullback` produces an affine `U'`
weakly étale over `T` with `h : U' ⟶ U` whose base change `W ×_U U' ⟶ W` is surjective. Then
the structure morphism `U' ⟶ T` is surjective as well, so the one-member family `{U' ⟶ T}` is a
pro-étale covering of `T`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_weaklyEtale_affine_proetaleCovering_pullback`: the refinement
  together with surjectivity of `U' ⟶ T` and membership of `{U' ⟶ T}` in the pro-étale
  precoverage of `T`.

## References

* [Stacks Project, Tag 0F65](https://stacks.math.columbia.edu/tag/0F65)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- Let `T` be affine, let `a : U ⟶ T` be weakly étale with `U` affine, let `b : W ⟶ T` be flat
and surjective with `W` affine, and let `φ : W ⟶ U` be a morphism over `T`. Then there is an affine
`U'` and a morphism `h : U' ⟶ U` such that `U' ⟶ T` is weakly étale and surjective, `{U' ⟶ T}` is
a pro-étale covering of `T`, and `W' = W ×_U U'` is affine, `W' ⟶ W` is surjective and weakly
étale, and `W' ⟶ U'` is surjective. -/
public theorem exists_weaklyEtale_affine_proetaleCovering_pullback {T U W : Scheme.{u}}
    [IsAffine T] [IsAffine U] [IsAffine W] (a : U ⟶ T) (b : W ⟶ T) (φ : W ⟶ U) [WeaklyEtale a]
    [Flat b] [Surjective b] (hφ : φ ≫ a = b) :
    ∃ (U' : Scheme.{u}) (_ : IsAffine U') (h : U' ⟶ U),
      WeaklyEtale (h ≫ a) ∧ Surjective (h ≫ a) ∧
        Presieve.singleton (h ≫ a) ∈ Scheme.proetalePrecoverage T ∧
          IsAffine (pullback φ h) ∧ WeaklyEtale (pullback.fst φ h) ∧
            Surjective (pullback.fst φ h) ∧ Surjective (pullback.snd φ h) := by
  obtain ⟨U', hU', h, hwe, hpaff, hpwe, hpfst, hpsnd⟩ :=
    exists_weaklyEtale_affine_surjective_pullback a b φ hφ
  have hcomm : pullback.fst φ h ≫ b = pullback.snd φ h ≫ (h ≫ a) := by
    rw [← hφ, ← Category.assoc, pullback.condition, Category.assoc]
  have hsurj : Surjective (h ≫ a) := by
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨w, hw⟩ := (‹Surjective b›).surj t
    obtain ⟨z, hz⟩ := hpfst.surj w
    refine ⟨pullback.snd φ h z, ?_⟩
    calc (h ≫ a) (pullback.snd φ h z)
        = (pullback.snd φ h ≫ (h ≫ a)) z := (Scheme.Hom.comp_apply _ _ z).symm
      _ = (pullback.fst φ h ≫ b) z := by rw [hcomm]
      _ = b (pullback.fst φ h z) := Scheme.Hom.comp_apply _ _ z
      _ = t := by rw [hz, hw]
  have : IsAffine U' := hU'
  have : WeaklyEtale (h ≫ a) := hwe
  have : Surjective (h ≫ a) := hsurj
  have : QuasiCompact (h ≫ a) := quasiCompact_of_compactSpace _
  exact ⟨U', hU', h, hwe, hsurj,
    Scheme.Hom.singleton_mem_propQCPrecoverage hwe, hpaff, hpwe, hpfst, hpsnd⟩

end AlgebraicGeometry.ProEtale

end
