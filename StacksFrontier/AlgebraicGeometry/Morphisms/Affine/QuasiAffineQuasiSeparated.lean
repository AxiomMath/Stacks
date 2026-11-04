module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.QuasiAffineImmersion

/-!
# Quasi-affineness over a quasi-separated morphism

Let `g : X ⟶ Y` and `h : Y ⟶ S` be morphisms of schemes. If `X` is quasi-affine over `S`,
that is if `g ≫ h` is quasi-affine, and if `Y` is quasi-separated over `S`, then `g` itself
is quasi-affine.

## Main results

* `AlgebraicGeometry.IsQuasiAffineHom.of_comp`: a morphism to a scheme quasi-separated over a
  base is quasi-affine as soon as its composite to the base is quasi-affine.

## References

* [Stacks Project, Tag 054G](https://stacks.math.columbia.edu/tag/054G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism `g : X ⟶ Y` to a scheme quasi-separated over a base `S` via `h : Y ⟶ S` is
quasi-affine as soon as the structure morphism `g ≫ h` of `X` over `S` is quasi-affine. -/
@[stacks 054G "relative statement"]
theorem IsQuasiAffineHom.of_comp {X Y S : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ S)
    [IsQuasiAffineHom (g ≫ h)] [QuasiSeparated h] : IsQuasiAffineHom g := by
  have hpb := IsPullback.of_hasPullback (g ≫ h) h
  have _ : IsQuasiAffineHom (pullback.snd (g ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @IsQuasiAffineHom) hpb ‹_›
  have _ : QuasiSeparated (pullback.fst (g ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) hpb.flip ‹_›
  obtain ⟨s, hfst, hsnd⟩ : ∃ s : X ⟶ pullback (g ≫ h) h,
      s ≫ pullback.fst (g ≫ h) h = 𝟙 X ∧ s ≫ pullback.snd (g ≫ h) h = g :=
    ⟨pullback.lift (𝟙 X) g (by simp), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have _ : IsImmersion s := by
    have : IsImmersion (s ≫ pullback.fst (g ≫ h) h) := by rw [hfst]; infer_instance
    exact IsImmersion.of_comp s (pullback.fst (g ≫ h) h)
  have _ : QuasiCompact s := by
    have : QuasiCompact (s ≫ pullback.fst (g ≫ h) h) := by rw [hfst]; infer_instance
    exact QuasiCompact.of_comp s (pullback.fst (g ≫ h) h)
  rw [← hsnd]
  exact MorphismProperty.comp_mem (@IsQuasiAffineHom) s (pullback.snd (g ≫ h) h)
    inferInstance inferInstance

end AlgebraicGeometry
