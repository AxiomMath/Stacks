module

public import Mathlib.AlgebraicGeometry.QuasiAffine
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-affine schemes and the canonical morphism to the affine hull

A scheme `X` is quasi-affine if and only if the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is a
quasi-compact open immersion.

## Main results

* `AlgebraicGeometry.Scheme.compactSpace_and_exists_isOpenImmersion_iff_toSpecΓ`:
  **Stacks 01P9**, with quasi-affineness in the sense of Stacks 01P6: `X` is quasi-compact and
  admits an open immersion into an affine scheme `Spec R`.
* `AlgebraicGeometry.Scheme.isQuasiAffine_iff_quasiCompact_and_isOpenImmersion_toSpecΓ`: the same
  equivalence for Mathlib's `Scheme.IsQuasiAffine`, which is defined as quasi-compactness together
  with `X ⟶ Spec Γ(X, ⊤)` being an immersion.

## References

* [Stacks Project, Tag 01P9](https://stacks.math.columbia.edu/tag/01P9)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Mathlib's `Scheme.IsQuasiAffine` (quasi-compact, with `X ⟶ Spec Γ(X, ⊤)` an immersion) holds
if and only if the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is a quasi-compact open immersion. The
form of Stacks 01P9 with Stacks' own notion of quasi-affine is
`compactSpace_and_exists_isOpenImmersion_iff_toSpecΓ`. -/
theorem isQuasiAffine_iff_quasiCompact_and_isOpenImmersion_toSpecΓ (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ QuasiCompact X.toSpecΓ ∧ IsOpenImmersion X.toSpecΓ := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace X.toSpecΓ
  constructor

/-- **Stacks 01P9.** Let `X` be a scheme. Then `X` is quasi-affine in the sense of Stacks 01P6
(quasi-compact and isomorphic to an open subscheme of an affine scheme `Spec R`) if and only if
the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is a quasi-compact open immersion. -/
@[stacks 01P9]
theorem compactSpace_and_exists_isOpenImmersion_iff_toSpecΓ (X : Scheme.{u}) :
    (CompactSpace X ∧ ∃ (R : CommRingCat.{u}) (f : X ⟶ Spec R), IsOpenImmersion f) ↔
      QuasiCompact X.toSpecΓ ∧ IsOpenImmersion X.toSpecΓ := by
  rw [← isQuasiAffine_iff_quasiCompact_and_isOpenImmersion_toSpecΓ]
  refine ⟨fun ⟨_, R, f, _⟩ ↦ IsQuasiAffine.of_isImmersion f, fun _ ↦ ?_⟩
  exact ⟨inferInstance, _, X.toSpecΓ, inferInstance⟩

end AlgebraicGeometry.Scheme
