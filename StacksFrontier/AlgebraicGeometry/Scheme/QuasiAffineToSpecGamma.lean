module

public import Mathlib.AlgebraicGeometry.QuasiAffine
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-affine schemes and the canonical morphism to the affine hull

A scheme `X` is quasi-affine if and only if the canonical morphism `X ⟶ Spec Γ(X, ⊤)` is a
quasi-compact open immersion.

## Main results

* `AlgebraicGeometry.Scheme.isQuasiAffine_iff_quasiCompact_and_isOpenImmersion_toSpecΓ`:
  **Stacks 01P9**.

## References

* [Stacks Project, Tag 01P9](https://stacks.math.columbia.edu/tag/01P9)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- **Stacks 01P9.** A scheme `X` is quasi-affine if and only if the canonical morphism
`X ⟶ Spec Γ(X, ⊤)` is a quasi-compact open immersion. -/
@[stacks 01P9]
theorem isQuasiAffine_iff_quasiCompact_and_isOpenImmersion_toSpecΓ (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ QuasiCompact X.toSpecΓ ∧ IsOpenImmersion X.toSpecΓ := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace X.toSpecΓ
  constructor

end AlgebraicGeometry.Scheme
