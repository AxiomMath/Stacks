module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOverField
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens

/-!
# `p^!ω_S^•` is normalized on every open separated over the base

The closing remark of [Stacks, Tag 0AUE] in its covering-free form: for `X` separated and of
finite type over a Noetherian `S` with structure morphism `p`, the complex `p^!ω_S^•` together
with the canonical comparisons `(p^!ω_S^•)|_W ≅ (W → S)^!ω_S^•` of
`Stacks.Duality.upperShriekLocalIso` is normalized relative to `ω_S^•` in the sense of
`Stacks.Duality.NormalizedOnOpens`.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.ofShriek` — `p^!ω_S^•` as a complex normalized on every open
  separated over `S`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v' w

namespace Stacks.Duality

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]
  (A : UpperShriek 𝒟) {X S : Scheme.{u}} {p : X ⟶ S}
  (hp : IsFiniteTypeOverNoetherian p) (hps : IsShriekable p) (ωS : 𝒟 S)

/-- **[Stacks, Tag 0AUE], the closing remark on the separated case, covering-free.** For `X`
separated and of finite type over a Noetherian `S` with structure morphism `p`, the complex
`p^!ω_S^•` with the canonical comparisons `(p^!ω_S^•)|_W ≅ (W → S)^!ω_S^•` is normalized relative
to `ω_S^•`. -/
def NormalizedOnOpens.ofShriek : NormalizedOnOpens A hp ωS where
  complex := (A.shriek p hps).obj ωS
  localIso _ hW := upperShriekLocalIso A hp hps ωS hW
  compat h hW _ := restrictLocalIso_upperShriekLocalIso A hp hps ωS h hW

end Stacks.Duality

end
