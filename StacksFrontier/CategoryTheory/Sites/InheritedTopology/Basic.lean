module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EffectiveDescent
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.IsomSheaf

/-! # Stacks in groupoids for an inherited topology

A 1-morphism of stacks in groupoids over a site which makes the source fibred in
groupoids over the target makes it a stack in groupoids over the target, for the
inherited topology (Stacks 06NX).

## Main results

* `CategoryTheory.Functor.isStackInGroupoids_of_isFiberedInGroupoids`: a 1-morphism of stacks in
  groupoids making the source fibred in groupoids over the target makes it a stack in groupoids
  over the target, for the inherited topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒞] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]

/-- Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be stacks in groupoids over
`𝒞` and let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over `𝒞`, that is `F ⋙ q = p`.
If `F` makes `𝒳` a category fibred in groupoids over `𝒴`, then `𝒳` is a stack in
groupoids over `𝒴` for the topology `J𝒴` inherited from `(𝒞, J)`. -/
@[stacks 06NX]
theorem isStackInGroupoids_of_isFiberedInGroupoids
    (J : GrothendieckTopology 𝒞) (J𝒴 : GrothendieckTopology 𝒴)
    (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)
    (hp : IsStackInGroupoids.{w} p J) (hq : IsStackInGroupoids.{w} q J)
    (hF₁ : F ⋙ q = p)
    (hF₂ : F.IsFiberedInGroupoids)
    (hJ𝒴 : IsInheritedTopology.{w} q J J𝒴) :
    IsStackInGroupoids.{w} F J𝒴 := by
  refine ⟨hF₂, ?_, ?_⟩
  · intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
    exact isom_isSheaf_of_isFiberedInGroupoids J J𝒴 p q F hp hq hF₁ hJ𝒴
      x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
  · intro U I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    exact effective_descent_of_isFiberedInGroupoids J J𝒴 p q F hp hq hF₁ hF₂ hJ𝒴
      V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D

end CategoryTheory.Functor
