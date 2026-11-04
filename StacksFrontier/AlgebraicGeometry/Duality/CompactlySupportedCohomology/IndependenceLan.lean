module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Independence
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforwardLan
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompactificationData

/-!
# Independence of `Rf_!` from the compactification

For a cofiltered category of compactifications of `X` over `Y`, each carrying a
`CategoryTheory.CompactificationData`, with an isomorphism of the attached functors `Rf_!` for
each of its morphisms, the functors `Rf_!` of any two compactifications are isomorphic.

## Main definitions

* `CategoryTheory.CompactificationData.shriekImageIso`: the isomorphism between the functors
  `Rf_!` of two compactifications.

## References

* [Stacks Project, Tag 0G50](https://stacks.math.columbia.edu/tag/0G50)
* [Stacks Project, Tag 0G4X](https://stacks.math.columbia.edu/tag/0G4X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃ w₁ w₂

namespace CategoryTheory

namespace CompactificationData

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]

/-- The functor `Rf_!` is, up to isomorphism, independent of the choice of the compactification.

The compactifications of `X` over `Y` are the objects of a cofiltered category `𝒦`, each carrying
the data of a `CategoryTheory.CompactificationData`, and each morphism of `𝒦` induces an
isomorphism of the attached functors `Rf_!`, that of Stacks, Tag 0G4X. The isomorphism between the
functors of `c` and `c'` is the composite of the isomorphisms to the functor of a compactification
dominating both. -/
@[stacks 0G50 "the per-compactification data, the cofilteredness of the category of \
compactifications, and the isomorphisms attached to its morphisms by Tag 0G4X, supplied as data"]
public def shriekImageIso {𝒦 : Type w₁} [Category.{w₂} 𝒦] [IsCofiltered 𝒦] {ℳ : 𝒦 → Type u₃}
    [∀ c, Category.{v} (ℳ c)] (C : ∀ c, CompactificationData 𝒞 𝒟 (ℳ c))
    [∀ c (A : ℳ c ⥤ Type v), (C c).direct.HasLeftKanExtension A]
    (e : ∀ {c c' : 𝒦}, (c ⟶ c') → ((C c').shriekImage ≅ (C c).shriekImage)) (c c' : 𝒦) :
    (C c).shriekImage ≅ (C c').shriekImage :=
  e (IsCofiltered.minToLeft c c') ≪≫ (e (IsCofiltered.minToRight c c')).symm

end CompactificationData

end CategoryTheory

end
