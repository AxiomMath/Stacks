module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackShrink

/-!
# Shrinking a composite whose head is a comparison and whose tail is arbitrary

For a functor `F`, a composite `l ≫ F.map (A ≫ Θ) ≫ m` whose head `A`, transported along `l` and
a comparison isomorphism `sh`, is a morphism `aq`, is rewritten as the shrunk head `A'` followed
by the tail `Θ`, conjugated by the comparisons of the two shrinkings. Nothing is assumed of `Θ`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.conj_head_shrink`: the transported composite is the
  comparison for the shrunk data followed by the tail, conjugated by the comparisons of the two
  shrinkings.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ w₁ w₂

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Let `F` be a functor, `A : Y₀ ⟶ Y` a head, `Θ : Y ⟶ GW` an arbitrary tail, and `l`, `m`
comparisons. If the head transported along `l` and the comparison `sh` is `aq`, and `aq` followed
by `thom` is the head `A'` of the shrunk data, with `thom ≫ u ≫ v = 𝟙`, then
`l ≫ F.map (A ≫ Θ) ≫ m` is `A'` followed by `u`, `v`, `sh.inv` and `F.map Θ ≫ m`. -/
theorem conj_head_shrink {D : Type w₁} {E : Type w₂} [Category.{v₁} D] [Category.{v₂} E]
    (F : E ⥤ D) {Y₀ Y GW : E} {P Z Y' Y₁ G' : D} (l : P ⟶ F.obj Y₀) (A : Y₀ ⟶ Y)
    (sh : F.obj Y ≅ Z) (aq : P ⟶ Z) (A' : P ⟶ Y') (thom : Z ⟶ Y') (u : Y' ⟶ Y₁) (v : Y₁ ⟶ Z)
    (m : F.obj GW ⟶ G') (hi : l ≫ F.map A ≫ sh.hom = aq) (hs : A' = aq ≫ thom)
    (ht : thom ≫ u ≫ v = 𝟙 Z) (Θ : Y ⟶ GW) :
    l ≫ F.map (A ≫ Θ) ≫ m = A' ≫ u ≫ v ≫ sh.inv ≫ F.map Θ ≫ m := by
  subst hs hi
  simp [reassoc_of% ht]

end Stacks.AlgebraicGeometry.ModuleLimits

end
