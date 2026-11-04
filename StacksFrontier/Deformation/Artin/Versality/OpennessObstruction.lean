module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteTypeIsom
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality.WeakTowerEffectivity

/-!
# Openness of versality from an obstruction theory

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, with diagonal representable by algebraic spaces, satisfying (RS*) and limit preserving.

If towers of square-zero thickenings are effective on lift classes, `𝒳` satisfies openness of
versality.

If moreover `𝒳` has an obstruction theory whose obstruction modules are injective on countable
products, and its tangent spaces commute with countable products, then towers of square-zero
thickenings are effective on lift classes, so `𝒳` satisfies openness of versality.

## Main results

* `Deformation.Artin.isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses`: openness of
  versality when towers of square-zero thickenings are effective on lift classes.
* `Deformation.Artin.isOpenVersality_of_obstructionTheory`: openness of versality from an
  obstruction theory compatible with countable products.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Hall, *Coherent versality for algebraic stacks*, Theorem 4.4][Hall-coherent]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of a scheme lies in an affine open. -/
lemma exists_isAffineOpen_mem (s : S) : ∃ G : S.Opens, IsAffineOpen G ∧ IsAffineOpen G ∧ s ∈ G := by
  obtain ⟨G, hG, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  exact ⟨G, hG, hG, hs⟩

/-- **Openness of versality from effective towers on lift classes.** Let `𝒳` be a category fibred
in groupoids over the big fppf site of a locally Noetherian scheme `S`, with diagonal representable
by algebraic spaces, satisfying (RS*) and limit preserving, in which compatible systems of lift
classes over towers of square-zero thickenings come from lift classes over the limit. Then `𝒳`
satisfies openness of versality. -/
theorem isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (h1 : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (h2 : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h3 : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (h4 : IsSquareZeroTowerEffectiveOnClasses B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx :=
  isOpenVersality_of_hasLocalRetractions B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids h2
    (hasLocalRetractions_of_hasRepresentableDiagonal B S hS 𝒳 h1
      (AlgebraicGeometry.Stack.isLocallyOfFiniteType_isom_of_isLimitPreserving B S hS 𝒳 h1 h3)
      (satisfiesRS_of_satisfiesRSStar B S hS _ _ h2))
    (hasThickeningDescent_of_isLimitPreserving B S hS 𝒳 h3) IsAffineOpen
    (exists_isAffineOpen_mem S)
    (hasWeaklyEffectiveThickeningTowers_of_isSquareZeroTowerEffectiveOnClasses _ h4)

/-- Let `S` be a locally Noetherian scheme and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Assume

1. the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces,
2. `𝒳` has (RS*),
3. `𝒳` is limit preserving,
4. there exists an obstruction theory `O`,
5. for an object `x` of `𝒳` over `Spec A` and `A`-modules `Mₙ`, `n ≥ 1`,
   (a) `T_x(∏ Mₙ) = ∏ T_x(Mₙ)`, and
   (b) `𝒪_x(∏ Mₙ) ⟶ ∏ 𝒪_x(Mₙ)` is injective.

Then `𝒳` satisfies openness of versality: if `x` over a scheme `U` locally of finite type over
`S` is versal at a finite type point `u₀`, it is versal at every finite type point of an open
neighbourhood of `u₀`. -/
@[stacks 0CYF]
theorem isOpenVersality_of_obstructionTheory [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (h1 : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (h2 : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h3 : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (O : ObstructionTheory B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h5a : TangentPreservesCountableProducts B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids h2)
    (h5b : O.InjectiveOnCountableProducts) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx :=
  isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses B S hS 𝒳 h1 h2 h3
    (isSquareZeroTowerEffectiveOnClasses_of_obstructionTheory h2 h5a O h5b)

end Deformation.Artin

end
