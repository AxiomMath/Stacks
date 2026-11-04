module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteTypeIsom
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality.OpennessObstruction

/-!
# Openness of versality from effective towers of thickenings

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, with diagonal representable by algebraic spaces, satisfying (RS*) and limit preserving.
If towers `x ⟶ x₁ ⟶ x₂ ⟶ ⋯` of objects over first-order thickenings `U ⟶ Uₙ` of affine schemes
of finite type over an affine open of `S` map compatibly to one object over a first-order
thickening of `U`, then `𝒳` satisfies openness of versality. This is Stacks 0CXU, with its
condition (4) in the form its proof uses.

## Main results

* `Deformation.Artin.isOpenVersality_of_hasWeaklyEffectiveThickeningTowers`: Stacks 0CXU, with
  condition (4) as weak effectivity of towers of first-order thickenings.
* `Deformation.Artin.isOpenVersality_of_hasEffectiveThickeningTowers`: the same with condition (4)
  as effectivity of towers of first-order thickenings.

## Implementation notes

Condition (4) of Stacks 0CXU asks that a system `(ξₙ)` over an inverse system `(Rₙ)` with
surjective transition maps whose kernels are square-zero come from an object over
`Spec (lim Rₙ)`. The proof of Stacks 0CXU applies it to the tower `x ⟶ x₁ ⟶ x₂ ⟶ ⋯` it
constructs, and only uses arrows `xₙ ⟶ ξ` compatible with the arrows out of `x`, with
`U ⟶ Spec (lim Rₙ)` a first-order thickening; that is
`Deformation.Artin.HasWeaklyEffectiveThickeningTowers`, and the stronger
`Deformation.Artin.HasEffectiveThickeningTowers` asks the arrows to be compatible with the
transition maps of the tower, as an effective system of Stacks 0CXT is.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CXU, with condition (4) as weak effectivity of towers.** Let `𝒳` be a category
fibred in groupoids over the big fppf site of a locally Noetherian scheme `S`, with diagonal
representable by algebraic spaces, satisfying (RS*) and limit preserving, in which towers of
first-order thickenings over affine opens of `S` map compatibly to one object over a first-order
thickening. Then `𝒳` satisfies openness of versality. -/
theorem isOpenVersality_of_hasWeaklyEffectiveThickeningTowers [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (h1 : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (h2 : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h3 : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (h4 : HasWeaklyEffectiveThickeningTowers B S hS 𝒳.val.p IsAffineOpen) :
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
    (exists_isAffineOpen_mem S) h4

/-- **Stacks 0CXU, with condition (4) as effectivity of towers.** Let `𝒳` be a category fibred
in groupoids over the big fppf site of a locally Noetherian scheme `S`, with diagonal
representable by algebraic spaces, satisfying (RS*) and limit preserving, in which towers of
first-order thickenings over affine opens of `S` are effective. Then `𝒳` satisfies openness of
versality. -/
theorem isOpenVersality_of_hasEffectiveThickeningTowers [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (h1 : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (h2 : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h3 : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (h4 : HasEffectiveThickeningTowers B S hS 𝒳.val.p IsAffineOpen) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : 𝒳.val.obj) (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx :=
  isOpenVersality_of_hasWeaklyEffectiveThickeningTowers B S hS 𝒳 h1 h2 h3
    (HasEffectiveThickeningTowers.weaklyEffective B S hS 𝒳.val.p h4)

end Deformation.Artin

end
