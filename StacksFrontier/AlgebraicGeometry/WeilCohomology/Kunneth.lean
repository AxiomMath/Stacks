module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Setup
public import StacksCore.Tactic.StacksAttribute

/-!
# Diagonal pullback of the Künneth exterior product, and the intersection product

For a contravariant multiplicative cohomology theory on smooth projective varieties the
composition `H^*(X) ⊗_F H^*(X) ⟶ H^*(X × X) --Δ^*--> H^*(X)`, whose first arrow is the Künneth
map `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`, is the cup product: pullback is an algebra homomorphism and
`prᵢ ∘ Δ = id`.

The intersection product of cycles is defined by the same diagram: `α · β = Δ^!(α × β)`, the
Gysin pullback of the exterior product along the diagonal. Consequently, granted the naturality
`γ(f^!β) = f^*γ(β)` of `(C)(a)`, the multiplicativity `γ(α · β) = γ(α) ∪ γ(β)` of `(C)(c)` is
equivalent to compatibility of the cycle class map with exterior products, namely
`γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`.

## Main results

* `Stacks.WeilCohomology.diagonalPullback_kunneth`: pulling the exterior product
  `pr₁^*a ∪ pr₂^*b` back along the diagonal gives `a ∪ b`.
* `Stacks.WeilCohomology.cycleClass_mul_iff_cycleClass_externalProduct`: granted `(C)(a)`, the
  identity of `(C)(c)` holds iff the cycle class map is compatible with exterior products.

## References

* [Stacks Project, Tag 0FGU](https://stacks.math.columbia.edu/tag/0FGU)
* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.WeilCohomology

/-- Pulling the Künneth exterior product `pr₁^*a ∪ pr₂^*b` back along the diagonal
`Δ : X ⟶ X × X` gives the cup product `a ∪ b`. -/
@[stacks 0FGU "diagonal_pullback_cup"]
theorem diagonalPullback_kunneth (k : Type u) [Field k] (F : Type v) [Field F]
    (H : (SmoothProjective k).FullSubcategory → ExternallyGradedAlgebra.{v, w} F)
    (pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory},
      (X ⟶ Y) → ∀ i : ℤ, (H Y).piece i →ₗ[F] (H X).piece i)
    (pullback_id : ∀ (X) (i : ℤ), pullback (𝟙 X) i = LinearMap.id)
    (pullback_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ),
      pullback (f ≫ g) i = (pullback f i).comp (pullback g i))
    (pullback_mul : ∀ {X Y} (f : X ⟶ Y) (i j : ℤ) (a : (H Y).piece i) (b : (H Y).piece j),
      pullback f (i + j) ((H Y).mul i j a b) =
        (H X).mul i j (pullback f i a) (pullback f j b))
    (X : (SmoothProjective k).FullSubcategory) [HasBinaryProduct X X]
    (i j : ℤ) (a : (H X).piece i) (b : (H X).piece j) :
    pullback (prod.lift (𝟙 X) (𝟙 X) : X ⟶ X ⨯ X) (i + j)
        ((H (X ⨯ X)).mul i j
          (pullback (prod.fst : X ⨯ X ⟶ X) i a) (pullback (prod.snd : X ⨯ X ⟶ X) j b)) =
      (H X).mul i j a b := by
  rw [pullback_mul]
  simp [← LinearMap.comp_apply, ← pullback_comp, pullback_id]

add_to_stacks 0FHD "the first assertion of the remark, shared verbatim with 0FGU"
  Stacks.WeilCohomology.diagonalPullback_kunneth

/-- Pulling the exterior product `pr₁^*u ∪ pr₂^*v` back along the diagonal `Δ : X ⟶ X ⨯ X` gives
the cup product `u ∪ v`, for a cohomology theory graded by codimension rather than by degree. -/
private theorem diagonalPullback_cup {k : Type u} [Field k]
    {A : (SmoothProjective k).FullSubcategory → ℤ → Type w}
    {cup : ∀ {X : (SmoothProjective k).FullSubcategory} (r s : ℤ), A X r → A X s → A X (r + s)}
    {pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory}, (X ⟶ Y) → ∀ r : ℤ, A Y r → A X r}
    (pullback_id : ∀ (X) (r : ℤ) (u : A X r), pullback (𝟙 X) r u = u)
    (pullback_comp : ∀ {X Y Z : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
      (r : ℤ) (u : A Z r), pullback (f ≫ g) r u = pullback f r (pullback g r u))
    (pullback_cup : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r s : ℤ)
      (u : A Y r) (v : A Y s),
      pullback f (r + s) (cup r s u v) = cup r s (pullback f r u) (pullback f s v))
    (X : (SmoothProjective k).FullSubcategory) [HasBinaryProduct X X] (r s : ℤ)
    (u : A X r) (v : A X s) :
    pullback (prod.lift (𝟙 X) (𝟙 X) : X ⟶ X ⨯ X) (r + s)
        (cup r s (pullback (prod.fst : X ⨯ X ⟶ X) r u)
          (pullback (prod.snd : X ⨯ X ⟶ X) s v)) =
      cup r s u v := by
  rw [pullback_cup, ← pullback_comp, ← pullback_comp, prod.lift_fst, prod.lift_snd,
    pullback_id, pullback_id]

/-- Let the intersection and exterior products of cycles satisfy `α · β = Δ^!(α × β)` and
`α × β = pr₁^!α · pr₂^!β`, and let the cycle class map satisfy axiom `(C)(a)`,
`γ(f^!β) = f^*γ(β)`. Then axiom `(C)(c)`, `γ(α · β) = γ(α) ∪ γ(β)`, holds for every smooth
projective variety if and only if the cycle class map is compatible with exterior products, that
is `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`. -/
@[stacks 0FHD "axiom (C)(c) as compatibility with exterior products"]
theorem cycleClass_mul_iff_cycleClass_externalProduct (k : Type u) [Field k]
    [HasBinaryProducts ((SmoothProjective k).FullSubcategory)]
    (A : (SmoothProjective k).FullSubcategory → ℤ → Type v)
    (cup : ∀ {X : (SmoothProjective k).FullSubcategory} (r s : ℤ), A X r → A X s → A X (r + s))
    (pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory}, (X ⟶ Y) → ∀ r : ℤ, A Y r → A X r)
    (pullback_id : ∀ (X) (r : ℤ) (u : A X r), pullback (𝟙 X) r u = u)
    (pullback_comp : ∀ {X Y Z : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
      (r : ℤ) (u : A Z r), pullback (f ≫ g) r u = pullback f r (pullback g r u))
    (pullback_cup : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r s : ℤ)
      (u : A Y r) (v : A Y s),
      pullback f (r + s) (cup r s u v) = cup r s (pullback f r u) (pullback f s v))
    (CH : (SmoothProjective k).FullSubcategory → ℤ → Type w)
    (chowMul : ∀ {X : (SmoothProjective k).FullSubcategory} (r s : ℤ),
      CH X r → CH X s → CH X (r + s))
    (gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory}, (X ⟶ Y) → ∀ r : ℤ, CH Y r → CH X r)
    (externalProduct : ∀ {X Y : (SmoothProjective k).FullSubcategory} (r s : ℤ),
      CH X r → CH Y s → CH (X ⨯ Y) (r + s))
    (cycleClass : ∀ (X) (r : ℤ), CH X r → A X r)
    -- naturality, `(C)(a)`
    (cycleClass_gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
      (β : CH Y r), cycleClass X r (gysin f r β) = pullback f r (cycleClass Y r β))
    -- `α × β = pr₁^!α · pr₂^!β`
    (externalProduct_eq : ∀ {X Y : (SmoothProjective k).FullSubcategory} (r s : ℤ)
      (α : CH X r) (β : CH Y s), externalProduct r s α β =
        chowMul r s (gysin (prod.fst : X ⨯ Y ⟶ X) r α) (gysin (prod.snd : X ⨯ Y ⟶ Y) s β))
    -- `α · β = Δ^!(α × β)`, the definition of the intersection product
    (chowMul_eq : ∀ {X : (SmoothProjective k).FullSubcategory} (r s : ℤ)
      (α : CH X r) (β : CH X s), chowMul r s α β =
        gysin (prod.lift (𝟙 X) (𝟙 X) : X ⟶ X ⨯ X) (r + s) (externalProduct r s α β)) :
    (∀ (X) (r s : ℤ) (α : CH X r) (β : CH X s),
        cycleClass X (r + s) (chowMul r s α β) =
          cup r s (cycleClass X r α) (cycleClass X s β)) ↔
      ∀ (X Y) (r s : ℤ) (α : CH X r) (β : CH Y s),
        cycleClass (X ⨯ Y) (r + s) (externalProduct r s α β) =
          cup r s (pullback (prod.fst : X ⨯ Y ⟶ X) r (cycleClass X r α))
            (pullback (prod.snd : X ⨯ Y ⟶ Y) s (cycleClass Y s β)) := by
  constructor
  · intro hmul X Y r s α β
    rw [externalProduct_eq, hmul, cycleClass_gysin, cycleClass_gysin]
  · intro hext X r s α β
    rw [chowMul_eq, cycleClass_gysin, hext]
    exact diagonalPullback_cup pullback_id pullback_comp pullback_cup X r s _ _

end Stacks.WeilCohomology

end
