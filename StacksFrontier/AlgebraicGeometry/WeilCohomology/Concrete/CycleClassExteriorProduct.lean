module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExteriorProductGysin
public import StacksCore.Tactic.StacksAttribute

/-!
# Remark 0FHD: compatibility with intersection products is compatibility with exterior products

Let `k` be a field and `F` a field of characteristic zero, and let data (D0)–(D3) of Section 45.9
be given satisfying axiom (C)(a), `γ(f^!β) = f^*γ(β)`. Remark 0FHD of the Stacks Project makes
four observations, for a smooth projective scheme `X` over `k` with diagonal
`Δ : X ⟶ X × X`:

1. `H^*(X) ⊗_F H^*(X) ⟶ H^*(X × X) ⟶ H^*(X)`, the Künneth map followed by `Δ^*`, is the cup
   product (`Stacks.WeilCohomology.WeilData.pull_diag_mul`);
2. the intersection product is `α · β = Δ^!(α × β)`
   (`Stacks.Chow.codimensionIntersectionProduct_eq_codimensionGysin_diag`);
3. `α × β = pr₁^*α · pr₂^*β` in `CH^*(X × Y)`, which the source states without proof
   (`Stacks.Chow.codimensionExteriorProduct_eq_codimensionIntersectionProduct`);
4. hence, given (C)(a), axiom (C)(c) holds if and only if `γ` is compatible with exterior products,
   `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)` in `H^*(X × X)`
   (`Stacks.WeilCohomology.WeilData.cycleClassMul_iff_cycleClass_codimensionExteriorProduct`;
   the compatibility on `X × Y` for two schemes is
   `Stacks.WeilCohomology.WeilData.cycleClass_codimensionExteriorProduct`).

All objects are the actual ones: `CH^*(X) = ∏_d CH_{d-*}(X_d)` (Chow Homology, Section 0FE2),
the Gysin maps of Stacks 0FF3, the intersection product of Stacks 0FC0 and the exterior product
of Stacks 0FBV. The equivalence uses neither (A) nor (B), which the source assumes; it is proved
without them.

## References

* [Stacks Project, Tag 0FGU](https://stacks.math.columbia.edu/tag/0FGU)
* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Chow

open Stacks.WeilCohomology (prodBase)

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-- The Gysin map of a morphism depends on it only up to equality. -/
theorem codimensionGysin_congr {Y : Scheme.{u}} (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]
    {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (h : f = f')
    (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (i : ℤ) (β : codimensionChowGroup k sY i) :
    codimensionGysin sX sY hf i β = codimensionGysin sX sY hf' i β := by
  subst h
  rfl

variable [IsProper sX]

/-- **Remark 0FHD: the intersection product is `α · β = Δ^!(α × β)`**, the Gysin map of the
diagonal `Δ : X ⟶ X ×_k X` (Stacks 0FF3) applied to the exterior product (Stacks 0FBV), for `X`
smooth and proper over `k` and `α ∈ CH^i(X)`, `β ∈ CH^j(X)`. -/
@[stacks 0FHD "the intersection product is α · β = Δ^!(α × β)"]
theorem codimensionIntersectionProduct_eq_codimensionGysin_diag (i j : ℤ)
    (α : codimensionChowGroup k sX i) (β : codimensionChowGroup k sX j) :
    codimensionIntersectionProduct k sX i j α β =
      codimensionGysin sX (prodBase sX sX) (f := pullback.diagonal sX)
        (by rw [prodBase, pullback.diagonal_fst_assoc]) (i + j)
        (codimensionExteriorProduct k sX sX i j α β) := by
  have hΔ : pullback.diagonal sX ≫ prodBase sX sX = sX := by
    rw [prodBase, pullback.diagonal_fst_assoc]
  have hid : ∀ (p : ℤ) (γ : codimensionChowGroup k sX p) (g : (pullback sX sX : Scheme.{u}) ⟶ X)
      [LocallyOfFiniteType g] (hg : g ≫ sX = prodBase sX sX), pullback.diagonal sX ≫ g = 𝟙 X →
      codimensionGysin sX (prodBase sX sX) hΔ p (codimensionGysin (prodBase sX sX) sX hg p γ) =
        γ := by
    intro p γ g _ hg hcomp
    rw [← codimensionGysin_comp sX (prodBase sX sX) hΔ sX hg p γ,
      codimensionGysin_congr sX sX hcomp _ (Category.id_comp sX), codimensionGysin_id]
  rw [codimensionExteriorProduct_eq_codimensionIntersectionProduct,
    codimensionGysin_codimensionIntersectionProduct sX (prodBase sX sX) hΔ,
    hid i α _ rfl (pullback.diagonal_fst sX), hid j β _ _ (pullback.diagonal_snd sX)]

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

add_to_stacks 0FHD "the Künneth map followed by pullback along the diagonal is the cup product"
  Stacks.WeilCohomology.WeilData.pull_diag_mul

add_to_stacks 0FHD "α × β = pr₁^!α · pr₂^!β in CH^*(X × Y), stated without proof in the source"
  Stacks.Chow.codimensionExteriorProduct_eq_codimensionIntersectionProduct

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- Given (C)(a) and (C)(c), the cycle class map is compatible with exterior products:
`γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)` in `H^*(X × Y)` for smooth projective `X`, `Y` over `k`,
`α ∈ CH^i(X)`, `β ∈ CH^j(Y)`. -/
theorem cycleClass_codimensionExteriorProduct (hCa : W.CycleClassPullback)
    (hmul : W.CycleClassMul) (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k Y.obj.hom j) :
    W.cycleClass (SmoothProjectiveScheme.prod X Y) (i + j)
        (codimensionExteriorProduct k X.obj.hom Y.obj.hom i j α β) =
      W.cupTw (SmoothProjectiveScheme.prod X Y) (2 * i) (2 * j) _ (by ring) i j _ rfl
        (W.pullTw (SmoothProjectiveScheme.fst X Y) _ _ (W.cycleClass X i α))
        (W.pullTw (SmoothProjectiveScheme.snd X Y) _ _ (W.cycleClass Y j β)) := by
  rw [codimensionExteriorProduct_eq_codimensionIntersectionProduct]
  refine (hmul (SmoothProjectiveScheme.prod X Y) i j _ _).trans ?_
  rw [← hCa (SmoothProjectiveScheme.fst X Y) i α, ← hCa (SmoothProjectiveScheme.snd X Y) j β]
  rfl

/-- **Remark 0FHD.** Given axiom (C)(a), `γ(f^!β) = f^*γ(β)`, axiom (C)(c),
`γ(α · β) = γ(α) ∪ γ(β)` for every smooth projective `X` over `k`, holds if and only if `γ` is
compatible with exterior products in the sense that `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)` in
`H^*(X × X)` for every smooth projective `X` over `k` and `α ∈ CH^i(X)`, `β ∈ CH^j(X)`. The source
assumes (A) and (B) as well; they are not needed. -/
@[stacks 0FHD "given (C)(a), axiom (C)(c) is equivalent to compatibility of γ with exterior \
products; (A) and (B), assumed in the source, are not used"]
theorem cycleClassMul_iff_cycleClass_codimensionExteriorProduct (hCa : W.CycleClassPullback) :
    W.CycleClassMul ↔
      ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
          (α : codimensionChowGroup k X.obj.hom i)
        (β : codimensionChowGroup k X.obj.hom j),
        W.cycleClass (SmoothProjectiveScheme.prod X X) (i + j)
            (codimensionExteriorProduct k X.obj.hom X.obj.hom i j α β) =
          W.cupTw (SmoothProjectiveScheme.prod X X) (2 * i) (2 * j) _ (by ring) i j _ rfl
            (W.pullTw (SmoothProjectiveScheme.fst X X) _ _ (W.cycleClass X i α))
            (W.pullTw (SmoothProjectiveScheme.snd X X) _ _ (W.cycleClass X j β)) := by
  refine ⟨fun hmul X i j α β ↦ W.cycleClass_codimensionExteriorProduct hCa hmul X X i j α β,
    fun hext X i j α β ↦ ?_⟩
  rw [codimensionIntersectionProduct_eq_codimensionGysin_diag]
  have h := hCa (SmoothProjectiveScheme.diag X) (i + j)
    (codimensionExteriorProduct k X.obj.hom X.obj.hom i j α β)
  refine h.trans ?_
  rw [hext X i j α β, pullTw_cupTw, ← pullTw_comp, ← pullTw_comp,
    SmoothProjectiveScheme.diag_fst, SmoothProjectiveScheme.diag_snd, pullTw_id, pullTw_id]

end WeilData

add_to_stacks 0FGU "the intersection product is α · β = Δ^!(α × β), for the intersection product \
of Stacks 0FC0, the exterior product of Stacks 0FBV and the Gysin map of the diagonal"
  Stacks.Chow.codimensionIntersectionProduct_eq_codimensionGysin_diag

add_to_stacks 0FGU "α × β = pr₁^!α · pr₂^!β in CH^*(X × Y), stated without proof in the source"
  Stacks.Chow.codimensionExteriorProduct_eq_codimensionIntersectionProduct

add_to_stacks 0FGU "given (C)(a), axiom (C)(c) is equivalent to compatibility of γ with exterior \
products, γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β); (A) and (B) are not used"
  Stacks.WeilCohomology.WeilData.cycleClassMul_iff_cycleClass_codimensionExteriorProduct

end Stacks.WeilCohomology

end
