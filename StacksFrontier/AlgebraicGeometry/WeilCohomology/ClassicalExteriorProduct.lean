module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalChowCycleData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassExteriorProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Remark 0FGU: in a classical Weil cohomology theory, (C)(c) is compatibility with exterior products

Let `k` be an algebraically closed field and `F` a field of characteristic zero. Remark 0FGU of
the Stacks Project observes that, for a smooth projective variety `X` with diagonal
`Δ : X ⟶ X × X`, the intersection product is `α · β = Δ^!(α × β)` and
`α × β = pr₁^*α · pr₂^*β`, so that, given axiom (C)(a), `γ(f^!β) = f^*γ(β)`, axiom (C)(c),
`γ(α · β) = γ(α) ∪ γ(β)`, is equivalent to `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`.

This file states and proves that equivalence for the data of a classical Weil cohomology theory
(Stacks 0FGV): a Poincaré duality setup `H^*` on smooth projective varieties and cycle class
maps `γ : CH^r(X) ⟶ H^{2r}(X)` on the Chow groups of Chapter 42, graded by codimension
(`Stacks.WeilCohomology.chowCycleData`), with their actual intersection product (Stacks 0FC0),
Gysin maps (Stacks 0FF3) and exterior product (Stacks 0FBV).

## Main definitions

* `Stacks.WeilCohomology.SmoothProjective.prod`: the product `X ×_k Y` of two smooth projective
  varieties over an algebraically closed field, a smooth projective variety (Stacks 05P3).
* `Stacks.WeilCohomology.SmoothProjective.fst`, `Stacks.WeilCohomology.SmoothProjective.snd`,
  `Stacks.WeilCohomology.SmoothProjective.diag`: its projections and the diagonal.

## Main results

* `Stacks.WeilCohomology.SmoothProjective.isPullback_fst_snd`: `X ×_k Y` is the fibre product.
* `Stacks.WeilCohomology.cycleClass_mul_iff_cycleClass_codimensionExteriorProduct`:
  **Remark 0FGU**, given (C)(a), (C)(c) holds if and only if `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClass_codimensionExteriorProduct`:
  the cycle class map of a classical Weil cohomology theory on the Chow groups of Chapter 42 is
  compatible with exterior products.

## References

* [Stacks Project, Tag 0FGU](https://stacks.math.columbia.edu/tag/0FGU)
* [Stacks Project, Tag 0FGV](https://stacks.math.columbia.edu/tag/0FGV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u v w

namespace Stacks.WeilCohomology

namespace SmoothProjective

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The product `X ×_k Y` of two smooth projective varieties** over an algebraically closed
field `k`: the product of the underlying smooth projective schemes, which is a variety by
Stacks 05P3. Its underlying scheme is the fibre product `X ×_{Spec k} Y` and its structure
morphism is `X ×_k Y ⟶ X ⟶ Spec k`. -/
def prod (X Y : (SmoothProjective k).FullSubcategory) : (SmoothProjective k).FullSubcategory :=
  ⟨(SmoothProjectiveScheme.prod ((toSchemeCat k).obj X) ((toSchemeCat k).obj Y)).obj, by
    have : IsVariety k X.obj.hom := X.2.1.toIsVariety
    have : IsVariety k Y.obj.hom := Y.2.1.toIsVariety
    exact ⟨(isSmoothVariety_iff k _).2 ⟨isVariety_pullback k X.obj.hom Y.obj.hom,
        (SmoothProjectiveScheme.prod ((toSchemeCat k).obj X) ((toSchemeCat k).obj Y)).2.1⟩,
      (isProjective_iff_isProjectiveMorphism_of_isAffine _).1
        (SmoothProjectiveScheme.prod ((toSchemeCat k).obj X) ((toSchemeCat k).obj Y)).2.2⟩⟩

/-- The first projection `pr₁ : X ×_k Y ⟶ X`. -/
def fst (X Y : (SmoothProjective k).FullSubcategory) : prod X Y ⟶ X :=
  ObjectProperty.homMk (Over.homMk (pullback.fst X.obj.hom Y.obj.hom) rfl)

/-- The second projection `pr₂ : X ×_k Y ⟶ Y`. -/
def snd (X Y : (SmoothProjective k).FullSubcategory) : prod X Y ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.snd X.obj.hom Y.obj.hom) pullback.condition.symm)

/-- The diagonal `Δ : X ⟶ X ×_k X`. -/
def diag (X : (SmoothProjective k).FullSubcategory) : X ⟶ prod X X :=
  ObjectProperty.homMk (Over.homMk (pullback.diagonal X.obj.hom) (by
    change pullback.diagonal X.obj.hom ≫ pullback.fst _ _ ≫ X.obj.hom = X.obj.hom
    rw [pullback.diagonal_fst_assoc]))

/-- `X ×_k Y`, with its two projections, is the fibre product of `X` and `Y` over `k`. -/
theorem isPullback_fst_snd (X Y : (SmoothProjective k).FullSubcategory) :
    IsPullback (fst X Y).hom.left (snd X Y).hom.left X.obj.hom Y.obj.hom :=
  IsPullback.of_hasPullback X.obj.hom Y.obj.hom

/-- The diagonal followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
theorem diag_fst (X : (SmoothProjective k).FullSubcategory) : diag X ≫ fst X X = 𝟙 X :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.diagonal_fst X.obj.hom))

/-- The diagonal followed by the second projection is the identity. -/
@[reassoc (attr := simp)]
theorem diag_snd (X : (SmoothProjective k).FullSubcategory) : diag X ≫ snd X X = 𝟙 X :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.diagonal_snd X.obj.hom))

end SmoothProjective

open SmoothProjective

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

/-- **Remark 0FGU.** Let `H^*` with its trace maps be a Poincaré duality setup on the smooth
projective varieties over an algebraically closed field `k`, and let `γ : CH^r(X) ⟶ H^{2r}(X)`
be group homomorphisms on the Chow groups of Chapter 42, graded by codimension, satisfying axiom
(C)(a), `γ(f^!β) = f^*γ(β)` for the Gysin maps of Stacks 0FF3. Then axiom (C)(c),
`γ(α · β) = γ(α) ∪ γ(β)` for the intersection product of Stacks 0FC0, holds if and only if `γ` is
compatible with exterior products: `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)` in `H^*(X ×_k X)` for the
exterior product of Stacks 0FBV, for every smooth projective variety `X` and `α ∈ CH^r(X)`,
`β ∈ CH^s(X)`. -/
@[stacks 0FGU "given (C)(a), axiom (C)(c) is equivalent to compatibility of γ with exterior \
products, γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β) in H^*(X ×_k X), for the data of a classical Weil \
cohomology theory with cycle classes on the Chow groups of Chapter 42"]
theorem cycleClass_mul_iff_cycleClass_codimensionExteriorProduct
    (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
    (cycleClass : ∀ (X : (SmoothProjective k).FullSubcategory) (r : ℤ),
      (chowCycleData k).group X r →+ (S.H X).piece (2 * r))
    (cycleClass_gysin : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (r : ℤ)
      (β : (chowCycleData k).group Y r),
      cycleClass X r ((chowCycleData k).gysin f r β) = S.pullback f (2 * r) (cycleClass Y r β)) :
    (∀ (X : (SmoothProjective k).FullSubcategory) (r s : ℤ) (α : (chowCycleData k).group X r)
        (β : (chowCycleData k).group X s),
        cycleClass X (r + s) (codimensionIntersectionProduct k _ r s α β) =
          (S.H X).evenCup r s (cycleClass X r α) (cycleClass X s β)) ↔
      ∀ (X : (SmoothProjective k).FullSubcategory) (r s : ℤ) (α : (chowCycleData k).group X r)
        (β : (chowCycleData k).group X s),
        cycleClass (prod X X) (r + s) (codimensionExteriorProduct k _ _ r s α β) =
          (S.H (prod X X)).evenCup r s (S.pullback (fst X X) (2 * r) (cycleClass X r α))
            (S.pullback (snd X X) (2 * s) (cycleClass X s β)) := by
  have hid : ∀ (V : (SmoothProjective k).FullSubcategory) (i : ℤ) (a : (S.H V).piece i),
      S.pullback (𝟙 V) i a = a := by
    intro V i a
    rw [S.pullback_id]
    rfl
  have hcomp : ∀ {U V W : (SmoothProjective k).FullSubcategory} (f : U ⟶ V) (g : V ⟶ W) (i : ℤ)
      (a : (S.H W).piece i), S.pullback (f ≫ g) i a = S.pullback f i (S.pullback g i a) := by
    intro U V W f g i a
    rw [S.pullback_comp]
    rfl
  refine ⟨fun hmul X r s α β ↦ ?_, fun hext X r s α β ↦ ?_⟩
  · refine (congrArg (cycleClass (prod X X) (r + s))
      (codimensionExteriorProduct_eq_codimensionIntersectionProduct _ _ r s α β)).trans
      ((hmul (prod X X) r s _ _).trans ?_)
    exact congr_arg₂ (fun a b ↦ (S.H (prod X X)).evenCup r s a b)
      (cycleClass_gysin (fst X X) r α) (cycleClass_gysin (snd X X) s β)
  · refine (congrArg (cycleClass X (r + s))
      (codimensionIntersectionProduct_eq_codimensionGysin_diag _ r s α β)).trans
      ((cycleClass_gysin (diag X) (r + s) (codimensionExteriorProduct k _ _ r s α β)).trans
        ((congrArg (S.pullback (diag X) (2 * (r + s))) (hext X r s α β)).trans ?_))
    rw [S.pullback_evenCup, ← hcomp, ← hcomp, diag_fst, diag_snd, hid, hid]

namespace ClassicalWeilCohomologyTheory

/-- The cycle class map of a classical Weil cohomology theory on the Chow groups of Chapter 42 is
compatible with exterior products: `γ(α × β) = pr₁^*γ(α) ∪ pr₂^*γ(β)` in `H^*(X ×_k X)`. -/
theorem cycleClass_codimensionExteriorProduct
    (T : ChowClassicalWeilCohomologyTheory.{u, v, w} k F)
    (X : (SmoothProjective k).FullSubcategory) (r s : ℤ) (α : (chowCycleData k).group X r)
    (β : (chowCycleData k).group X s) :
    T.cycleClass (prod X X) (r + s) (codimensionExteriorProduct k _ _ r s α β) =
      (T.H (prod X X)).evenCup r s (T.pullback (fst X X) (2 * r) (T.cycleClass X r α))
        (T.pullback (snd X X) (2 * s) (T.cycleClass X s β)) :=
  (cycleClass_mul_iff_cycleClass_codimensionExteriorProduct T.toPoincareDualityPushforwardSetup
    T.cycleClass T.cycleClass_gysin).1 T.cycleClass_mul X r s α β

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
