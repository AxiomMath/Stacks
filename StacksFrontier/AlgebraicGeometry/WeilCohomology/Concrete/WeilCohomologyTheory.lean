module

public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FiniteEtaleSpec
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Weil cohomology theories, II: the definition

Section 45.11 of the Stacks Project (Tag 0FHY) defines a *Weil cohomology theory* over `k` with
coefficients in `F` (Definition 0FI2) as data (D0)–(D3) satisfying the axioms (A), (B), (C) of
Section 45.9 and, in addition, the equivalent conditions (1) and (2) of Lemma 0FI0 for every
smooth projective `X` over `k`. This file states that definition, taking condition (2): with
`k' = Γ(X, 𝒪_X)`, the map `H^0(Spec(k')) → H^0(X)` is an isomorphism.

Condition (2) makes sense because `k'` is a finite separable `k`-algebra (Varieties, Lemma 0BUG),
so that `Spec(k')` is smooth and projective over `k`; this is proved here
(`Stacks.WeilCohomology.SmoothProjectiveScheme.etale_globalSections_of_smoothProjective`), and
`Spec(k')` is the object `SmoothProjectiveScheme.spec k k'` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FiniteEtaleSpec`. The morphism
`X ⟶ Spec(k')` is the canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)`, which lies over `k`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.specGlobalSections`: `Spec Γ(X, 𝒪_X)`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.toSpecGlobalSections`: `X ⟶ Spec Γ(X, 𝒪_X)`.
* `Stacks.WeilCohomology.WeilData.GlobalSectionsCondition`: condition (2) of Lemma 0FI0 for every
  smooth projective `X`.
* `Stacks.WeilCohomology.WeilCohomologyTheory`: **Definition 0FI2**.

## References

* [Stacks Project, Section 45.11 (Tag 0FHY)](https://stacks.math.columbia.edu/tag/0FHY)
* [Stacks Project, Tag 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **`Γ(X, 𝒪_X)` is a finite étale `k`-algebra** for `X` smooth projective over `k`
(Varieties, Lemma 0BUG (1), (3), (4)): `X` is proper and, being smooth, geometrically reduced. -/
theorem etale_globalSections_of_smoothProjective :
    Algebra.Etale k (globalSections X) ∧ Module.Finite k (globalSections X) := by
  have : GeometricallyReduced X.obj.hom := geometricallyReduced_of_smooth X.obj.hom
  exact Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_globalSections_of_geometricallyReduced
    k X.obj.hom

/-- `Γ(X, 𝒪_X)` is an étale `k`-algebra for `X` smooth projective over `k`. -/
instance : Algebra.Etale k (globalSections X) :=
  (etale_globalSections_of_smoothProjective X).1

/-- `Γ(X, 𝒪_X)` is a finite `k`-module for `X` smooth projective over `k`. -/
instance : Module.Finite k (globalSections X) :=
  (etale_globalSections_of_smoothProjective X).2

/-- **`Spec(k')` for `k' = Γ(X, 𝒪_X)`**, as a smooth projective scheme over `k`. -/
abbrev specGlobalSections : (SmoothProjectiveScheme k).FullSubcategory :=
  spec k (globalSections X)

/-- The canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)`, a morphism of schemes over `k`. -/
def toSpecGlobalSections : X ⟶ specGlobalSections X :=
  ObjectProperty.homMk (Over.homMk X.obj.left.toSpecΓ (by
    change X.obj.left.toSpecΓ ≫ Spec.map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.obj.hom.appTop) = X.obj.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc X.obj.hom,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]))

/-- The underlying morphism of schemes of `toSpecGlobalSections X` is `X ⟶ Spec Γ(X, 𝒪_X)`. -/
@[simp]
theorem toSpecGlobalSections_left : (toSpecGlobalSections X).hom.left = X.obj.left.toSpecΓ :=
  rfl

end SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F]

namespace WeilData

variable (W : WeilData k F)

/-- **Condition (2) of Lemma 0FI0, for every smooth projective `X` over `k`**: with
`k' = Γ(X, 𝒪_X)`, the map `H^0(Spec(k')) → H^0(X)` is an isomorphism. -/
def GlobalSectionsCondition : Prop :=
  ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    Function.Bijective (W.pullDeg (SmoothProjectiveScheme.toSpecGlobalSections X) 0)

end WeilData

variable (k F) in
/-- **Definition 0FI2.** A *Weil cohomology theory* over `k` with coefficients in `F` is given by
data (D0), (D1), (D2) and (D3) satisfying Poincaré duality, the Künneth formula and compatibility
with cycle classes — axioms (A), (B) and (C) of Section 45.9 — and in addition such that the
equivalent conditions (1) and (2) of Lemma 0FI0 hold for every smooth projective `X` over `k`;
condition (2) is the one recorded. -/
structure WeilCohomologyTheory extends WeilData k F where
  /-- Axiom (A). -/
  poincareDuality : toWeilData.PoincareDuality
  /-- Axiom (B). -/
  kunneth : toWeilData.Kunneth
  /-- Axiom (C). -/
  cycleClassAxiom : toWeilData.CycleClassAxiom poincareDuality.perfectPairing
  /-- Condition (2) of Lemma 0FI0 for every smooth projective `X` over `k`. -/
  globalSections : toWeilData.GlobalSectionsCondition

end Stacks.WeilCohomology

end
