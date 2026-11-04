module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.AlgebraIso

/-!
# Naturality of the comparison morphism of extension of scalars

Let `g : T ⟶ S` be a morphism of schemes. Extension of scalars of a sheaf of `𝒪_S`-algebras
along `g` comes with a comparison morphism `g^*A ⟶ g⁺A` of underlying `𝒪_T`-modules
(`Stacks.ModuleStalkTensor.comparison`), which is invertible for every `g` and every `A`. This
file records that it is natural in `A`, which is what makes it usable to transport exactness
properties of `g^*` to `g⁺`.

Naturality is proved where it is cheapest, namely one adjunction at a time: the comparison is
the adjoint transpose of a morphism whose components on sections are those of the unit-like map
`Stacks.ModuleStalkTensor.adjointAlgebraMap`, and that map is natural because it is itself the
transpose of the natural transformation
`Stacks.AffineAlgebraEquivalence.algebraPullbackMap`.

## Main results

* `Stacks.ModuleStalkTensor.adjointAlgebraMap_naturality` — the transpose
  `A ⟶ g_*(g⁺A)` is natural in `A`.
* `Stacks.ModuleStalkTensor.comparisonPushforward_naturality` — the same on underlying modules,
  checked on sections.
* `Stacks.ModuleStalkTensor.comparison_naturality` — **the comparison morphism
  `g^*A ⟶ g⁺A` is natural in `A`.**

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.AlgebraPullbackQcoh

universe u

namespace Stacks.ModuleStalkTensor

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The morphism `adjointAlgebraMap g A : A ⟶ g_*(g⁺A)` of sheaves of rings on `S` is natural
in the sheaf of `𝒪_S`-algebras `A`. -/
theorem adjointAlgebraMap_naturality {A A' : AlgebraSheaf S} (h : A ⟶ A') :
    h.right ≫ adjointAlgebraMap g A' =
      adjointAlgebraMap g A ≫ (TopCat.Sheaf.pushforward CommRingCat g.base).map
        ((algebraPullback g).map h).right :=
  (Adjunction.homEquiv_naturality_left _ h.right _).symm.trans
    ((congrArg _ ((algebraPullbackMap g).naturality h)).trans
      (Adjunction.homEquiv_naturality_right _ _ _))

/-- The morphism `comparisonPushforward g A : A ⟶ g_*(g⁺A)` of underlying `𝒪_S`-modules is
natural in the sheaf of `𝒪_S`-algebras `A`. -/
theorem comparisonPushforward_naturality {A A' : AlgebraSheaf S} (h : A ⟶ A') :
    moduleMap h ≫ comparisonPushforward g A' =
      comparisonPushforward g A ≫
        (Scheme.Modules.pushforward g).map (moduleMap ((algebraPullback g).map h)) := by
  have key : ∀ (U : (Opens S)ᵒᵖ) (x : (Under.right A).obj.obj U),
      ((adjointAlgebraMap g A').hom.app U) ((h.right.hom.app U) x) =
        (((TopCat.Sheaf.pushforward CommRingCat g.base).map
          ((algebraPullback g).map h).right).hom.app U) ((adjointAlgebraMap g A).hom.app U x) :=
    fun U x => ConcreteCategory.congr_hom
      (congrArg (fun k => k.hom.app U) (adjointAlgebraMap_naturality g h)) x
  ext U x
  exact key (op U) x

/-- The comparison morphism `comparison g A : g^*A ⟶ g⁺A` of `𝒪_T`-modules is natural in the
sheaf of `𝒪_S`-algebras `A`. -/
theorem comparison_naturality {A A' : AlgebraSheaf S} (h : A ⟶ A') :
    (Scheme.Modules.pullback g).map (moduleMap h) ≫ comparison g A' =
      comparison g A ≫ moduleMap ((algebraPullback g).map h) := by
  rw [comparison, comparison, ← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  exact congrArg _ (comparisonPushforward_naturality g h)

end Stacks.ModuleStalkTensor

end
