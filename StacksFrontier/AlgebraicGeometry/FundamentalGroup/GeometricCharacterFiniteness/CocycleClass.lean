module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoinducedEffacement
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteDimensionalDegreeOne

/-!
# The class of a continuous cocycle in derived-functor cohomology

Let `G` be a compact topological group, `k` a field and `V` a continuous discrete `k`-`G`-module.
The universal extension `0 → V → V × Z¹(G, V) → Z¹(G, V) → 0`
(`Stacks.ContinuousCohomology.cocyclesExtension`) has a connecting map
`Z¹(G, V) = H⁰(G, Z¹(G, V)) → H¹(G, V)` into the derived-functor cohomology
`Stacks.ContinuousCohomology.invariantsDelta`. Its kernel consists of the coboundaries: this is
the half of the identification `H¹(G, V) = Z¹/B¹` needed to bound cocycles by cohomology.

## Main definitions

* `Stacks.ContinuousCohomology.cocycleClass` — the class `[c] ∈ H¹(G, V)` of a continuous
  cocycle.

## Main results

* `Stacks.ContinuousCohomology.exists_eq_sub_of_cocycleClass_eq` — two cocycles with the same
  class differ by a coboundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
  (V : Stacks.Injectives.ContinuousModule.{u, v, max u v w} k G)

/-- The identification of the degree-zero part of `invariantsDelta` with the invariants. -/
abbrev invariantsDeltaZeroIso : (invariantsDelta.{u, v, w} k (G := G)).functor 0 ≅
    continuousModuleRingInvariants.{u, v, max u v w} k G :=
  eqToIso (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor _ 0) ≪≫
    (continuousModuleRingInvariants.{u, v, max u v w} k G).rightDerivedZeroIsoSelf

/-- A cocycle, as an invariant of the trivially acting module of cocycles. -/
def cocycleInvariant (c : cocycles₁.{u, v, max u v w} k G V) :
    (continuousModuleRingInvariants.{u, v, max u v w} k G).obj (cocyclesTrivial.{u, v, w} V) :=
  ⟨c, fun _ ↦ rfl⟩

/-- **The class `[c] ∈ H¹(G, V)` of a continuous cocycle**: the connecting map of the universal
extension `Stacks.ContinuousCohomology.cocyclesExtension` applied to `c`. -/
def cocycleClass (c : cocycles₁.{u, v, max u v w} k G V) :
    ((invariantsDelta.{u, v, w} k (G := G)).functor 1).obj V :=
  (invariantsDelta.{u, v, w} k (G := G)).δ (cocyclesExtension_shortExact.{u, v, w} V) 0
    ((invariantsDeltaZeroIso.{u, v, w} (k := k) (G := G)).inv.app _
      (cocycleInvariant.{u, v, w} V c))

/-- **Cocycles with the same class differ by a coboundary.** If `[c] = [c']` in `H¹(G, V)` then
`c g - c' g = g • x - x` for some `x ∈ V` and all `g`. -/
theorem exists_eq_sub_of_cocycleClass_eq (c c' : cocycles₁.{u, v, max u v w} k G V)
    (h : cocycleClass.{u, v, w} V c = cocycleClass.{u, v, w} V c') :
    ∃ x : V.obj.obj.V, ∀ g : G, c.1 g - c'.1 g = rep k G V g x - x := by
  let F := invariantsDelta.{u, v, w} k (G := G)
  let e0 := invariantsDeltaZeroIso.{u, v, w} (k := k) (G := G)
  let hS := cocyclesExtension_shortExact.{u, v, w} V
  let S := cocyclesExtensionComplex.{u, v, w} V
  have hsub : cocycleInvariant.{u, v, w} V (c - c') =
      cocycleInvariant.{u, v, w} V c - cocycleInvariant.{u, v, w} V c' := rfl
  let z := e0.inv.app _ (cocycleInvariant.{u, v, w} V (c - c'))
  have hz : F.δ hS 0 z = 0 := by
    have key := (e0.inv.app (cocyclesTrivial.{u, v, w} V) ≫ F.δ hS 0).hom.map_sub
      (cocycleInvariant.{u, v, w} V c) (cocycleInvariant.{u, v, w} V c')
    exact key.trans (sub_eq_zero.2 h)
  obtain ⟨w', hw'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (F.exact_δ₁ hS 0) z hz
  let w0 := e0.hom.app S.X₂ w'
  have hnat := ConcreteCategory.congr_hom (e0.hom.naturality S.g) w'
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  have hw0 : (continuousModuleRingInvariants.{u, v, max u v w} k G).map S.g w0 =
      cocycleInvariant.{u, v, w} V (c - c') := by
    rw [← hnat, hw']
    exact ConcreteCategory.congr_hom (e0.inv_hom_id_app _) _
  have h2 : w0.1.2 = c - c' := congrArg Subtype.val hw0
  refine ⟨-w0.1.1, fun g ↦ ?_⟩
  have hinv := congrArg Prod.fst (w0.2 g)
  change rep k G V g w0.1.1 + w0.1.2.1 g = w0.1.1 at hinv
  rw [h2] at hinv
  change c.1 g - c'.1 g = _
  rw [map_neg]
  have : (c - c').1 g = c.1 g - c'.1 g := rfl
  have h3 : (c - c').1 g = w0.1.1 - rep k G V g w0.1.1 := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hinv
  rw [← this, h3]
  abel

end Stacks.ContinuousCohomology

end
