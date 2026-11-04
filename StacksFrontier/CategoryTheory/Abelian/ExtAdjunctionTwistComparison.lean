module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionTwist
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero

/-!
# The twisted action on `Ext` against the comparison of Stacks 03FD

Let `Φ ⊣ Ψ` be an adjunction of exact endofunctors of an abelian monoidal category `C`, with `Φ`
lax monoidal. The map `θ = Stacks.ExtCup.adjunctionExtMap : Ext^n(𝟙, Ψ N) ⟶ Ext^n(𝟙, N)`,
`b ↦ ε_N ∘ Φ(b)` read out of the unit, is a left inverse, up to the unit `ε : 𝟙 ⟶ Φ 𝟙` of the
lax structure, of the `Ext`-level map
`Stacks.Cohomology.ModuleComparison.extMapComp Ψ η : Ext^n(Φ 𝟙, N) ⟶ Ext^n(𝟙, Ψ N)`,
`c ↦ Ψ(c) ∘ η_𝟙`, which is the comparison of Stacks 03FD for the exact functor `Ψ`
(`ModuleComparison.comparisonIso_hom_eq_extMapComp`):

`θ (Ψ(c) ∘ η_𝟙) = c ∘ ε` (`adjunctionExtMap_extMapCompHom`).

Both sides are morphisms of `δ`-functors out of the universal `δ`-functor `Ext^*(Φ 𝟙, -)`, so it
is enough to check this in degree zero, where it is a triangle identity of the adjunction.

This is the `Ext` half of the comparison, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), of the canonical geometric Frobenius with
the twisted action `Stacks.ExtCup.twistAction`: the derived half reads the canonical Frobenius on
`Hⁱ` as the edge morphism of `(Ψ, Γ)` followed by a map induced by `Γ ∘ Ψ ≅ Γ`, the edge morphism
is the inverse of the comparison of Stacks 03FD
(`Stacks.Cohomology.RightDerivedEdge.edge_eq_comparisonIso_inv`), and this file turns the result
into `θ`.

## Main results

* `Stacks.ExtCup.extDeltaFunctorMapComp_comp_adjunctionExtDeltaHom`: the identity above as an
  equation of morphisms of `δ`-functors.
* `Stacks.ExtCup.adjunctionExtMap_extMapCompHom`: the identity above on classes.
-/

@[expose] public noncomputable section

universe v u

namespace Stacks.ExtCup

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
  ModuleSheafCohomology Stacks.Cohomology.ModuleComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{v} C]
  [EnoughInjectives C] (Φ Ψ : C ⥤ C) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] (adj : Φ ⊣ Ψ) [Ψ.Additive] [PreservesFiniteLimits Ψ]
  [PreservesFiniteColimits Ψ]

/-- **`θ` after the comparison of Stacks 03FD is precomposition with the lax unit**, as an equation
of morphisms of `δ`-functors out of `Ext^*(Φ 𝟙, -)`. The source is universal, so the equation is
checked in degree zero, where it is the triangle identity `Φ η ≫ ε_Φ = 𝟙`. -/
theorem extDeltaFunctorMapComp_comp_adjunctionExtDeltaHom :
    extDeltaFunctorMapComp Ψ (adj.unit.app (𝟙_ C)) ≫ adjunctionExtDeltaHom Φ Ψ adj =
      extDeltaFunctorPrecomp (𝟭 C) (Functor.LaxMonoidal.ε Φ) := by
  have : (extDeltaFunctor (𝟭 C) (Φ.obj (𝟙_ C))).IsUniversal :=
    extDeltaFunctor_isUniversal (𝟭 C) _ (fun I _ n e => Ext.eq_zero_of_injective e)
  refine DeltaFunctor.IsUniversal.hom_ext_zero _ ?_
  refine NatTrans.ext (funext fun N => ?_)
  ext c
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (X := Φ.obj (𝟙_ C)) (Y := N)).2 c
  show adjunctionExtMap Φ Ψ adj N
      ((Ext.mk₀ (adj.unit.app (𝟙_ C))).comp ((Ext.mk₀ f).mapExactFunctor Ψ) (zero_add 0)) =
    (Ext.mk₀ (Functor.LaxMonoidal.ε Φ)).comp (Ext.mk₀ f) (zero_add 0)
  simp only [adjunctionExtMap, mapUnit, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  have key : Φ.map (adj.unit.app (𝟙_ C)) ≫ Φ.map (Ψ.map f) ≫ adj.counit.app N = f := by
    have hn := adj.counit.naturality f
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn]
    simp
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  rw [key]

/-- **`θ (Ψ(c) ∘ η_𝟙) = c ∘ ε`**: the map `Stacks.ExtCup.adjunctionExtMap` undoes the `Ext`-level
comparison of Stacks 03FD for the exact right adjoint `Ψ`, up to the unit `ε : 𝟙 ⟶ Φ 𝟙` of the lax
monoidal structure of `Φ`. -/
theorem adjunctionExtMap_extMapCompHom (N : C) {n : ℕ} (c : Ext.{v} (Φ.obj (𝟙_ C)) N n) :
    adjunctionExtMap Φ Ψ adj N (extMapCompHom Ψ (adj.unit.app (𝟙_ C)) n N c) =
      (Ext.mk₀ (Functor.LaxMonoidal.ε Φ)).comp c (zero_add n) :=
  congrArg (fun η => (η.app n).app N c)
    (extDeltaFunctorMapComp_comp_adjunctionExtDeltaHom Φ Ψ adj)

end Stacks.ExtCup

end
