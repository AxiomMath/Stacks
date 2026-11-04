module

public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyConstantCoefficients

/-!
# Nondegeneracy of the cup product pairing from duality

Let `C` be an abelian monoidal category, `μ : F ⊗ G ⟶ T` a pairing with `- ⊗ G` exact, and `t` a
trace on `Ext^N(𝟙, T)` with values in `ℤ/pᵐ`. Suppose that

* `a ↦ μ ∘ (a ⊗ G) ∘ λ⁻¹ : Ext^i(𝟙, F) → Ext^i(G, T)` is bijective (for étale sheaves, a pairing
  perfect on the geometric fibres, `Stacks.EtaleCohomology.bijective_tensorPairingExt`), and
* duality holds at `G` for `t` (`CategoryTheory.Abelian.Ext.IsDualityPerfect`).

Then the pairing `(a, b) ↦ t(a ∪_μ b)` of `Ext^i(𝟙, F)` and `Ext^{N-i}(𝟙, G)` is nondegenerate on
both sides (`Stacks.ExtCup.cup_nondegenerate`): `a ∪_μ b = b ∘ Θ(a)` with `Θ` the bijection above,
`b ↦ t(b ∘ -)` is an isomorphism onto the characters of `Ext^i(G, T)`, and characters separate the
points of a `ℤ/pᵐ`-module (`ℤ/pᵐ` is self-injective). This is the nondegeneracy of the
finite-level Poincaré pairing in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `CategoryTheory.Abelian.Ext.exists_addMonoidHom_zmodPow_apply_ne_zero`.
* `Stacks.ExtCup.cup_eq_comp`.
* `Stacks.ExtCup.cup_nondegenerate`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

universe w v u

namespace CategoryTheory.Abelian.Ext

/-- **Characters separate the points of a `ℤ/pᵐ`-module**: the cyclic submodule of `v ≠ 0` is
finite, so carries a character nonzero at `v`, which extends (`ℤ/pᵐ` is self-injective,
`CategoryTheory.Abelian.Ext.exists_extend_zmodPow`). -/
theorem exists_addMonoidHom_zmodPow_apply_ne_zero {p m : ℕ} [Fact p.Prime] {E : Type*}
    [AddCommGroup E] [Module (ZMod (p ^ m)) E] {v : E} (hv : v ≠ 0) :
    ∃ φ : E →+ ZMod (p ^ m), φ v ≠ 0 := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let Hs : Submodule (ZMod (p ^ m)) E := Submodule.span (ZMod (p ^ m)) {v}
  have : Finite Hs := by
    obtain ⟨s, hs⟩ : Hs.FG := Submodule.fg_span_singleton v
    have : Module.Finite (ZMod (p ^ m)) Hs := Module.Finite.iff_fg.2 ⟨s, hs⟩
    exact Module.finite_of_finite (ZMod (p ^ m))
  have hv' : (⟨v, Submodule.mem_span_singleton_self v⟩ : Hs) ≠ 0 := fun h =>
    hv (congrArg Subtype.val h)
  obtain ⟨χ, hχ⟩ := Stacks.EtaleCohomology.exists_zmodLinearMap_apply_ne_zero (m := p ^ m) hv'
  obtain ⟨ψ, hψ⟩ := exists_extend_zmodPow (p := p) (m := m) Hs.toAddSubgroup
    (χ.toAddMonoidHom.comp (AddMonoidHom.mk' (fun x : Hs.toAddSubgroup => (⟨x.1, x.2⟩ : Hs))
      (fun _ _ => rfl)))
  exact ⟨ψ, (hψ ⟨v, Submodule.mem_span_singleton_self v⟩).trans_ne hχ⟩

end CategoryTheory.Abelian.Ext

namespace Stacks.ExtCup

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  {F G T : C} [(MonoidalCategory.tensorRight G).Additive]
  [PreservesFiniteLimits (MonoidalCategory.tensorRight G)]
  [PreservesFiniteColimits (MonoidalCategory.tensorRight G)] (μ : F ⊗ G ⟶ T)

/-- The cup product `a ∪_μ b` is `b` followed by `Θ(a) = μ ∘ (a ⊗ G) ∘ λ⁻¹`. -/
theorem cup_eq_comp {i j n : ℕ} (h : j + i = n) (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) :
    cup μ a b h = b.comp ((Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i)) h := by
  rw [cup, Ext.comp_assoc_of_second_deg_zero]

/-- **The cup product pairing is nondegenerate on both sides**, given that `Θ` is bijective and
that duality holds at `G` for a trace `t` with values in `ℤ/pᵐ`. -/
theorem cup_nondegenerate {p m : ℕ} [Fact p.Prime] {N : ℕ} (t : Ext.{w} (𝟙_ C) T N →+ ZMod (p ^ m))
    [∀ (j : ℕ), Module (ZMod (p ^ m)) (Ext.{w} G T j)] {i j : ℕ} (h : j + i = N)
    (hΘ : Function.Bijective (fun a : Ext.{w} (𝟙_ C) F i => (Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i)))
    (hPD : Ext.IsDualityPerfect (𝟙_ C) T N t G) :
    (∀ a : Ext.{w} (𝟙_ C) F i, (∀ b : Ext.{w} (𝟙_ C) G j, t (cup μ a b h) = 0) → a = 0) ∧
      (∀ b : Ext.{w} (𝟙_ C) G j, (∀ a : Ext.{w} (𝟙_ C) F i, t (cup μ a b h) = 0) → b = 0) := by
  have hb := hPD j i h
  refine ⟨fun a ha => ?_, fun b hb' => ?_⟩
  · set y := (Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i)
    have hy : y = 0 := by
      by_contra hy
      obtain ⟨φ, hφ⟩ := Ext.exists_addMonoidHom_zmodPow_apply_ne_zero (p := p) (m := m) hy
      obtain ⟨b, hb₀⟩ := hb.2 φ
      refine hφ ?_
      rw [← hb₀, Ext.dualityPairing_apply, ← cup_eq_comp]
      exact ha b
    refine hΘ.1 ?_
    show y = _
    rw [hy]
    simp
  · refine hb.1 ?_
    ext y
    obtain ⟨a, rfl⟩ := hΘ.2 y
    rw [Ext.dualityPairing_apply, ← cup_eq_comp, hb' a, map_zero, AddMonoidHom.zero_apply]

end Stacks.ExtCup

end
