module

public import StacksFrontier.CategoryTheory.Abelian.ExtCupTwist
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The twisted action on `Ext` through an adjunction

Let `Φ ⊣ Ψ` be an adjunction of endofunctors of an abelian monoidal category `C`, with `Φ`
exact and lax monoidal and `Ψ` exact. For a morphism `τ : F ⟶ Ψ F`, the action
`Stacks.ExtCup.twistAction Φ σ` with `σ : Φ F ⟶ F` the adjoint of `τ` factors as
`a ↦ θ (a ∘ τ)`, where

`θ : Ext^i(𝟙, Ψ N) ⟶ Ext^i(𝟙, N)`, `b ↦ ε_N ∘ Φ(b)`

(`Stacks.ExtCup.adjunctionExtMap`), read out of the unit through `𝟙 ⟶ Φ 𝟙`. The map `θ` is a
morphism of `δ`-functors from `N ↦ Ext^i(𝟙, Ψ N)` to `N ↦ Ext^i(𝟙, N)`
(`Stacks.ExtCup.adjunctionExtDeltaHom`): `Φ` carries extension classes to extension classes
and the counit is natural.

This is the `Ext` side of the comparison of the geometric Frobenius `π_X^*` on
`Hⁱ_c(X_k̄, K) = Ext^i(Λ, (j_! K)|_{X̄_k̄})` with the canonical Frobenius of
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` (`Φ = π̄⁻¹`, `Ψ = π̄_*`, `τ` the base
change of the Frobenius descent isomorphism), in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): there the canonical action is `θ ∘ τ_*`
with `θ` defined through derived direct images, and the universality of `N ↦ Ext^i(𝟙, Ψ N)`
reduces the comparison to degree zero.

## Main definitions

* `Stacks.ExtCup.adjunctionExtMap`: `θ`.
* `Stacks.ExtCup.adjunctionExtDeltaHom`: `θ` as a morphism of `δ`-functors.

## Main results

* `Stacks.ExtCup.twistAction_homEquiv_symm`: `twistAction Φ (adj.homEquiv.symm τ) a = θ (a ∘ τ)`.
-/

@[expose] public noncomputable section

universe w v u

namespace Stacks.ExtCup

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  [EnoughInjectives C] (Φ Ψ : C ⥤ C) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] (adj : Φ ⊣ Ψ)

/-- **The map `Ext^i(𝟙, Ψ N) ⟶ Ext^i(𝟙, N)` attached to an adjunction `Φ ⊣ Ψ`**: apply the exact
lax monoidal functor `Φ`, read out of the unit, then compose with the counit `Φ Ψ N ⟶ N`. -/
def adjunctionExtMap (N : C) {i : ℕ} (b : Ext.{w} (𝟙_ C) (Ψ.obj N) i) : Ext.{w} (𝟙_ C) N i :=
  (mapUnit Φ b).comp (Ext.mk₀ (adj.counit.app N)) (add_zero i)

omit [EnoughInjectives C] in
/-- The twisted action by the adjoint `σ = ε_F ∘ Φ τ` of `τ : F ⟶ Ψ F` is the map `θ` applied to
`a ∘ τ`. -/
theorem twistAction_homEquiv_symm {F : C} (τ : F ⟶ Ψ.obj F) {i : ℕ}
    (a : Ext.{w} (𝟙_ C) F i) :
    twistAction Φ ((adj.homEquiv _ _).symm τ) a =
      adjunctionExtMap Φ Ψ adj F (a.comp (Ext.mk₀ τ) (add_zero i)) := by
  simp only [twistAction, adjunctionExtMap, mapUnit, Adjunction.homEquiv_counit,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]

omit [EnoughInjectives C] in
/-- `θ` is additive. -/
theorem adjunctionExtMap_add (N : C) {i : ℕ} (b b' : Ext.{w} (𝟙_ C) (Ψ.obj N) i) :
    adjunctionExtMap Φ Ψ adj N (b + b') =
      adjunctionExtMap Φ Ψ adj N b + adjunctionExtMap Φ Ψ adj N b' := by
  simp [adjunctionExtMap, mapUnit, Ext.mapExactFunctor_add]

omit [EnoughInjectives C] in
/-- `θ` commutes with the connecting morphisms of `Ext^*(𝟙, -)`: for a short exact sequence
`S` the image under `θ` of `b ∘ [Ψ S]` is `θ b ∘ [S]`. -/
theorem adjunctionExtMap_comp_extClass [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
    [Ψ.Additive] {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (b : Ext.{w} (𝟙_ C) (Ψ.obj S.X₃) n) :
    adjunctionExtMap Φ Ψ adj S.X₁ (b.comp (hS.map_of_exact Ψ).extClass rfl) =
      (adjunctionExtMap Φ Ψ adj S.X₃ b).comp hS.extClass rfl := by
  have hΦΨ : ((S.map Ψ).map Φ).ShortExact := (hS.map_of_exact Ψ).map_of_exact Φ
  let c : (S.map Ψ).map Φ ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  simp only [adjunctionExtMap, mapUnit, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass Φ (hS.map_of_exact Ψ)]
  simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [ShortComplex.ShortExact.extClass_naturality hΦΨ hS c, ← Ext.comp_assoc_of_second_deg_zero]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by lia)).symm

omit [EnoughInjectives C] in
/-- `θ` is natural: for `g : N ⟶ N'`, `θ (b ∘ Ψ g) = θ b ∘ g`. -/
theorem adjunctionExtMap_comp_mk₀ {N N' : C} (g : N ⟶ N') {i : ℕ}
    (b : Ext.{w} (𝟙_ C) (Ψ.obj N) i) :
    adjunctionExtMap Φ Ψ adj N' (b.comp (Ext.mk₀ (Ψ.map g)) (add_zero i)) =
      (adjunctionExtMap Φ Ψ adj N b).comp (Ext.mk₀ g) (add_zero i) := by
  simp only [adjunctionExtMap, mapUnit, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  congr 3
  exact adj.counit.naturality g

/-- **`θ` as a morphism of `δ`-functors** from `N ↦ Ext^*(𝟙, Ψ N)` to `N ↦ Ext^*(𝟙, N)`. When
`Ψ` preserves injective objects the source is universal
(`ModuleSheafCohomology.extDeltaFunctor_isUniversal`), so `θ` is the unique
morphism of `δ`-functors extending its degree-zero component. -/
def adjunctionExtDeltaHom [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] [Ψ.Additive] :
    ModuleSheafCohomology.extDeltaFunctor.{w} Ψ (𝟙_ C) ⟶
      ModuleSheafCohomology.extDeltaFunctor.{w} (𝟭 C) (𝟙_ C) where
  app n :=
    { app N := AddCommGrpCat.ofHom
        { toFun := adjunctionExtMap Φ Ψ adj N
          map_zero' := by simp [adjunctionExtMap, mapUnit]
          map_add' := adjunctionExtMap_add Φ Ψ adj N }
      naturality N N' g := by
        ext b
        change adjunctionExtMap Φ Ψ adj N' (b.comp (Ext.mk₀ (Ψ.map g)) (add_zero n)) =
          (adjunctionExtMap Φ Ψ adj N b).comp (Ext.mk₀ g) (add_zero n)
        exact adjunctionExtMap_comp_mk₀ Φ Ψ adj g b }
  comm {S} hS n := by
    have := hS.mono_f
    have := hS.epi_g
    ext b
    change (adjunctionExtMap Φ Ψ adj S.X₃ b).comp (hS.map_of_exact (𝟭 C)).extClass rfl =
      adjunctionExtMap Φ Ψ adj S.X₁ (b.comp (hS.map_of_exact Ψ).extClass rfl)
    exact (adjunctionExtMap_comp_extClass Φ Ψ adj hS b).symm

end Stacks.ExtCup

end
