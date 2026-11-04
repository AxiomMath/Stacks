module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupPairingNondegenerate
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorialSquare

/-!
# Cup product pairings nondegenerate up to bounded torsion

Let `μ : F ⊗ G ⟶ T` be a pairing in an abelian monoidal category and `Θ_μ(a) = μ ∘ (a ⊗ G) ∘ λ⁻¹`,
so that `a ∪_μ b = b ∘ Θ_μ(a)` (`Stacks.ExtCup.cup_eq_comp`). This file provides three tools for
cup product pairings in which `Θ_μ` is only bijective up to bounded torsion, as for the pairing
of `H¹_c` with `H¹_c` on an affine curve, where `Θ_μ` is the forgetting of supports
`H¹_c → H¹` followed by coefficient duality:

* `Stacks.ExtCup.mapExactFunctor_tensorDual`: an exact lax monoidal functor `Φ` carries
  `Θ_μ(a)` to `Θ_{μ'}(Φ a)` for the pairing `μ' : Φ F ⊗ Φ G ⟶ Φ (F ⊗ G) ⟶ Φ T`;
* `Stacks.ExtAdjunction.bijective_mapExactFunctor_of_isIso_unit`: for an adjunction `L ⊣ R` of
  exact functors whose unit is invertible at `A`, the functor `R` is bijective on
  `Ext^n(L A, M) → Ext^n(R L A, R M)` (restriction along an open immersion, out of an extension
  by zero);
* `Stacks.ExtCup.cup_nondegenerate_of_bounds`: if duality holds at `G` and `Θ_μ` has kernel killed
  by `c₁` and image containing `c₂ Ext^i(G, T)`, the left kernel of the cup product pairing is
  killed by `c₁` and the right kernel by `c₂`.

These are the nondegeneracy steps of Poincaré duality on an affine curve in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

universe w w' v v' u u'

namespace Stacks.ExtCup

section Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [MonoidalCategory D] [HasExt.{w} D]
  [EnoughInjectives C] (Φ : C ⥤ D) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- **`Θ_μ` under an exact lax monoidal functor.** For `Φ` exact and lax monoidal,
`Φ (μ ∘ (a ⊗ G) ∘ λ⁻¹) = μ' ∘ (Φ a ⊗ Φ G) ∘ λ⁻¹` with `μ' = Φ μ ∘ μ_Φ` and `Φ a` read out of the
unit through `ε : 𝟙 ⟶ Φ 𝟙` (`Stacks.ExtCup.mapUnit`). -/
theorem mapExactFunctor_tensorDual {F G T : C} [(MonoidalCategory.tensorRight G).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight G)]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight G)]
    [(MonoidalCategory.tensorRight (Φ.obj G)).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight (Φ.obj G))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight (Φ.obj G))]
    (μ : F ⊗ G ⟶ T) {i : ℕ} (a : Ext.{w} (𝟙_ C) F i) :
    ((Ext.mk₀ (λ_ G).inv).comp
        ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ)
          (add_zero i)) (zero_add i)).mapExactFunctor Φ =
      (Ext.mk₀ (λ_ (Φ.obj G)).inv).comp (((mapUnit Φ a).mapExactFunctor
        (MonoidalCategory.tensorRight (Φ.obj G))).comp
          (Ext.mk₀ (Functor.LaxMonoidal.μ Φ F G ≫ Φ.map μ))
          (add_zero i)) (zero_add i) := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (tensorRightLaxμ Φ G) (𝟙_ C) i a
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor] at key
  have hu : (λ_ (Φ.obj G)).inv ≫
      (MonoidalCategory.tensorRight (Φ.obj G)).map (Functor.LaxMonoidal.ε Φ) ≫
      Functor.LaxMonoidal.μ Φ (𝟙_ C) G = Φ.map (λ_ G).inv := by
    show _ ≫ Functor.LaxMonoidal.ε Φ ▷ Φ.obj G ≫ _ = _
    rw [← cancel_epi (λ_ (Φ.obj G)).hom, Iso.hom_inv_id_assoc, Functor.LaxMonoidal.left_unitality,
      Category.assoc, Category.assoc, ← Φ.map_comp, Iso.hom_inv_id, Φ.map_id, Category.comp_id]
  have key' : (Ext.mk₀ ((MonoidalCategory.tensorRight (Φ.obj G)).map (Functor.LaxMonoidal.ε Φ) ≫
      Functor.LaxMonoidal.μ Φ (𝟙_ C) G)).comp
        ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).mapExactFunctor Φ) (zero_add i) =
      (Ext.mk₀ ((MonoidalCategory.tensorRight (Φ.obj G)).map (Functor.LaxMonoidal.ε Φ))).comp
        (((a.mapExactFunctor Φ).mapExactFunctor (MonoidalCategory.tensorRight (Φ.obj G))).comp
          (Ext.mk₀ (Functor.LaxMonoidal.μ Φ F G)) (add_zero i)) (zero_add i) := by
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
    exact congrArg (fun x => (Ext.mk₀ _).comp x (zero_add i)) key
  have := congrArg (fun x => (Ext.mk₀ (λ_ (Φ.obj G)).inv).comp
    (x.comp (Ext.mk₀ (Φ.map μ)) (add_zero i)) (zero_add i)) key'
  simp only [mapUnit, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc] at this ⊢
  rw [hu] at this
  exact this

/-- **Bounds for `Θ_μ` from bounds for its restriction.** Let `Φ` be exact lax monoidal,
`μ : F ⊗ G ⟶ T` and `c : Φ T ≅ T'`. Suppose that `a ↦ Φ a` (out of the unit) on `Ext^i(𝟙, F)` has
kernel killed by `c₁` and image containing `c₂ Ext^i(𝟙, Φ F)`, that `Θ` for the pairing
`Φ F ⊗ Φ G ⟶ Φ T ≅ T'` is bijective, and that `Φ` is injective on `Ext^i(G, T)`. Then `Θ_μ` has
kernel killed by `c₁` and image containing `c₂ Ext^i(G, T)`. -/
theorem bounds_tensorDual_of_mapUnit {F G T : C} {T' : D}
    [(MonoidalCategory.tensorRight G).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight G)]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight G)]
    [(MonoidalCategory.tensorRight (Φ.obj G)).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight (Φ.obj G))]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight (Φ.obj G))]
    (μ : F ⊗ G ⟶ T) (c : Φ.obj T ≅ T') {i : ℕ} (c₁ c₂ : ℕ)
    (hb₁ : ∀ a : Ext.{w} (𝟙_ C) F i, mapUnit Φ a = 0 → c₁ • a = 0)
    (hb₂ : ∀ z : Ext.{w} (𝟙_ D) (Φ.obj F) i, ∃ a : Ext.{w} (𝟙_ C) F i, mapUnit Φ a = c₂ • z)
    (hΘ : Function.Bijective (fun b : Ext.{w} (𝟙_ D) (Φ.obj F) i =>
      (Ext.mk₀ (λ_ (Φ.obj G)).inv).comp ((b.mapExactFunctor
        (MonoidalCategory.tensorRight (Φ.obj G))).comp
          (Ext.mk₀ (Functor.LaxMonoidal.μ Φ F G ≫ Φ.map μ ≫ c.hom)) (add_zero i)) (zero_add i)))
    (hΦ : Function.Injective (fun y : Ext.{w} G T i => y.mapExactFunctor Φ)) :
    (∀ a : Ext.{w} (𝟙_ C) F i, (Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i) = 0 → c₁ • a = 0) ∧
    ∀ y : Ext.{w} G T i, ∃ a : Ext.{w} (𝟙_ C) F i, (Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i) = c₂ • y := by
  let ΘU : Ext.{w} (𝟙_ D) (Φ.obj F) i →+ Ext.{w} (Φ.obj G) T' i :=
    ((Ext.mk₀ (λ_ (Φ.obj G)).inv).precomp _ (zero_add i)).comp
      (((Ext.mk₀ (Functor.LaxMonoidal.μ Φ F G ≫ Φ.map μ ≫ c.hom)).postcomp _ (add_zero i)).comp
        ((MonoidalCategory.tensorRight (Φ.obj G)).mapExtAddHom _ _ i))
  have hΘU : Function.Bijective ΘU := hΘ
  let Ψ : Ext.{w} G T i →+ Ext.{w} (Φ.obj G) T' i :=
    ((Ext.mk₀ c.hom).postcomp _ (add_zero i)).comp (Φ.mapExtAddHom G T i)
  have hrel : ∀ a : Ext.{w} (𝟙_ C) F i, ΘU (mapUnit Φ a) =
      Ψ ((Ext.mk₀ (λ_ G).inv).comp ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp
        (Ext.mk₀ μ) (add_zero i)) (zero_add i)) := fun a => by
    change _ = (Ext.mapExactFunctor Φ _).comp (Ext.mk₀ c.hom) (add_zero i)
    rw [mapExactFunctor_tensorDual Φ μ a, Ext.comp_assoc_of_third_deg_zero,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
    rfl
  refine ⟨fun a ha => hb₁ a (hΘU.1 ?_), fun y => ?_⟩
  · rw [hrel, ha, map_zero, map_zero]
  · obtain ⟨z, hz⟩ := hΘU.2 (Ψ y)
    obtain ⟨a, ha⟩ := hb₂ z
    have hΨ : Function.Injective Ψ :=
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso c.hom i).1.comp hΦ
    refine ⟨a, hΨ ?_⟩
    rw [← hrel, ha, map_nsmul, hz, map_nsmul]

end Functor

section Bounds

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  {F G T : C} [(MonoidalCategory.tensorRight G).Additive]
  [PreservesFiniteLimits (MonoidalCategory.tensorRight G)]
  [PreservesFiniteColimits (MonoidalCategory.tensorRight G)] (μ : F ⊗ G ⟶ T)

/-- **The cup product pairing is nondegenerate up to bounded torsion**, given duality at `G` for
a trace `t` with values in `ℤ/pᵐ` and that `Θ_μ : Ext^i(𝟙, F) → Ext^i(G, T)` has kernel killed by
`c₁` and image containing `c₂ Ext^i(G, T)`: the left kernel is killed by `c₁`, the right kernel
by `c₂`. -/
theorem cup_nondegenerate_of_bounds {p m : ℕ} [Fact p.Prime] {N : ℕ}
    (t : Ext.{w} (𝟙_ C) T N →+ ZMod (p ^ m))
    [∀ (j : ℕ), Module (ZMod (p ^ m)) (Ext.{w} G T j)] {i j : ℕ} (h : j + i = N) (c₁ c₂ : ℕ)
    (hker : ∀ a : Ext.{w} (𝟙_ C) F i, (Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i) = 0 → c₁ • a = 0)
    (hrange : ∀ y : Ext.{w} G T i, ∃ a : Ext.{w} (𝟙_ C) F i, (Ext.mk₀ (λ_ G).inv).comp
      ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i))
        (zero_add i) = c₂ • y)
    (hPD : Ext.IsDualityPerfect (𝟙_ C) T N t G) :
    (∀ a : Ext.{w} (𝟙_ C) F i, (∀ b : Ext.{w} (𝟙_ C) G j, t (cup μ a b h) = 0) → c₁ • a = 0) ∧
      (∀ b : Ext.{w} (𝟙_ C) G j, (∀ a : Ext.{w} (𝟙_ C) F i, t (cup μ a b h) = 0) →
        c₂ • b = 0) := by
  have hb := hPD j i h
  refine ⟨fun a ha => hker a ?_, fun b hb' => ?_⟩
  · by_contra hy
    obtain ⟨φ, hφ⟩ := Ext.exists_addMonoidHom_zmodPow_apply_ne_zero (p := p) (m := m) hy
    obtain ⟨b, hb₀⟩ := hb.2 φ
    refine hφ ?_
    rw [← hb₀, Ext.dualityPairing_apply, ← cup_eq_comp]
    exact ha b
  · refine hb.1 ?_
    ext y
    rw [map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul, map_zero, AddMonoidHom.zero_apply]
    obtain ⟨a, ha⟩ := hrange y
    rw [← ha, Ext.dualityPairing_apply, ← cup_eq_comp]
    exact hb' a

end Bounds

end Stacks.ExtCup

namespace Stacks.ExtAdjunction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]

/-- **`R` undoes the adjunction map up to the unit**: for `e ∈ Ext^n(A, R M)`,
`R (extMap e) ∘ η_A = e`. -/
theorem mk₀_unit_comp_mapExactFunctor_extMap (A : C) (M : D) (n : ℕ)
    (e : Ext.{w} A (R.obj M) n) :
    (Ext.mk₀ (adj.unit.app A)).comp ((extMap.{w, w'} adj A M n e).mapExactFunctor R)
      (zero_add n) = e := by
  rw [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor, ← Ext.comp_assoc_of_third_deg_zero,
    Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adj.unit A n e,
    Stacks.ExtFunctorial.mapExactFunctor_id, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  show e.comp (Ext.mk₀ (adj.unit.app (R.obj M) ≫ R.map (adj.counit.app M))) _ = e
  rw [adj.right_triangle_components, Ext.comp_mk₀_id]

/-- **`R` is bijective on `Ext` out of `L A`** when the unit of `L ⊣ R` is invertible at `A`:
`Ext^n(L A, M) → Ext^n(R L A, R M)`, `x ↦ R x`. -/
theorem bijective_mapExactFunctor_of_isIso_unit [EnoughInjectives D] (A : C)
    [IsIso (adj.unit.app A)] (M : D) (n : ℕ) :
    Function.Bijective (fun x : Ext.{w'} (L.obj A) M n => x.mapExactFunctor R) := by
  have hE := extMap_bijective.{w, w'} adj A M n
  have hU := Stacks.ExtFunctorial.bijective_mk₀_comp.{w} (asIso (adj.unit.app A))
    (Y := R.obj M) n
  have hg : Function.Bijective (fun x : Ext.{w'} (L.obj A) M n =>
      (Ext.mk₀ (adj.unit.app A)).comp (x.mapExactFunctor R) (zero_add n)) := by
    have hinv : Function.LeftInverse (fun x : Ext.{w'} (L.obj A) M n =>
        (Ext.mk₀ (adj.unit.app A)).comp (x.mapExactFunctor R) (zero_add n))
        (extMap.{w, w'} adj A M n) :=
      fun e => mk₀_unit_comp_mapExactFunctor_extMap adj A M n e
    refine ⟨fun x y hxy => ?_, hinv.surjective⟩
    obtain ⟨x', rfl⟩ := hE.2 x
    obtain ⟨y', rfl⟩ := hE.2 y
    rw [hinv x', hinv y'] at hxy
    rw [hxy]
  exact (Function.Bijective.of_comp_iff' hU
    (fun x : Ext.{w'} (L.obj A) M n => x.mapExactFunctor R)).1 hg

end Stacks.ExtAdjunction

end
