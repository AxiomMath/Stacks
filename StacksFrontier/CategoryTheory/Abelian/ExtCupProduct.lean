module

public import Mathlib.CategoryTheory.Monoidal.Category
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# The cup product on `Ext` out of the tensor unit

Let `C` be an abelian monoidal category and `G` an object such that tensoring with `G` on the
right is exact. A morphism `μ : F ⊗ G ⟶ T` induces a cup product

`Ext^i(𝟙, F) × Ext^j(𝟙, G) ⟶ Ext^{j+i}(𝟙, T)`,   `a ∪ b = b ∘ λ⁻¹ ∘ (a ⊗ G) ∘ μ`,

where `a ⊗ G ∈ Ext^i(𝟙 ⊗ G, F ⊗ G)` is the image of `a` under the exact functor `- ⊗ G`
(`CategoryTheory.Abelian.Ext.mapExactFunctor`). For sheaves of `Λ`-modules on a site, `𝟙` is
the constant sheaf `Λ`, `Ext^i(Λ, F) = Hⁱ(F)`, and this is the cup product
`Hⁱ(F) × Hʲ(G) → H^{i+j}(T)` attached to a pairing `F ⊗ G → T` with `G` flat.

## Main definitions

* `Stacks.ExtCup.cup`: the cup product attached to `μ : F ⊗ G ⟶ T`.
* `Stacks.ExtCup.cupHom`: the same, as a biadditive map.
* `Stacks.ExtCup.mapUnit`: the image of a class under an exact lax monoidal functor.

## Main results

* `Stacks.ExtCup.add_cup`, `Stacks.ExtCup.cup_add`: the cup product is biadditive.
* `Stacks.ExtCup.cup_comp_mk₀`: naturality in the target of the pairing.
* `Stacks.ExtCup.comp_mk₀_cup`: naturality in the first coefficient.
* `Stacks.ExtCup.cup_comp_mk₀_right`: naturality in the second coefficient.
* `Stacks.ExtCup.mk₀_cup_mk₀`: in degree zero the cup product is the composite
  `𝟙 ≅ 𝟙 ⊗ 𝟙 ⟶ F ⊗ G ⟶ T`.
* `Stacks.ExtCup.mapUnit_cup`: exact lax monoidal functors carry cup products to cup
  products.
-/

@[expose] public noncomputable section

universe w v u

namespace Stacks.ExtCup

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]

section

variable {F G T : C} [(tensorRight G).Additive] [PreservesFiniteLimits (tensorRight G)]
  [PreservesFiniteColimits (tensorRight G)]

/-- **The cup product** `Ext^i(𝟙, F) × Ext^j(𝟙, G) ⟶ Ext^{j+i}(𝟙, T)` attached to a morphism
`μ : F ⊗ G ⟶ T`, for `G` such that `- ⊗ G` is exact: the composite of `b`, the inverse left
unitor `G ≅ 𝟙 ⊗ G`, the image `a ⊗ G` of `a` under the exact functor `- ⊗ G`, and `μ`. -/
def cup (μ : F ⊗ G ⟶ T) {i j : ℕ} (a : Ext.{w} (𝟙_ C) F i) (b : Ext.{w} (𝟙_ C) G j) {n : ℕ}
    (h : j + i = n) : Ext.{w} (𝟙_ C) T n :=
  (b.comp (Ext.mk₀ (λ_ G).inv) (add_zero j)).comp
    ((a.mapExactFunctor (tensorRight G)).comp (Ext.mk₀ μ) (add_zero i)) h

variable (μ : F ⊗ G ⟶ T) {i j n : ℕ} (h : j + i = n)

/-- The cup product is additive in the first variable. -/
@[simp]
theorem add_cup (a a' : Ext.{w} (𝟙_ C) F i) (b : Ext.{w} (𝟙_ C) G j) :
    cup μ (a + a') b h = cup μ a b h + cup μ a' b h := by
  simp only [cup, Ext.mapExactFunctor_add, Ext.add_comp, Ext.comp_add]

/-- The cup product is additive in the second variable. -/
@[simp]
theorem cup_add (a : Ext.{w} (𝟙_ C) F i) (b b' : Ext.{w} (𝟙_ C) G j) :
    cup μ a (b + b') h = cup μ a b h + cup μ a b' h := by
  simp only [cup, Ext.add_comp]

/-- The cup product with zero on the left vanishes. -/
@[simp]
theorem zero_cup (b : Ext.{w} (𝟙_ C) G j) : cup μ (0 : Ext.{w} (𝟙_ C) F i) b h = 0 := by
  simp only [cup, Ext.mapExactFunctor_zero, Ext.zero_comp, Ext.comp_zero]

/-- The cup product with zero on the right vanishes. -/
@[simp]
theorem cup_zero (a : Ext.{w} (𝟙_ C) F i) : cup μ a (0 : Ext.{w} (𝟙_ C) G j) h = 0 := by
  simp only [cup, Ext.zero_comp]

/-- The cup product as a biadditive map. -/
def cupHom : Ext.{w} (𝟙_ C) F i →+ Ext.{w} (𝟙_ C) G j →+ Ext.{w} (𝟙_ C) T n :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => cup μ a b h) (cup_add μ h a))
    (fun a a' => AddMonoidHom.ext fun b => add_cup μ h a a' b)

/-- Evaluating `cupHom μ h` at `a` and `b` gives the cup product `cup μ a b h`. -/
@[simp]
theorem cupHom_apply (a : Ext.{w} (𝟙_ C) F i) (b : Ext.{w} (𝟙_ C) G j) :
    cupHom μ h a b = cup μ a b h :=
  rfl

/-- **Naturality in the target of the pairing**: composing the cup product with `τ : T ⟶ T'` is
the cup product attached to `μ ≫ τ`. -/
theorem cup_comp_mk₀ {T' : C} (τ : T ⟶ T') (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) :
    (cup μ a b h).comp (Ext.mk₀ τ) (add_zero n) = cup (μ ≫ τ) a b h := by
  simp only [cup, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- **Naturality in the first coefficient**: for `φ : F ⟶ F'` and `μ' : F' ⊗ G ⟶ T`, the cup
product of `a ∘ φ` attached to `μ'` is the cup product of `a` attached to `(φ ▷ G) ≫ μ'`. -/
theorem comp_mk₀_cup {F' : C} (φ : F ⟶ F') (μ' : F' ⊗ G ⟶ T) (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) :
    cup μ' (a.comp (Ext.mk₀ φ) (add_zero i)) b h = cup (φ ▷ G ≫ μ') a b h := by
  simp only [cup, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rfl

/-- **The cup product in degree zero** is composition with `𝟙 ≅ 𝟙 ⊗ 𝟙 ⟶ F ⊗ G ⟶ T`. -/
theorem mk₀_cup_mk₀ (s : 𝟙_ C ⟶ F) (t : 𝟙_ C ⟶ G) :
    cup μ (Ext.mk₀ s) (Ext.mk₀ t) (add_zero 0) = Ext.mk₀ (t ≫ (λ_ G).inv ≫ s ▷ G ≫ μ) := by
  simp only [cup, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]
  rfl

end

/-- **Naturality in the second coefficient**: for `ψ : G ⟶ G'` and `μ' : F ⊗ G' ⟶ T`, the cup
product with `b ∘ ψ` attached to `μ'` is the cup product with `b` attached to `(F ◁ ψ) ≫ μ'`. -/
theorem cup_comp_mk₀_right [EnoughInjectives C] {F G G' T : C}
    [(tensorRight G).Additive] [PreservesFiniteLimits (tensorRight G)]
    [PreservesFiniteColimits (tensorRight G)]
    [(tensorRight G').Additive] [PreservesFiniteLimits (tensorRight G')]
    [PreservesFiniteColimits (tensorRight G')]
    (ψ : G ⟶ G') (μ' : F ⊗ G' ⟶ T) {i j n : ℕ} (h : j + i = n) (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) :
    cup μ' a (b.comp (Ext.mk₀ ψ) (add_zero j)) h = cup (F ◁ ψ ≫ μ') a b h := by
  have key : (Ext.mk₀ ((𝟙_ C) ◁ ψ)).comp (a.mapExactFunctor (tensorRight G')) (zero_add i) =
      (a.mapExactFunctor (tensorRight G)).comp (Ext.mk₀ (F ◁ ψ)) (add_zero i) :=
    Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ((tensoringRight C).map ψ) (𝟙_ C) i a
  have hl : ψ ≫ (λ_ G').inv = (λ_ G).inv ≫ (𝟙_ C) ◁ ψ := by simp
  simp only [cup, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hl]
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    ← Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ ((𝟙_ C) ◁ ψ)), key,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

section Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D : Type*} [Category D] [Abelian D] [MonoidalCategory D] [HasExt.{w} D]
  [EnoughInjectives C] (Φ : C ⥤ D) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- The structure maps `Φ X ⊗ Φ G ⟶ Φ (X ⊗ G)` of a lax monoidal functor, as a natural
transformation `Φ ⋙ (- ⊗ Φ G) ⟶ (- ⊗ G) ⋙ Φ`. -/
@[simps]
def tensorRightLaxμ (G : C) : Φ ⋙ tensorRight (Φ.obj G) ⟶ tensorRight G ⋙ Φ where
  app X := Functor.LaxMonoidal.μ Φ X G
  naturality _ _ f := Functor.LaxMonoidal.μ_natural_left Φ f G

/-- The image of a class under an exact lax monoidal functor `Φ`, read in `Ext` out of the unit
of the target through `ε : 𝟙 ⟶ Φ 𝟙`. -/
def mapUnit {F : C} {i : ℕ} (a : Ext.{w} (𝟙_ C) F i) : Ext.{w} (𝟙_ D) (Φ.obj F) i :=
  (Ext.mk₀ (Functor.LaxMonoidal.ε Φ)).comp (a.mapExactFunctor Φ) (zero_add i)

/-- **The cup product commutes with exact lax monoidal functors**: for `Φ` exact and lax
monoidal, the image of `a ∪_μ b` is `Φ a ∪ Φ b` for the pairing `Φ F ⊗ Φ G ⟶ Φ (F ⊗ G) ⟶ Φ T`. -/
theorem mapUnit_cup {F G T : C} [(tensorRight G).Additive]
    [PreservesFiniteLimits (tensorRight G)] [PreservesFiniteColimits (tensorRight G)]
    [(tensorRight (Φ.obj G)).Additive] [PreservesFiniteLimits (tensorRight (Φ.obj G))]
    [PreservesFiniteColimits (tensorRight (Φ.obj G))]
    (μ : F ⊗ G ⟶ T) {i j n : ℕ} (h : j + i = n) (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) :
    mapUnit Φ (cup μ a b h) =
      cup (Functor.LaxMonoidal.μ Φ F G ≫ Φ.map μ) (mapUnit Φ a) (mapUnit Φ b) h := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (tensorRightLaxμ Φ G) (𝟙_ C) i a
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor] at key
  have hu : (λ_ (Φ.obj G)).inv ≫ (tensorRight (Φ.obj G)).map (Functor.LaxMonoidal.ε Φ) ≫
      Functor.LaxMonoidal.μ Φ (𝟙_ C) G = Φ.map (λ_ G).inv := by
    change _ ≫ Functor.LaxMonoidal.ε Φ ▷ Φ.obj G ≫ _ = _
    rw [← cancel_epi (λ_ (Φ.obj G)).hom, Iso.hom_inv_id_assoc, Functor.LaxMonoidal.left_unitality,
      Category.assoc, Category.assoc, ← Φ.map_comp, Iso.hom_inv_id, Φ.map_id, Category.comp_id]
  simp only [mapUnit, cup, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.comp_assoc (Ext.mk₀ (Functor.LaxMonoidal.ε Φ)) _ _ (zero_add j) h (by omega)]
  congr 1
  rw [Ext.comp_assoc_of_second_deg_zero]
  congr 1
  have key' : (Ext.mk₀ ((tensorRight (Φ.obj G)).map (Functor.LaxMonoidal.ε Φ) ≫
      Functor.LaxMonoidal.μ Φ (𝟙_ C) G)).comp
        ((a.mapExactFunctor (tensorRight G)).mapExactFunctor Φ) (zero_add i) =
      (Ext.mk₀ ((tensorRight (Φ.obj G)).map (Functor.LaxMonoidal.ε Φ))).comp
        (((a.mapExactFunctor Φ).mapExactFunctor (tensorRight (Φ.obj G))).comp
          (Ext.mk₀ (Functor.LaxMonoidal.μ Φ F G)) (add_zero i)) (zero_add i) := by
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
    exact congrArg (fun x => (Ext.mk₀ _).comp x (zero_add i)) key
  have := congrArg (fun x => (Ext.mk₀ (λ_ (Φ.obj G)).inv).comp
    (x.comp (Ext.mk₀ (Φ.map μ)) (add_zero i)) (zero_add i)) key'
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc] at this ⊢
  rw [hu] at this
  exact this

end Functor

end Stacks.ExtCup
