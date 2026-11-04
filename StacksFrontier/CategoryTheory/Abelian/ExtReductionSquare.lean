module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# Squares of `Ext` classes along an exact functor

Let `R : D ⥤ C` be an exact functor of abelian categories. For `x ∈ Ext^p_C(A, B)`,
`x' ∈ Ext^p_D(A', B')` and maps `α : A ⟶ R A'`, `β : B ⟶ R B'`, the square `(α, β)` from `x` to
`x'` **commutes** if `x ∘ β = α ∘ R(x')` in `Ext^p_C(A, R B')` (`Stacks.ExtReduction.ExtSq`).
Commuting squares compose (`Stacks.ExtReduction.ExtSq.comp`), exist between morphisms forming a
commutative square (`Stacks.ExtReduction.ExtSq.mk₀`) and between the classes of two short exact
sequences related by a morphism `S ⟶ R(S')` (`Stacks.ExtReduction.ExtSq.extClass`), and are
carried to commuting squares by exact functors `F`, `F'` intertwined by a natural transformation
`R ⋙ F ⟶ F' ⋙ R₂` (`Stacks.ExtReduction.ExtSq.map`), hence also by the adjunction maps
`Ext(A, G B) → Ext(L A, B)` of compatible adjunctions (`Stacks.ExtReduction.ExtSq.extMap`).

## Main definitions

* `Stacks.ExtReduction.ExtSq`: a commuting square of `Ext` classes along `R`.

## Main results

* `Stacks.ExtReduction.ExtSq.comp`: commuting squares compose.
* `Stacks.ExtReduction.ExtSq.mk₀`: a commutative square of morphisms is a commuting square of
  `Ext⁰` classes.
* `Stacks.ExtReduction.ExtSq.extClass`: the classes of two short exact sequences related by a
  morphism `S ⟶ R(S')` form a commuting square.
* `Stacks.ExtReduction.ExtSq.map`: exact functors intertwined by a natural transformation carry
  commuting squares to commuting squares.
* `Stacks.ExtReduction.ExtSq.extMap`: compatible adjunctions carry commuting squares to
  commuting squares.
-/

@[expose] public noncomputable section

universe w w' w₂ w₂' v v' v₂ v₂' u u' u₂ u₂'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Stacks.ExtReduction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : D ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **A commuting square of `Ext` classes along `R`**: for `x ∈ Ext^p(A, B)`,
`x' ∈ Ext^p(A', B')`, `α : A ⟶ R A'` and `β : B ⟶ R B'`, the equality `x ∘ β = α ∘ R(x')` in
`Ext^p(A, R B')`. -/
def ExtSq {A B : C} {A' B' : D} (α : A ⟶ R.obj A') (β : B ⟶ R.obj B') {p : ℕ}
    (x : Ext.{w} A B p) (x' : Ext.{w'} A' B' p) : Prop :=
  x.comp (Ext.mk₀ β) (add_zero p) = (Ext.mk₀ α).comp (x'.mapExactFunctor R) (zero_add p)

variable {R}

/-- **Commuting squares compose.** -/
theorem ExtSq.comp {A B E : C} {A' B' E' : D} {α : A ⟶ R.obj A'} {β : B ⟶ R.obj B'}
    {γ : E ⟶ R.obj E'} {p q : ℕ} {x : Ext.{w} A B p} {x' : Ext.{w'} A' B' p}
    {y : Ext.{w} B E q} {y' : Ext.{w'} B' E' q} (hx : ExtSq R α β x x')
    (hy : ExtSq R β γ y y') {s : ℕ} (h : p + q = s) :
    ExtSq R α γ (x.comp y h) (x'.comp y' h) := by
  unfold ExtSq at *
  rw [Ext.mapExactFunctor_comp, Ext.comp_assoc x y (Ext.mk₀ γ) h (add_zero q) (by omega), hy,
    ← Ext.comp_assoc x (Ext.mk₀ β) _ (add_zero p) (zero_add q) (by omega), hx,
    Ext.comp_assoc _ _ _ (zero_add p) h (by omega)]

/-- **A commutative square of morphisms is a commuting square of `Ext⁰` classes.** -/
theorem ExtSq.mk₀ {A B : C} {A' B' : D} {α : A ⟶ R.obj A'} {β : B ⟶ R.obj B'} {f : A ⟶ B}
    {f' : A' ⟶ B'} (hf : f ≫ β = α ≫ R.map f') : ExtSq R α β (Ext.mk₀ f) (Ext.mk₀ f') := by
  unfold ExtSq
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, hf]

/-- **The classes of two short exact sequences related by a morphism `S ⟶ R(S')` form a
commuting square.** -/
theorem ExtSq.extClass {S : ShortComplex C} {S' : ShortComplex D} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (φ : S ⟶ S'.map R) :
    ExtSq R φ.τ₃ φ.τ₁ hS.extClass hS'.extClass := by
  unfold ExtSq
  rw [Ext.mapExactFunctor_extClass]
  exact hS.extClass_naturality (hS'.map_of_exact R) φ

/-- **Scaling both sides of a commuting square.** -/
theorem ExtSq.nsmul {A B : C} {A' B' : D} {α : A ⟶ R.obj A'} {β : B ⟶ R.obj B'} {p : ℕ}
    {x : Ext.{w} A B p} {x' : Ext.{w'} A' B' p} (hx : ExtSq R α β x x') (m : ℕ) :
    ExtSq R (m • α) (m • β) x x' := by
  unfold ExtSq at *
  induction m with
  | zero => rw [zero_smul, zero_smul, Ext.mk₀_zero, Ext.mk₀_zero, Ext.comp_zero, Ext.zero_comp]
  | succ m ih => rw [succ_nsmul, succ_nsmul, Ext.mk₀_add, Ext.mk₀_add, Ext.comp_add, Ext.add_comp,
      ih, hx]

variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w₂} C₂]
  {D₂ : Type u₂'} [Category.{v₂'} D₂] [Abelian D₂] [HasExt.{w₂'} D₂]
  {R₂ : D₂ ⥤ C₂} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]

/-- **Exact functors intertwined by a natural transformation carry commuting squares to commuting
squares**: for `θ : R ⋙ F ⟶ F' ⋙ R₂`, a square `(α, β)` from `x` to `x'` gives the square
`(F α ≫ θ, F β ≫ θ)` from `F x` to `F' x'`. -/
theorem ExtSq.map [EnoughInjectives D] (F : C ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (F' : D ⥤ D₂) [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (θ : R ⋙ F ⟶ F' ⋙ R₂) {A B : C} {A' B' : D}
    {α : A ⟶ R.obj A'} {β : B ⟶ R.obj B'} {p : ℕ} {x : Ext.{w} A B p} {x' : Ext.{w'} A' B' p}
    (hx : ExtSq R α β x x') :
    ExtSq R₂ (F.map α ≫ θ.app A') (F.map β ≫ θ.app B') (x.mapExactFunctor F)
      (x'.mapExactFunctor F') := by
  unfold ExtSq at *
  have h1 := congrArg (fun t => (t.mapExactFunctor F).comp (Ext.mk₀ (θ.app B')) (add_zero p)) hx
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at h1
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero, h1,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor R F A' p x',
    Ext.comp_assoc_of_third_deg_zero,
    ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor θ A' p x',
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor F' R₂ A' p x']

/-- **Compatible adjunctions carry commuting squares to commuting squares.** For `L ⊣ G`,
`L' ⊣ G'` with `L`, `L'` exact and `θ : R ⋙ L ⟶ L' ⋙ R₂`, a square `(α, β)` from
`x ∈ Ext(A, G B)` to `x' ∈ Ext(A', G' B')` whose right side `β` is compatible with
`γ : B ⟶ R₂ B'` through the counits gives the square `(L α ≫ θ, γ)` between the adjunction
images `Ext(L A, B)` and `Ext(L' A', B')`. -/
theorem ExtSq.extMap [EnoughInjectives D] {L : C ⥤ C₂} {G : C₂ ⥤ C} (adj : L ⊣ G) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] {L' : D ⥤ D₂} {G' : D₂ ⥤ D}
    (adj' : L' ⊣ G') [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (θ : R ⋙ L ⟶ L' ⋙ R₂) {A : C} {B : C₂} {A' : D} {B' : D₂} {α : A ⟶ R.obj A'}
    {β : G.obj B ⟶ R.obj (G'.obj B')} {γ : B ⟶ R₂.obj B'} {p : ℕ} {x : Ext.{w} A (G.obj B) p}
    {x' : Ext.{w'} A' (G'.obj B') p} (hx : ExtSq R α β x x')
    (hε : L.map β ≫ θ.app (G'.obj B') ≫ R₂.map (adj'.counit.app B') = adj.counit.app B ≫ γ) :
    ExtSq R₂ (L.map α ≫ θ.app A') γ (Stacks.ExtAdjunction.extMap adj A B p x)
      (Stacks.ExtAdjunction.extMap adj' A' B' p x') := by
  rw [Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply]
  refine (hx.map L L' θ).comp (ExtSq.mk₀ ?_) (add_zero p)
  rw [← hε, Category.assoc]

end Stacks.ExtReduction

end
