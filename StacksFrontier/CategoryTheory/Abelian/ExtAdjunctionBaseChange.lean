module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# The adjunction map on `Ext` across a square of adjunctions

Consider a square of abelian categories

```
     L
  A ---→ B
G |      | G'
  v      v
  A' --→ B'
     L'
```

with adjunctions `L ⊣ R` and `L' ⊣ R'`, exact functors `L, L', G, G'`, a natural transformation
`τ : G ⋙ L' ⟶ L ⋙ G'` comparing the two composites, and a base change morphism
`β : R ⋙ G ⟶ G' ⋙ R'` related to `τ` by the mate identity
`L' (β_M) ≫ ε'_{G' M} = τ_{R M} ≫ G' (ε_M)`. This file shows that the adjunction maps
`Ext^n(P, R M) → Ext^n(L P, M)` of `Stacks.ExtAdjunction.extMap` intertwine the map on `Ext`
induced by `G` (followed by `β`) with the map induced by `G'` (preceded by `τ`).

## Main results

* `Stacks.ExtAdjunction.extMap_mapExactFunctor_comp_mk₀`: the intertwining identity.
* `Stacks.ExtAdjunction.bijective_mapExtAddHom_iff_of_baseChange` and
  `Stacks.ExtAdjunction.surjective_mapExtAddHom_iff_of_baseChange`: when `R` and `R'` are exact,
  the target categories have enough injectives and `β_M`, `τ_P` are isomorphisms, the map on
  `Ext^n(P, R M)` induced by `G` is bijective (resp. surjective) if and only if the map on
  `Ext^n(L P, M)` induced by `G'` is.
* `Stacks.ExtAdjunction.bijective_mapExtAddHom_iff_of_twoSquare` and its surjective companion:
  the same for the canonical base change morphism `Stacks.CategoryTheory.BaseChange.twoSquare`,
  whose mate identity is `Stacks.ExtAdjunction.map_twoSquare_comp_counit`.
-/

@[expose] public noncomputable section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.ExtAdjunction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

/-- If `e₁ ∘ g = e₂ ∘ g' ∘ e₃` with `e₁, e₂, e₃` bijective, then `g` is bijective if and only if
`g'` is. -/
theorem bijective_iff_of_comp_eq {α β γ δ ε : Type*} {g : α → β} {g' : γ → δ}
    {e₁ : β → ε} {e₂ : δ → ε} {e₃ : α → γ} (h₁ : Function.Bijective e₁)
    (h₂ : Function.Bijective e₂) (h₃ : Function.Bijective e₃)
    (h : ∀ x, e₁ (g x) = e₂ (g' (e₃ x))) :
    Function.Bijective g ↔ Function.Bijective g' := by
  rw [← Function.Bijective.of_comp_iff' h₁ g,
    (funext h : e₁ ∘ g = e₂ ∘ (g' ∘ e₃)), Function.Bijective.of_comp_iff' h₂,
    Function.Bijective.of_comp_iff _ h₃]

/-- If `e₁ ∘ g = e₂ ∘ g' ∘ e₃` with `e₁, e₂, e₃` bijective, then `g` is surjective if and only if
`g'` is. -/
theorem surjective_iff_of_comp_eq {α β γ δ ε : Type*} {g : α → β} {g' : γ → δ}
    {e₁ : β → ε} {e₂ : δ → ε} {e₃ : α → γ} (h₁ : Function.Bijective e₁)
    (h₂ : Function.Bijective e₂) (h₃ : Function.Bijective e₃)
    (h : ∀ x, e₁ (g x) = e₂ (g' (e₃ x))) :
    Function.Surjective g ↔ Function.Surjective g' := by
  rw [← Function.Surjective.of_comp_iff' h₁ g,
    (funext h : e₁ ∘ g = e₂ ∘ (g' ∘ e₃)), Function.Surjective.of_comp_iff' h₂,
    Function.Surjective.of_comp_iff _ h₃.surjective]

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A'] {B' : Type u₄} [Category.{v₄} B'] [Abelian B']
  [HasExt.{w} A] [HasExt.{w} B] [HasExt.{w} A'] [HasExt.{w} B'] [EnoughInjectives A]
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'} {G : A ⥤ A'} {G' : B ⥤ B'}
  (adj : L ⊣ R) (adj' : L' ⊣ R')
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : G ⋙ L' ⟶ L ⋙ G') (β : R ⋙ G ⟶ G' ⋙ R')
  (hβ : ∀ M : B, L'.map (β.app M) ≫ adj'.counit.app (G'.obj M) =
    τ.app (R.obj M) ≫ G'.map (adj.counit.app M))

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

include hβ in
/-- The adjunction maps intertwine the two maps on `Ext`: for `x : Ext^n(P, R M)`, applying `G`
and then `β_M`, and then the adjunction map of `L' ⊣ R'`, is the same as applying the adjunction
map of `L ⊣ R`, then `G'`, and then precomposing with `τ_P`. -/
theorem extMap_mapExactFunctor_comp_mk₀ (P : A) (M : B) (n : ℕ) (x : Ext.{w} P (R.obj M) n) :
    extMap adj' (G.obj P) (G'.obj M) n
        ((x.mapExactFunctor G).comp (Ext.mk₀ (β.app M)) (add_zero n)) =
      (Ext.mk₀ (τ.app P)).comp ((extMap adj P M n x).mapExactFunctor G') (zero_add n) := by
  simp only [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hβ M, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_third_deg_zero,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor G L' P n x,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor L G' P n x,
    Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor τ P n x]

variable [EnoughInjectives B] [EnoughInjectives B']
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [R'.Additive] [PreservesFiniteLimits R'] [PreservesFiniteColimits R']

include hβ in
/-- Bijectivity on `Ext` across a square of adjunctions: if `β_M` and `τ_P` are
isomorphisms, the map `Ext^n(P, R M) → Ext^n(G P, G R M)` induced by `G` is bijective if and only
if the map `Ext^n(L P, M) → Ext^n(G' L P, G' M)` induced by `G'` is. -/
theorem bijective_mapExtAddHom_iff_of_baseChange (P : A) (M : B) (n : ℕ)
    [IsIso (β.app M)] [IsIso (τ.app P)] :
    Function.Bijective (G.mapExtAddHom P (R.obj M) n) ↔
      Function.Bijective (G'.mapExtAddHom (L.obj P) M n) :=
  bijective_iff_of_comp_eq
    ((extMap_bijective adj' (G.obj P) (G'.obj M) n).comp
      (postcomp_mk₀_bijective_of_isIso (β.app M) n))
    (precomp_mk₀_bijective_of_isIso (τ.app P) n) (extMap_bijective adj P M n)
    (fun x ↦ extMap_mapExactFunctor_comp_mk₀ adj adj' τ β hβ P M n x)

include hβ in
/-- Surjectivity on `Ext` across a square of adjunctions: if `β_M` and `τ_P` are isomorphisms,
the map on `Ext^n(P, R M)` induced by `G` is surjective if and only if the map on `Ext^n(L P, M)`
induced by `G'` is. -/
theorem surjective_mapExtAddHom_iff_of_baseChange (P : A) (M : B) (n : ℕ)
    [IsIso (β.app M)] [IsIso (τ.app P)] :
    Function.Surjective (G.mapExtAddHom P (R.obj M) n) ↔
      Function.Surjective (G'.mapExtAddHom (L.obj P) M n) :=
  surjective_iff_of_comp_eq
    ((extMap_bijective adj' (G.obj P) (G'.obj M) n).comp
      (postcomp_mk₀_bijective_of_isIso (β.app M) n))
    (precomp_mk₀_bijective_of_isIso (τ.app P) n) (extMap_bijective adj P M n)
    (fun x ↦ extMap_mapExactFunctor_comp_mk₀ adj adj' τ β hβ P M n x)

section TwoSquare

variable {Lc : A ⥤ B'} (eg : G ⋙ L' ≅ Lc) (ef : L ⋙ G' ≅ Lc)

omit [Abelian A] [Abelian B] [Abelian A'] [Abelian B'] [HasExt.{w} A] [HasExt.{w} B]
  [HasExt.{w} A'] [HasExt.{w} B'] [EnoughInjectives A] [L.Additive] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G'.Additive]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] [EnoughInjectives B] [EnoughInjectives B']
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] [R'.Additive]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R'] in
/-- The base change morphism `β = Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef`
satisfies the mate identity `L' (β_M) ≫ ε'_{G' M} = τ_{R M} ≫ G' (ε_M)` for
`τ = eg.hom ≫ ef.inv`. -/
theorem map_twoSquare_comp_counit (M : B) :
    L'.map ((Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef).app M) ≫
        adj'.counit.app (G'.obj M) =
      (eg.hom ≫ ef.inv).app (R.obj M) ≫ G'.map (adj.counit.app M) := by
  have := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map adj adj' eg ef M
  rw [Adjunction.homEquiv_counit] at this
  rwa [NatTrans.comp_app, Category.assoc]

/-- Bijectivity on `Ext` across a square of adjunctions, for the canonical base change
morphism `Stacks.CategoryTheory.BaseChange.twoSquare`. -/
theorem bijective_mapExtAddHom_iff_of_twoSquare (P : A) (M : B) (n : ℕ)
    [IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef).app M)] :
    Function.Bijective (G.mapExtAddHom P (R.obj M) n) ↔
      Function.Bijective (G'.mapExtAddHom (L.obj P) M n) :=
  bijective_mapExtAddHom_iff_of_baseChange adj adj' (eg.hom ≫ ef.inv)
    (Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef)
    (map_twoSquare_comp_counit adj adj' eg ef) P M n

/-- Surjectivity on `Ext` across a square of adjunctions, for the canonical base change
morphism `Stacks.CategoryTheory.BaseChange.twoSquare`. -/
theorem surjective_mapExtAddHom_iff_of_twoSquare (P : A) (M : B) (n : ℕ)
    [IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef).app M)] :
    Function.Surjective (G.mapExtAddHom P (R.obj M) n) ↔
      Function.Surjective (G'.mapExtAddHom (L.obj P) M n) :=
  surjective_mapExtAddHom_iff_of_baseChange adj adj' (eg.hom ≫ ef.inv)
    (Stacks.CategoryTheory.BaseChange.twoSquare adj adj' eg ef)
    (map_twoSquare_comp_counit adj adj' eg ef) P M n

end TwoSquare

end Stacks.ExtAdjunction

end
