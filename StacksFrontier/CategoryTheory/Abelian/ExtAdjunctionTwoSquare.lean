module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# Bijectivity on `Ext` across an adjunction with invertible base change

Consider a square of adjunctions between abelian categories
```
A  --Lf-->  B           Lf ⊣ Rf,   Lf' ⊣ Rf'
|Lg         |Lg'
v           v
A' --Lf'--> B'
```
with all six functors exact, together with identifications `eg : Lg ⋙ Lf' ≅ Lc` and
`ef : Lf ⋙ Lg' ≅ Lc` of the two composites around the square. Their mate is the base change map
`Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` of `Stacks.CategoryTheory.BaseChange.twoSquare`. When the base change map
is invertible, `Lg` is bijective on `Ext^n(a, Rf K)` exactly when `Lg'` is bijective on
`Ext^n(Lf a, K)`.

The geometric reading: for a finite morphism of schemes `ν : Y ⟶ X` and a base change
`g : X' ⟶ X`, the restriction map on the cohomology of `ν_* G` along `g` is bijective exactly
when the restriction map on the cohomology of `G` along the base change `Y' ⟶ Y` is. This is
the transfer that Stacks Project Tag 0A5D makes through the Leray spectral sequence.

## Main results

* `Stacks.ExtAdjunction.extMap_mapExactFunctor_comm`: the square comparing the two adjunction
  maps of `Stacks.ExtAdjunction.extMap` with the maps induced by `Lg` and `Lg'` commutes, up to
  the base change map and the comparison of the composites.
* `Stacks.ExtAdjunction.isBijectiveOnExt_iff_of_isIso_twoSquare`: the transfer of bijectivity
  on `Ext`, stated through `Stacks.EtaleCohomology.IsBijectiveOnExt`.

## Implementation notes

The square commutes by naturality of the comparison `Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` on `Ext`
(`Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor`), functoriality of `Ext.mapExactFunctor` in the
functor, and the defining property of the mate at a component
(`Stacks.CategoryTheory.BaseChange.homEquiv_symm_map`). Enough injectives is required in `A`,
for the functoriality statements, and in `B` and `B'`, for bijectivity of the adjunction maps.
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Stacks.ExtAdjunction

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁} {Lf' : C₃ ⥤ C₄} {Rf' : C₄ ⥤ C₃}
  {Lg : C₁ ⥤ C₃} {Lg' : C₂ ⥤ C₄} {Lc : C₁ ⥤ C₄}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  [Lf.Additive] [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf]
  [Lf'.Additive] [PreservesFiniteLimits Lf'] [PreservesFiniteColimits Lf']
  [Lg.Additive] [PreservesFiniteLimits Lg] [PreservesFiniteColimits Lg]
  [Lg'.Additive] [PreservesFiniteLimits Lg'] [PreservesFiniteColimits Lg']

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Square

variable [HasExt.{w₁} C₁] [HasExt.{w₂} C₂] [HasExt.{w₃} C₃] [HasExt.{w₄} C₄]
  [EnoughInjectives C₁]

/-- The comparison `Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` of the two composites around the square. -/
abbrev composite (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) : Lg ⋙ Lf' ⟶ Lf ⋙ Lg' :=
  eg.hom ≫ ef.inv

/-- **The adjunction maps commute with base change.** For `x ∈ Ext^n(a, Rf K)`, applying the
adjunction map of `Lf ⊣ Rf` and then `Lg'`, and precomposing with the comparison of the composites
at `a`, is the same as applying `Lg`, postcomposing with the base change map at `K`, and applying
the adjunction map of `Lf' ⊣ Rf'`. -/
theorem extMap_mapExactFunctor_comm (a : C₁) (K : C₂) (n : ℕ)
    (x : Ext.{w₁} a (Rf.obj K) n) :
    (Ext.mk₀ ((composite eg ef).app a)).comp
        ((extMap adjf a K n x).mapExactFunctor Lg') (zero_add n) =
      extMap adjf' (Lg.obj a) (Lg'.obj K) n
        ((x.mapExactFunctor Lg).comp
          (Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K)) (add_zero n)) := by
  have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (composite eg ef) a n x
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor Lf Lg' a n x,
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor Lg Lf' a n x] at hnat
  have hmate := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map adjf adjf' eg ef K
  rw [Adjunction.homEquiv_counit] at hmate
  rw [extMap_apply, extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, hnat, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, hmate]
  simp [composite]

variable [EnoughInjectives C₂] [EnoughInjectives C₄]
  [Rf.Additive] [PreservesFiniteLimits Rf] [PreservesFiniteColimits Rf]
  [Rf'.Additive] [PreservesFiniteLimits Rf'] [PreservesFiniteColimits Rf']

/-- **The map induced by `Lg'` is a conjugate of the map induced by `Lg`.** Under an invertible
base change map there are bijections `α` and `β` with `Lg' ∘ α = β ∘ Lg` on the relevant `Ext`
groups; injectivity, surjectivity and bijectivity therefore transfer in both directions. -/
theorem exists_bijective_conj_of_isIso_twoSquare
    [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef)]
    (a : C₁) (K : C₂) (n : ℕ) :
    ∃ (α : Ext.{w₁} a (Rf.obj K) n → Ext.{w₂} (Lf.obj a) K n)
      (β : Ext.{w₃} (Lg.obj a) (Lg.obj (Rf.obj K)) n →
        Ext.{w₄} (Lg'.obj (Lf.obj a)) (Lg'.obj K) n),
      Function.Bijective α ∧ Function.Bijective β ∧
        (Lg'.mapExtAddHom (Lf.obj a) K n) ∘ α = β ∘ (Lg.mapExtAddHom a (Rf.obj K) n) := by
  have hβ : IsIso (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K) :=
    inferInstanceAs
      (IsIso ((Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef).app K))
  have hψ : IsIso ((composite eg ef).app a) :=
    inferInstanceAs (IsIso (eg.hom.app a ≫ ef.inv.app a))
  have h3 : Function.Bijective ((Ext.mk₀ ((composite eg ef).app a)).precomp (a := n) (b := n)
      (Lg'.obj K) (zero_add n) : Ext.{w₄} _ _ n → _) :=
    precomp_mk₀_bijective_of_isIso _ n
  have h4 : Function.Bijective
      ((Ext.mk₀ (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K)).postcomp
        (a := n) (b := n) (Lg.obj a) (add_zero n) : Ext.{w₃} _ _ n → _) :=
    postcomp_mk₀_bijective_of_isIso _ n
  let e₁ := Equiv.ofBijective _ h3
  let e₂ := Equiv.ofBijective _ h4
  refine ⟨extMap adjf a K n, e₁.symm ∘ extMap adjf' (Lg.obj a) (Lg'.obj K) n ∘ e₂,
    extMap_bijective adjf a K n,
    e₁.symm.bijective.comp ((extMap_bijective adjf' (Lg.obj a) (Lg'.obj K) n).comp e₂.bijective),
    ?_⟩
  funext x
  exact (e₁.symm_apply_eq.mpr (extMap_mapExactFunctor_comm adjf adjf' eg ef a K n x).symm).symm

/-- **Transfer of injectivity on `Ext` across an invertible base change map.** -/
theorem mapExtAddHom_injective_iff_of_isIso_twoSquare
    [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef)]
    (a : C₁) (K : C₂) (n : ℕ) :
    Function.Injective (Lg.mapExtAddHom a (Rf.obj K) n : Ext.{w₁} _ _ n → Ext.{w₃} _ _ n) ↔
      Function.Injective (Lg'.mapExtAddHom (Lf.obj a) K n :
        Ext.{w₂} _ _ n → Ext.{w₄} _ _ n) := by
  obtain ⟨α, β, hα, hβ, h⟩ := exists_bijective_conj_of_isIso_twoSquare adjf adjf' eg ef a K n
  constructor
  · intro hi
    exact (Function.Injective.of_comp_iff' _ hα).mp (h ▸ hβ.injective.comp hi)
  · intro hi
    exact (Function.Injective.of_comp_iff hβ.injective _).mp (h ▸ hi.comp hα.injective)

/-- **Transfer of surjectivity on `Ext` across an invertible base change map.** -/
theorem mapExtAddHom_surjective_iff_of_isIso_twoSquare
    [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef)]
    (a : C₁) (K : C₂) (n : ℕ) :
    Function.Surjective (Lg.mapExtAddHom a (Rf.obj K) n : Ext.{w₁} _ _ n → Ext.{w₃} _ _ n) ↔
      Function.Surjective (Lg'.mapExtAddHom (Lf.obj a) K n :
        Ext.{w₂} _ _ n → Ext.{w₄} _ _ n) := by
  obtain ⟨α, β, hα, hβ, h⟩ := exists_bijective_conj_of_isIso_twoSquare adjf adjf' eg ef a K n
  constructor
  · intro hs
    exact Function.Surjective.of_comp (g := α) (h ▸ hβ.surjective.comp hs)
  · intro hs
    exact (Function.Surjective.of_comp_iff' hβ _).mp (h ▸ hs.comp hα.surjective)

/-- **Transfer of bijectivity on `Ext` across an invertible base change map.** -/
theorem mapExtAddHom_bijective_iff_of_isIso_twoSquare
    [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef)]
    (a : C₁) (K : C₂) (n : ℕ) :
    Function.Bijective (Lg.mapExtAddHom a (Rf.obj K) n : Ext.{w₁} _ _ n → Ext.{w₃} _ _ n) ↔
      Function.Bijective (Lg'.mapExtAddHom (Lf.obj a) K n :
        Ext.{w₂} _ _ n → Ext.{w₄} _ _ n) :=
  and_congr (mapExtAddHom_injective_iff_of_isIso_twoSquare adjf adjf' eg ef a K n)
    (mapExtAddHom_surjective_iff_of_isIso_twoSquare adjf adjf' eg ef a K n)

end Square

section IsBijectiveOnExt

attribute [local instance] HasDerivedCategory.standard

variable [EnoughInjectives C₁] [EnoughInjectives C₂] [EnoughInjectives C₄]
  [Rf.Additive] [PreservesFiniteLimits Rf] [PreservesFiniteColimits Rf]
  [Rf'.Additive] [PreservesFiniteLimits Rf'] [PreservesFiniteColimits Rf']

/-- **Transfer of `IsBijectiveOnExt` across an invertible base change map**, the form consumed
by the dévissage of Stacks Project Tag 03SC: `Lg` is bijective on `Ext` from `a` into `Rf K` in
degree `n` exactly when `Lg'` is bijective on `Ext` from `Lf a` into `K` in degree `n`. -/
theorem isBijectiveOnExt_iff_of_isIso_twoSquare
    [IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef)]
    (a : C₁) (K : C₂) (n : ℕ) :
    Stacks.EtaleCohomology.IsBijectiveOnExt Lg a (Rf.obj K) n ↔
      Stacks.EtaleCohomology.IsBijectiveOnExt Lg' (Lf.obj a) K n := by
  let := HasExt.standard C₁
  let := HasExt.standard C₂
  let := HasExt.standard C₃
  let := HasExt.standard C₄
  exact (Stacks.EtaleCohomology.mapExt_bijective_iff_mapDerivedCategory _ _ _ _).symm.trans
    ((mapExtAddHom_bijective_iff_of_isIso_twoSquare.{max u₁ v₁, max u₂ v₂, max u₃ v₃, max u₄ v₄}
      adjf adjf' eg ef a K n).trans
      (Stacks.EtaleCohomology.mapExt_bijective_iff_mapDerivedCategory _ _ _ _))

end IsBijectiveOnExt

end Stacks.ExtAdjunction

end
