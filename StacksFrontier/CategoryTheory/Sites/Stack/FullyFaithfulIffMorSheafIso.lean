module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence

/-!
# Fully faithful 1-morphisms of stacks (Stacks 04WQ)

Let `(𝒞, J)` be a site, let `p : 𝒳 ⥤ 𝒞` and `r : 𝒴 ⥤ 𝒞` be stacks over `𝒞`
(`CategoryTheory.Functor.IsStack`, Stacks 026F) and let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of fibred
categories over `𝒞` (`CategoryTheory.Functor.IsFibredOneMorphism`). For `x y` in the fibre over
`U`, `F` induces a map of presheaves `Mor(x, y) ⟶ Mor(F x, F y)` on `𝒞/U`
(`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`); since `p` and `r` are stacks, its
source and target are sheaves, and it is a morphism of sheaves on `𝒞/U`
(`CategoryTheory.Functor.IsFibredOneMorphism.morSheafMap`).

Stacks 04WQ says that `F` is fully faithful, as a functor between the total categories, if and
only if every such map of sheaves is an isomorphism.

## Main definitions

* `CategoryTheory.Functor.IsFibredOneMorphism.morSheafMap`: the morphism of sheaves
  `Mor(x, y) ⟶ Mor(F x, F y)` on `𝒞/U` induced by a 1-morphism of stacks.

## Main results

* `CategoryTheory.Functor.IsFibredOneMorphism.full_and_faithful_iff_isIso_morSheafMap`:
  Stacks 04WQ.

## References

* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
-/

@[expose] public section

namespace CategoryTheory.Functor.IsFibredOneMorphism

open Opposite

universe v v' u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {J : GrothendieckTopology 𝒞}
  {𝒳 : Type u₂} [Category.{v'} 𝒳] {𝒴 : Type u₃} [Category.{v'} 𝒴]
  {p : 𝒳 ⥤ 𝒞} {r : 𝒴 ⥤ 𝒞} [p.IsFibered] [r.IsFibered] {F : 𝒳 ⥤ 𝒴}

/-- The morphism of sheaves `Mor(x, y) ⟶ Mor(F x, F y)` on `𝒞/U` induced by a 1-morphism `F` of
stacks over `(𝒞, J)`, for `x y` in the fibre over `U`. Its underlying map of presheaves is
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`; its source and target are sheaves by
condition (2) of Stacks 026F for `p` and for `r`. -/
noncomputable def morSheafMap (hF : p.IsFibredOneMorphism r F) (hp : p.IsStack J)
    (hr : r.IsStack J) {U : 𝒞} (x y : p.Fiber U) :
    (⟨morPresheaf p x y, hp.isMorSheaf U x y⟩ : Sheaf (J.over U) (Type v')) ⟶
      ⟨morPresheaf r ((fiberFunctorOfCompEq hF.comp_eq U).obj x)
          ((fiberFunctorOfCompEq hF.comp_eq U).obj y),
        hr.isMorSheaf U _ _⟩ :=
  ⟨hF.morPresheafMap x y⟩

/-- The map of presheaves underlying `CategoryTheory.Functor.IsFibredOneMorphism.morSheafMap` is
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`. -/
lemma sheafToPresheaf_map_morSheafMap (hF : p.IsFibredOneMorphism r F) (hp : p.IsStack J)
    (hr : r.IsStack J) {U : 𝒞} (x y : p.Fiber U) :
    (sheafToPresheaf (J.over U) (Type v')).map (hF.morSheafMap hp hr x y) =
      hF.morPresheafMap x y :=
  rfl

/-- **Stacks 04WQ.** Let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of stacks `p : 𝒳 ⥤ 𝒞`, `r : 𝒴 ⥤ 𝒞` over a
site `(𝒞, J)`. Then `F` is fully faithful (as a functor between the total categories) if and only
if for every object `U` of `𝒞` and all `x y` in the fibre over `U`, the induced map
`Mor(x, y) ⟶ Mor(F x, F y)` is an isomorphism of sheaves on `𝒞/U`.

(1) ⇒ (2): over `f : V ⟶ U` the map is the action of `F` on morphisms of the fibre over `V`,
conjugated by the comparison isomorphisms between chosen pullbacks, and a fully faithful `F` is
fully faithful on fibres. (2) ⇒ (1): evaluating at the identity of `U` makes `F` fully faithful on
every fibre; a morphism of `𝒳` over `f` factors uniquely as a morphism of the fibre followed by a
strongly cartesian lift of `f`, which `F` preserves, so `F` is full and faithful on the total
categories (`CategoryTheory.Comma.full_of_fiber_full`,
`CategoryTheory.Comma.faithful_of_fiber_faithful`). -/
@[stacks 04WQ]
theorem full_and_faithful_iff_isIso_morSheafMap (hF : p.IsFibredOneMorphism r F)
    (hp : p.IsStack J) (hr : r.IsStack J) :
    (F.Full ∧ F.Faithful) ↔
      ∀ (U : 𝒞) (x y : p.Fiber U), IsIso (hF.morSheafMap hp hr x y) := by
  constructor
  · rintro ⟨_, _⟩ U x y
    have : IsIso ((sheafToPresheaf (J.over U) (Type v')).map (hF.morSheafMap hp hr x y)) :=
      Comma.isIso_morPresheafMap_of_fullyFaithful hF x y
    exact isIso_of_reflects_iso _ (sheafToPresheaf (J.over U) (Type v'))
  · intro h
    have hb : ∀ (U : 𝒞) (x y : p.Fiber U),
        Function.Bijective (fun m : x ⟶ y => (fiberFunctorOfCompEq hF.comp_eq U).map m) := by
      intro U x y
      have : IsIso (hF.morPresheafMap x y) := by
        rw [← sheafToPresheaf_map_morSheafMap hF hp hr]
        exact (sheafToPresheaf (J.over U) (Type v')).map_isIso _
      exact Comma.bijective_fiberFunctor_map_of_bijective_app hF x y
        ((isIso_iff_bijective _).mp (NatIso.isIso_app_of_isIso _ _))
    exact ⟨Comma.full_of_fiber_full hF fun U => ⟨fun {x y} g => (hb U x y).2 g⟩,
      Comma.faithful_of_fiber_faithful hF fun U => ⟨fun {x y} _ _ e => (hb U x y).1 e⟩⟩

end CategoryTheory.Functor.IsFibredOneMorphism
