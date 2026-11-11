module

public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # The stalk of a presheaf agrees with the stalk of its sheafification, abstractly

## Main results

* `main_theorem00Y8`: for a functor `L` with right adjoint `R` whose values are sheaves,
  precomposition by `L.map (toSheafify J F)` is a bijection on maps out of `L.obj (sheafify J F)`.
  This is the abstract categorical core of the proof of Stacks 00Y8 (3); the lemma itself, for a
  functor `u : C ⥤ Type w` satisfying the covering conditions (a) and (b), is in
  `StacksFrontier.CategoryTheory.Sites.Point.StalkOfCoveringFunctor`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

/--
The abstract categorical core of the proof of Stacks 00Y8 (3).

Let `C` be a small category equipped with a Grothendieck topology `J`, let
`L : (Cᵒᵖ ⥤ Type v) ⥤ Type v` be the "stalk-at-a-point" functor on presheaves,
and let `R : Type v ⥤ (Cᵒᵖ ⥤ Type v)` be the "point-pushforward" functor.
Assume:

* `L ⊣ R` (for the stalk functor of a functor `u : C ⥤ Type v` this is Stacks 00Y7), and
* for every set `E`, the presheaf `R.obj E` is a sheaf for `J`.

Then for every presheaf `F` and every set `E`, precomposition by
`L.map (toSheafify J F)` is a bijection
`(L.obj (sheafify J F) ⟶ E) → (L.obj F ⟶ E)`. This is a general fact about adjunctions and
does not by itself state Stacks 00Y8: the lemma itself, for a functor `u` satisfying the
covering conditions (a) and (b), is
`PresheafPushforwardStalkAdjunction.isSheaf_presheafPushforward`,
`PresheafPushforwardStalkAdjunction.sheafStalk_adjoint_skyscraper` and
`PresheafPushforwardStalkAdjunction.isIso_presheafStalk_map_toSheafify` in
`StacksFrontier.CategoryTheory.Sites.Point.StalkOfCoveringFunctor`.
-/
theorem main_theorem00Y8
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)]
    (L : (Cᵒᵖ ⥤ Type v) ⥤ Type v) (R : Type v ⥤ Cᵒᵖ ⥤ Type v)
    (adj : L ⊣ R)
    (hR : ∀ E : Type v, Presheaf.IsSheaf J (R.obj E))
    (F : Cᵒᵖ ⥤ Type v) (E : Type v) :
    Function.Bijective
      (fun g : L.obj (sheafify J F) ⟶ E => L.map (toSheafify J F) ≫ g) := by
  -- Chain three Hom-bijections:
  --   `e₁`, the adjunction `L ⊣ R` at `sheafify J F`;
  --   `e₂`, the universal property of sheafification, available because `R.obj E` is a sheaf;
  --   `e₃`, the adjunction `L ⊣ R` at `F`, backwards.
  let e₁ := adj.homEquiv (sheafify J F) E
  let e₃ := (adj.homEquiv F E).symm
  let e₂ : (sheafify J F ⟶ R.obj E) ≃ (F ⟶ R.obj E) :=
    { toFun := fun α => toSheafify J F ≫ α
      invFun := fun β => sheafifyLift J β (hR E)
      left_inv := fun α => by
        symm
        apply sheafifyLift_unique
        rfl
      right_inv := fun β => toSheafify_sheafifyLift J β (hR E) }
  let Φ : (L.obj (sheafify J F) ⟶ E) ≃ (L.obj F ⟶ E) := e₁.trans (e₂.trans e₃)
  -- Naturality of the adjunction in the left variable identifies `Φ` with the map in question.
  have hΦ : ∀ g, Φ g = L.map (toSheafify J F) ≫ g := fun g => by
    dsimp only [Φ, e₁, e₂, e₃, Equiv.trans_apply, Equiv.coe_fn_mk]
    rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply]
  convert Φ.bijective using 1
  exact (funext hΦ).symm
