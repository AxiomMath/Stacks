module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Yoneda

/-!
# Mates along equivalences, and the transposes they relate

Consider a square of categories whose horizontal edges are adjunctions `L ⊣ R` and `L' ⊣ R'`
and whose vertical edges are functors `G` and `H`:
```
      L
   C --→ D
 G |     | H
   v     v
   C' -→ D'
      L'
```
An isomorphism `e : R ⋙ G ≅ H ⋙ R'` between the composites of the right adjoints has a mate
`G ⋙ L' ⟶ L ⋙ H`. This file records two facts about it.

First, it relates the transposes of the two adjunctions: for `g : X ⟶ R Y`, the mate followed by
`H` applied to the transpose `L X ⟶ Y` of `g` is the transpose along `L' ⊣ R'` of the image of
`g`, corrected by `e`. This needs no hypothesis on `G` and `H`.

Second, when `G` and `H` are equivalences (fully faithful, and `H` essentially surjective) the mate
is itself an isomorphism. In general it is not: that is the Beck–Chevalley phenomenon.

Together they say that a comparison map defined as a transpose along `L ⊣ R` is an isomorphism
exactly when the corresponding transpose along `L' ⊣ R'` is.

## Main definitions

* `CategoryTheory.Adjunction.mateOfRightIso`: the mate `G ⋙ L' ⟶ L ⋙ H` of
  `e : R ⋙ G ≅ H ⋙ R'`.

## Main results

* `CategoryTheory.Adjunction.mateOfRightIso_app_comp_map_homEquiv_symm`: the mate relates the
  transposes of the two adjunctions.
* `CategoryTheory.Adjunction.isIso_mateOfRightIso`: along equivalences, the mate is an
  isomorphism.
* `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_mateOfRightIso`: a transpose along
  `L ⊣ R` is an isomorphism exactly when the corresponding transpose along `L' ⊣ R'` is.

## Implementation notes

The mate is Mathlib's `CategoryTheory.mateEquiv`, inverted. Invertibility is proved by the Yoneda
criterion `CategoryTheory.isIso_iff_coyoneda_map_bijective`: precomposition with a component of
the mate is, by the first fact, a composite of bijections.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {C' : Type*} [Category* C'] {D' : Type*} [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}

/-- The mate `G ⋙ L' ⟶ L ⋙ H` of an isomorphism `R ⋙ G ≅ H ⋙ R'` between the composites of the
right adjoints of two adjunctions `L ⊣ R` and `L' ⊣ R'`. -/
def mateOfRightIso (e : R ⋙ G ≅ H ⋙ R') : G ⋙ L' ⟶ L ⋙ H :=
  (mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ e.hom)

/-- **The mate relates the transposes.** For `g : X ⟶ R Y`, the component at `X` of the mate of
`e`, followed by `H` of the transpose `L X ⟶ Y` of `g`, is the transpose along `L' ⊣ R'` of
`G g` followed by `e`. -/
theorem mateOfRightIso_app_comp_map_homEquiv_symm (e : R ⋙ G ≅ H ⋙ R') {X : C} {Y : D}
    (g : X ⟶ R.obj Y) :
    (mateOfRightIso adj adj' e).app X ≫ H.map ((adj.homEquiv X Y).symm g) =
      (adj'.homEquiv (G.obj X) (H.obj Y)).symm (G.map g ≫ e.hom.app Y) := by
  have h := mateEquiv_counit_symm adj adj' (TwoSquare.mk _ _ _ _ e.hom) Y
  have hn := (mateOfRightIso adj adj' e).naturality g
  simp only [Functor.comp_map] at hn
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change _ = L'.map (G.map g) ≫ L'.map (e.hom.app Y) ≫ adj'.counit.app (H.obj Y)
  change L'.map (e.hom.app Y) ≫ adj'.counit.app (H.obj Y) =
    (mateOfRightIso adj adj' e).app (R.obj Y) ≫ H.map (adj.counit.app Y) at h
  rw [h, ← Category.assoc, ← Category.assoc, hn]

/-- **Along equivalences, the mate is an isomorphism.** If `G` and `H` are fully faithful and `H`
is essentially surjective, the mate of an isomorphism `R ⋙ G ≅ H ⋙ R'` is an isomorphism. -/
theorem isIso_mateOfRightIso (e : R ⋙ G ≅ H ⋙ R') (hG : G.FullyFaithful)
    (hH : H.FullyFaithful) [H.EssSurj] : IsIso (mateOfRightIso adj adj' e) := by
  suffices ∀ X, IsIso ((mateOfRightIso adj adj' e).app X) from NatIso.isIso_of_isIso_app _
  intro X
  refine (isIso_iff_coyoneda_map_bijective _).mpr fun T => ?_
  let Z := H.objPreimage T
  let ε : H.obj Z ≅ T := H.objObjPreimageIso T
  let eq : (H.obj (L.obj X) ⟶ T) ≃ (L'.obj (G.obj X) ⟶ T) :=
    (Iso.homCongr (Iso.refl _) ε.symm).trans <| hH.homEquiv.symm.trans <|
      (adj.homEquiv _ _).trans <| hG.homEquiv.trans <|
        (Iso.homCongr (Iso.refl _) (e.app Z)).trans <| (adj'.homEquiv _ _).symm.trans <|
          Iso.homCongr (Iso.refl _) ε
  have heq : ∀ x, eq x = (mateOfRightIso adj adj' e).app X ≫ x := by
    intro x
    simp only [eq, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Iso.symm_hom, Iso.app_hom]
    have hk := mateOfRightIso_app_comp_map_homEquiv_symm adj adj' e
      (adj.homEquiv _ _ (hH.homEquiv.symm (x ≫ ε.inv)))
    rw [Equiv.symm_apply_apply] at hk
    change (adj'.homEquiv (G.obj X) (H.obj Z)).symm
      (G.map (adj.homEquiv _ _ (hH.homEquiv.symm (x ≫ ε.inv))) ≫ e.hom.app Z) ≫ ε.hom = _
    rw [← hk, Category.assoc]
    change _ ≫ H.map (hH.preimage (x ≫ ε.inv)) ≫ ε.hom = _
    rw [hH.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hfun : (fun x : (L ⋙ H).obj X ⟶ T => (mateOfRightIso adj adj' e).app X ≫ x) = eq :=
    funext fun x => (heq x).symm
  rw [hfun]
  exact eq.bijective

/-- **Transposes along the two adjunctions are isomorphisms together.** If `G` and `H` are fully
faithful and `H` is essentially surjective, then for `g : X ⟶ R Y` the transpose `L X ⟶ Y` of
`g` is an isomorphism exactly when the transpose `L' (G X) ⟶ H Y` of `G g` followed by `e` is. -/
theorem isIso_homEquiv_symm_iff_of_mateOfRightIso (e : R ⋙ G ≅ H ⋙ R')
    (hG : G.FullyFaithful) (hH : H.FullyFaithful) [H.EssSurj] {X : C} {Y : D}
    (g : X ⟶ R.obj Y) :
    IsIso ((adj.homEquiv X Y).symm g) ↔
      IsIso ((adj'.homEquiv (G.obj X) (H.obj Y)).symm (G.map g ≫ e.hom.app Y)) := by
  have := isIso_mateOfRightIso adj adj' e hG hH
  rw [← mateOfRightIso_app_comp_map_homEquiv_symm adj adj' e g, isIso_comp_left_iff]
  exact ⟨fun _ => inferInstance, fun _ => hH.isIso_of_isIso_map _⟩

end CategoryTheory.Adjunction

end
