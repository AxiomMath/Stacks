module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap

/-!
# Projection-formula maps at an object whose tensor functor is an equivalence

Let `L ⊣ R` be an adjunction, `A`, `B` bifunctors on its source and target and
`α : A ⋙ L ⟶ L.prod L ⋙ B` an isomorphism. If tensoring with `H` on the source and with `L H`
on the target are autoequivalences, then the projection-formula map
`A(H, R G) ⟶ R(B(L H, G))` is an isomorphism for every `G`; no compatibility of `α` with unit
or shift constraints is needed. The same holds for the map with the counit in the first factor.

## Main results

* `CategoryTheory.Adjunction.isIso_homEquiv_comp_map_counit`: the transpose of
  `β_{R G} ≫ P'(ε_G)` is invertible for an isomorphism `β : P ⋙ L ≅ L ⋙ P'` along
  equivalences `P`, `P'`.
* `Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_of_isEquivalence`
* `CategoryTheory.isIso_adjunctionTensorMap_of_isEquivalence`
* `CategoryTheory.isEquivalence_curry_uncurry_obj`, `…_flip_obj`: the hypotheses for an
  uncurried bifunctor.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **The mate of an isomorphism along equivalences is invertible.** For an isomorphism
`β : P ⋙ L ≅ L ⋙ P'`, with `P` an equivalence and `P'` fully faithful, the transpose
`P(R G) ⟶ R(P' G)` of `β_{R G} ≫ P'(ε_G)` is an isomorphism. -/
theorem isIso_homEquiv_comp_map_counit {P : C ⥤ C} {P' : D ⥤ D} (β : P ⋙ L ≅ L ⋙ P')
    (hP : P.FullyFaithful) [P.EssSurj] (hP' : P'.FullyFaithful) (G : D) :
    IsIso (adj.homEquiv _ _ (β.hom.app (R.obj G) ≫ P'.map (adj.counit.app G))) := by
  refine (isIso_iff_yoneda_map_bijective _).mpr fun T => ?_
  let W := P.objPreimage T
  let ε : P.obj W ≅ T := P.objObjPreimageIso T
  let eq : (T ⟶ P.obj (R.obj G)) ≃ (T ⟶ R.obj (P'.obj G)) :=
    (Iso.homCongr ε.symm (Iso.refl _)).trans <| hP.homEquiv.symm.trans <|
      (adj.homEquiv _ _).symm.trans <| hP'.homEquiv.trans <|
        (Iso.homCongr (β.app W).symm (Iso.refl _)).trans <| (adj.homEquiv _ _).trans <|
          Iso.homCongr ε (Iso.refl _)
  have h2 : (⇑eq) = fun x => x ≫ adj.homEquiv _ _
      (β.hom.app (R.obj G) ≫ P'.map (adj.counit.app G)) := by
    funext x
    obtain ⟨y, rfl⟩ : ∃ y, ε.inv ≫ P.map y = x :=
      ⟨hP.preimage (ε.hom ≫ x), by rw [hP.map_preimage, Iso.inv_hom_id_assoc]⟩
    simp only [eq, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
      Iso.symm_inv, Iso.app_hom, Iso.hom_inv_id_assoc, Functor.FullyFaithful.homEquiv_symm_apply,
      Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.preimage_map, Category.assoc]
    have hβ := β.hom.naturality y
    simp only [Functor.comp_map] at hβ
    simp only [← Adjunction.homEquiv_naturality_left]
    congr 2
    rw [reassoc_of% hβ, ← P'.map_comp, Adjunction.homEquiv_counit]
  exact h2 ▸ eq.bijective

/-- The mate of a natural family `e Z : L (P Z) ≅ P' (L Z)` along equivalences `P`, `P'` is
invertible. -/
private theorem isIso_homEquiv_comp_map_counit_of_natural {P : C ⥤ C} {P' : D ⥤ D}
    [P.IsEquivalence] [P'.IsEquivalence] (e : ∀ Z, L.obj (P.obj Z) ≅ P'.obj (L.obj Z))
    (he : ∀ {Z Z'} (g : Z ⟶ Z'), L.map (P.map g) ≫ (e Z').hom = (e Z).hom ≫ P'.map (L.map g))
    (G : D) : IsIso (adj.homEquiv _ _ ((e (R.obj G)).hom ≫ P'.map (adj.counit.app G))) :=
  adj.isIso_homEquiv_comp_map_counit (NatIso.ofComponents e he)
    (.ofFullyFaithful _) (.ofFullyFaithful _) G

end CategoryTheory.Adjunction

namespace Stacks.ProjectionFormula

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)


/-- The projection-formula map with the counit in the second factor, followed by `R` of a natural
map `B(-, G) ⟶ -` at `L H`, is natural in `H`. -/
theorem adjunctionTensorMapSnd_comp_map_naturality (G : D) (ρ : ∀ W : D, B.obj (W, G) ⟶ W)
    (hρ : ∀ {W W' : D} (w : W ⟶ W'), B.map (w ×ₘ 𝟙 G) ≫ ρ W' = ρ W ≫ w) {H H' : C}
    (k : H ⟶ H') :
    A.map (k ×ₘ 𝟙 (R.obj G)) ≫ adjunctionTensorMapSnd adj A B α H' G ≫ R.map (ρ (L.obj H')) =
      (adjunctionTensorMapSnd adj A B α H G ≫ R.map (ρ (L.obj H))) ≫ R.map (L.map k) := by
  have h := adjunctionTensorMapSnd_natural adj A B α k (𝟙 G)
  rw [R.map_id] at h
  rw [reassoc_of% h, Category.assoc, ← R.map_comp, ← R.map_comp, hρ]

/-- **The projection-formula map with the counit in the second factor is invertible at `H`** as
soon as `α` is invertible and tensoring with `H` and with `L H` are equivalences. -/
theorem isIso_adjunctionTensorMapSnd_of_isEquivalence [IsIso α] (H : C) (G : D)
    [((Functor.curry.obj A).obj H).IsEquivalence]
    [((Functor.curry.obj B).obj (L.obj H)).IsEquivalence] :
    IsIso (adjunctionTensorMapSnd adj A B α H G) := by
  exact adj.isIso_homEquiv_comp_map_counit_of_natural (P := (Functor.curry.obj A).obj H)
    (P' := (Functor.curry.obj B).obj (L.obj H)) (fun Z => asIso (α.app (H, Z)))
    (fun {Z Z'} g => by simpa using α.naturality ((𝟙 H, g) : ((H, Z) : C × C) ⟶ (H, Z'))) G

end Stacks.ProjectionFormula

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The projection-formula map with the counit in the first factor is invertible at `K`** as
soon as `α` is invertible and tensoring with `K` and with `L K` on the right are equivalences. -/
theorem isIso_adjunctionTensorMap_of_isEquivalence [IsIso α] (G : D) (K : C)
    [((Functor.curry.obj A).flip.obj K).IsEquivalence]
    [((Functor.curry.obj B).flip.obj (L.obj K)).IsEquivalence] :
    IsIso (adjunctionTensorMap adj A B α G K) := by
  exact adj.isIso_homEquiv_comp_map_counit_of_natural (P := (Functor.curry.obj A).flip.obj K)
    (P' := (Functor.curry.obj B).flip.obj (L.obj K)) (fun Z => asIso (α.app (Z, K)))
    (fun {Z Z'} g => by simpa using α.naturality ((g, 𝟙 K) : ((Z, K) : C × C) ⟶ (Z', K))) G

/-- Tensoring with `H` on the left through the uncurried bifunctor is an equivalence when it
is one through the curried bifunctor. -/
theorem isEquivalence_curry_uncurry_obj {E : Type*} [Category* E] (F : E ⥤ E ⥤ E) (H : E)
    [(F.obj H).IsEquivalence] :
    ((Functor.curry.obj (Functor.uncurry.obj F)).obj H).IsEquivalence :=
  Functor.isEquivalence_of_iso (F := F.obj H) (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))

/-- Tensoring with `K` on the right through the uncurried bifunctor is an equivalence when it
is one through the curried bifunctor. -/
theorem isEquivalence_curry_uncurry_flip_obj {E : Type*} [Category* E] (F : E ⥤ E ⥤ E) (K : E)
    [(F.flip.obj K).IsEquivalence] :
    ((Functor.curry.obj (Functor.uncurry.obj F)).flip.obj K).IsEquivalence :=
  Functor.isEquivalence_of_iso (F := F.flip.obj K)
    (NatIso.ofComponents (fun _ => Iso.refl _) (by simp))

end CategoryTheory

end
