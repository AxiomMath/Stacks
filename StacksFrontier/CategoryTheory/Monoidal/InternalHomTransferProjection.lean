module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransfer

/-!
# Internal homs are carried along a right adjoint satisfying the projection formula

Let `E ⊣ R` with `R : C ⥤ D`, tensor bifunctors on `C` and `D`, and `c : R(A ⊗ B) ≅ R A ⊗ R B`
natural in `A`. Suppose the **canonical projection map** `E(Z ⊗ R L) ⟶ E Z ⊗ L`, the transpose of
`Z ⊗ R L ⟶ R E Z ⊗ R L ≅ R(E Z ⊗ L)`, is an isomorphism. Then, as in
`CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective` but with no condition on the
unit of `E ⊣ R`, the canonical comparison `R H ⟶ H'` of internal homs is an isomorphism. This is
the formal half of the statement that pullback along an étale morphism commutes with the derived
internal hom through the map of [Stacks, Tag 08JF], with `E` extension by zero.

## Main results

* `CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective_of_isIso_projection`.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.InternalHomTransfer

variable {C D : Type*} [Category C] [Category D]
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) {R : C ⥤ D} {E : D ⥤ C} (adj : E ⊣ R)
  (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))

/-- **The comparison of internal homs along a right adjoint satisfying the projection formula
is an isomorphism.** If for every `Z` the transpose `E(Z ⊗ R L) ⟶ E Z ⊗ L` of
`(η_Z ⊗ 1) ≫ c⁻¹ : Z ⊗ R L ⟶ R(E Z ⊗ L)` is an isomorphism, the morphism `t : R H ⟶ H'` whose
transpose under the bijection of `H'` is `c⁻¹ ≫ R e` is an isomorphism. -/
theorem isIso_of_tensorHomBijective_of_isIso_projection
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    {L M H : C}
    (hp : ∀ Z : D, IsIso ((adj.homEquiv ((TD.obj Z).obj (R.obj L)) ((TC.obj (E.obj Z)).obj L)).symm
      ((TD.map (adj.unit.app Z)).app (R.obj L) ≫ (c (E.obj Z) L).inv)))
    (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (R.obj L) ⟶ R.obj M)
    (he' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e'))
    (t : R.obj H ⟶ H')
    (ht : (TD.map t).app (R.obj L) ≫ e' = (c H L).inv ≫ R.map e) :
    IsIso t := by
  rw [isIso_iff_yoneda_map_bijective]
  intro Z
  rw [← Function.Bijective.of_comp_iff' (he' Z)]
  have h1 : ((fun g : Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e') ∘
      (fun x : Z ⟶ R.obj H => x ≫ t)) =
      fun x => (TD.map x).app (R.obj L) ≫ (c H L).inv ≫ R.map e := by
    funext x
    simp only [Function.comp_apply, Functor.map_comp, NatTrans.comp_app, Category.assoc, ht]
  rw [h1, ← Function.Bijective.of_comp_iff _ (adj.homEquiv Z H).bijective]
  let p : (TD.obj Z).obj (R.obj L) ⟶ R.obj ((TC.obj (E.obj Z)).obj L) :=
    (TD.map (adj.unit.app Z)).app (R.obj L) ≫ (c (E.obj Z) L).inv
  have h2 : ((fun x : Z ⟶ R.obj H => (TD.map x).app (R.obj L) ≫ (c H L).inv ≫ R.map e) ∘
      (adj.homEquiv Z H)) =
      (fun h => p ≫ R.map h) ∘ (fun f : E.obj Z ⟶ H => (TC.map f).app L ≫ e) := by
    funext f
    have hcf : (TD.map (R.map f)).app (R.obj L) ≫ (c H L).inv =
        (c (E.obj Z) L).inv ≫ R.map ((TC.map f).app L) := by
      rw [Iso.comp_inv_eq, Category.assoc, hc f L, Iso.inv_hom_id_assoc]
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      NatTrans.comp_app, Category.assoc, p]
    rw [reassoc_of% hcf]
  rw [h2]
  have h3 : (fun h : (TC.obj (E.obj Z)).obj L ⟶ M => p ≫ R.map h) =
      (adj.homEquiv _ M) ∘ (fun h => (adj.homEquiv _ _).symm p ≫ h) := by
    funext h
    rw [Function.comp_apply, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [h3]
  have := hp Z
  exact ((adj.homEquiv _ M).bijective.comp (bijective_comp_left _)).comp (he (E.obj Z))

end CategoryTheory.InternalHomTransfer

end
