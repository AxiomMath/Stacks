module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Internal homs are carried along a functor with a fully faithful left adjoint

Let `C` and `D` be categories with tensor bifunctors `⊗_C` and `⊗_D`, and let `R : C ⥤ D` be a
functor with a left adjoint `E` whose unit is an isomorphism. Suppose `R` carries tensor
products to tensor products, `c : R(A ⊗ B) ≅ R A ⊗ R B`, naturally in `A`, and suppose the
*projection formula* `E Z ⊗ L ≅ E (Z ⊗ R L)` holds for *some* isomorphism, with no
compatibility asked of it. Let `e : H ⊗ L ⟶ M` exhibit `H` as an internal hom from `L` to `M`
in `C` — every `Z ⟶ H` corresponds to exactly one `Z ⊗ L ⟶ M` under `g ↦ (g ⊗ 1) ≫ e` — and
let `e' : H' ⊗ R L ⟶ R M` exhibit `H'` as one from `R L` to `R M` in `D`. Then the **canonical
comparison** `t : R H ⟶ H'`, the morphism whose transpose is

`R H ⊗ R L ≅ R(H ⊗ L) ⟶ R M`,

is an isomorphism.

This is the formal half of the statement that restriction to an open commutes with the derived
internal hom ([Stacks, Tag 08DL]) *through the canonical map* of [Stacks, Tag 08I3]: with `R`
restriction to an open, `E` extension by zero, and the projection formula
[Stacks, Tag 0GL1], it says that the transpose of the restricted evaluation morphism is an
isomorphism. It applies just as well when `R` is an equivalence, with `E` its inverse.

## Main results

* `CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective`: the comparison is an
  isomorphism.
* `CategoryTheory.InternalHomTransfer.isIso_map_iff_of_tensorHomBijective`: consequently `R`
  carries the evaluation morphism `e` to an isomorphism exactly when `e'` is one.

## Implementation notes

The proof is Yoneda's lemma. Postcomposition with `t` on morphisms out of `Z`, followed by the
bijection of `H'`, is `g ↦ (g ⊗ 1) ≫ c⁻¹ ≫ R e`. Entered through the adjunction, this becomes
`f ↦ p ≫ R((f ⊗ 1) ≫ e)` for an isomorphism `p : Z ⊗ R L ⟶ R(E Z ⊗ L)` built from the unit and
from `c`, which is bijective because the bijection of `H` is and because, through the projection
formula and the unit at `Z ⊗ R L`, applying `R` to morphisms out of `E Z ⊗ L` is the adjunction
bijection up to isomorphisms. Only the existence of the projection isomorphism is used, never a
formula for it.

Tensor products are taken as bifunctors rather than as monoidal structures, so that the
statement can be read at a tensor bifunctor that is not, or not syntactically, the tensor
product of a monoidal structure.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.InternalHomTransfer

variable {C D : Type*} [Category C] [Category D]
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) {R : C ⥤ D} {E : D ⥤ C} (adj : E ⊣ R)
  (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))

/-- Postcomposition with an isomorphism is a bijection. -/
lemma bijective_comp_left {X Y Z : D} (σ : X ⟶ Y) [IsIso σ] :
    Function.Bijective (fun y : Y ⟶ Z => σ ≫ y) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun y => inv σ ≫ y, fun y => by simp, fun y => by simp⟩

omit TC TD c in
/-- Applying `R` to morphisms out of an object isomorphic to `E W`, after an isomorphism
`W ⟶ R A`, is a bijection, when the unit of `E ⊣ R` is an isomorphism. -/
lemma bijective_map_comp [IsIso adj.unit] {W : D} {A M : C} (p : W ⟶ R.obj A) [IsIso p]
    (ρ : A ≅ E.obj W) : Function.Bijective (fun h : A ⟶ M => p ≫ R.map h) := by
  have h3 : (fun h : A ⟶ M => p ≫ R.map h) =
      (fun y => (p ≫ R.map ρ.hom ≫ inv (adj.unit.app W)) ≫ y) ∘ (adj.homEquiv W M) ∘
        (fun h => ρ.inv ≫ h) := by
    funext h
    rw [Function.comp_apply, Function.comp_apply, Adjunction.homEquiv_unit, R.map_comp,
      Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, ← R.map_comp_assoc,
      Iso.hom_inv_id, R.map_id, Category.id_comp]
  rw [h3]
  exact (bijective_comp_left _).comp ((adj.homEquiv W M).bijective.comp
    (bijective_comp_left ρ.inv))

/-- **The comparison of internal homs along `R` is an isomorphism.** With the hypotheses of the
module documentation, the morphism `t : R H ⟶ H'` whose transpose under the bijection of `H'`
is `c⁻¹ ≫ R e` is an isomorphism. -/
theorem isIso_of_tensorHomBijective [IsIso adj.unit]
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    (ρ : ∀ (Z : D) (L : C), (TC.obj (E.obj Z)).obj L ≅ E.obj ((TD.obj Z).obj (R.obj L)))
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
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
  -- the transported map, entered through the adjunction
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
  have : IsIso p := by
    dsimp only [p]
    infer_instance
  exact (bijective_map_comp adj p (ρ Z L)).comp (he (E.obj Z))

/-- **`R` carries the evaluation morphism to an isomorphism exactly when the evaluation morphism
of the images is one.** The comparison `t` of `isIso_of_tensorHomBijective` is an isomorphism,
and `(t ⊗ 1) ≫ e' = c⁻¹ ≫ R e`. -/
theorem isIso_map_iff_of_tensorHomBijective [IsIso adj.unit]
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    (ρ : ∀ (Z : D) (L : C), (TC.obj (E.obj Z)).obj L ≅ E.obj ((TD.obj Z).obj (R.obj L)))
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (R.obj L) ⟶ R.obj M)
    (he' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e'))
    (t : R.obj H ⟶ H')
    (ht : (TD.map t).app (R.obj L) ≫ e' = (c H L).inv ≫ R.map e) :
    IsIso (R.map e) ↔ IsIso e' := by
  have := isIso_of_tensorHomBijective TC TD adj c hc ρ e he e' he' t ht
  rw [show R.map e = (c H L).hom ≫ (TD.map t).app (R.obj L) ≫ e' by
    rw [ht, Iso.hom_inv_id_assoc], isIso_comp_left_iff, isIso_comp_left_iff]

/-- **The comparison exists, and is an isomorphism.** The surjectivity of the bijection of `H'`
supplies a morphism `t : R H ⟶ H'` whose transpose is `c⁻¹ ≫ R e`, and
`isIso_of_tensorHomBijective` makes it an isomorphism; with it, `R e` is an isomorphism exactly
when `e'` is. -/
theorem exists_iso_and_isIso_map_iff [IsIso adj.unit]
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    (ρ : ∀ (Z : D) (L : C), (TC.obj (E.obj Z)).obj L ≅ E.obj ((TD.obj Z).obj (R.obj L)))
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (R.obj L) ⟶ R.obj M)
    (he' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e')) :
    Nonempty (R.obj H ≅ H') ∧ (IsIso (R.map e) ↔ IsIso e') := by
  obtain ⟨t, ht⟩ := (he' (R.obj H)).surjective ((c H L).inv ≫ R.map e)
  have := isIso_of_tensorHomBijective TC TD adj c hc ρ e he e' he' t ht
  exact ⟨⟨asIso t⟩, isIso_map_iff_of_tensorHomBijective TC TD adj c hc ρ e he e' he' t ht⟩

/-- **Internal homs along an equivalence.** If `eq : C ≌ D` carries tensor products to tensor
products, naturally in the first variable, then it carries an internal hom from `L` to `M` to
one from `eq L` to `eq M`, and an evaluation morphism is an isomorphism exactly when the
evaluation morphism of the images is. The left adjoint is the inverse equivalence, and the
projection isomorphism is produced from `c` and the two isomorphisms of the equivalence. -/
theorem exists_iso_and_isIso_iff_of_equivalence (eq : C ≌ D)
    (c : ∀ A B, eq.functor.obj ((TC.obj A).obj B) ≅
      (TD.obj (eq.functor.obj A)).obj (eq.functor.obj B))
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      eq.functor.map ((TC.map f).app B) ≫ (c A' B).hom =
        (c A B).hom ≫ (TD.map (eq.functor.map f)).app (eq.functor.obj B))
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (eq.functor.obj L) ⟶ eq.functor.obj M)
    (he' : ∀ Z, Function.Bijective
      (fun g : Z ⟶ H' => (TD.map g).app (eq.functor.obj L) ≫ e')) :
    Nonempty (eq.functor.obj H ≅ H') ∧ (IsIso e ↔ IsIso e') := by
  let adj : eq.inverse ⊣ eq.functor := eq.symm.toAdjunction
  have : IsIso adj.unit := inferInstanceAs (IsIso eq.counitIso.inv)
  let ρ : ∀ (Z : D) (L : C), (TC.obj (eq.inverse.obj Z)).obj L ≅
      eq.inverse.obj ((TD.obj Z).obj (eq.functor.obj L)) := fun Z L =>
    eq.unitIso.app _ ≪≫ eq.inverse.mapIso
      (c (eq.inverse.obj Z) L ≪≫ (TD.mapIso (eq.counitIso.app Z)).app (eq.functor.obj L))
  obtain ⟨h1, h2⟩ := exists_iso_and_isIso_map_iff TC TD adj c hc ρ e he e' he'
  refine ⟨h1, ?_⟩
  rw [← h2]
  exact ⟨fun _ => inferInstance, fun _ => isIso_of_fully_faithful eq.functor e⟩

/-- `exists_iso_and_isIso_iff_of_equivalence` with the tensor comparison given as an isomorphism
of bifunctors, in the shape `TC ⋙ (- ⋙ R) ≅ R ⋙ TD ⋙ (R ⋙ -)`, so that its naturality in the
first variable is part of the datum. -/
theorem exists_iso_and_isIso_iff_of_equivalence_of_natIso (eq : C ≌ D)
    (α : TC ⋙ (Functor.whiskeringRight C C D).obj eq.functor ≅
      eq.functor ⋙ TD ⋙ (Functor.whiskeringLeft C D D).obj eq.functor)
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (eq.functor.obj L) ⟶ eq.functor.obj M)
    (he' : ∀ Z, Function.Bijective
      (fun g : Z ⟶ H' => (TD.map g).app (eq.functor.obj L) ≫ e')) :
    Nonempty (eq.functor.obj H ≅ H') ∧ (IsIso e ↔ IsIso e') :=
  exists_iso_and_isIso_iff_of_equivalence TC TD eq (fun A B => (α.app A).app B)
    (fun f B => NatTrans.congr_app (α.hom.naturality f) B) e he e' he'

/-- **Internal homs for isomorphic pairs.** If `H` is an internal hom from `L` to `M` through
`e` and `H'` one from `L'` to `M'` through `e'`, and `L ≅ L'`, `M ≅ M'`, then `H ≅ H'`, and `e`
is an isomorphism exactly when `e'` is. -/
theorem exists_iso_and_isIso_iff_of_iso (T : C ⥤ C ⥤ C) {L L' M M' H H' : C}
    (a : L ≅ L') (b : M ≅ M')
    (e : (T.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (T.map g).app L ≫ e))
    (e' : (T.obj H').obj L' ⟶ M')
    (he' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (T.map g).app L' ≫ e')) :
    Nonempty (H ≅ H') ∧ (IsIso e ↔ IsIso e') := by
  let e'' : (T.obj H').obj L ⟶ M := (T.obj H').map a.hom ≫ e' ≫ b.inv
  have he'' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (T.map g).app L ≫ e'') := by
    intro Z
    have hfun : (fun g : Z ⟶ H' => (T.map g).app L ≫ e'') =
        (fun y => (T.obj Z).map a.hom ≫ y) ∘ (fun y => y ≫ b.inv) ∘
          (fun g : Z ⟶ H' => (T.map g).app L' ≫ e') := by
      funext g
      simp only [Function.comp_apply, e'', Category.assoc]
      rw [← NatTrans.naturality_assoc]
    rw [hfun]
    exact (bijective_comp_left _).comp
      ((Function.bijective_iff_has_inverse.2
        ⟨fun y => y ≫ b.hom, fun y => by simp, fun y => by simp⟩).comp (he' Z))
  obtain ⟨h1, h2⟩ := exists_iso_and_isIso_iff_of_equivalence T T (Equivalence.refl)
    (fun A B => Iso.refl _)
    (fun f B => by
      change (T.map f).app B ≫ 𝟙 _ = 𝟙 _ ≫ (T.map f).app B
      simp) e he e'' he''
  refine ⟨h1, h2.trans ?_⟩
  change IsIso ((T.obj H').map a.hom ≫ e' ≫ b.inv) ↔ IsIso e'
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

end CategoryTheory.InternalHomTransfer
