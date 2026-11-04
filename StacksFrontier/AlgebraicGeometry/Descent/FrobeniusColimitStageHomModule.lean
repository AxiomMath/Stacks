module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictHom

/-!
# The comparison of Stacks Tag 0EXB on Hom-sets, read on underlying modules

Let `p` be a prime and let `X` be a scheme in characteristic `p`. The comparison of Stacks Tag
0EXB on Hom-sets is `AlgebraicGeometry.frobeniusStageHomMap`, which lives in `Vect(X)` and in the
finite locally free modules over `colim_F 𝒪_X`;
`AlgebraicGeometry.frobeniusStageModuleHomMap` is the same comparison with both categories
replaced by all modules, and with the comparison of the stage functors replaced by
`CategoryTheory.Adjunction.leftAdjointUniq`. This file identifies the two: **the underlying
morphism of modules of `frobeniusStageHomMap` is `frobeniusStageModuleHomMap` of the underlying
morphism of modules.**

The transport `AlgebraicGeometry.ι_frobeniusPullbackIter_obj` enters because the `Vect(X)`-level
iterate of Frobenius pullback and the iterate of extension of scalars along the `p`-th power
endomorphism of the structure sheaf are equal and not definitionally equal, so a morphism of the
`j`-fold Frobenius pullbacks is a morphism of the `j`-fold extensions of scalars only after being
conjugated with that equality.

## Main definitions

* `AlgebraicGeometry.frobeniusPullbackIterHom`: a morphism of the `j`-fold Frobenius pullbacks of
  two finite locally free modules, read as a morphism of the `j`-fold extensions of scalars of
  their underlying modules.

## Main results

* `AlgebraicGeometry.ι_map_frobeniusStageFunctorIterIso_inv_app`: the inverse half of
  `AlgebraicGeometry.ι_map_frobeniusStageFunctorIterIso_hom_app`.
* `AlgebraicGeometry.frobeniusStageHomMap_hom`: **the comparison of Tag 0EXB on Hom-sets, read on
  underlying modules, is `AlgebraicGeometry.frobeniusStageModuleHomMap`.** This is what allows the
  colimit of the diagram of
  `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictDiagram`, which is a statement
  about all modules, to be read as a statement about the Hom-sets of `Vect(X)`.

## Implementation notes

Every goal below mentions an object of `X.Vect`, and such a goal is type-incorrect at the
transparency at which `rw` and `simp` match: `AlgebraicGeometry.Scheme.Vect` is a full subcategory
of `AlgebraicGeometry.Scheme.Modules`, whose `CategoryTheory.Category` instance is not
`SheafOfModules.instCategory`, while the object property feeds `X.ringCatSheaf` to
`SheafOfModules.IsFiniteLocallyFree`, which asks for a sheaf on the site of opens. So the category
algebra here is done by stating each identity abstractly and closing the goal with `exact`:
`CategoryTheory.eq_inv_of_comp_eq_id` and
`CategoryTheory.comp_eqToHom_comp_eqToHom_comp_eq_id` for the inverse half, and
`CategoryTheory.Functor.map_eqToHom_conj_eq` for the conjugation.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v v₂ u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **A one-sided inverse on each side determines the morphism.** If `c ≫ a` and `a ≫ b` are both
identities then `b = c`; this is the uniqueness of inverses, in the form in which the inverse half
of an isomorphism of a full subcategory is computed from the known value of its forward half. -/
lemma eq_inv_of_comp_eq_id {A B : C} {a : A ⟶ B} {b c : B ⟶ A} (h₁ : c ≫ a = 𝟙 B)
    (h₂ : a ≫ b = 𝟙 A) : b = c := by
  rw [← Category.id_comp b, ← h₁, Category.assoc, h₂, Category.comp_id]

/-- **A pair of mutually inverse morphisms, conjugated by a transport, is still a pair of mutually
inverse morphisms.** -/
lemma comp_eqToHom_comp_eqToHom_comp_eq_id {A Y Y' : C} (u : A ⟶ Y') (v : Y' ⟶ A) (e : Y' = Y)
    (h : u ≫ v = 𝟙 A) : (u ≫ eqToHom e) ≫ (eqToHom e.symm ≫ v) = 𝟙 A := by
  subst e
  rw [eqToHom_refl, Category.comp_id, Category.id_comp, h]

/-- **Two equal functors applied to a morphism, conjugated by transports with the same endpoints,
agree.** The two transports are not required to be the same term: any two proofs of an equality of
objects give the same `CategoryTheory.eqToHom`. -/
lemma Functor.map_eqToHom_conj_eq {D : Type u₂} [Category.{v₂} D] {F₁ F₂ : C ⥤ D} (hF : F₁ = F₂)
    {P₀ Q₀ P Q : C} (a : P₀ = P) (b : Q₀ = Q) (h : P₀ ⟶ Q₀)
    (a' : F₁.obj P₀ = F₂.obj P) (b' : F₁.obj Q₀ = F₂.obj Q) :
    eqToHom a'.symm ≫ F₁.map h ≫ eqToHom b' = F₂.map (eqToHom a.symm ≫ h ≫ eqToHom b) := by
  subst hF; subst a; subst b
  rw [eqToHom_refl, eqToHom_refl, eqToHom_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id, Category.id_comp, Category.comp_id]

/-- **Conjugating the image of a morphism by two transports is taking the image of the morphism
conjugated by them.** This is the shape in which the comparison of Stacks Tag 0EXB on Hom-sets is
compared with the one on all modules: both are a morphism of modules between the stage-`n + j`
extensions of scalars, framed by the comparisons of left adjoints, and the two frames differ by
the transport comparing the two iterates of Frobenius. -/
lemma Functor.comp_eqToHom_comp_map_comp_eqToHom_comp {D : Type u₂} [Category.{v₂} D] (T : C ⥤ D)
    {P P' Q Q' : C} (eP : P = P') (eQ : Q = Q') (h : P ⟶ Q) {A B : D} (a : A ⟶ T.obj P')
    (b : T.obj Q' ⟶ B) :
    (a ≫ eqToHom (congrArg T.obj eP).symm) ≫ (T.map h ≫ (eqToHom (congrArg T.obj eQ) ≫ b)) =
      a ≫ T.map (eqToHom eP.symm ≫ h ≫ eqToHom eQ) ≫ b := by
  subst eP; subst eQ
  simp

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **A morphism of the `j`-fold Frobenius pullbacks of two finite locally free modules, read as a
morphism of the `j`-fold extensions of scalars of their underlying modules.** The transport is
`AlgebraicGeometry.ι_frobeniusPullbackIter_obj`. -/
noncomputable def frobeniusPullbackIterHom (j : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX j).obj E ⟶ (frobeniusPullbackIter X p hX j).obj G) :
    ((frobeniusExtendScalars X p hX).endoIter j).obj E.obj ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G.obj :=
  eqToHom (ι_frobeniusPullbackIter_obj X p hX j E).symm ≫
    f.hom ≫ eqToHom (ι_frobeniusPullbackIter_obj X p hX j G)

/-- **The inverse comparison of the stage functors along `j` Frobenius pullbacks, read through
`ObjectProperty.ι`, is the inverse of `CategoryTheory.Adjunction.leftAdjointUniq` of the `j`-fold
adjunction and the stage-`n` one**, followed by the transport
`AlgebraicGeometry.ι_frobeniusPullbackIter_obj`. This is the inverse half of
`AlgebraicGeometry.ι_map_frobeniusStageFunctorIterIso_hom_app`. -/
lemma ι_map_frobeniusStageFunctorIterIso_inv_app (n j : ℕ) (E : X.Vect) :
    ((frobeniusStageFunctorIterIso X p hX n j).inv.app E).hom =
      (Adjunction.leftAdjointUniq (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
            (frobeniusStageExtendScalarsAdjunction X p hX n)).inv.app E.obj ≫
        eqToHom (congrArg (frobeniusStageExtendScalars X p hX (n + j)).obj
          (ι_frobeniusPullbackIter_obj X p hX j E)).symm := by
  refine eq_inv_of_comp_eq_id ((congrArg (_ ≫ ·)
    (ι_map_frobeniusStageFunctorIterIso_hom_app X p hX n j E)).trans ?_)
    (ObjectProperty.isoHom_inv_id_hom ((frobeniusStageFunctorIterIso X p hX n j).app E))
  exact comp_eqToHom_comp_eqToHom_comp_eq_id _ _ _ (Iso.inv_hom_id_app _ E.obj)

/-- **The comparison of Stacks Tag 0EXB on Hom-sets, read on underlying modules, is the comparison
on all modules.** The underlying morphism of modules of
`AlgebraicGeometry.frobeniusStageHomMap` at `f` is
`AlgebraicGeometry.frobeniusStageModuleHomMap` at the underlying morphism of modules of `f`.

Both sides are the stage-`n + j` extension of scalars of `f`, framed by a comparison of two left
adjoints of restriction of scalars along the stage-`n` coprojection; the frames agree by
`AlgebraicGeometry.ι_map_frobeniusStageFunctorIterIso_hom_app` and its inverse half, and what
remains is to move the transport comparing the two iterates of Frobenius inside the extension of
scalars. -/
theorem frobeniusStageHomMap_hom (n j : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX j).obj E ⟶ (frobeniusPullbackIter X p hX j).obj G) :
    (frobeniusStageHomMap X p hX n j f).hom =
      frobeniusStageModuleHomMap X p hX n j (frobeniusPullbackIterHom X p hX j f) := by
  have hsplit : (frobeniusStageHomMap X p hX n j f).hom =
      ((frobeniusStageFunctorIterIso X p hX n j).inv.app E).hom ≫
        ((frobeniusStageExtendScalars X p hX (n + j)).map f.hom ≫
          ((frobeniusStageFunctorIterIso X p hX n j).hom.app G).hom) := rfl
  exact hsplit.trans ((congrArg₂ (fun x y ↦ x ≫ ((frobeniusStageExtendScalars X p hX (n + j)).map
    f.hom ≫ y)) (ι_map_frobeniusStageFunctorIterIso_inv_app X p hX n j E)
    (ι_map_frobeniusStageFunctorIterIso_hom_app X p hX n j G)).trans
    (Functor.comp_eqToHom_comp_map_comp_eqToHom_comp _
      (ι_frobeniusPullbackIter_obj X p hX j E) (ι_frobeniusPullbackIter_obj X p hX j G) _ _ _))

end AlgebraicGeometry

end
