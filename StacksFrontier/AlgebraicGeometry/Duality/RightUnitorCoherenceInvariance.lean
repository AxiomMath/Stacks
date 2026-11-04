module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The right-unitor coherence of a comparison of bifunctors depends only on the isomorphism class

`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` derives
invertibility of the abstract projection-formula morphism at the unit object from one equation,
its *right-unitor coherence*: for a functor `L : C ⥤ D`, bifunctors `A` on `C` and `B` on `D`, a
morphism of bifunctors `α : A ⋙ L ⟶ (L × L) ⋙ B`, right unitors `ρA`, `ρB` for `A` and `B` at
unit objects `eC`, `eD`, and a unit comparison `ν : L(eC) ≅ eD`, the equation

`α.app (Z, eC) ≫ B(𝟙, ν) ≫ ρB(L Z) = L(ρA Z)`

at every object `Z` of `C`.  That equation has to be verified at an arbitrary `Z`, whereas the
comparisons it is built from are usually only *computable* on a distinguished class of objects —
the images of a localization, or of a subcategory of resolutions.  This file closes that gap: the
equation is invariant under isomorphism in `Z`, so it suffices to verify it on any essentially
surjective family.

Both statements are pure category theory: no additivity, no abelian structure, no monoidal
structure and no adjunction between `L` and anything.  In particular `L` is not assumed to have a
right adjoint, even though the consumer of the equation does.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherenceHom_of_iso`: the coherence
  transports backwards along an isomorphism `Z ≅ Z'`.
* `Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherenceHom_of_essSurj`: if the
  coherence holds at every object in the image of an essentially surjective functor `G : E ⥤ C`,
  it holds at every object of `C`.
* `Stacks.AlgebraicGeometry.ProjectionFormula.rightUnitorCoherence_of_iso` and
  `rightUnitorCoherence_of_essSurj`: the same two statements for a unit comparison presented as
  an isomorphism, which is the shape
  `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` consumes.

## Implementation notes

*The two naturality hypotheses are exactly the ones the consumer already carries.*  `hρB` is
verbatim the hypothesis `hρB` of
`Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_unitObj_comp`; `hρA` is its
mirror on `C`, and a right unitor presented as a natural isomorphism supplies both by
`CategoryTheory.NatTrans.naturality`.  Nothing else is needed: the transport is the naturality
square of `α` in the first variable pasted against those two, with `L` of the isomorphism
cancelled at the end.

*Why the proof cancels a monomorphism rather than rewriting forwards.*  The three naturality
squares move the isomorphism `L(i)` from the left of the equation to the right, so what they
prove is the wanted equation *composed with* `L(i.hom)`.  That morphism is invertible, hence a
monomorphism, so `CategoryTheory.cancel_mono` removes it; rewriting the goal directly would need
`L(i.inv)` inserted in three places first.

*The product morphisms are ascribed.*  Each `u ×ₘ 𝟙` carries an explicit type ascription naming
its source and target in the product category.  Without it the elaborator has to infer the pair
objects from the bifunctor's expected argument, which it does not do uniformly for `B` and for
`A`; with it the statements match the shape
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` consumes
syntactically.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open CategoryTheory

open scoped CategoryTheory.Prod

namespace Stacks.AlgebraicGeometry.ProjectionFormula

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {eC : C} {eD : D} (ρA : ∀ Z : C, A.obj (Z, eC) ≅ Z) (ρB : ∀ W : D, B.obj (W, eD) ≅ W)
  (ν : L.obj eC ≅ eD)

section OfHom

/-- **The right-unitor coherence transports backwards along an isomorphism of the object.**  If
it holds at `Z'` and `i : Z ≅ Z'`, it holds at `Z`.  The unit comparison `ν` is a morphism, not
an isomorphism: nothing below inverts it.

The proof is the naturality square of `α` at `(i.hom, 𝟙 eC)`, pasted against the naturality of
the two right unitors; the three together prove the wanted equation composed with the isomorphism
`L(i.hom)`, which is then cancelled. -/
theorem rightUnitorCoherenceHom_of_iso (ν : L.obj eC ⟶ eD)
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC)) ≫ (ρA Z').hom = (ρA Z).hom ≫ u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom = (ρB W).hom ≫ u)
    {Z Z' : C} (i : Z ≅ Z')
    (h : α.app (Z', eC) ≫ B.map ((𝟙 (L.obj Z') ×ₘ ν) :
          ((L.obj Z', L.obj eC) : D × D) ⟶ (L.obj Z', eD)) ≫ (ρB (L.obj Z')).hom =
        L.map (ρA Z').hom) :
    α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom := by
  have hL : IsIso (L.map i.hom) := (L.mapIso i).isIso_hom
  have hα := α.naturality ((i.hom ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC))
  dsimp only [Functor.comp_map, Functor.prod_map] at hα
  rw [CategoryTheory.Functor.map_id] at hα
  have hmid : B.map ((L.map i.hom ×ₘ 𝟙 (L.obj eC)) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z', L.obj eC)) ≫
      B.map ((𝟙 (L.obj Z') ×ₘ ν) :
        ((L.obj Z', L.obj eC) : D × D) ⟶ (L.obj Z', eD)) =
      B.map ((𝟙 (L.obj Z) ×ₘ ν) :
          ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫
        B.map ((L.map i.hom ×ₘ 𝟙 eD) : ((L.obj Z, eD) : D × D) ⟶ (L.obj Z', eD)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Prod.ext <;> simp
  apply (cancel_mono (L.map i.hom)).1
  calc (α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν) :
          ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom) ≫ L.map i.hom
      = α.app (Z, eC) ≫ B.map ((L.map i.hom ×ₘ 𝟙 (L.obj eC)) :
            ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z', L.obj eC)) ≫
          B.map ((𝟙 (L.obj Z') ×ₘ ν) :
            ((L.obj Z', L.obj eC) : D × D) ⟶ (L.obj Z', eD)) ≫ (ρB (L.obj Z')).hom := by
        rw [← Category.assoc (B.map _), hmid, Category.assoc, Category.assoc, Category.assoc,
          hρB (L.map i.hom)]
    _ = L.map (A.map ((i.hom ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC))) ≫ L.map (ρA Z').hom := by
        rw [← Category.assoc, ← hα, Category.assoc, h]
    _ = L.map (ρA Z).hom ≫ L.map i.hom := by
        rw [← Functor.map_comp, hρA i.hom, Functor.map_comp]

/-- **The right-unitor coherence needs checking only on an essentially surjective family.**  If
it holds at `G.obj e` for every object `e` of `E`, and `G : E ⥤ C` is essentially surjective,
then it holds at every object of `C`.  The unit comparison `ν` is a morphism, not an
isomorphism.

This is what makes the equation checkable: the comparisons it is built from are descended from a
distinguished class of objects — K-flat complexes, or the images of a localization — and
`CategoryTheory.Functor.objObjPreimageIso` is the isomorphism `rightUnitorCoherenceHom_of_iso`
consumes. -/
theorem rightUnitorCoherenceHom_of_essSurj (ν : L.obj eC ⟶ eD) {E : Type u₃} [Category.{v₃} E]
    (G : E ⥤ C) [G.EssSurj]
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC)) ≫ (ρA Z').hom = (ρA Z).hom ≫ u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom = (ρB W).hom ≫ u)
    (h : ∀ e : E, α.app (G.obj e, eC) ≫ B.map ((𝟙 (L.obj (G.obj e)) ×ₘ ν) :
          ((L.obj (G.obj e), L.obj eC) : D × D) ⟶ (L.obj (G.obj e), eD)) ≫
            (ρB (L.obj (G.obj e))).hom = L.map (ρA (G.obj e)).hom) (Z : C) :
    α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom :=
  rightUnitorCoherenceHom_of_iso A B α ρA ρB ν hρA hρB (G.objObjPreimageIso Z).symm
    (h (G.objPreimage Z))

end OfHom

/-- **The right-unitor coherence transports backwards along an isomorphism of the object.**  If
it holds at `Z'` and `i : Z ≅ Z'`, it holds at `Z`.

This is `rightUnitorCoherenceHom_of_iso` at the underlying morphism of the unit comparison; the
invertibility of `ν` plays no part in it, and is carried only because the consumer
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj` needs it. -/
theorem rightUnitorCoherence_of_iso
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC)) ≫ (ρA Z').hom = (ρA Z).hom ≫ u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom = (ρB W).hom ≫ u)
    {Z Z' : C} (i : Z ≅ Z')
    (h : α.app (Z', eC) ≫ B.map ((𝟙 (L.obj Z') ×ₘ ν.hom) :
          ((L.obj Z', L.obj eC) : D × D) ⟶ (L.obj Z', eD)) ≫ (ρB (L.obj Z')).hom =
        L.map (ρA Z').hom) :
    α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom :=
  rightUnitorCoherenceHom_of_iso A B α ρA ρB ν.hom hρA hρB i h

/-- **The right-unitor coherence needs checking only on an essentially surjective family.**  If
it holds at `G.obj e` for every object `e` of `E`, and `G : E ⥤ C` is essentially surjective,
then it holds at every object of `C`.

This is what makes the equation checkable: the comparisons it is built from are descended from a
distinguished class of objects — K-flat complexes, or the images of a localization — and
`CategoryTheory.Functor.objObjPreimageIso` is the isomorphism `rightUnitorCoherence_of_iso`
consumes. -/
theorem rightUnitorCoherence_of_essSurj {E : Type u₃} [Category.{v₃} E] (G : E ⥤ C) [G.EssSurj]
    (hρA : ∀ {Z Z' : C} (u : Z ⟶ Z'),
      A.map ((u ×ₘ 𝟙 eC) : ((Z, eC) : C × C) ⟶ (Z', eC)) ≫ (ρA Z').hom = (ρA Z).hom ≫ u)
    (hρB : ∀ {W W' : D} (u : W ⟶ W'),
      B.map ((u ×ₘ 𝟙 eD) : ((W, eD) : D × D) ⟶ (W', eD)) ≫ (ρB W').hom = (ρB W).hom ≫ u)
    (h : ∀ e : E, α.app (G.obj e, eC) ≫ B.map ((𝟙 (L.obj (G.obj e)) ×ₘ ν.hom) :
          ((L.obj (G.obj e), L.obj eC) : D × D) ⟶ (L.obj (G.obj e), eD)) ≫
            (ρB (L.obj (G.obj e))).hom = L.map (ρA (G.obj e)).hom) (Z : C) :
    α.app (Z, eC) ≫ B.map ((𝟙 (L.obj Z) ×ₘ ν.hom) :
        ((L.obj Z, L.obj eC) : D × D) ⟶ (L.obj Z, eD)) ≫ (ρB (L.obj Z)).hom =
      L.map (ρA Z).hom :=
  rightUnitorCoherenceHom_of_essSurj A B α ρA ρB ν.hom G hρA hρB h Z

end Stacks.AlgebraicGeometry.ProjectionFormula

end
