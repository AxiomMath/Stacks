module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The relative diagonal is representable exactly when its Isom presheaves are

Let `𝒞` be a category, let `p : X ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be categories fibred in groupoids over
`𝒞` and let `F : X ⥤ 𝒴` be a 1-morphism over `𝒞`. Its relative diagonal is

`Δ_F : X ⥤ X ×_{F, 𝒴, F} X`.

This file characterizes representability of `Δ_F` in the sense of Stacks 02Y7 — that is,
representability by *objects of `𝒞`* — presheaf by presheaf: `Δ_F` is a representable
1-morphism exactly when, for every object `U` of `𝒞` and every point `Y` of `X ×_𝒴 X` over the
slice `𝒞/U`, the presheaf on `𝒞/U` of vertical morphisms between the two components of `Y`
lying over the comparison isomorphism of `Y` is representable by an object of `𝒞/U`.

That presheaf is
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf`; in
sheaf-theoretic terms it is the fibre product

`Isom_X(Y₁, Y₂) ×_{Isom_𝒴(F Y₁, F Y₂), α} U`

of the cartesian square labelled 04XT in the proof of Stacks 04XS.

This is the exact counterpart, for representability by objects of the base, of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff`, which is the
same square read for representability by algebraic spaces. Neither direction uses anything
about algebraic geometry: the content is that a category fibred in groupoids over `𝒞/U` is a
slice exactly when the presheaf whose category of elements it is, is representable.

## Main results

* `Stacks.RepresentableMorphism.isRepresentableMorphism_relativeDiagonal_iff`: the criterion.
* `Stacks.RepresentableMorphism.isRepresentableMorphism_relativeDiagonal_of_forall_representable`:
  the direction a
  consumer uses.

## Implementation notes

The two inputs are
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.nonempty_equivalenceOver_fst_iff`,
which turns an equivalence over `𝒞/U` between the fibre of `Δ_F` and the category of elements of
a presheaf into an isomorphism of universe-lifted presheaves, and
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, which says that a slice
`(𝒞/U)/Z` *is* the category of elements of the presheaf on `𝒞/U` represented by `Z`. Composing
them turns the right-hand side of `nonempty_equivalenceOver_fst_iff` at a representable presheaf
into `StacksRepresentableCFG.IsRepresentable` of the fibre, which
`Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable` converts into the predicate of
  Stacks 02Y3
that Stacks 02Y7 quantifies over.

Note that the quantifier of `Stacks.RepresentableMorphism.IsRepresentableMorphism` is over the
  slice `𝒞/U` and
`Over.forget U`, not over a localization `Over.map` of it, so no iterated-slice reconciliation
(Stacks 03EH) enters: the presheaf of the criterion lives on the very category the predicate
quantifies over. A consumer whose hypotheses are stated over a localized site — as
`AlgebraicGeometry.IsRepresentableByAlgebraicSpaces` is — has to supply that comparison itself.

The statement is untagged. Stacks 04XT is the square inside the proof of Stacks 04XS and its
own statement is about algebraic stacks; the criterion below is a statement of general category
theory, as its hypotheses show.

## References

* [Stacks Project, Tag 02Y3](https://stacks.math.columbia.edu/tag/02Y3)
* [Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoFibreProductOver
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace Stacks.RepresentableMorphism

universe v₁ u₁ v₃ u₃ v₄ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒴 : Type u₄} [Category.{v₄} 𝒴] {p : X ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}

/-- **The relative diagonal criterion for representability by objects of the base.** The
relative diagonal of a 1-morphism `F` of categories fibred in groupoids over `𝒞` is a
representable 1-morphism in the sense of Stacks 02Y7 if and only if, for every object `U` of
`𝒞` and every point `Y` of `X ×_𝒴 X` over the slice `𝒞/U`, the presheaf of vertical morphisms
between the two components of `Y` lying over the comparison isomorphism of `Y` is representable
by an object of `𝒞/U`. -/
theorem isRepresentableMorphism_relativeDiagonal_iff (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p) :
    IsRepresentableMorphism p (RelProdP p q F) (RelDiag hF) ↔
      ∀ (U : 𝒞) (Y : Over U ⥤ RelProd p q F)
        (hY : Y ⋙ RelProdP p q F = Over.forget U),
        ∃ Z : Over U,
          Nonempty (relVertHomPresheaf hq hp hY hF ⋙ uliftFunctor.{v₁, v₃} ≅
            yoneda.obj Z ⋙ uliftFunctor.{v₃, v₁}) := by
  have hdiag : RelDiag (p := p) (q := q) (F := F) hF ⋙ RelProdP p q F = p := rfl
  have hrp : (RelProdP p q F).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p p q F F hp hp hq hF hF
  constructor
  · intro hrep U Y hY
    obtain ⟨Z, E, hE⟩ := hrep U Y hY
    obtain ⟨Ginv, hGinv, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
    obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (TwoFibreProductOver.fst_isFiberedInGroupoids U p (RelProdP p q F) (RelDiag hF) Y hp hrp
        hdiag hY)
      (StacksRepresentableCFG.over_isFiberedInSetoids Z).isFiberedInGroupoids E
      hE.isCartesianFunctor.comm
      (CategoryTheory.Equivalence.mk E Ginv ε.symm η).isEquivalence_functor
    exact ⟨Z, (nonempty_equivalenceOver_fst_iff hq hp hY hF (yoneda.obj Z)).1
      ⟨k.trans (PresheafOfCategories.sliceElementsEquivalenceOver Z)⟩⟩
  · intro h U Y hY
    obtain ⟨Z, hiso⟩ := h U Y hY
    obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff hq hp hY hF (yoneda.obj Z)).2 hiso
    exact isRepresentableCFG_of_isRepresentable _
      ⟨Z, ⟨e.trans (PresheafOfCategories.sliceElementsEquivalenceOver Z).symm⟩⟩

/-- **The relative diagonal criterion, in the direction a consumer uses.** If every Isom presheaf
of the relative diagonal of `F` is representable by an object of the slice it lives on, then the
relative diagonal is a representable 1-morphism in the sense of Stacks 02Y7. -/
theorem isRepresentableMorphism_relativeDiagonal_of_forall_representable
    (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids) (hF : F ⋙ q = p)
    (h : ∀ (U : 𝒞) (Y : Over U ⥤ RelProd p q F)
      (hY : Y ⋙ RelProdP p q F = Over.forget U),
      ∃ Z : Over U,
        Nonempty (relVertHomPresheaf hq hp hY hF ⋙ uliftFunctor.{v₁, v₃} ≅
          yoneda.obj Z ⋙ uliftFunctor.{v₃, v₁})) :
    IsRepresentableMorphism p (RelProdP p q F) (RelDiag hF) :=
  (isRepresentableMorphism_relativeDiagonal_iff hq hp hF).2 h

end Stacks.RepresentableMorphism

end
