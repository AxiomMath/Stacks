module

public import StacksFrontier.CategoryTheory.Triangulated.VerdierLocalizingQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hom groups of a Verdier quotient embedding, with the shift

Let `C` be a triangulated category and let `A`, `N` be strictly full triangulated subcategories
of it with `A` left `N`-localizing in the sense of Verdier. The functor

`J : A/(A ⊓ N) ⥤ C/N`

of `CategoryTheory.ObjectProperty.verdierEmbedding` is then fully faithful
(`CategoryTheory.ObjectProperty.fullyFaithfulVerdierEmbedding`) and exact
(`CategoryTheory.ObjectProperty.isTriangulated_verdierEmbedding`). For objects `x`, `y` of `A`
and an integer `n` this gives a bijection of Hom groups in which `J` does not appear:

`Hom_{A/(A ⊓ N)}(L x, (L y)⟦n⟧) ≃ Hom_{C/N}(Q x, (Q y)⟦n⟧)`,

where `L : A ⥤ A/(A ⊓ N)` is any localization of `A` at the morphisms whose cone lies in
`A ⊓ N` and `Q : C ⥤ C/N` is the Verdier quotient functor.

## Main definitions

* `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift`: the displayed bijection.

## Implementation notes

The target `C/N` is `N.trW.Localization`, as in
`CategoryTheory.ObjectProperty.verdierEmbedding`, while the source `A/(A ⊓ N)` is an arbitrary
localization `L`, whose morphisms may lie in a universe of their own. The commutation of `J`
with the shift is `CategoryTheory.Functor.commShiftOfLocalization`, introduced inside the
definition rather than assumed as an instance.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

open Category Limits Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (A N : ObjectProperty C) [A.IsClosedUnderIsomorphisms] [A.IsTriangulated]
  [N.IsClosedUnderIsomorphisms] [N.IsTriangulated]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (L : A.FullSubcategory ⥤ D) [L.IsLocalization (N.inverseImage A.ι).trW] [L.CommShift ℤ]
  [L.IsTriangulated]

/-- **The Hom groups of the Verdier quotient embedding.** Let `A` be left `N`-localizing in the
sense of Verdier, let `L : A ⥤ A/(A ⊓ N)` be a localization of `A` at the morphisms whose cone
lies in `A ⊓ N` and let `Q : C ⥤ C/N` be the Verdier quotient functor. Then for all objects
`x`, `y` of `A` and every integer `n`,

`Hom_{A/(A ⊓ N)}(L x, (L y)⟦n⟧) ≃ Hom_{C/N}(Q x, (Q y)⟦n⟧)`. -/
@[sga "4½ Etat_0 2.4.2" "special case"]
noncomputable def homEquivVerdierEmbeddingShift [A.IsVerdierLeftLocalizing N]
    (x y : A.FullSubcategory) (n : ℤ) :
    (L.obj x ⟶ (L.obj y)⟦n⟧) ≃ (N.trW.Q.obj x.1 ⟶ (N.trW.Q.obj y.1)⟦n⟧) :=
  letI := Functor.commShiftOfLocalization L (N.inverseImage A.ι).trW ℤ
    (A.ι ⋙ N.trW.Q) (verdierEmbedding A N L)
  (fullyFaithfulVerdierEmbedding A N L).homEquiv.trans
    (Iso.homCongr ((verdierEmbeddingCompIso A N L).app x)
      (((verdierEmbedding A N L).commShiftIso n).app (L.obj y) ≪≫
        (shiftFunctor N.trW.Localization n).mapIso ((verdierEmbeddingCompIso A N L).app y)))

end CategoryTheory.ObjectProperty

end
