module

public import StacksFrontier.CategoryTheory.Triangulated.LocalizingQuotient
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.CategoryTheory.Triangulated.VerdierLocalizing

/-!
# The embedding of a Verdier quotient induced by a left localizing subcategory

Let `C` be a triangulated category, let `N : ObjectProperty C` be a strictly full triangulated
subcategory and let `A : ObjectProperty C` be another one. The inclusion `A.ι` composed with
the quotient functor `C ⥤ C/N` kills every object of `N.inverseImage A.ι`, so it descends
along any localization `L : A.FullSubcategory ⥤ D` of `A` at `(N.inverseImage A.ι).trW` to a
functor

`J : D ⟶ C/N`,

which is exact, together with an isomorphism `L ⋙ J ≅ A.ι ⋙ N.trW.Q`. The functor `J` is
fully faithful as soon as `A` is left `N`-localizing in the sense of Verdier, which
`ObjectProperty.isVerdierLeftLocalizing_localizingClosure` supplies when `N` is generated as a
localizing subcategory by objects into which the morphisms from `A` are controlled and every
object of `A` is compact.

The source `D` of `J` is the Verdier quotient `A/(A ⊓ N)`: the morphisms inverted are those of
`(N.inverseImage A.ι).trW`, which by `ObjectProperty.trW_inverseImage_ι_iff` are the morphisms
of `A` whose cone lies in `A ⊓ N`.

## Main definitions

* `CategoryTheory.ObjectProperty.verdierEmbedding`: the functor `J`.
* `CategoryTheory.ObjectProperty.verdierEmbeddingCompIso`: its characteristic isomorphism.

## Main results

* `CategoryTheory.ObjectProperty.isTriangulated_verdierEmbedding`: `J` is exact.
* `CategoryTheory.ObjectProperty.fullyFaithfulVerdierEmbedding`: `J` is fully faithful when `A`
  is left `N`-localizing.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

open Category Limits Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (A N : ObjectProperty C) [A.IsClosedUnderIsomorphisms] [A.IsTriangulated]
  [N.IsClosedUnderIsomorphisms] [N.IsTriangulated]

omit [N.IsClosedUnderIsomorphisms] in
/-- An object of a strictly full triangulated subcategory `N` is killed by the Verdier quotient
functor `C ⥤ C/N`, by the minimality half of [Stacks, Tag 05RK]. -/
lemma isZero_trW_Q_obj {X : C} (hX : N X) : IsZero (N.trW.Q.obj X) :=
  (kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel N N.trW.Q).2.1.2.2.2 X hX

variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (L : A.FullSubcategory ⥤ D) [L.IsLocalization (N.inverseImage A.ι).trW] [L.CommShift ℤ]
  [L.IsTriangulated]

omit [A.IsClosedUnderIsomorphisms] [A.IsTriangulated] [N.IsClosedUnderIsomorphisms] in
/-- The composition of `A.ι` with the Verdier quotient functor kills `N.inverseImage A.ι`. -/
lemma isZero_ι_comp_trW_Q_obj (X : A.FullSubcategory) (hX : (N.inverseImage A.ι) X) :
    IsZero ((A.ι ⋙ N.trW.Q).obj X) :=
  isZero_trW_Q_obj N hX

/-- **The functor `J : A/(A ⊓ N) ⥤ C/N`.** It is the descent of `A.ι ⋙ N.trW.Q` through the
localization `L` of `A.FullSubcategory` at `(N.inverseImage A.ι).trW`. -/
noncomputable def verdierEmbedding : D ⥤ N.trW.Localization :=
  (N.inverseImage A.ι).descend L (A.ι ⋙ N.trW.Q) (isZero_ι_comp_trW_Q_obj A N)

/-- Restricting `ObjectProperty.verdierEmbedding` along `L` gives back `A.ι ⋙ N.trW.Q`. -/
noncomputable def verdierEmbeddingCompIso :
    L ⋙ verdierEmbedding A N L ≅ A.ι ⋙ N.trW.Q :=
  (N.inverseImage A.ι).descendCompIso L (A.ι ⋙ N.trW.Q) (isZero_ι_comp_trW_Q_obj A N)

/-- `ObjectProperty.verdierEmbedding` is a lifting of `A.ι ⋙ N.trW.Q` along the localization
`L` at `(N.inverseImage A.ι).trW`. -/
noncomputable instance :
    Localization.Lifting L (N.inverseImage A.ι).trW (A.ι ⋙ N.trW.Q) (verdierEmbedding A N L) :=
  inferInstanceAs (Localization.Lifting L (N.inverseImage A.ι).trW (A.ι ⋙ N.trW.Q)
    ((N.inverseImage A.ι).descend L (A.ι ⋙ N.trW.Q) (isZero_ι_comp_trW_Q_obj A N)))

omit [A.IsClosedUnderIsomorphisms] in
/-- `ObjectProperty.verdierEmbedding` is exact, for the commutation with the shift that the
factorization through `L` induces on it. -/
theorem isTriangulated_verdierEmbedding :
    letI := Functor.commShiftOfLocalization L (N.inverseImage A.ι).trW ℤ (A.ι ⋙ N.trW.Q)
      (verdierEmbedding A N L)
    (verdierEmbedding A N L).IsTriangulated :=
  (N.inverseImage A.ι).isTriangulated_descend L (A.ι ⋙ N.trW.Q) (isZero_ι_comp_trW_Q_obj A N)

/-- **`ObjectProperty.verdierEmbedding` is fully faithful when `A` is left `N`-localizing.**
This is Verdier's theorem, [Verdier, Proposition II.2.3.5]. -/
noncomputable def fullyFaithfulVerdierEmbedding [A.IsVerdierLeftLocalizing N] :
    (verdierEmbedding A N L).FullyFaithful :=
  IsVerdierLeftLocalizing.fullyFaithful (A := A) (B := N) (verdierEmbeddingCompIso A N L)

end CategoryTheory.ObjectProperty

end
