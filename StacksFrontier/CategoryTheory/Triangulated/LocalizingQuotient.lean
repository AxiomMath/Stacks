module

public import StacksFrontier.CategoryTheory.Triangulated.LocalObjects
public import StacksFrontier.CategoryTheory.Triangulated.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a functor through the Verdier quotient by a localizing subcategory

Let `C` be a triangulated category and let `N : ObjectProperty C` be a triangulated
subcategory — in the intended application `N = P.localizingClosure` for a family `P` of
generators, see `StacksFrontier/CategoryTheory/Triangulated/LocalizingClosure.lean`. The Verdier
quotient `C/N` is the localization of `C` at the class `N.trW` of morphisms whose cone lies in
`N`, and Mathlib already supplies everything about it that is needed here:

* `ObjectProperty.trW` and the fact that it has calculus of left and right fractions and is
  compatible with the triangulation, for `C` triangulated and `N` a triangulated subcategory;
* the pretriangulated (indeed triangulated) structure on `N.trW.Localization` and the
  exactness of the quotient functor `N.trW.Q`
  (`CategoryTheory.Localization.Triangulated.pretriangulated` and `isTriangulated_functor`);
* the universal property `CategoryTheory.Localization.lift`, with `Localization.fac` giving the
  isomorphism `L ⋙ Localization.lift F hF L ≅ F`;
* the exactness of the induced functor, which is this repository's
  `CategoryTheory.Functor.isTriangulated_of_localization` (Stacks 05R7 (2)) in
  `StacksFrontier/CategoryTheory/Triangulated/Localization.lean`.

What is missing, and is what this file adds, is the step that connects a hypothesis about
*objects* — the functor kills `N` — to the hypothesis about *morphisms* that the universal
property wants, namely that `N.trW` is inverted. That is
`ObjectProperty.trW_isInvertedBy_of_isZero`: an exact functor sends a distinguished triangle
with third vertex in `N` to a distinguished triangle with zero third vertex, and a
distinguished triangle whose third vertex is zero has its first morphism invertible.

The descended functor and its characteristic isomorphism are then packaged as
`ObjectProperty.descend` and `ObjectProperty.descendCompIso`, and
`ObjectProperty.isTriangulated_descend` records that the descended functor is exact for the
commutation with the shift that the factorization induces on it.

## What is deliberately not here

Nothing in this file produces a *reflector* `L : C ⥤ C` with a unit `𝟭 C ⟶ L` whose image is
the right orthogonal `N^⊥`. That is a Bousfield localization, and it does not exist for a
general triangulated `C` and a general localizing `N`: it is equivalent to asking that every
object `X` of `C` fit in a distinguished triangle `X' ⟶ X ⟶ L X ⟶ X'⟦1⟧` with `X'` in `N` and
`L X` in `N^⊥`, i.e. that the extension product `N ⋆ N^⊥` be everything. That hypothesis has to
be supplied, and once it is, the whole package is already in this repository: it is
`ObjectProperty.IsLeftAdmissible` for `N^⊥` in
`StacksFrontier/CategoryTheory/Triangulated/AdmissibleSubcategories.lean`, whose
`tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp`
([Stacks, Tag 0H0P]) also identifies `N^⊥` with the Verdier quotient `C/N`. The usual supplier
of `N ⋆ N^⊥ = ⊤` is Brown representability, [Stacks, Tag 0A8G], proved in this repository as
`CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated` in
`StacksFrontier/CategoryTheory/Triangulated/BrownRepresentability.lean`, which needs `C` to have
coproducts and to be compactly generated.

That bridge is now built, for `N` the localizing closure of a family of *compact* generators
indexed by the morphism universe of `C`:
`StacksFrontier/CategoryTheory/Triangulated/LocalizingAdmissible.lean` proves `N` right admissible
and draws the consequences of [Stacks, Tag 0H0P], and
`StacksFrontier/CategoryTheory/Triangulated/LocalizingReflector.lean` assembles the reflector `L`
with its unit. Compactness of the generators is the one hypothesis that has to be supplied; it
is not a consequence of anything here.

## Main results

* `CategoryTheory.ObjectProperty.trW_isInvertedBy_of_isZero`.
* `CategoryTheory.ObjectProperty.descend`, `descendCompIso` and `isTriangulated_descend`.
-/

@[expose] public section

universe v₃ v₂ v₁ u₃ u₂ u₁

namespace CategoryTheory.ObjectProperty

open Category Limits Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
  [∀ (n : ℤ), (shiftFunctor E n).Additive] [Pretriangulated E]

/-- An exact functor which sends every object of `N : ObjectProperty C` to a zero object
inverts `N.trW`, the class of morphisms whose cone lies in `N`. Indeed a morphism of `N.trW`
sits in a distinguished triangle whose third vertex lies in `N`; its image is a distinguished
triangle whose third vertex is zero, and such a triangle has an invertible first morphism. -/
@[sga "4½ Etat_0 2.2" "Inclusion φ(B(F)) ⊆ S(F)"]
lemma trW_isInvertedBy_of_isZero (N : ObjectProperty C) (F : C ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] (hF : ∀ X, N X → IsZero (F.obj X)) :
    N.trW.IsInvertedBy F := by
  rintro X Y s ⟨Z, g, h, hT, hZ⟩
  exact (Triangle.isZero₃_iff_isIso₁ _ (F.map_distinguished _ hT)).1 (hF Z hZ)

section Descent

variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated C] (N : ObjectProperty C) [N.IsTriangulated]
  (L : C ⥤ D) [L.IsLocalization N.trW] [L.CommShift ℤ] [L.IsTriangulated]
  (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated] (hF : ∀ X, N X → IsZero (F.obj X))

/-- The functor induced on the Verdier quotient `C/N` by an exact functor `F : C ⥤ E` which
sends every object of `N` to a zero object. -/
@[sga "4½ Etat_0 Problem1" "partial"]
noncomputable def descend : D ⥤ E :=
  Localization.lift F (N.trW_isInvertedBy_of_isZero F hF) L

/-- Restricting the descended functor along the quotient functor gives back `F`. -/
noncomputable def descendCompIso : L ⋙ N.descend L F hF ≅ F :=
  Localization.fac F (N.trW_isInvertedBy_of_isZero F hF) L

/-- The descended functor `N.descend L F hF` is a lifting of `F` along `L`, with the isomorphism
`N.descendCompIso L F hF`. -/
noncomputable instance : Localization.Lifting L N.trW F (N.descend L F hF) :=
  Localization.liftingLift F (N.trW_isInvertedBy_of_isZero F hF) L

/-- The descended functor is exact, for the commutation with the shift that the factorization
through the quotient functor induces on it. -/
@[sga "4½ Etat_0 2.3.2" "partial"]
theorem isTriangulated_descend :
    letI := Functor.commShiftOfLocalization L N.trW ℤ F (N.descend L F hF)
    (N.descend L F hF).IsTriangulated :=
  have := Localization.essSurj_mapArrow L N.trW
  Functor.isTriangulated_of_localization L N.trW F (N.descend L F hF)

end Descent

section Examples

variable [IsTriangulated C] (N : ObjectProperty C) [N.IsTriangulated]

noncomputable example : Pretriangulated N.trW.Localization := inferInstance

example : IsTriangulated N.trW.Localization := inferInstance

example : N.trW.Q.IsTriangulated := inferInstance

end Examples

end CategoryTheory.ObjectProperty
