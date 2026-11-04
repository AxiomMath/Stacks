module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Localization.Predicate
public import StacksFrontier.CategoryTheory.Triangulated.LocalObjects
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms into the values of a reflector onto the local objects

Let `C` be a triangulated category, let `P : ObjectProperty C` be a family of generators and
write `N = P.localizingClosure` for the localizing subcategory it generates. A *reflector onto
the local objects* is an endofunctor `L` of `C` together with a unit `η : 𝟭 C ⟶ L` such that

* every `L X` lies in the right orthogonal `N^⊥`, and
* the fibre of `η.app X` lies in `N`: whenever `Z ⟶ X ⟶ L X ⟶ Z⟦1⟧` is a distinguished
  triangle whose second morphism is `η.app X`, the object `Z` satisfies `N`.

The second condition is what makes `η.app X` a morphism inverted by the Verdier quotient at
`N`, and it is the condition that is usually dropped: it is not needed to know that `L`
annihilates `N`, which is all that the construction of a descended functor uses. It is needed
as soon as one wants to *compare* `Hom(-, L X)` with `Hom(-, X)` in the quotient, which is what
this file does.

The two statements that come out are

`Hom_C(A, (L X)⟦n⟧) ≃ Hom_D(Q A, Q ((L X)⟦n⟧))`

for `Q : C ⥤ D` a Verdier quotient at `N.trW`, because `(L X)⟦n⟧` is local; and

`Hom_D(A, (Q X)⟦n⟧) ≃ Hom_D(A, (Q (L X))⟦n⟧)`,

because `Q (η.app X)` is an isomorphism. Composing them identifies `Hom_C(A, (L X)⟦n⟧)` with
`Hom_D(Q A, (Q X)⟦n⟧)`: a Hom group in `C` out of an object with no reflection applied, into a
*shift of a reflected* object, is a Hom group in the quotient with no reflector in sight.

## Main definitions

* `CategoryTheory.ObjectProperty.localizingClosureUnitIso`: the isomorphism
  `Q X ≅ Q (L X)` induced by the unit.
* `CategoryTheory.ObjectProperty.homEquivShiftLocalizingClosureUnit`: the second display above.
* `CategoryTheory.ObjectProperty.homEquivMapOfRightOrthogonalShift`: the first display above.
* `CategoryTheory.ObjectProperty.homEquivReflectorShift`: the composite.

## Main results

* `CategoryTheory.ObjectProperty.trW_localizingClosure_unit_app`: the unit is inverted by the
  Verdier quotient, from the condition on the fibre of `η`.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.ObjectProperty

open Category Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-! ### The unit of a reflector is inverted by the Verdier quotient -/

/-- **The fibre condition on the unit makes the unit a `trW`-morphism.** If `Z` satisfies the
localizing subcategory `N = P.localizingClosure` for every distinguished triangle
`Z ⟶ X ⟶ L X ⟶ Z⟦1⟧` whose second morphism is `η.app X`, then `η.app X` is inverted by the
Verdier quotient at `N`.

Only one such triangle is needed, and
`CategoryTheory.Pretriangulated.distinguished_cocone_triangle₁` produces it; the cone of
`η.app X` is then a shift of that `Z`, so it satisfies `N` as well. -/
theorem trW_localizingClosure_unit_app {L : C ⥤ C} {η : 𝟭 C ⟶ L}
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (X : C) : P.localizingClosure.{w}.trW (η.app X) := by
  obtain ⟨Z, f, g, hT⟩ := distinguished_cocone_triangle₁ (η.app X)
  exact trW.mk' _ hT (hη X Z f g hT)

section Localization

variable {D : Type u'} [Category.{v'} D] (Q : C ⥤ D)
  [Q.IsLocalization P.localizingClosure.{w}.trW]

/-- **The unit becomes an isomorphism in the Verdier quotient.** -/
noncomputable def localizingClosureUnitIso {L : C ⥤ C} {η : 𝟭 C ⟶ L}
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (X : C) : Q.obj X ≅ Q.obj (L.obj X) :=
  Localization.isoOfHom Q P.localizingClosure.{w}.trW (η.app X)
    (P.trW_localizingClosure_unit_app hη X)

/-- The forward map of `CategoryTheory.ObjectProperty.localizingClosureUnitIso` is the image of
the unit under the quotient functor. -/
@[simp] theorem localizingClosureUnitIso_hom {L : C ⥤ C} {η : 𝟭 C ⟶ L}
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (X : C) : (P.localizingClosureUnitIso Q hη X).hom = Q.map (η.app X) := rfl

variable [HasShift D ℤ]

/-- **Link across the unit.** Morphisms in the quotient into a shift of `Q X` are morphisms
into the same shift of `Q (L X)`: the unit is an isomorphism there, by
`CategoryTheory.ObjectProperty.localizingClosureUnitIso`. -/
noncomputable def homEquivShiftLocalizingClosureUnit {L : C ⥤ C} {η : 𝟭 C ⟶ L}
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A : D) (X : C) (n : ℤ) :
    (A ⟶ (Q.obj X)⟦n⟧) ≃ (A ⟶ (Q.obj (L.obj X))⟦n⟧) :=
  Iso.homCongr (Iso.refl A) ((shiftFunctor D n).mapIso (P.localizingClosureUnitIso Q hη X))

variable [IsTriangulated C]

/-- **Link into a local object.** For `Y` in the right orthogonal of `N = P.localizingClosure`
the Verdier quotient is bijective on morphisms into every shift of `Y`, because the right
orthogonal is stable under the shift.

This is `CategoryTheory.ObjectProperty.map_bijective_of_rightOrthogonal_localizingClosure`. -/
@[sga "4½ Etat_0 2.6.3" "Right clause of 6-3"]
noncomputable def homEquivMapOfRightOrthogonalShift {Y : C}
    (hY : P.localizingClosure.{w}.rightOrthogonal Y) (A : C) (n : ℤ) :
    (A ⟶ Y⟦n⟧) ≃ (Q.obj A ⟶ Q.obj (Y⟦n⟧)) :=
  Equiv.ofBijective _ (P.map_bijective_of_rightOrthogonal_localizingClosure
    (P.localizingClosure.{w}.rightOrthogonal.le_shift n Y hY) Q A)

omit [HasShift D ℤ] in
/-- The bijection `CategoryTheory.ObjectProperty.homEquivMapOfRightOrthogonalShift` is the action
of the quotient functor on morphisms. -/
@[simp] theorem homEquivMapOfRightOrthogonalShift_apply {Y : C}
    (hY : P.localizingClosure.{w}.rightOrthogonal Y) (A : C) (n : ℤ) (f : A ⟶ Y⟦n⟧) :
    P.homEquivMapOfRightOrthogonalShift Q hY A n f = Q.map f := rfl

variable [Q.CommShift ℤ]

/-- **The Hom groups of a reflector, after the quotient.** Let `L` be a reflector onto the
objects local for the localizing subcategory `N = P.localizingClosure`, with unit `η` whose
fibres lie in `N`. Then for every pair of objects `A`, `X` of `C` and every integer `n`,

`Hom_C(A, (L X)⟦n⟧) ≃ Hom_{C/N}(Q A, (Q X)⟦n⟧)`.

The reflector and its unit have disappeared from the right-hand side. The three steps are: the
Verdier quotient is bijective on morphisms into `(L X)⟦n⟧`, which is local; the quotient
commutes with the shift; and the unit `Q X ⟶ Q (L X)` is an isomorphism, by the condition on
its fibres. -/
noncomputable def homEquivReflectorShift {L : C ⥤ C} {η : 𝟭 C ⟶ L}
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A X : C) (n : ℤ) : (A ⟶ (L.obj X)⟦n⟧) ≃ (Q.obj A ⟶ (Q.obj X)⟦n⟧) :=
  (P.homEquivMapOfRightOrthogonalShift Q (hL X) A n).trans
    ((Iso.homCongr (Iso.refl (Q.obj A)) ((Q.commShiftIso n).app (L.obj X))).trans
      (P.homEquivShiftLocalizingClosureUnit Q hη (Q.obj A) X n).symm)

end Localization

end CategoryTheory.ObjectProperty

end
