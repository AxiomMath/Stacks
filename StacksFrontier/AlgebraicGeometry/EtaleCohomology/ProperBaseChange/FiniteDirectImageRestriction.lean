module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionTwoSquare

/-!
# Restriction of the cohomology of a finite direct image

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` finite, and let `F` be an abelian sheaf on the small
étale site of `X`. The restriction map on étale cohomology
`H^q(Y, f_* F) → H^q(Y', g^{-1} f_* F)` is injective (respectively surjective, bijective) exactly
when the restriction map `H^q(X, F) → H^q(X', (g')^{-1} F)` is.

This is the transfer the source makes in Stacks Project Tag 0A5D for statements (6) and (7) of
Situation 0A52, through the vanishing of the higher direct images of a finite morphism (Tag
03QP), the Leray spectral sequence (Tag 0733) and the compatibility of a finite direct image with
base change (Tag 0959). Here the Leray identification is the adjunction isomorphism
`Ext^q(Z_Y, f_* F) ≅ Ext^q(f^{-1} Z_Y, F)`, valid because both `f^{-1}` and `f_*` are exact, and
the compatibility with base change is Tag 0A4E,
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_injective_directImage_iff`,
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_surjective_directImage_iff`,
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_directImage_iff`: the three
  transfers, for a commutative square whose underived base change comparison is invertible and
  whose direct images are exact.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_injective_directImage_iff_of_isFinite`,
  and its surjective and bijective companions: the same for a cartesian square with `f` finite,
  at the coefficients `AddCommGrpCat.{u + 1}`.

## Implementation notes

No `@[stacks]` attribute is attached: Tag 0A5D asserts the transfer of all eight statements of
Situation 0A52 at once, and the statement carrying it is
`Stacks.EtaleCohomology.curveCohomologyStatements_smallEtaleDirectImageAb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section FirstArgument

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [HasExt.{w} C] [HasExt.{w} D]

/-- The map induced by an exact functor on `Ext` is intertwined, through precomposition with an
isomorphism `φ : X ≅ X'` and with its image, with the map on `Ext` out of `X'`. -/
private lemma mapExtAddHom_comp_precomp {X X' Y : C} (φ : X ≅ X') (n : ℕ) :
    (G.mapExtAddHom X Y n) ∘ ((Ext.mk₀ φ.hom).precomp (a := n) (b := n) Y (zero_add n)) =
      ((Ext.mk₀ (G.map φ.hom)).precomp (a := n) (b := n) (G.obj Y) (zero_add n)) ∘
        (G.mapExtAddHom X' Y n) := by
  funext e
  show ((Ext.mk₀ φ.hom).comp e (zero_add n)).mapExactFunctor G =
    (Ext.mk₀ (G.map φ.hom)).comp (e.mapExactFunctor G) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- For an isomorphism `X ≅ X'`, the map induced by an exact functor `G` on `Ext^n(X, Y)` is
injective if and only if the one on `Ext^n(X', Y)` is. -/
lemma mapExtAddHom_injective_iff_of_iso {X X' Y : C} (φ : X ≅ X') (n : ℕ) :
    Function.Injective (G.mapExtAddHom X Y n) ↔ Function.Injective (G.mapExtAddHom X' Y n) := by
  rw [← Function.Injective.of_comp_iff' _
      (ExtAdjunction.precomp_mk₀_bijective_of_isIso φ.hom n),
    mapExtAddHom_comp_precomp G φ n]
  exact Function.Injective.of_comp_iff
    (ExtAdjunction.precomp_mk₀_bijective_of_isIso (G.map φ.hom) n).injective _

/-- For an isomorphism `X ≅ X'`, the map induced by an exact functor `G` on `Ext^n(X, Y)` is
surjective if and only if the one on `Ext^n(X', Y)` is. -/
lemma mapExtAddHom_surjective_iff_of_iso {X X' Y : C} (φ : X ≅ X') (n : ℕ) :
    Function.Surjective (G.mapExtAddHom X Y n) ↔
      Function.Surjective (G.mapExtAddHom X' Y n) := by
  rw [← Function.Surjective.of_comp_iff _
      (ExtAdjunction.precomp_mk₀_bijective_of_isIso φ.hom n).surjective,
    mapExtAddHom_comp_precomp G φ n]
  exact Function.Surjective.of_comp_iff'
    (ExtAdjunction.precomp_mk₀_bijective_of_isIso (G.map φ.hom) n) _

end FirstArgument

section Restriction

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The restriction map on étale cohomology is injective exactly when the map the inverse image
induces on `Ext` out of the constant sheaf `ℤ` is. -/
lemma etaleCohomologyRestrictionMap_injective_iff
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} f F q) ↔
    Function.Injective ((etaleAbelianInverseImage.{u, v} f).mapExtAddHom
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q) :=
  Function.Injective.of_comp_iff
    (ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).injective _

/-- The restriction map on étale cohomology is surjective exactly when the map the inverse image
induces on `Ext` out of the constant sheaf `ℤ` is. -/
lemma etaleCohomologyRestrictionMap_surjective_iff
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} f F q) ↔
    Function.Surjective ((etaleAbelianInverseImage.{u, v} f).mapExtAddHom
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q) :=
  Function.Surjective.of_comp_iff' (ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q) _

end Restriction

section DirectImage

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)
  [PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f)]
  [PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f')]
  [IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h)]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

include f' h

private lemma isIso_twoSquare :
    IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
      (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
      ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))).natTrans :=
  inferInstanceAs (IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h))

/-- The constant sheaf `ℤ` on `Y`, at the coefficients of this file. -/
private abbrev constZ (Y : Scheme.{u}) : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))

/-- The inverse image of the constant sheaf `ℤ`. -/
private abbrev constZIso :
    (etaleAbelianInverseImage.{u, v} f).obj (constZ.{u, v} Y) ≅ constZ.{u, v} X :=
  (etaleAbelianInverseImageConstantIso.{u, v} f).app (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))

/-- **Restriction of the cohomology of a direct image, injectivity.** For a commutative square
whose base change comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` is invertible and whose direct images
are exact, restriction along `g` is injective on `H^q(Y, f_* F)` exactly when restriction along
`g'` is injective on `H^q(X, F)`. -/
theorem etaleCohomologyRestrictionMap_injective_directImage_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} g
        ((etaleAbelianDirectImage.{u, v} f).obj F) q) ↔
      Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} g' F q) := by
  have := isIso_twoSquare.{u, v} f g g' f' h
  rw [etaleCohomologyRestrictionMap_injective_iff, etaleCohomologyRestrictionMap_injective_iff,
    ← mapExtAddHom_injective_iff_of_iso _ (constZIso.{u, v} f)]
  exact ExtAdjunction.mapExtAddHom_injective_iff_of_isIso_twoSquare
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
    (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
    ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
      eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h)) _ _ _

/-- **Restriction of the cohomology of a direct image, surjectivity.** -/
theorem etaleCohomologyRestrictionMap_surjective_directImage_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} g
        ((etaleAbelianDirectImage.{u, v} f).obj F) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} g' F q) := by
  have := isIso_twoSquare.{u, v} f g g' f' h
  rw [etaleCohomologyRestrictionMap_surjective_iff, etaleCohomologyRestrictionMap_surjective_iff,
    ← mapExtAddHom_surjective_iff_of_iso _ (constZIso.{u, v} f)]
  exact ExtAdjunction.mapExtAddHom_surjective_iff_of_isIso_twoSquare
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
    (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
    ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
      eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h)) _ _ _

/-- **Restriction of the cohomology of a direct image, bijectivity.** -/
theorem etaleCohomologyRestrictionMap_bijective_directImage_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} g
        ((etaleAbelianDirectImage.{u, v} f).obj F) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} g' F q) :=
  and_congr (etaleCohomologyRestrictionMap_injective_directImage_iff.{u, v, w} f g g' f' h F q)
    (etaleCohomologyRestrictionMap_surjective_directImage_iff.{u, v, w} f g g' f' h F q)

end DirectImage

section Finite

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (sq : IsPullback g' f' f g) [IsFinite f]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})]

include f' sq

private lemma isFinite_snd : IsFinite f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹IsFinite f›

/-- **Restriction of the cohomology of a finite direct image, injectivity.** For a cartesian
square with `f` finite, restriction along `g` is injective on `H^q(Y, f_* F)` exactly when
restriction along `g'` is injective on `H^q(X, F)`. -/
theorem etaleCohomologyRestrictionMap_injective_directImage_iff_of_isFinite
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Injective (etaleCohomologyRestrictionMap.{u, 0, w} g' F q) := by
  have := isFinite_snd f g g' f' sq
  have := isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite f g g' f' sq
  exact etaleCohomologyRestrictionMap_injective_directImage_iff.{u, 0, w} f g g' f' sq.w F q

/-- **Restriction of the cohomology of a finite direct image, surjectivity.** -/
theorem etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} g' F q) := by
  have := isFinite_snd f g g' f' sq
  have := isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite f g g' f' sq
  exact etaleCohomologyRestrictionMap_surjective_directImage_iff.{u, 0, w} f g g' f' sq.w F q

/-- **Restriction of the cohomology of a finite direct image, bijectivity.** -/
theorem etaleCohomologyRestrictionMap_bijective_directImage_iff_of_isFinite
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} g
        ((etaleAbelianDirectImage.{u, 0} f).obj F) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} g' F q) :=
  and_congr
    (etaleCohomologyRestrictionMap_injective_directImage_iff_of_isFinite.{u, w} f g g' f' sq F q)
    (etaleCohomologyRestrictionMap_surjective_directImage_iff_of_isFinite.{u, w} f g g' f' sq F q)

end Finite

end Stacks.EtaleCohomology

end
