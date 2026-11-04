module

public import StacksFrontier.Homology.ExtendScalars.Monoidal
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# Monoidality of derived base change

Let `f : R → S` be a homomorphism of commutative rings. Derived extension of scalars
`β = - ⊗ᴸ_R S : D(R) ⥤ D(S)` is monoidal: for `K, L` in `D(R)` there is a canonical
isomorphism `β(K ⊗ᴸ_R L) ≅ βK ⊗ᴸ_S βL`.

This file constructs that comparison on K-flat representatives, where it is a composite of the
following identifications:

* a K-flat complex computes derived extension of scalars, so `β(Q P) ≅ Q(S ⊗_R P)`
  (`TotalDerivedExtensionScalars.comparison_isIso_of_kFlat`);
* a tensor product of K-flat complexes computes the derived tensor product
  (`DerivedTensorProduct.comparison`), and a tensor product of K-flat complexes is K-flat;
* degreewise extension of scalars is monoidal on complexes
  (`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`);
* extension of scalars preserves K-flatness
  (`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`).

## Main definitions

* `CochainComplex.ExtendScalars.kFlatComparisonIso`: a K-flat complex computes derived
  extension of scalars.
* `CochainComplex.ExtendScalars.derivedMonoidalIso`: the monoidality comparison
  `β(Q P ⊗ᴸ_R Q T) ≅ β(Q P) ⊗ᴸ_S β(Q T)` for K-flat `P` and `T`.

## Main results

* `CochainComplex.ExtendScalars.kFlatComparisonIso_naturality` and
  `CochainComplex.ExtendScalars.kFlatComparisonIso_inv_naturality`: the K-flat comparison for
  derived base change is natural.
* `CochainComplex.ExtendScalars.derivedMonoidalIso_naturality_left` and
  `CochainComplex.ExtendScalars.derivedMonoidalIso_naturality_right`: the monoidality comparison
  is natural in both K-flat complexes.
* `CochainComplex.ExtendScalars.derivedMonoidalIso_comparison`: read through the K-flat
  comparisons on both sides, the monoidality comparison is the degreewise monoidality isomorphism
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`.

## Implementation notes

The ring and module universes agree, as they must for `canonicalDerivedTensorProduct`, whose
K-flat comparison is stated at `ModuleCat.{u} R` for `R : Type u`.

This is the special case `A = B = R`, `C = K = S` of Stacks Lemma 08YU, stated in another
language as
`CochainComplex.DerivedTensor.IteratedChangeOfRings.derivedTensorProduct_doubleBaseChange`.

## References

* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 08YU](https://stacks.math.columbia.edu/tag/08YU)
* [The Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CochainComplex.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- A K-flat complex computes derived extension of scalars: the derived base change of the
class of a K-flat complex `X` is the class of the degreewise base change `S ⊗_R X`. -/
noncomputable def kFlatComparisonIso (X : CochainComplex (ModuleCat.{u} R) ℤ)
    (hX : CochainComplex.KFlat.{u, u} X) :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj ((mapCochainComplex f).obj X) := by
  have h := (derivedExtensionScalarsGeneral.{u, u, u} f).comparison_isIso_of_kFlat X hX
  exact @asIso _ _ _ _ ((derivedExtensionScalarsGeneral.{u, u, u} f).comparison.app X) h

/-- **Monoidality of derived base change on K-flat representatives.** For K-flat complexes `P`
and `T` of `R`-modules there is a canonical isomorphism
`(P ⊗ᴸ_R T) ⊗ᴸ_R S ≅ (P ⊗ᴸ_R S) ⊗ᴸ_S (T ⊗ᴸ_R S)` in `D(S)`.

It is the composite of the K-flat comparison for the derived tensor product over `R`, the
K-flat comparison for derived base change of `P ⊗ T`, the monoidality of degreewise extension
of scalars, the K-flat comparison for the derived tensor product over `S`, and the K-flat
comparisons for derived base change of `P` and of `T`. -/
noncomputable def derivedMonoidalIso (P T : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hT : CochainComplex.KFlat.{u, u} T) :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj T)) ≅
      ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj P))).obj
        ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj (DerivedCategory.Q.obj T)) :=
  (derivedExtensionScalarsGeneral.{u, u, u} f).functor.mapIso
      ((canonicalDerivedTensorProduct R).comparison P T hP hT) ≪≫
    kFlatComparisonIso f (P ⊗ T) (CochainComplex.KFlat.tensor R P T hP hT) ≪≫
    DerivedCategory.Q.mapIso (extendScalarsMonoidalIso f P T).symm ≪≫
    ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex f).obj P)
      ((mapCochainComplex f).obj T)
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f P hP)
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f T hT)).symm ≪≫
    ((canonicalDerivedTensorProductFunctor S).mapIso
      (kFlatComparisonIso f P hP).symm).app _ ≪≫
    ((canonicalDerivedTensorProductFunctor S).obj
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
        (DerivedCategory.Q.obj P))).mapIso (kFlatComparisonIso f T hT).symm

/-- The K-flat comparison for derived base change is natural in the complex. -/
lemma kFlatComparisonIso_naturality {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
    (hX : CochainComplex.KFlat.{u, u} X) (hY : CochainComplex.KFlat.{u, u} Y) (h : X ⟶ Y) :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map (DerivedCategory.Q.map h) ≫
        (kFlatComparisonIso f Y hY).hom =
      (kFlatComparisonIso f X hX).hom ≫
        DerivedCategory.Q.map ((mapCochainComplex f).map h) :=
  (derivedExtensionScalarsGeneral.{u, u, u} f).comparison.naturality h

/-- The inverse of the K-flat comparison for derived base change is natural in the complex. -/
lemma kFlatComparisonIso_inv_naturality {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
    (hX : CochainComplex.KFlat.{u, u} X) (hY : CochainComplex.KFlat.{u, u} Y) (h : X ⟶ Y) :
    DerivedCategory.Q.map ((mapCochainComplex f).map h) ≫ (kFlatComparisonIso f Y hY).inv =
      (kFlatComparisonIso f X hX).inv ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map (DerivedCategory.Q.map h) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (kFlatComparisonIso_naturality f hX hY h).symm

/-- **The monoidality comparison of derived base change, on K-flat representatives, is the
degreewise monoidality isomorphism.**

Transporting `CochainComplex.ExtendScalars.derivedMonoidalIso` along the three comparison
isomorphisms that identify the derived tensor product over `S` of the derived base changes of
`P` and `T` with the class of `(S ⊗_R P) ⊗_S (S ⊗_R T)` — the two K-flat comparisons
`CochainComplex.ExtendScalars.kFlatComparisonIso` for derived base change and the K-flat
comparison of the canonical derived tensor product over `S` — gives the class of the inverse of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, precomposed with the derived base change
of the K-flat comparison over `R`. -/
lemma derivedMonoidalIso_comparison (P T : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hT : CochainComplex.KFlat.{u, u} T) :
    (derivedMonoidalIso f P T hP hT).hom ≫
        ((canonicalDerivedTensorProductFunctor S).obj
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
              (DerivedCategory.Q.obj P))).map (kFlatComparisonIso f T hT).hom ≫
        ((canonicalDerivedTensorProductFunctor S).map (kFlatComparisonIso f P hP).hom).app
            (DerivedCategory.Q.obj ((mapCochainComplex f).obj T)) ≫
        ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj T)
          (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f P hP)
          (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f T hT)).hom =
      (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          ((canonicalDerivedTensorProduct R).comparison P T hP hT).hom ≫
        (kFlatComparisonIso f (P ⊗ T) (CochainComplex.KFlat.tensor R P T hP hT)).hom ≫
        DerivedCategory.Q.map (extendScalarsMonoidalIso f P T).inv := by
  dsimp only [derivedMonoidalIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_hom]
  simp

/-- The monoidality comparison of derived base change is natural in the second K-flat
complex. -/
lemma derivedMonoidalIso_naturality_right
    (P T T' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hT : CochainComplex.KFlat.{u, u} T)
    (hT' : CochainComplex.KFlat.{u, u} T') (b : T ⟶ T') :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map b)) ≫ (derivedMonoidalIso f P T' hP hT').hom =
      (derivedMonoidalIso f P T hP hT).hom ≫
        ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj P))).map
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map (DerivedCategory.Q.map b)) := by
  have hPT : CochainComplex.KFlat.{u, u} (P ⊗ T) := CochainComplex.KFlat.tensor R P T hP hT
  have hPT' : CochainComplex.KFlat.{u, u} (P ⊗ T') := CochainComplex.KFlat.tensor R P T' hP hT'
  have hPS := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f P hP
  have hTS := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f T hT
  have hTS' := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f T' hT'
  have h1 : ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
        (DerivedCategory.Q.map b) ≫
        ((canonicalDerivedTensorProduct R).comparison P T' hP hT').hom =
      ((canonicalDerivedTensorProduct R).comparison P T hP hT).hom ≫
        DerivedCategory.Q.map (𝟙 P ⊗ₘ b) := by
    have h := (canonicalDerivedTensorProduct R).comparison_naturality (𝟙 P) b hP hP hT hT'
    rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
  have h3 : (mapCochainComplex f).map (𝟙 P ⊗ₘ b) ≫ (extendScalarsMonoidalIso f P T').inv =
      (extendScalarsMonoidalIso f P T).inv ≫
        (𝟙 ((mapCochainComplex f).obj P) ⊗ₘ (mapCochainComplex f).map b) := by
    have h := extendScalarsMonoidalIso_naturality f (𝟙 P) b
    rw [CategoryTheory.Functor.map_id] at h
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h4 : DerivedCategory.Q.map
        (𝟙 ((mapCochainComplex f).obj P) ⊗ₘ (mapCochainComplex f).map b) ≫
        ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj T') hPS hTS').inv =
      ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj T) hPS hTS).inv ≫
        ((canonicalDerivedTensorProductFunctor S).obj
          (DerivedCategory.Q.obj ((mapCochainComplex f).obj P))).map
            (DerivedCategory.Q.map ((mapCochainComplex f).map b)) := by
    have h := (canonicalDerivedTensorProduct S).comparison_naturality
      (𝟙 ((mapCochainComplex f).obj P)) ((mapCochainComplex f).map b) hPS hPS hTS hTS'
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    rw [show HomologicalComplex.tensorHom (𝟙 ((mapCochainComplex f).obj P))
        ((mapCochainComplex f).map b) =
        (𝟙 ((mapCochainComplex f).obj P) ⊗ₘ (mapCochainComplex f).map b) from rfl] at h
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1' : (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map b)) ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          ((canonicalDerivedTensorProduct R).comparison P T' hP hT').hom =
      (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          ((canonicalDerivedTensorProduct R).comparison P T hP hT).hom ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          (DerivedCategory.Q.map (𝟙 P ⊗ₘ b)) := by
    rw [← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_comp]
  have h3' : DerivedCategory.Q.map ((mapCochainComplex f).map (𝟙 P ⊗ₘ b)) ≫
        DerivedCategory.Q.map (extendScalarsMonoidalIso f P T').inv =
      DerivedCategory.Q.map (extendScalarsMonoidalIso f P T).inv ≫
        DerivedCategory.Q.map
          (𝟙 ((mapCochainComplex f).obj P) ⊗ₘ (mapCochainComplex f).map b) := by
    rw [← CategoryTheory.Functor.map_comp, h3, CategoryTheory.Functor.map_comp]
  have h6 : ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj P))).map
        (DerivedCategory.Q.map ((mapCochainComplex f).map b)) ≫
        ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj P))).map (kFlatComparisonIso f T' hT').inv =
      ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj P))).map (kFlatComparisonIso f T hT).inv ≫
        ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj P))).map
            ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
              (DerivedCategory.Q.map b)) := by
    rw [← CategoryTheory.Functor.map_comp, kFlatComparisonIso_inv_naturality f hT hT' b,
      CategoryTheory.Functor.map_comp]
  dsimp only [derivedMonoidalIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h1',
    reassoc_of% (kFlatComparisonIso_naturality f hPT hPT' (𝟙 P ⊗ₘ b)),
    reassoc_of% h3', reassoc_of% h4,
    reassoc_of% (((canonicalDerivedTensorProductFunctor S).map
      (kFlatComparisonIso f P hP).inv).naturality
      (DerivedCategory.Q.map ((mapCochainComplex f).map b))),
    h6]

/-- The monoidality comparison of derived base change is natural in the first K-flat
complex. -/
lemma derivedMonoidalIso_naturality_left
    (P P' T : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) (hP' : CochainComplex.KFlat.{u, u} P')
    (hT : CochainComplex.KFlat.{u, u} T) (a : P ⟶ P') :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
        (((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj T)) ≫ (derivedMonoidalIso f P' T hP' hT).hom =
      (derivedMonoidalIso f P T hP hT).hom ≫
        ((canonicalDerivedTensorProductFunctor S).map
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
            (DerivedCategory.Q.map a))).app
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
            (DerivedCategory.Q.obj T)) := by
  have hPT : CochainComplex.KFlat.{u, u} (P ⊗ T) := CochainComplex.KFlat.tensor R P T hP hT
  have hPT' : CochainComplex.KFlat.{u, u} (P' ⊗ T) := CochainComplex.KFlat.tensor R P' T hP' hT
  have hPS := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f P hP
  have hPS' := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f P' hP'
  have hTS := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f T hT
  have h1 : ((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).app
        (DerivedCategory.Q.obj T) ≫
        ((canonicalDerivedTensorProduct R).comparison P' T hP' hT).hom =
      ((canonicalDerivedTensorProduct R).comparison P T hP hT).hom ≫
        DerivedCategory.Q.map (a ⊗ₘ 𝟙 T) := by
    have h := (canonicalDerivedTensorProduct R).comparison_naturality a (𝟙 T) hP hP' hT hT
    rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h1' : (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
        (((canonicalDerivedTensorProductFunctor R).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj T)) ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          ((canonicalDerivedTensorProduct R).comparison P' T hP' hT).hom =
      (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          ((canonicalDerivedTensorProduct R).comparison P T hP hT).hom ≫
        (derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
          (DerivedCategory.Q.map (a ⊗ₘ 𝟙 T)) := by
    rw [← CategoryTheory.Functor.map_comp, h1, CategoryTheory.Functor.map_comp]
  have h3 : (mapCochainComplex f).map (a ⊗ₘ 𝟙 T) ≫ (extendScalarsMonoidalIso f P' T).inv =
      (extendScalarsMonoidalIso f P T).inv ≫
        ((mapCochainComplex f).map a ⊗ₘ 𝟙 ((mapCochainComplex f).obj T)) := by
    have h := extendScalarsMonoidalIso_naturality f a (𝟙 T)
    rw [CategoryTheory.Functor.map_id] at h
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h3' : DerivedCategory.Q.map ((mapCochainComplex f).map (a ⊗ₘ 𝟙 T)) ≫
        DerivedCategory.Q.map (extendScalarsMonoidalIso f P' T).inv =
      DerivedCategory.Q.map (extendScalarsMonoidalIso f P T).inv ≫
        DerivedCategory.Q.map
          ((mapCochainComplex f).map a ⊗ₘ 𝟙 ((mapCochainComplex f).obj T)) := by
    rw [← CategoryTheory.Functor.map_comp, h3, CategoryTheory.Functor.map_comp]
  have h4 : DerivedCategory.Q.map
        ((mapCochainComplex f).map a ⊗ₘ 𝟙 ((mapCochainComplex f).obj T)) ≫
        ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex f).obj P')
          ((mapCochainComplex f).obj T) hPS' hTS).inv =
      ((canonicalDerivedTensorProduct S).comparison ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj T) hPS hTS).inv ≫
        ((canonicalDerivedTensorProductFunctor S).map
          (DerivedCategory.Q.map ((mapCochainComplex f).map a))).app
          (DerivedCategory.Q.obj ((mapCochainComplex f).obj T)) := by
    have h := (canonicalDerivedTensorProduct S).comparison_naturality
      ((mapCochainComplex f).map a) (𝟙 ((mapCochainComplex f).obj T)) hPS hPS' hTS hTS
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [show HomologicalComplex.tensorHom ((mapCochainComplex f).map a)
        (𝟙 ((mapCochainComplex f).obj T)) =
        ((mapCochainComplex f).map a ⊗ₘ 𝟙 ((mapCochainComplex f).obj T)) from rfl] at h
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h5 : ((canonicalDerivedTensorProductFunctor S).map
        (DerivedCategory.Q.map ((mapCochainComplex f).map a))).app
        (DerivedCategory.Q.obj ((mapCochainComplex f).obj T)) ≫
        ((canonicalDerivedTensorProductFunctor S).map (kFlatComparisonIso f P' hP').inv).app
          (DerivedCategory.Q.obj ((mapCochainComplex f).obj T)) =
      ((canonicalDerivedTensorProductFunctor S).map (kFlatComparisonIso f P hP).inv).app
          (DerivedCategory.Q.obj ((mapCochainComplex f).obj T)) ≫
        ((canonicalDerivedTensorProductFunctor S).map
          ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
            (DerivedCategory.Q.map a))).app
          (DerivedCategory.Q.obj ((mapCochainComplex f).obj T)) := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, kFlatComparisonIso_inv_naturality f hP hP' a]
  dsimp only [derivedMonoidalIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h1',
    reassoc_of% (kFlatComparisonIso_naturality f hPT hPT' (a ⊗ₘ 𝟙 T)),
    reassoc_of% h3', reassoc_of% h4, reassoc_of% h5,
    ((canonicalDerivedTensorProductFunctor S).map
      ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.map
        (DerivedCategory.Q.map a))).naturality (kFlatComparisonIso f T hT).inv]

end CochainComplex.ExtendScalars

end
