module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroUnconditional
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.Homology.TensorComplex.SingleTensor

/-!
# The degree-`c` cohomology of a derived tensor product with a shifted module

`Stacks.DerivedTensor.RingedSite.degreeZeroTensorIso` identifies `H^0(A[0] ⊗^L_O G[0])` with
`A ⊗_O G`, unconditionally. This file identifies

`H^c(K ⊗^L_O G[0]⟦-c⟧)`,

the degree-`c` cohomology of a derived tensor product whose right factor is a module placed in
degree `c`, with the degree-zero cohomology of the unshifted product, as the composite of two
standard isomorphisms:

* the right factor can be shifted out of the tensor product, because `K ⊗^L_O -` commutes with
  the shift — that is the field `DerivedTensorProduct.commShift_right`;
* `H^c` of a `(-c)`-shift is `H^0`, by the shift sequence on the homology functors of a derived
  category.

Neither step needs flatness or K-flatness, so the composite inherits the unconditionality of
`degreeZeroTensorIso`.

## Main definitions

* `Stacks.HomologyShift.homologyShiftIso`: `H^i(-⟦n⟧) ≅ H^{n+i}(-)` on the derived category of
  an arbitrary abelian category.
* `Stacks.DerivedTensor.RingedSite.tensorShiftRightIso`: `K ⊗^L_O L⟦n⟧ ≅ (K ⊗^L_O L)⟦n⟧`.
* `Stacks.DerivedTensor.RingedSite.homologyShiftedTensorIso`:
  `H^c(K ⊗^L_O L⟦-c⟧) ≅ H^0(K ⊗^L_O L)`, for arbitrary `K` and `L`.
* `Stacks.DerivedTensor.RingedSite.degreeShiftedTensorIso`: **the read-off**,
  `H^c(A[0] ⊗^L_O G[0]⟦-c⟧) ≅ A ⊗_O G`, with no flatness and no K-flatness on either factor.
* `Stacks.DerivedTensor.RingedSite.singleShiftIso`: `G[c] ≅ G[0]⟦-c⟧`.
* `Stacks.DerivedTensor.RingedSite.degreeSingleTensorIso`: the read-off with the right factor
  spelled as a single complex in degree `c`.
* `Stacks.DerivedTensor.RingedSite.tensorSingleToSingle`: **the canonical map
  `A[0] ⊗^L_O F[0] ⟶ (A ⊗_O F)[0]`**, again with no flatness and no K-flatness. Unlike the
  isomorphisms above this is only a map: away from degree zero its source has the Tor sheaves
  of `A` and `F` as cohomology.

## Main results

* `Stacks.DerivedTensor.RingedSite.degreeShiftedTensorIso_hom`: the forward map of the read-off
  is the degree-zero comparison `degreeZeroTensorMap` preceded by the two shift isomorphisms,
  so the identification remains the one induced by `DerivedTensorProduct.toTensor`.
* `Stacks.DerivedTensor.RingedSite.homologyMap_tensorSingleToSingle`: in degree zero
  `tensorSingleToSingle` *is* `degreeZeroTensorMap`.
* `CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f_zero`: the degree-zero component of
  `CochainComplex.KFlatBifunctor.totalSingleIso`, read on the `(0, 0)`-summand of the total
  complex.
* `Stacks.DerivedTensor.RingedSite.totSingleIsoSingle_hom_eq_singleTensor`: the two
  identifications of `Tot(A[0] ⊗_O F[0])` with `(A ⊗_O F)[0]` — the one through
  `CochainComplex.KFlatBifunctor.totalSingleIso` and the one through
  `TotalTensorComplex.SingleTensor.singleTensorIso` — agree.
* `Stacks.DerivedTensor.RingedSite.tensorSingleToSingle_eq_singleTensor`:
  `tensorSingleToSingle` in the termwise model of the total tensor complex.

## Implementation notes

`Stacks.HomologyShift.homologyShiftIso` is stated for an arbitrary abelian category with a
derived category rather than for `Modules R`; it is the Mathlib instance
`(homologyFunctor C 0).ShiftSequence ℤ` read at a fixed pair of degrees.

The shift index is a general `n` in `tensorShiftRightIso` and is specialised to `-c` only in
`homologyShiftedTensorIso`, where the degree `c` and the shift `-c` cancel.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' u' u d

namespace Stacks.DegreeZeroTensor

/-- **A four-fold composite out of a split summand.** If `i ≫ m = e ≫ j`, `j ≫ v = s`,
`z = 𝟙 T`, `e = r ≫ sinv` and `sinv ≫ s = 𝟙 T`, then `i ≫ m ≫ v ≫ z = r`. -/
theorem comp_four_of_split {C : Type*} [Category C] {X Y Y' Z T : C}
    (i : X ⟶ Y) (m : Y ⟶ Z) (v : Z ⟶ T) (z : T ⟶ T) (e : X ⟶ Y') (j : Y' ⟶ Z)
    (s : Y' ⟶ T) (sinv : T ⟶ Y') (r : X ⟶ T)
    (hi : i ≫ m = e ≫ j) (hv : j ≫ v = s) (hz : z = CategoryStruct.id T)
    (he : e = r ≫ sinv) (hsi : sinv ≫ s = CategoryStruct.id T) :
    i ≫ m ≫ v ≫ z = r := by
  rw [← Category.assoc, hi, hz, Category.comp_id, Category.assoc, hv, he, Category.assoc,
    hsi, Category.comp_id]

/-- **Cancelling the first-variable image of an identity morphism of a bifunctor.** If
`a = 𝟙 X`, then `(Φ.map a).app Y ≫ g = g`. -/
theorem map_id_app_comp {C E Z : Type*} [Category C] [Category E] [Category Z] (Φ : C ⥤ E ⥤ Z)
    {X : C} (a : X ⟶ X) (ha : a = CategoryStruct.id X) (Y : E) {T : Z}
    (g : (Φ.obj X).obj Y ⟶ T) :
    (Φ.map a).app Y ≫ g = g := by
  rw [ha, Φ.map_id, NatTrans.id_app, Category.id_comp]

/-- Re-associating a three-fold composite whose first two factors are known: if `i ≫ m = p`,
then `i ≫ m ≫ n = p ≫ n`. -/
theorem comp_assoc_of_comp {C : Type*} [Category C] {X Y Z T : C}
    (i : X ⟶ Y) (m : Y ⟶ Z) (n : Z ⟶ T) (p : X ⟶ Z) (h : i ≫ m = p) :
    i ≫ m ≫ n = p ≫ n := by
  rw [← Category.assoc, h]

end Stacks.DegreeZeroTensor

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **The degree-zero component of the termwise identification of a total complex.** The
inclusion of the `(0, 0)`-summand of `Tot(F(K, M[0]))` followed by
`CochainComplex.KFlatBifunctor.totalSingleIso` is the image under `F(K^0, -)` of the
identification of `M[0]` in degree zero with `M`. -/
theorem ι_totalSingleIso_hom_f_zero (K : CochainComplex A ℤ) (M : B) :
    HomologicalComplex.ιMapBifunctor K
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
        0 0 0 rfl ≫ (totalSingleIso F K M).hom.f 0 =
      (F.obj (K.X 0)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom := by
  let W := rowComplex F K M
  let _hT : (StacksDraft.TotalSingleRow.singleRow W 0).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (mapBifunctorSingleIso F K M 0) _
  have hiso : IsIso (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0) :=
    StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit _ _
  have hK0 : (totalSingleIso F K M).hom.f 0 =
      (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).hom
          (ComplexShape.up ℤ)).f 0 ≫
        (CategoryTheory.inv (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0)).f 0 ≫
          ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ)
            neg_zero).hom.app W).f 0 := rfl
  have hz : ((CategoryTheory.shiftFunctorZero' (CochainComplex D ℤ) (-0 : ℤ)
      neg_zero).hom.app W).f 0 = 𝟙 (W.X 0) := by
    simp [CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_hom_app_f,
      HomologicalComplex.XIsoOfEq]
  have hU0 : (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X 0)).inv ≫
        (StacksDraft.TotalSingleRow.singleRow W 0).ιTotal (ComplexShape.up ℤ) 0 0 0 rfl := by
    dsimp only [StacksDraft.TotalSingleRow.totalSingleRowUnit]
    rw [show ((0 : ℤ) * 0).negOnePow = 1 by simp, one_smul]
    rfl
  have h1 : (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0).f 0 ≫
      (CategoryTheory.inv (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0)).f 0 = 𝟙 _ :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ 0)
      (IsIso.hom_inv_id (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0))
  rw [hU0, Category.assoc] at h1
  have hv : (StacksDraft.TotalSingleRow.singleRow W 0).ιTotal (ComplexShape.up ℤ) 0 0 0 rfl ≫
        (CategoryTheory.inv (StacksDraft.TotalSingleRow.totalSingleRowUnit W 0)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X 0)).hom :=
    ((Iso.inv_comp_eq _).1 h1).trans (Category.comp_id _)
  have hι : HomologicalComplex.ιMapBifunctor K
          ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj M) F (ComplexShape.up ℤ)
          0 0 0 rfl ≫
        (HomologicalComplex₂.total.map (mapBifunctorSingleIso F K M 0).hom
          (ComplexShape.up ℤ)).f 0 =
      ((mapBifunctorSingleIso F K M 0).hom.f 0).f 0 ≫
        (StacksDraft.TotalSingleRow.singleRow W 0).ιTotal (ComplexShape.up ℤ) 0 0 0 rfl :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ 0 0 0 rfl
  have he : ((mapBifunctorSingleIso F K M 0).hom.f 0).f 0 =
      (F.obj (K.X 0)).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X 0)).inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self (F.obj (K.X 0))
      (ComplexShape.up ℤ) 0 M
  rw [hK0]
  exact Stacks.DegreeZeroTensor.comp_four_of_split _ _ _ _ _ _ _ _ _ hι hv hz he
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (W.X 0)).inv_hom_id

end CochainComplex.KFlatBifunctor

namespace Stacks.HomologyShift

/-- **`H^i` of an `n`-shift is `H^{n+i}`.** The shift sequence on the homology functors of a
derived category, read as a natural isomorphism at a fixed pair of degrees. -/
def homologyShiftIso (C : Type u') [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w} C]
    (n i j : ℤ) (h : n + i = j) :
    shiftFunctor (DerivedCategory C) n ⋙ DerivedCategory.homologyFunctor C i ≅
      DerivedCategory.homologyFunctor C j :=
  (DerivedCategory.homologyFunctor C 0).shiftIso n i j h

end Stacks.HomologyShift

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **A shift of the right factor comes out of the derived tensor product**, as
`K ⊗^L_O L⟦n⟧ ≅ (K ⊗^L_O L)⟦n⟧`. This is the `CommShift` datum `commShift_right` of the derived
tensor product, evaluated at `L`. -/
def tensorShiftRightIso (T : DerivedTensorProduct.{d} R) (K L : DerivedModules R) (n : ℤ) :
    (T.tensor.obj K).obj (L⟦n⟧) ≅ ((T.tensor.obj K).obj L)⟦n⟧ :=
  ((T.tensor.obj K).commShiftIso n).app L

/-- **The degree-`c` cohomology of a derived tensor product whose right factor is shifted by
`-c` is the degree-zero cohomology of the unshifted product.** Shift the factor out of the
tensor product, then cancel the degree against the shift. No hypothesis is needed on either
object. -/
def homologyShiftedTensorIso (T : DerivedTensorProduct.{d} R) (K L : DerivedModules R) (c : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) c).obj ((T.tensor.obj K).obj (L⟦-c⟧)) ≅
      (DerivedCategory.homologyFunctor (Modules R) 0).obj ((T.tensor.obj K).obj L) :=
  (DerivedCategory.homologyFunctor (Modules R) c).mapIso
      (tensorShiftRightIso R T K L (-c)) ≪≫
    (Stacks.HomologyShift.homologyShiftIso (Modules R) (-c) c 0 (by lia)).app
      ((T.tensor.obj K).obj L)

/-- **The degree-`c` read-off of the unconditional degree-zero comparison.** For sheaves of
modules `A` and `G` on a small ringed site,

`H^c(A[0] ⊗^L_O G[0]⟦-c⟧) ≅ A ⊗_O G`,

**with no flatness and no K-flatness hypothesis on either factor.** The right-hand factor
`G[0]⟦-c⟧` is `G` placed in degree `c`.

This is `degreeZeroTensorIso` composed with `homologyShiftedTensorIso`, so the identification is
still the one induced by `DerivedTensorProduct.toTensor`. -/
def degreeShiftedTensorIso (G A : Modules R) (c : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) c).obj
        (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
          ((DerivedCategory.Q.obj (sg R G))⟦-c⟧)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G :=
  homologyShiftedTensorIso R (canonicalDerivedTensorProduct R)
      (DerivedCategory.Q.obj (sg R A)) (DerivedCategory.Q.obj (sg R G)) c ≪≫
    degreeZeroTensorIso R G A

/-- **A module placed in degree `c` is a module placed in degree zero, shifted by `-c`.** The
shift datum of `DerivedCategory.singleFunctors`, read at the pair of degrees `0` and `c`. -/
def singleShiftIso (G : Modules R) (c : ℤ) :
    (DerivedCategory.singleFunctor (Modules R) c).obj G ≅
      (DerivedCategory.Q.obj (sg R G))⟦-c⟧ :=
  (((DerivedCategory.singleFunctors (Modules R)).shiftIso (-c) c 0 (by lia)).app G).symm

/-- **The degree-`c` read-off, with the right factor spelled as a single complex in degree
`c`.** For sheaves of modules `A` and `G` on a small ringed site,

`H^c(A[0] ⊗^L_O G[c]) ≅ A ⊗_O G`,

**with no flatness and no K-flatness hypothesis on either factor.**

This is `degreeShiftedTensorIso` with `singleShiftIso` inserted. -/
def degreeSingleTensorIso (G A : Modules R) (c : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) c).obj
        (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
          ((DerivedCategory.singleFunctor (Modules R) c).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj G :=
  (DerivedCategory.homologyFunctor (Modules R) c).mapIso
      (((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).mapIso
        (singleShiftIso R G c)) ≪≫
    degreeShiftedTensorIso R G A c

/-- The forward map of the degree-`c` read-off is the degree-zero comparison
`degreeZeroTensorMap` preceded by the two shift isomorphisms. -/
theorem degreeShiftedTensorIso_hom (G A : Modules R) (c : ℤ) :
    (degreeShiftedTensorIso R G A c).hom =
      (homologyShiftedTensorIso R (canonicalDerivedTensorProduct R)
          (DerivedCategory.Q.obj (sg R A)) (DerivedCategory.Q.obj (sg R G)) c).hom ≫
        degreeZeroTensorMap R G A :=
  rfl

/-! ### The derived tensor product of two modules, compared with their ordinary one -/

/-- **The canonical map `A[0] ⊗^L_O F[0] ⟶ (A ⊗_O F)[0]`**, with no flatness and no K-flatness
hypothesis on either factor.

Unlike `degreeZeroTensorMap`, which compares the two in degree zero only and is invertible
there (`isIso_degreeZeroTensorMap`), this is a map of complexes and is *not* invertible in
general: its lower cohomology sheaves are the Tor sheaves of `A` and `F`.

It is the field `DerivedTensorProduct.toTensor` at the two single complexes, followed by
`totSingleIsoSingle`, which identifies the total tensor complex of two modules in degree zero
with their tensor product in degree zero. -/
def tensorSingleToSingle (A F : Modules R) :
    ((derivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (sg R A))).obj
        (DerivedCategory.Q.obj (sg R F)) ⟶
      DerivedCategory.Q.obj (sg R (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj F)) :=
  (canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R F) ≫
    DerivedCategory.Q.map (totSingleIsoSingle R F A).hom

/-- The canonical map to the ordinary tensor product is `DerivedTensorProduct.toTensor`
followed by the identification of the total tensor complex. -/
theorem tensorSingleToSingle_eq (A F : Modules R) :
    tensorSingleToSingle R A F =
      (canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R F) ≫
        DerivedCategory.Q.map (totSingleIsoSingle R F A).hom :=
  rfl

/-- **In degree zero the canonical map `A[0] ⊗^L_O F[0] ⟶ (A ⊗_O F)[0]` is the degree-zero
comparison:** on `H^0`, followed by the identification `H^0((A ⊗_O F)[0]) ≅ A ⊗_O F`, it is
`degreeZeroTensorMap`. -/
theorem homologyMap_tensorSingleToSingle (A F : Modules R) :
    (DerivedCategory.homologyFunctor (Modules R) 0).map (tensorSingleToSingle R A F) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R) 0).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj F)).hom =
      degreeZeroTensorMap R F A := by
  rw [tensorSingleToSingle, Functor.map_comp, Category.assoc, degreeZeroTensorMap,
    totSingleHomologyIso_hom]

/-! ### The canonical map in the termwise model of the total tensor complex -/

section TermwiseModel

open CategoryTheory.MonoidalCategory

/-- The monoidal structure on `Mod(O)` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`. `Mod(O)` also carries a localized monoidal structure;
only this one has `sheafTensor` as its `MonoidalCategory.curriedTensor`. -/
local instance monoidalModules : MonoidalCategory (Modules R) :=
  SheafOfModules.monoidalCategorySheafTensor R

/-- The tensor product of `monoidalModules` is additive in each variable on morphisms. -/
local instance monoidalPreadditiveModules : MonoidalPreadditive (Modules R) :=
  SheafOfModules.monoidalPreadditiveSheafTensor R

omit [HasDerivedCategory (Modules R)] in
/-- **The total tensor complex of two modules in degree zero, read through the termwise model.**
`totSingleIsoSingle` and the composite of
`TotalTensorComplex.SingleTensor.singleTensorIso` with
`CategoryTheory.Functor.mapHomologicalComplexSingleIso` are the same identification
`Tot(A[0] ⊗_O F[0]) ≅ (A ⊗_O F)[0]`. -/
theorem totSingleIsoSingle_hom_eq_singleTensor (A F : Modules R) :
    (totSingleIsoSingle R F A).hom =
      (TotalTensorComplex.SingleTensor.singleTensorIso A (sg R F)).hom ≫
        (Functor.mapHomologicalComplexSingleIso (tensorLeft A) 0 F).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    refine (Iso.cancel_iso_inv_left
      (TotalTensorComplex.SingleTensor.singleTensorTermIso A (sg R F) 0) _ _).1 ?_
    have hinv : (TotalTensorComplex.SingleTensor.singleTensorTermIso A (sg R F) 0).inv =
        HomologicalComplex.ιMapBifunctor (sg R A) (sg R F)
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) 0 0 0 rfl :=
      TotalTensorComplex.SingleTensor.singleTensorTermIso_inv A (sg R F) 0
    have hL : (totSingleIsoSingle R F A).hom.f 0 =
        (CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) F).hom.f 0 ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor R).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom).app F ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj F)).inv := by
      refine Eq.trans (HomologicalComplex.comp_f _ _ 0) ?_
      exact congrArg
        (fun x => (CochainComplex.KFlatBifunctor.totalSingleIso
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) F).hom.f 0 ≫ x)
        (HomologicalComplex.singleMapHomologicalComplex_hom_app_self
          ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj F) (ComplexShape.up ℤ) 0 A)
    have h1 : HomologicalComplex.ιMapBifunctor (sg R A) (sg R F)
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) 0 0 0 rfl ≫
        (CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) F).hom.f 0 =
          ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj ((sg R A).X 0)).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom :=
      CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f_zero
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) F
    have h1' : (TotalTensorComplex.SingleTensor.singleTensorTermIso A (sg R F) 0).inv ≫
          (CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) F).hom.f 0 =
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj ((sg R A).X 0)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom :=
      (congrArg (fun x => x ≫ (CochainComplex.KFlatBifunctor.totalSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (sg R A) F).hom.f 0) hinv).trans h1
    have hR : ((TotalTensorComplex.SingleTensor.singleTensorIso A (sg R F)).hom ≫
          (Functor.mapHomologicalComplexSingleIso (tensorLeft A) 0 F).hom).f 0 =
        (TotalTensorComplex.SingleTensor.singleTensorTermIso A (sg R F) 0).hom ≫
          (Functor.mapHomologicalComplexSingleIso (tensorLeft A) 0 F).hom.f 0 := rfl
    have ha : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom = 𝟙 A := rfl
    have e1 : (TotalTensorComplex.SingleTensor.singleTensorTermIso A (sg R F) 0).inv ≫
          (totSingleIsoSingle R F A).hom.f 0 =
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj ((sg R A).X 0)).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj F)).inv := by
      rw [hL]
      refine Eq.trans (Stacks.DegreeZeroTensor.comp_assoc_of_comp _ _ _ _ h1') ?_
      exact congrArg
        (fun x => ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj ((sg R A).X 0)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ x)
        (Stacks.DegreeZeroTensor.map_id_app_comp
          (Stacks.SheafOfModules.Tensor.sheafTensor R) _ ha F _)
    have e2 : (TotalTensorComplex.SingleTensor.singleTensorTermIso A (sg R F) 0).inv ≫
          ((TotalTensorComplex.SingleTensor.singleTensorIso A (sg R F)).hom ≫
            (Functor.mapHomologicalComplexSingleIso (tensorLeft A) 0 F).hom).f 0 =
        (tensorLeft A).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            ((tensorLeft A).obj F)).inv := by
      rw [hR, Iso.inv_hom_id_assoc, Functor.mapHomologicalComplexSingleIso_hom_f_self]
    exact e1.trans e2.symm
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj F) n hn).eq_of_tgt _ _

/-- **The canonical map `A[0] ⊗^L_O F[0] ⟶ (A ⊗_O F)[0]`, in the termwise model of the total
tensor complex.** `DerivedTensorProduct.toTensor` followed by
`TotalTensorComplex.SingleTensor.singleTensorIso` and
`CategoryTheory.Functor.mapHomologicalComplexSingleIso`. -/
theorem tensorSingleToSingle_eq_singleTensor (A F : Modules R) :
    tensorSingleToSingle R A F =
      (canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R F) ≫
        DerivedCategory.Q.map
          ((TotalTensorComplex.SingleTensor.singleTensorIso A (sg R F)).hom ≫
            (Functor.mapHomologicalComplexSingleIso (tensorLeft A) 0 F).hom) := by
  rw [tensorSingleToSingle_eq]
  exact congrArg
    (fun x => (canonicalDerivedTensorProduct R).toTensor (sg R A) (sg R F) ≫
      DerivedCategory.Q.map x)
    (totSingleIsoSingle_hom_eq_singleTensor R A F)

end TermwiseModel

end Stacks.DerivedTensor.RingedSite

end
