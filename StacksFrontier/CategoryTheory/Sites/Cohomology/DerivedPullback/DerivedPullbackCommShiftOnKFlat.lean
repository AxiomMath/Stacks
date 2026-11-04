module

public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedCounitCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TriangulatedSubcategory

/-! # The commutation of the derived pullback with the shift, at a K-flat complex

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of the
underlying sites which is a morphism of sites.  `Lf^*` commutes with the shift
([Stacks, Tag 06YY]), and the commutation isomorphism is constructed as the one of a left derived
functor; it therefore comes with no formula.  This file supplies one at the image of a K-flat
complex with flat terms, where `Lf^*` is the degreewise pullback: there the commutation
isomorphism is the degreewise pullback's own commutation with the shift, which is the identity in
each degree.

## Main results

* `Stacks.Sheaves.DerivedPullback.kFlat_shift`: a shift of a K-flat complex is K-flat.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackComparison_shift_square`: the square expressing
  that the canonical comparison `Lf^*𝒦 ⟶ f^*𝒦` commutes with the shift.  This is
  `CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift` with the commutation
  isomorphism of the composite `Qh ⋙ Lf^*` split into its two factors.
* `Stacks.Sheaves.DerivedPullback.flatPullbackIso_commShift`: **the commutation of `Lf^*` with
  the shift, at the image of a K-flat complex with flat terms**, read against
  `Stacks.Sheaves.DerivedPullback.flatPullbackIso`.

## Implementation notes

The translation from the homotopy category to complexes is the one `flatPullbackIso` already
performs: `DerivedCategory.Q` is `HomotopyCategory.quotient` followed by
`DerivedCategory.Qh` up to `DerivedCategory.quotientCompQhIso`, and that isomorphism is
compatible with the shifts
(`CategoryTheory.NatTrans.CommShift (DerivedCategory.quotientCompQhIso _).hom ℤ` in Mathlib), as
is the quotient functor itself.

K-flatness of a shift is read off from the triangulated-subcategory statement of
[Stacks, Tag 07A3]: `Stacks.SheafOfModules.kFlatObjects_isTriangulated` has
`isStableUnderShiftBy` among its fields, and `kFlatObjects` is K-flatness of the underlying
complex by definition.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## A shift of a K-flat complex is K-flat -/

section KFlatShift

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **A shift of a K-flat complex is K-flat.**  The K-flat objects of the homotopy category form
a triangulated subcategory ([Stacks, Tag 07A3]), hence one stable under the shift, and
`Stacks.SheafOfModules.kFlatObjects` is K-flatness of the underlying complex. -/
theorem kFlat_shift
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat R K) (n : ℤ) :
    Stacks.SheafOfModules.IsKFlat R
      ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
        n).obj K) := by
  have := (Stacks.SheafOfModules.kFlatObjects_isTriangulated R).isStableUnderShiftBy n
  have h := (Stacks.SheafOfModules.kFlatObjects R).le_shift n
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) hK
  rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj] at h
  exact h

end KFlatShift

/-! ## The commutation of the derived pullback with the shift at a K-flat complex -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **The canonical comparison `Lf^*𝒦 ⟶ f^*𝒦` commutes with the shift.**  This is the
`CategoryTheory.NatTrans.CommShift` instance of the comparison, with the commutation isomorphism
of the composite `Qh ⋙ Lf^*` split into the one of `Qh` and the one of `Lf^*`. -/
theorem derivedPullbackComparison_shift_square (n : ℤ)
    (Z : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso n).hom.app Z) ≫
        ((derivedPullback f).commShiftIso n).hom.app (DerivedCategory.Qh.obj Z) ≫
          ((derivedPullbackComparison f).app Z)⟦n⟧' =
      (derivedPullbackComparison f).app (Z⟦n⟧) ≫
        ((pullbackOnHomotopy f).commShiftIso n).hom.app Z := by
  have h := NatTrans.shift_app_comm (derivedPullbackComparison f) n Z
  rw [CategoryTheory.Functor.commShiftIso_comp_hom_app] at h
  rw [← Category.assoc]
  exact h

/-- **The comparison `Lf^*(QK) ⟶ Q(f^*K)` as a natural transformation of functors on
complexes.**  It is the comparison `Lf^*𝒦 ⟶ f^*𝒦` of [Stacks, Tag 06YY] on the homotopy
category, transported to complexes by the identification of `DerivedCategory.Q` with
`HomotopyCategory.quotient` followed by `DerivedCategory.Qh` and by the factorisation of the
functor induced on homotopy categories through the degreewise one.

Writing it as a transformation of functors on complexes — rather than one object at a time, as
`Stacks.Sheaves.DerivedPullback.flatPullbackIso` does — is what makes its compatibility with the
shift an instance: each of its four factors is compatible with the shifts, and
`CategoryTheory.NatTrans.CommShift` is closed under composition and whiskering. -/
def flatPullbackTrans :
    DerivedCategory.Q ⋙ derivedPullback f ⟶ pullbackComplex f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv
      (derivedPullback f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))
      (derivedPullbackComparison f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pullbackComplex f)
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom

/-- **The comparison is compatible with the shifts.**

It is the vertical composition of two squares of functors commuting with the shifts — the
factorisation of the functor induced on homotopy categories through the degreewise one on top,
and the comparison `Lf^* ⟶ f^*` on the homotopy category below — against the two identifications
of `DerivedCategory.Q` with `HomotopyCategory.quotient` followed by `DerivedCategory.Qh`.  Each
of those four transformations commutes with the shifts: the two identifications by Mathlib's
`CategoryTheory.NatTrans.CommShift (DerivedCategory.quotientCompQhIso _).hom ℤ`, the
factorisation by Mathlib's instance for `CategoryTheory.Functor.mapHomotopyCategoryFactors`, and
the comparison by `CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift`.

`CategoryTheory.NatTrans.CommShift.verticalComposition` is exactly that pasting, and
`flatPullbackTrans` is defined to be its composite on the nose, so the hypothesis is `rfl`.
Letting instance search assemble the composite from
`CategoryTheory.NatTrans.CommShift.comp` instead exhausts the synthesis budget: the associators
are then absent and the two spellings of each intermediate functor meet only after
`CategoryTheory.Quotient.lift` is unfolded. -/
instance flatPullbackTrans_commShift : NatTrans.CommShift (flatPullbackTrans f) ℤ :=
  NatTrans.CommShift.verticalComposition
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
    (f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
    (derivedPullbackComparison f) (flatPullbackTrans f) ℤ rfl

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- At a K-flat complex with flat terms the comparison is
`Stacks.Sheaves.DerivedPullback.flatPullbackIso`: the associators and the factorisation through
the degreewise functor are identities in each component. -/
theorem flatPullbackTrans_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (flatPullbackTrans f).app K = (flatPullbackIso f hmos K hK hflat).hom := by
  have h1 : DerivedCategory.Qh.map
        ((f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj K) =
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj K) :=
    (congrArg (fun z => z ≫ (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
            ((pullbackComplex f).obj K))
        ((congrArg DerivedCategory.Qh.map
            (show (f.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K =
              𝟙 _ from rfl)).trans (DerivedCategory.Qh.map_id _))).trans
      (Category.id_comp _)
  dsimp only [flatPullbackTrans, flatPullbackIso, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app]
  simp only [Category.id_comp]
  exact congrArg (fun z => (derivedPullback f).map
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
      (derivedPullbackComparison f).app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)).obj K) ≫ z) h1

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The commutation of `Lf^*` with the shift, at the image of a K-flat complex with flat
terms.**  Read against `Stacks.Sheaves.DerivedPullback.flatPullbackIso`, which computes `Lf^*`
there by the degreewise pullback, it becomes the commutation of the degreewise pullback with the
shift — whose components are identities.

This is the one formula for `((derivedPullback f).commShiftIso n)` that the shifted-unitor
coherence of [Stacks, Tag 07A4] needs: the commutation isomorphism of a left derived functor is
constructed from the universal property and comes with no formula at all, but it is pinned down
at an object where the comparison `Lf^* ⟶ f^*` is invertible. -/
theorem flatPullbackIso_commShift (n : ℤ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (derivedPullback f).map ((DerivedCategory.Q.commShiftIso n).hom.app K) ≫
        ((derivedPullback f).commShiftIso n).hom.app (DerivedCategory.Q.obj K) ≫
          ((flatPullbackIso f hmos K hK hflat).hom)⟦n⟧' =
      (flatPullbackIso f hmos
            ((CategoryTheory.shiftFunctor
              (CochainComplex (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) n).obj K)
            (kFlat_shift Y.O K hK n) (fun i => hflat (i + n))).hom ≫
        DerivedCategory.Q.map (((pullbackComplex f).commShiftIso n).hom.app K) ≫
          (DerivedCategory.Q.commShiftIso n).hom.app ((pullbackComplex f).obj K) := by
  have h := NatTrans.shift_app_comm (flatPullbackTrans f) n K
  rw [CategoryTheory.Functor.commShiftIso_comp_hom_app,
    CategoryTheory.Functor.commShiftIso_comp_hom_app,
    flatPullbackTrans_app f hmos K hK hflat,
    flatPullbackTrans_app f hmos _ (kFlat_shift Y.O K hK n) (fun i => hflat (i + n)),
    Category.assoc] at h
  exact h

end Derived

end Stacks.Sheaves.DerivedPullback

end
