module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoLocalization
public import StacksFrontier.CategoryTheory.Functor.FlipObjOfUncurryIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ComparisonCommShift

/-!
# Derived pullback, the derived tensor product and the shift

Let `f` be a morphism of ringed topoi. This file collects the pieces of the isomorphism
`Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of Stacks 07A4, on K-flat complexes with flat terms, which
commute with the shift in the first variable.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackNatIsoOf`: `Lf^*(QK) ≅ Q(f^*K)` as an
  isomorphism of functors of a K-flat complex `K` with flat terms, commuting with the shift.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexFlipObjIso_commShift`:
  the comparison `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` of Stacks 03EL commutes with the shift in `K`.

These are assembled in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorFlipCommShift`
into `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorFlipObjIso_commShift`:
Stacks 07A4 with the second variable fixed commutes with the shift in the first, for the canonical
derived tensor products.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

universe c u d c'

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

variable (Y) in
/-- The K-flat complexes with flat terms, as a property of cochain complexes. -/
abbrev flatKFlatComplexes :
    ObjectProperty (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :=
  fun K => CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K ∧
    ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)

/-- The K-flat complexes with flat terms are stable under the shift. -/
instance flatKFlatComplexes_isStableUnderShift :
    (flatKFlatComplexes Y).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ hK =>
    ⟨CochainComplex.KFlatBifunctor.kFlat_shift _ hK.1 n, fun i => hK.2 (i + n)⟩⟩

/-- `Lf^*(QK) ≅ Q(f^*K)` as an isomorphism of functors of `P`, for a functor `ι'` to complexes
whose values are K-flat with flat terms. -/
noncomputable def flatPullbackNatIsoOf {V : Type*} [Category V]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hι' : ∀ P, flatKFlatComplexes Y (ι'.obj P)) :
    ι' ⋙ DerivedCategory.Q ⋙ derivedPullback f ≅ ι' ⋙ pullbackComplex f ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun P => flatPullbackIso f (ι'.obj P) (hι' P).1 (hι' P).2)
    (fun {P P'} a => flatPullbackIso_naturality f (ι'.map a) (hι' P).1 (hι' P').1
      (hι' P).2 (hι' P').2)

/-- The component of `flatPullbackNatIsoOf` at `P` is `flatPullbackIso`. -/
lemma flatPullbackNatIsoOf_hom_app {V : Type*} [Category V]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hι' : ∀ P, flatKFlatComplexes Y (ι'.obj P)) (P : V) :
    (flatPullbackNatIsoOf f ι' hι').hom.app P =
      (flatPullbackIso f (ι'.obj P) (hι' P).1 (hι' P).2).hom := rfl

/-- The isomorphism `flatPullbackNatIsoOf` commutes with the shift. -/
instance flatPullbackNatIsoOf_commShift {V : Type*} [Category V] [HasShift V ℤ]
    (ι' : V ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    [ι'.CommShift ℤ] (hι' : ∀ P, flatKFlatComplexes Y (ι'.obj P)) :
    NatTrans.CommShift (flatPullbackNatIsoOf f ι' hι').hom ℤ := by
  refine NatTrans.commShift_of_eq (θ :=
    Functor.whiskerLeft ι'
      (Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (derivedPullback f)) ≫
    Functor.whiskerLeft ι' (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ι'
      (Functor.whiskerLeft (HomotopyCategory.quotient _ _) (derivedPullbackComparison f)) ≫
    Functor.whiskerLeft ι' (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft ι'
      (Functor.whiskerRight ((f.toModulesHom.pullbackModules).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh) ≫
    Functor.whiskerLeft ι' (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ι'
      (Functor.whiskerLeft (pullbackComplex f) (DerivedCategory.quotientCompQhIso _).hom)) ?_
  ext P
  refine (flatPullbackIso_hom_eq f (ι'.obj P) (hι' P).1 (hι' P).2).trans ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom, Functor.comp_obj]
  have h0 := DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    ((pullbackComplex f).obj (ι'.obj P)))
  refine Eq.symm ((congrArg (fun x => (derivedPullback f).map
      ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).inv.app
        (ι'.obj P)) ≫ (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (ι'.obj P)) ≫ x ≫
        (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).hom.app
              ((pullbackComplex f).obj (ι'.obj P))) h0).trans ?_)
  exact congrArg (fun x => _ ≫ _ ≫ x) (Category.id_comp _)

end Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- The comparison `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` of Stacks 03EL as an isomorphism of
functors of `K`. -/
noncomputable def pullbackTensorTotalComplexFlipObjIso
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O).map₂CochainComplex.flip.obj L ⋙
        pullbackComplex f ≅
      pullbackComplex f ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.obj
          ((pullbackComplex f).obj L) :=
  NatIso.ofComponents (fun K => pullbackTensorTotalComplexIso f K L) (fun {K K'} a => by
    refine (pullbackTensorTotalComplexIso_hom_naturality f a (𝟙 L)).trans ?_
    rw [CategoryTheory.Functor.map_id]
    rfl)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The component of `pullbackTensorTotalComplexFlipObjIso f L` at `K` is
`pullbackTensorTotalComplexIso f K L`. -/
lemma pullbackTensorTotalComplexFlipObjIso_hom_app
    (L K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackTensorTotalComplexFlipObjIso f L).hom.app K =
      (pullbackTensorTotalComplexIso f K L).hom := rfl

/-- The comparison of total tensor complexes of Stacks 03EL commutes with the shift in the first
variable. -/
instance pullbackTensorTotalComplexFlipObjIso_commShift
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    NatTrans.CommShift (pullbackTensorTotalComplexFlipObjIso f L).hom ℤ :=
  CochainComplex.commShift_of_ιMapBifunctor
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toModulesHom)
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    L (pullbackTensorTotalComplexFlipObjIso f L).hom
    (fun a b => (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (a, b))
    (fun K p q n h =>
      Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom f.toModulesHom K L p q n h)
    (fun K n _ _ _ h => Stacks.Sheaves.DerivedPullback.hom_ext_pullbackTotal f.toModulesHom K L n h)

end Stacks.Cohomology.DerivedPullbackOfToposHom


namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J (Type u)] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify Y.J (Type u)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Every object of `D(𝒪')` is the class of a K-flat complex with flat terms. -/
lemma exists_flatKFlatComplexes_iso
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    ∃ N, flatKFlatComplexes Y N ∧ Nonempty (DerivedCategory.Q.obj N ≅ L) := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) L
  obtain ⟨K, hK, s, hs⟩ := hasResolutions_isKFlat (Y := Y) M
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) s hs
  exact ⟨K.as, hK, ⟨(DerivedCategory.quotientCompQhIso _).symm.app K.as ≪≫
    @asIso _ _ _ _ (DerivedCategory.Qh.map s) this ≪≫ e⟩⟩

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
