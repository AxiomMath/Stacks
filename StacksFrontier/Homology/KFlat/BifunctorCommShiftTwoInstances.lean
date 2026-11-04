module

public import StacksFrontier.Homology.KFlat.BifunctorShift
public import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwo
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived bifunctor commutes with the shifts in both variables

Let `F : A ⥤ B ⥤ D` be an additive bifunctor between abelian categories whose total complexes
exist.  `CochainComplex.KFlatBifunctor.derivedBifunctor F : D(A) ⥤ D(B) ⥤ D(D)` is the descent of
`Tot(F(-, -))` along the two K-flat localizations.  This file equips it with
`CategoryTheory.Functor.CommShift₂Int`, the two-variable shift coherence of [Stacks, Tag 079U]:
the commutation isomorphisms in the two variables exist, are natural, and commute with each other
up to Mathlib's sign `(-1) ^ (p * q)`.

## Main results

* `CochainComplex.KFlatBifunctor.homotopyBifunctor_commShift₂Int`: the descent of `Tot(F(-, -))`
  to the homotopy categories commutes with the shifts in both variables.
* `CochainComplex.KFlatBifunctor.derivedBifunctor_commShift₂Int`: **the derived bifunctor commutes
  with the shifts in both variables.**
* `CochainComplex.KFlatBifunctor.derivedBifunctor_isTriangulated_flipObj` and
  `derivedBifunctor_isTriangulated_obj`: **the derived bifunctor is exact in each variable at the
  commutation with the shift that the two-variable structure descends**, i.e. at
  `CategoryTheory.Functor.CommShift₂.commShiftFlipObj` and
  `CategoryTheory.Functor.CommShift₂.commShiftObj`.

## Implementation notes

`kFlatToDerived` is written with `CategoryTheory.Functor.whiskeringLeft₂`, and
`((whiskeringLeft₂ E).obj F₁).obj F₂ |>.obj G` unfolds to
`F₁ ⋙ (G ⋙ (whiskeringLeft _ _ _).obj F₂)`, which is the shape that
`CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂` match.  Since `whiskeringLeft₂` is a
plain `def`, instance search does not unfold it, so the instances on `kFlatToDerived F` are given
by `inferInstanceAs` at the unfolded spelling.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory

/-! ### Exactness at a canonically descended commutation with the shift

A `CategoryTheory.Functor.CommShift₂` structure equips `G'.obj Y₁` and `G'.flip.obj Y₂` with a
*canonical* `CategoryTheory.Functor.CommShift`, and `CategoryTheory.Functor.IsTriangulated`
depends on which commutation isomorphisms are in play.  The lemmas here prove exactness at the
structure that `CategoryTheory.Functor.CommShift₂.ofLocalization` produces. -/

namespace CategoryTheory

namespace Functor.CommShift

variable {A₀ B₀ : Type*} [Category* A₀] [Category* B₀] {M : Type*} [AddMonoid M]
  [HasShift A₀ M] [HasShift B₀ M] {G G' : A₀ ⥤ B₀} [G.CommShift M]

/-- **The isomorphism along which `CategoryTheory.Functor.CommShift.ofConj` transports a
commutation with the shift is itself compatible with the shifts.**  This is
`CategoryTheory.Functor.CommShift.ofIso_compatibility` for `ofConj`. -/
theorem natTrans_commShift_ofConj (α : G ≅ G')
    (κ : ∀ n : M, shiftFunctor A₀ n ⋙ G' ≅ G' ⋙ shiftFunctor B₀ n)
    (hκ : ∀ n : M, (G.commShiftIso n).hom ≫ Functor.whiskerRight α.hom (shiftFunctor B₀ n) =
      Functor.whiskerLeft (shiftFunctor A₀ n) α.hom ≫ (κ n).hom) :
    letI := ofConj α κ hκ
    NatTrans.CommShift α.hom M :=
  let := ofConj α κ hκ
  ⟨hκ⟩

end Functor.CommShift

namespace Localization

section WhiskerLeft

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]

/-- **A natural transformation between two functors out of a localization commutes with the
shifts as soon as its restriction along the localization functor does.**  Mathlib has the
converse implication as the instance `CategoryTheory.NatTrans.CommShift.whiskerLeft`. -/
theorem natTrans_commShift_of_whiskerLeft (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [L.CommShift M] {P Q : D ⥤ E} [P.CommShift M] [Q.CommShift M]
    (τ : P ⟶ Q) (h : NatTrans.CommShift (Functor.whiskerLeft L τ) M) :
    NatTrans.CommShift τ M := by
  have := h
  refine ⟨fun n => natTrans_ext L W fun X => ?_⟩
  have hw := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) n X
  have hnat := τ.naturality ((L.commShiftIso n).hom.app X)
  dsimp at hw hnat ⊢
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hw
  simp only [Category.assoc] at hw
  rw [← reassoc_of% hnat] at hw
  exact (Iso.cancel_iso_hom_left (P.mapIso ((L.commShiftIso n).app X)) _ _).mp hw

end WhiskerLeft

section Triangulated

open Limits Pretriangulated

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [HasShift C ℤ]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  [HasZeroObject E] [HasShift E ℤ] [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E]

/-- **Two functors out of a localization which lift the same functor are exact together**, for
the commutations with the shift that they inherit from the lifting data. -/
theorem isTriangulated_of_lifting (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [L.CommShift ℤ] (G₀ : C ⥤ E) [G₀.CommShift ℤ] (P Q : D ⥤ E) [P.CommShift ℤ]
    [P.IsTriangulated] [Lifting L W G₀ Q] (eP : L ⋙ P ≅ G₀)
    (hP : NatTrans.CommShift eP.hom ℤ) :
    letI := Functor.commShiftOfLocalization L W ℤ G₀ Q
    Q.IsTriangulated := by
  let := Functor.commShiftOfLocalization L W ℤ G₀ Q
  have := hP
  let : Lifting L W G₀ P := ⟨eP⟩
  have : NatTrans.CommShift (liftNatIso L W G₀ G₀ P Q (Iso.refl G₀)).hom ℤ := by
    refine natTrans_commShift_of_whiskerLeft L W _ ?_
    have heq : Functor.whiskerLeft L (liftNatIso L W G₀ G₀ P Q (Iso.refl G₀)).hom =
        (Lifting.iso L W G₀ P).hom ≫ (Lifting.iso L W G₀ Q).inv := by
      ext X
      simp
    rw [heq]
    infer_instance
  exact Functor.isTriangulated_of_iso (liftNatIso L W G₀ G₀ P Q (Iso.refl G₀))

end Triangulated

section ObjCommShift

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E] {M : Type*} [AddMonoid M] [HasShift C₂ M] [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₂.CommShift M]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ G G']
  [∀ X₁ : C₁, (G.obj X₁).CommShift M]
  [∀ (X₁ Y₁ : C₁) (f : X₁ ⟶ Y₁), NatTrans.CommShift (G.map f) M]

/-- **The isomorphism `G'.obj Y₁ ≅ G'.obj (L₁.obj (L₁.objPreimage Y₁))` used to build
`CategoryTheory.Localization.objCommShift` is compatible with the shifts.** -/
theorem natTrans_commShift_objCommShift (Y₁ : D₁) :
    haveI := Localization.essSurj L₁ W₁
    letI := Lifting₂.fst L₁ L₂ W₁ W₂ G G' (L₁.objPreimage Y₁)
    letI := Functor.commShiftOfLocalization L₂ W₂ M (G.obj (L₁.objPreimage Y₁))
      (G'.obj (L₁.obj (L₁.objPreimage Y₁)))
    letI := objCommShift (M := M) L₁ L₂ W₁ W₂ G G' Y₁
    NatTrans.CommShift (G'.mapIso (L₁.objObjPreimageIso Y₁)).hom M := by
  have := Localization.essSurj L₁ W₁
  let := Lifting₂.fst L₁ L₂ W₁ W₂ G G' (L₁.objPreimage Y₁)
  let := Functor.commShiftOfLocalization L₂ W₂ M (G.obj (L₁.objPreimage Y₁))
    (G'.obj (L₁.obj (L₁.objPreimage Y₁)))
  exact Functor.CommShift.natTrans_commShift_ofConj
    (G'.mapIso (L₁.objObjPreimageIso Y₁))
    (fun n => (bifunctorCommShiftIso L₁ L₂ W₁ W₂ G G' n).app Y₁)
    (fun n => by
      rw [bifunctorCommShiftIso_hom_app_image]
      exact ((bifunctorCommShiftIso L₁ L₂ W₁ W₂ G G' n).hom.naturality
        (L₁.objObjPreimageIso Y₁).hom).symm)

end ObjCommShift

section ObjCommShiftTriangulated

open Limits Pretriangulated

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E] [HasShift C₂ ℤ]
  [HasZeroObject D₂] [HasShift D₂ ℤ] [Preadditive D₂] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [Pretriangulated D₂]
  [HasZeroObject E] [HasShift E ℤ] [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₂.CommShift ℤ]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ G G']
  [∀ X₁ : C₁, (G.obj X₁).CommShift ℤ]
  [∀ (X₁ Y₁ : C₁) (f : X₁ ⟶ Y₁), NatTrans.CommShift (G.map f) ℤ]

/-- **A bifunctor descended through two localizations is exact in the second variable at the
canonically descended commutation with the shift**, as soon as it is exact over the image of the
first localization functor. -/
theorem isTriangulated_objCommShift
    (h : ∀ X₁ : C₁,
      letI := Lifting₂.fst L₁ L₂ W₁ W₂ G G' X₁
      letI := Functor.commShiftOfLocalization L₂ W₂ ℤ (G.obj X₁) (G'.obj (L₁.obj X₁))
      (G'.obj (L₁.obj X₁)).IsTriangulated)
    (Y₁ : D₁) :
    letI := objCommShift (M := ℤ) L₁ L₂ W₁ W₂ G G' Y₁
    (G'.obj Y₁).IsTriangulated := by
  let := objCommShift (M := ℤ) L₁ L₂ W₁ W₂ G G' Y₁
  have := Localization.essSurj L₁ W₁
  let := Lifting₂.fst L₁ L₂ W₁ W₂ G G' (L₁.objPreimage Y₁)
  let := Functor.commShiftOfLocalization L₂ W₂ ℤ (G.obj (L₁.objPreimage Y₁))
    (G'.obj (L₁.obj (L₁.objPreimage Y₁)))
  have := h (L₁.objPreimage Y₁)
  have := natTrans_commShift_objCommShift (M := ℤ) L₁ L₂ W₁ W₂ G G' Y₁
  exact Functor.isTriangulated_of_iso (G'.mapIso (L₁.objObjPreimageIso Y₁))

end ObjCommShiftTriangulated

end Localization

end CategoryTheory

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- `totalToHomotopy F` commutes with the shifts in both variables, by instance search. -/
example : (totalToHomotopy F).CommShift₂Int := by infer_instance

/-- **The homotopy-category descent of `Tot(F(-, -))` commutes with the shifts in both
variables.** -/
instance homotopyBifunctor_commShift₂Int : (homotopyBifunctor F).CommShift₂Int :=
  Functor.CommShift₂.ofLocalizationInt
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)

/-- **Fixing the second variable in the homotopy-category descent gives an exact functor**, at
the commutation with the shift that `homotopyBifunctor_commShift₂Int` descends. -/
@[sga "4 XVII 1.1.7" "partial", sga "4½ Etat_0 1.3.3" "Exactness of P•(−"]
instance homotopyBifunctor_isTriangulated_flipObj
    (Y₂ : HomotopyCategory B (ComplexShape.up ℤ)) :
    ((homotopyBifunctor F).flip.obj Y₂).IsTriangulated :=
  Localization.isTriangulated_objCommShift
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (totalToHomotopy F).flip (homotopyBifunctor F).flip
    (fun K₂ => by
      let := Localization.Lifting₂.fst
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (totalToHomotopy F).flip (homotopyBifunctor F).flip K₂
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR F K₂
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated F K₂
      exact Localization.isTriangulated_of_lifting
        (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        ((totalToHomotopy F).flip.obj K₂)
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F K₂)
        ((homotopyBifunctor F).flip.obj
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂))
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors F K₂)
        (Quotient.liftCommShift_compatibility _ _ _ _))
    Y₂

/-- **Fixing the first variable in the homotopy-category descent gives an exact functor**, at
the commutation with the shift that `homotopyBifunctor_commShift₂Int` descends. -/
instance homotopyBifunctor_isTriangulated_obj
    (Y₁ : HomotopyCategory A (ComplexShape.up ℤ)) :
    ((homotopyBifunctor F).obj Y₁).IsTriangulated :=
  Localization.isTriangulated_objCommShift
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)
    (fun K₁ => by
      let := Localization.Lifting₂.fst
        (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        (totalToHomotopy F) (homotopyBifunctor F) K₁
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F K₁
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated F K₁
      exact Localization.isTriangulated_of_lifting
        (HomotopyCategory.quotient B (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
        ((totalToHomotopy F).obj K₁)
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K₁)
        ((homotopyBifunctor F).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K₁))
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors F K₁)
        (Quotient.liftCommShift_compatibility _ _ _ _))
    Y₁

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

/-- **The models bifunctor commutes with the shifts in both variables.**  `kFlatToDerived F` is
`homotopyBifunctor F` postcomposed with `DerivedCategory.Qh` and precomposed in both variables
with the inclusions of the K-flat objects. -/
instance kFlatToDerived_commShift₂Int : (kFlatToDerived F).CommShift₂Int :=
  inferInstanceAs ((kFlatObjectsLeft F).ι ⋙
    ((homotopyBifunctor F ⋙
        (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Qh (C := D))) ⋙
      (Functor.whiskeringLeft _ _ _).obj (kFlatObjects F).ι)).CommShift₂Int

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- **The derived bifunctor commutes with the shifts in both variables**, with Mathlib's sign
`(-1) ^ (p * q)`. -/
instance derivedBifunctor_commShift₂Int : (derivedBifunctor F).CommShift₂Int :=
  Functor.CommShift₂.ofLocalizationInt
    (kFlatQLeft F) (kFlatQ F) (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
    (kFlatToDerived F) (derivedBifunctor F)

/-! ### Exactness in each variable, at the two-variable structure -/

attribute [local instance] kFlatObjects_isTriangulated kFlatObjectsLeft_isTriangulated
  kFlatQ_mapArrow_essSurj kFlatQLeft_mapArrow_essSurj

/-- **Fixing the second variable in the models bifunctor gives an exact functor**, at the
commutation with the shift that `kFlatToDerived_commShift₂Int` builds. -/
instance kFlatToDerived_isTriangulated_flipObj (K : (kFlatObjects F).FullSubcategory) :
    ((kFlatToDerived F).flip.obj K).IsTriangulated :=
  inferInstanceAs ((kFlatObjectsLeft F).ι ⋙
    ((homotopyBifunctor F).flip.obj ((kFlatObjects F).ι.obj K) ⋙
      DerivedCategory.Qh (C := D))).IsTriangulated

/-- **Fixing the first variable in the models bifunctor gives an exact functor**, at the
commutation with the shift that `kFlatToDerived_commShift₂Int` builds. -/
instance kFlatToDerived_isTriangulated_obj (K : (kFlatObjectsLeft F).FullSubcategory) :
    ((kFlatToDerived F).obj K).IsTriangulated :=
  inferInstanceAs ((kFlatObjects F).ι ⋙
    ((homotopyBifunctor F).obj ((kFlatObjectsLeft F).ι.obj K) ⋙
      DerivedCategory.Qh (C := D))).IsTriangulated

/-- **The derived bifunctor is exact in the first variable**, at the commutation with the shift
that `derivedBifunctor_commShift₂Int` descends, namely
`CategoryTheory.Functor.CommShift₂.commShiftFlipObj CategoryTheory.CommShift₂Setup.int L`. -/
instance derivedBifunctor_isTriangulated_flipObj (L : DerivedCategory B) :
    ((derivedBifunctor F).flip.obj L).IsTriangulated :=
  Localization.isTriangulated_objCommShift (kFlatQ F) (kFlatQLeft F)
    (kFlatQuasiIso F) (kFlatQuasiIsoLeft F)
    (kFlatToDerived F).flip (derivedBifunctor F).flip
    (fun K => by
      let := Localization.Lifting₂.fst (kFlatQ F) (kFlatQLeft F)
        (kFlatQuasiIso F) (kFlatQuasiIsoLeft F)
        (kFlatToDerived F).flip (derivedBifunctor F).flip K
      exact Functor.isTriangulated_of_localization (kFlatQLeft F) (kFlatQuasiIsoLeft F)
        ((kFlatToDerived F).flip.obj K)
        ((derivedBifunctor F).flip.obj ((kFlatQ F).obj K)))
    L

/-- **The derived bifunctor is exact in the second variable**, at the commutation with the shift
that `derivedBifunctor_commShift₂Int` descends, namely
`CategoryTheory.Functor.CommShift₂.commShiftObj CategoryTheory.CommShift₂Setup.int K`. -/
instance derivedBifunctor_isTriangulated_obj (K : DerivedCategory A) :
    ((derivedBifunctor F).obj K).IsTriangulated :=
  Localization.isTriangulated_objCommShift (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
    (kFlatToDerived F) (derivedBifunctor F)
    (fun K' => by
      let := Localization.Lifting₂.fst (kFlatQLeft F) (kFlatQ F)
        (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
        (kFlatToDerived F) (derivedBifunctor F) K'
      exact Functor.isTriangulated_of_localization (kFlatQ F) (kFlatQuasiIso F)
        ((kFlatToDerived F).obj K')
        ((derivedBifunctor F).obj ((kFlatQLeft F).obj K')))
    K

/-- Instance search proves that `(derivedBifunctor F).flip.obj L` is exact. -/
example (L : DerivedCategory B) : ((derivedBifunctor F).flip.obj L).IsTriangulated :=
  by infer_instance

/-- Instance search proves that `(derivedBifunctor F).obj K` is exact. -/
example (K : DerivedCategory A) : ((derivedBifunctor F).obj K).IsTriangulated :=
  by infer_instance

/-- `(derivedBifunctor F).flip.obj L` is exact at
`CategoryTheory.Functor.CommShift₂.commShiftFlipObj`, the commutation with the shift given by the
two-variable structure. -/
example (L : DerivedCategory B) :
    letI := Functor.CommShift₂.commShiftFlipObj (G := derivedBifunctor F) CommShift₂Setup.int L
    ((derivedBifunctor F).flip.obj L).IsTriangulated :=
  inferInstance

/-- `(derivedBifunctor F).obj K` is exact at `CategoryTheory.Functor.CommShift₂.commShiftObj`,
the commutation with the shift given by the two-variable structure. -/
example (K : DerivedCategory A) :
    letI := Functor.CommShift₂.commShiftObj (G := derivedBifunctor F) CommShift₂Setup.int K
    ((derivedBifunctor F).obj K).IsTriangulated :=
  inferInstance

end Derived

end CochainComplex.KFlatBifunctor

end
