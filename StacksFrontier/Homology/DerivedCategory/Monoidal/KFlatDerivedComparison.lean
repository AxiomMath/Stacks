module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedTwoSided
public import StacksFrontier.CategoryTheory.Category.CompositionChains

/-!
# The localized tensor product and the two-sided K-flat comparison

`CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso` identifies the localized tensor
bifunctor of `D(A)` — the tensor product of
`CochainComplex.KFlatMonoidal.derivedMonoidal` — with the generic derived bifunctor
`CochainComplex.KFlatBifunctor.derivedBifunctor`.  Each of the two carries its own comparison
with the image of the total tensor product of complexes: the tensorator of the two
localizations on the one side and `CochainComplex.KFlatBifunctor.comparison` on the other.
This file shows that the identification matches them up.

## Main results

* `CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso_hom_app_app'`: the identification, at
  the images of two K-flat complexes, is the tensorator of the second localization followed by
  the inverse of the K-flat comparison of `derivedBifunctor`.
* `CochainComplex.KFlatMonoidal.comparison_hom`: `comparison` written out as a composite.
* `CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso_comp_comparison`: **the
  identification followed by `comparison` is the comparison of `derivedMonoidal`**, written as
  the tensorator of the two localizations conjugated by the `Q` versus `Qh ∘ quotient` bridges.
  This is the shape in which the clause of Stacks Tag 0FPT on the commutativity constraint is
  reduced to the already-proved statement for the localized structure.

## Implementation notes

Every statement below is proved in term mode, through the generic lemmas of
`StacksFrontier/CategoryTheory/Category/CompositionChains.lean`.  The reason is transparency:
`CategoryTheory.Localization.Monoidal.μ` is typed at the type synonym
`CategoryTheory.LocalizedMonoidal`, and a goal mixing it with morphisms typed at
`DerivedCategory A` is not type-correct at the transparency `rw` and `simp` unify their
`Category` instance argument at, so neither `Category.assoc` nor `Iso.trans_hom` fires on such
a composite.  Applying a lemma stated in a bare category by `exact` discharges the definitional
equality once, at elaboration.

For the same reason the tensorator of the first localization is given a name here,
`homotopyMuAux`, which spells it as the `CategoryTheory.Localization.Lifting₂` isomorphism it is
rather than through the synonym, and the tensorator of the second localization is written out in
that spelling at each occurrence; `homotopyMuAux_eq` and `derivedMu_eq` record that nothing
changes.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization CochainComplex.KFlatBifunctor

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopyBraided

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]

attribute [local instance] derivedLocalizedTensorLifting derivedBifunctorLiftingKFlatQ

/-! ### The two tensorators, spelled without the type synonym -/

omit [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- **The tensorator of the second localization is `CategoryTheory.Localization.Monoidal.μ`**,
read as the `Localization.Lifting₂` isomorphism of `derivedLocalizedTensor` rather than through
the type synonym `CategoryTheory.LocalizedMonoidal` that `μ` is typed at: the two are the same
term. -/
theorem derivedMu_eq (X Y : (kFlatObjects (curriedTensor A)).FullSubcategory) :
    ((Localization.Lifting₂.iso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
          (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (derivedTensorSource A) (derivedLocalizedTensor A)).app X).app Y =
      Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
        (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X Y := rfl

/-- The tensorator of the first localization, read as the `Localization.Lifting₂` isomorphism
of `homotopyBifunctor`: this is the spelling `CochainComplex.KFlatBifunctor.comparison` is
built from, and it mentions neither the monoidal structure of `K(A)` nor its synonym. -/
abbrev homotopyMuAux (K L : CochainComplex A ℤ) :=
  ((Localization.Lifting₂.iso
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (totalToHomotopy (curriedTensor A))
      (homotopyBifunctor (curriedTensor A))).app K).app L

omit [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- `homotopyMuAux` is `CochainComplex.KFlatMonoidal.homotopyMu`, the tensorator of the
monoidal localization at the homotopy equivalences. -/
theorem homotopyMuAux_eq (K L : CochainComplex A ℤ) :
    homotopyMuAux A K L = homotopyMu A K L := rfl

/-! ### The identification at a pair of K-flat objects -/

/-- **The identification of `derivedLocalizedTensor` with `derivedBifunctor`, at the images of
two K-flat complexes**: it is the tensorator of the second localization followed by the inverse
of the K-flat comparison of `derivedBifunctor`.  The left K-flatness witness is named. -/
theorem derivedLocalizedTensorIso_hom_app_app' {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hK' : KFlatLeft (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    ((derivedLocalizedTensorIso A).hom.app ((DerivedCategory.Qh (C := A)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).app
        ((DerivedCategory.Qh (C := A)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) =
      (((Localization.Lifting₂.iso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
        (derivedTensorSource A) (derivedLocalizedTensor A)).app
          (kFlatObjOf (curriedTensor A) K hK)).app (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (((derivedBifunctorComparisonIso (curriedTensor A)).app
          (kFlatObjLeftOf (curriedTensor A) K hK')).app
          (kFlatObjOf (curriedTensor A) L hL)).inv := by
  refine (Localization.lift₂NatTrans_app_app (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (derivedTensorSource A) (derivedTensorSource A) (derivedLocalizedTensor A)
    (derivedBifunctor (curriedTensor A)) (Iso.refl _).hom
    (kFlatObjOf (curriedTensor A) K hK) (kFlatObjOf (curriedTensor A) L hL)).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- The identification followed by the K-flat comparison of `derivedBifunctor` is the
tensorator of the second localization. -/
theorem derivedLocalizedTensorIso_hom_app_app_comp {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hK' : KFlatLeft (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    ((derivedLocalizedTensorIso A).hom.app ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).app
          ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
        (((derivedBifunctorComparisonIso (curriedTensor A)).app
          (kFlatObjLeftOf (curriedTensor A) K hK')).app
          (kFlatObjOf (curriedTensor A) L hL)).hom =
      (((Localization.Lifting₂.iso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
        (derivedTensorSource A) (derivedLocalizedTensor A)).app
          (kFlatObjOf (curriedTensor A) K hK)).app (kFlatObjOf (curriedTensor A) L hL)).hom :=
  comp_iso_hom_of_eq_comp_inv _ (derivedLocalizedTensorIso_hom_app_app' A hK hK' hL)

/-! ### The two-sided comparison as a composite -/

omit [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory (CochainComplex A ℤ)] in
/-- `CochainComplex.KFlatBifunctor.comparison` written out as a composite, with the two
`DerivedCategory.quotientCompQhIso` transports read as actions of `derivedBifunctor`. -/
theorem comparison_hom {K L : CochainComplex A ℤ} (hK' : KFlatLeft (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    (comparison (curriedTensor A) K L hK' hL).hom =
      ((derivedBifunctor (curriedTensor A)).map (derivedQIso A K).inv).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor (curriedTensor A)).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          (derivedQIso A L).inv ≫
        (((derivedBifunctorComparisonIso (curriedTensor A)).app
            (kFlatObjLeftOf (curriedTensor A) K hK')).app
            (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (DerivedCategory.Qh (C := A)).map (homotopyMuAux A K L).hom ≫
        (derivedQIso A (totalComplex (curriedTensor A) K L)).hom := by
  dsimp only [comparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]

/-- **The identification of the localized tensor product with the derived bifunctor, followed
by the two-sided K-flat comparison of the latter, is the comparison of `derivedMonoidal`**:
the tensorator of the two localizations, conjugated by the `Q` versus `Qh ∘ quotient`
bridges. -/
theorem derivedLocalizedTensorIso_comp_comparison {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hK' : KFlatLeft (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    ((derivedLocalizedTensorIso A).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (comparison (curriedTensor A) K L hK' hL).hom =
      ((derivedLocalizedTensor A).map (derivedQIso A K).inv).app (DerivedCategory.Q.obj L) ≫
        ((derivedLocalizedTensor A).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          (derivedQIso A L).inv ≫
        (((Localization.Lifting₂.iso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
        (derivedTensorSource A) (derivedLocalizedTensor A)).app
          (kFlatObjOf (curriedTensor A) K hK)).app (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (DerivedCategory.Qh (C := A)).map (homotopyMuAux A K L).hom ≫
        (derivedQIso A (totalComplex (curriedTensor A) K L)).hom := by
  rw [comparison_hom A hK' hL]
  exact comp_chain_two_squares
    (NatTrans.naturality_app (derivedLocalizedTensorIso A).hom
      (DerivedCategory.Q.obj L) (derivedQIso A K).inv)
    (((derivedLocalizedTensorIso A).hom.app
      ((DerivedCategory.Qh (C := A)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).naturality
      (derivedQIso A L).inv)
    (derivedLocalizedTensorIso_hom_app_app_comp A hK hK' hL)

/-! ### The comparison of `derivedMonoidal` on two K-flat complexes -/

section Monoidal

variable (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
  KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- The tensorator of the first localization, read in the full monoidal subcategory of K-flat
objects of `K(A)`.  This is the isomorphism
`CochainComplex.KFlatMonoidal.derivedTensorIso` is built from. -/
abbrev kFlatHomotopyMu {K L : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    kFlatObjOf (curriedTensor A) K hK ⊗ kFlatObjOf (curriedTensor A) L hL ≅
      (⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (K ⊗ L),
        kFlat_tensor A hK hL⟩ : (kFlatObjects (curriedTensor A)).FullSubcategory) :=
  (kFlatObjects (curriedTensor A)).isoMk (homotopyMu A K L)

omit [BraidedCategory (CochainComplex A ℤ)]
  [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- `kFlatHomotopyMu`, pushed into `D(A)`, is the tensorator of the first localization in the
spelling `CochainComplex.KFlatBifunctor.comparison` uses. -/
theorem kFlatQ_map_kFlatHomotopyMu {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    (kFlatQ (curriedTensor A)).map (kFlatHomotopyMu A hK hL).hom =
      (DerivedCategory.Qh (C := A)).map (homotopyMuAux A K L).hom := rfl

omit [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- **The comparison of `derivedMonoidal` at two K-flat complexes, as a composite of four
morphisms**: the two `Q` versus `Qh ∘ quotient` bridges on the left, then the tensorator of the
second localization, then that of the first, then the bridge on the right. -/
theorem derivedTensorIso_hom_tensorHom {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    (derivedTensorIso A hres hK hL).hom =
      ((derivedQIso A K).inv ⊗ₘ (derivedQIso A L).inv) ≫
        (((Localization.Lifting₂.iso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
        (derivedTensorSource A) (derivedLocalizedTensor A)).app
          (kFlatObjOf (curriedTensor A) K hK)).app (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (kFlatQ (curriedTensor A)).map (kFlatHomotopyMu A hK hL).hom ≫
        (derivedQIso A (K ⊗ L)).hom := rfl

omit [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
/-- The same with the tensor product of the two bridges expanded into the two one-variable
actions of `derivedLocalizedTensor`, and the tensorator of the first localization in the
spelling `CochainComplex.KFlatBifunctor.comparison` uses. -/
theorem derivedTensorIso_hom {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    (derivedTensorIso A hres hK hL).hom =
      ((derivedLocalizedTensor A).map (derivedQIso A K).inv).app (DerivedCategory.Q.obj L) ≫
        ((derivedLocalizedTensor A).obj ((DerivedCategory.Qh (C := A)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
          (derivedQIso A L).inv ≫
        (((Localization.Lifting₂.iso (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
        (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
        (derivedTensorSource A) (derivedLocalizedTensor A)).app
          (kFlatObjOf (curriedTensor A) K hK)).app (kFlatObjOf (curriedTensor A) L hL)).hom ≫
        (DerivedCategory.Qh (C := A)).map (homotopyMuAux A K L).hom ≫
        (derivedQIso A (totalComplex (curriedTensor A) K L)).hom :=
  Eq.trans rfl (comp_assoc_congr _ _ _ _ (kFlatQ_map_kFlatHomotopyMu A hK hL))

/-- **The identification of the localized tensor product with the derived bifunctor, followed
by the two-sided K-flat comparison of the latter, is the comparison of `derivedMonoidal` with
the total tensor product of complexes.** -/
theorem derivedLocalizedTensorIso_comp_comparison_eq {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hK' : KFlatLeft (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    ((derivedLocalizedTensorIso A).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (comparison (curriedTensor A) K L hK' hL).hom =
      (derivedTensorIso A hres hK hL).hom :=
  (derivedLocalizedTensorIso_comp_comparison A hK hK' hL).trans
    (derivedTensorIso_hom A hres hK hL).symm

end Monoidal

end CochainComplex.KFlatMonoidal

end
