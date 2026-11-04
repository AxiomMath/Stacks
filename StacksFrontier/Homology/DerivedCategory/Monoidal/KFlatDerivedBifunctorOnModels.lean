module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor

/-!
# The comparison of the two derived tensor products, computed on K-flat complexes

`CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso` identifies the tensor product of
`CochainComplex.KFlatMonoidal.derivedMonoidal` with
`CochainComplex.KFlatBifunctor.derivedBifunctor`, but it is produced by a universal property
and is therefore a black box: nothing about it is known at any particular pair of objects.
This file computes it at the image of a pair of K-flat complexes, where both sides have a
comparison with the total tensor product of complexes — `derivedTensorIso` on the monoidal
side, `CochainComplex.KFlatBifunctor.comparison` on the derived-bifunctor side — and shows
that it is the one followed by the inverse of the other.

That is what makes the two K-flat comparisons interchangeable, and so lets a coherence
equation proved for one be read off for the other.  It is the missing link between the
constraints of `derivedMonoidal`, which are known on K-flat representatives
(`CochainComplex.KFlatMonoidal.associator_derivedTensorIso`,
`braiding_derivedTensorIso`), and a monoidal structure re-seated onto a prescribed derived
tensor bifunctor, whose comparison is that bifunctor's own.

## Main results

* `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso_hom`: the `eqToIso` factor of
  `derivedMonoidalTensorIso` is an identity, so the comparison is
  `derivedLocalizedTensorIso`.
* `CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso_hom_app_app`: its component at the
  image of a pair of K-flat objects of `K(A)` is Mathlib's localized tensorator followed by
  the inverse of `CochainComplex.KFlatBifunctor.derivedBifunctorComparisonIso`.
* `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso_hom_app_app_comp_comparison`: **the
  comparison, at the image of a pair of K-flat complexes, carries
  `CochainComplex.KFlatBifunctor.comparison` back to `derivedTensorIso`.**

## Implementation notes

The proof is a cancellation and nothing more.  Both `derivedTensorIso` and
`CochainComplex.KFlatBifunctor.comparison` are built from the *same* two descent data — the
`CategoryTheory.Localization.Lifting₂` isomorphism of the K-flat localization and the one of
the homotopy localization — with the `Q` versus `Qh ∘ quotient` bridge
`DerivedCategory.quotientCompQhIso` inserted in each variable.  The component of
`derivedLocalizedTensorIso` at images of K-flat objects, read off
`CategoryTheory.Localization.lift₂NatTrans_app_app`, carries the *inverse* of the first of
those; composing with `comparison` cancels it, and what is left is `derivedTensorIso` with
the three bridges transported into place by naturality.

Two identifications are definitional and are used as such.  The homotopy-level `Lifting₂`
isomorphism of `CochainComplex.KFlatBifunctor.totalToHomotopy` *is* Mathlib's localized
tensorator `homotopyMu`, because `homotopyBifunctor` of `curriedTensor A` is
`CategoryTheory.Localization.Monoidal.tensorBifunctor` of the homotopy quotient; and
`kFlatQ` of `ObjectProperty.isoMk` of a morphism is `DerivedCategory.Qh` of that morphism.

The `eqToIso` factor of `derivedMonoidalTensorIso` has to be removed in term mode.  Its two
endpoints are definitionally equal but not syntactically so, so `CategoryTheory.eqToHom_refl`
does not match as a rewrite; applied as a term it elaborates, the unifier doing the
definitional work, and `congrArg` then moves it under the composition.
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

/-- **The homotopy-level descent datum of the total complex is Mathlib's localized
tensorator.**  `homotopyBifunctor` of `curriedTensor A` is
`CategoryTheory.Localization.Monoidal.tensorBifunctor` of the homotopy quotient, and both
descent data are the canonical `CategoryTheory.Localization.Lifting₂` of the same
`CategoryTheory.Localization.lift₂`, so this is `rfl`. -/
theorem lifting₂Iso_totalToHomotopy_app_app (K L : CochainComplex A ℤ) :
    (((Localization.Lifting₂.iso
        (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
        (totalToHomotopy (curriedTensor A))
        (homotopyBifunctor (curriedTensor A))).app K).app L).hom =
      (homotopyMu A K L).hom :=
  rfl

section Derived

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **`derivedMonoidalTensorIso` is `derivedLocalizedTensorIso`**: the `eqToIso` factor
transporting the tensor product of `derivedMonoidal` to `derivedLocalizedTensor` is an
identity, `CochainComplex.KFlatMonoidal.curriedTensor_derivedMonoidal` being `rfl`. -/
theorem derivedMonoidalTensorIso_hom :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    (derivedMonoidalTensorIso A hres).hom = (derivedLocalizedTensorIso A).hom :=
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  (congrArg (fun m : @curriedTensor (DerivedCategory A) _ (derivedMonoidal A hres) ⟶
        derivedLocalizedTensor A => m ≫ (derivedLocalizedTensorIso A).hom)
      (eqToHom_refl _ (curriedTensor_derivedMonoidal A hres))).trans (Category.id_comp _)

include hres in
/-- Mathlib's localized tensorator of the K-flat localization at a pair of K-flat complexes,
ascribed at `D(A)`.

`CategoryTheory.Localization.Monoidal.μ` lives in the type synonym
`CategoryTheory.LocalizedMonoidal`, so its composition is at that type's `Category` instance,
not at `D(A)`'s.  The two are definitionally equal and `Lean` accepts a composite mixing them,
but `CategoryTheory.Category.assoc` then has no single instance to match against and *cannot
fire*.  Ascribing once here puts every composite below at one instance. -/
def derivedMu {K L : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    (letI := derivedMonoidal A hres
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⊗
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ⟶
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).hom

include hres in
/-- The descent datum of `CochainComplex.KFlatBifunctor.derivedBifunctor` at a pair of K-flat
objects of `K(A)`, named rather than written out.  It occurs once in each direction — inverted
in `derivedTensorCompare_kFlat` and straight in
`derivedTensorCompare_comp_comparison_eq` — and naming it is what lets the two cancel: written
out, `CategoryTheory.Iso.app` is projected away and `CategoryTheory.Iso.inv_hom_id_assoc` no
longer matches. -/
def derivedBifunctorMu {K L : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (hL : KFlat (curriedTensor A) L) :
    (letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    ((derivedBifunctor (curriedTensor A)).obj
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  ((derivedBifunctorComparisonIso (curriedTensor A)).app
      ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, kFlatLeft_of_kFlat A hK⟩).app
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩

include hres in
/-- **The comparison of the two derived tensor bifunctors, at the image of a pair of K-flat
objects of `K(A)`**: it is Mathlib's localized tensorator of the K-flat localization followed
by the inverse of the descent datum of `derivedBifunctor`.  This is
`CategoryTheory.Localization.lift₂NatTrans_app_app` for the identity transformation. -/
theorem derivedLocalizedTensorIso_hom_app_app {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    (((derivedLocalizedTensorIso A).hom.app
          ((kFlatQ (curriedTensor A)).obj
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩)).app
        ((kFlatQ (curriedTensor A)).obj
          ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩)) =
      derivedMu A hres hK hL ≫
        (((derivedBifunctorComparisonIso (curriedTensor A)).app
              ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K,
                kFlatLeft_of_kFlat A hK⟩).app
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).inv := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedLocalizedTensorLifting A
  let := derivedBifunctorLiftingKFlatQ A
  refine (Localization.lift₂NatTrans_app_app (kFlatQ (curriedTensor A)) (kFlatQ (curriedTensor A))
    (kFlatQuasiIso (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
    (derivedTensorSource A) (derivedTensorSource A) (derivedLocalizedTensor A)
    (derivedBifunctor (curriedTensor A)) (Iso.refl _).hom
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

include hres in
/-- **The comparison of the two derived tensor bifunctors at a pair of objects**, with its
source ascribed at the tensor product of `derivedMonoidal`.

This ascription is the whole reason the file is organised this way.  `X ⊗ Y` for
`derivedMonoidal` and `(derivedLocalizedTensor A).obj X |>.obj Y` are definitionally equal, but
identifying them needs `DerivedCategory.Qh` unfolded, which the module system does not expose;
so a goal mixing the two spellings is not type-correct at `implicit` transparency and *no*
rewriting tactic — not even `Category.assoc` — can act on it.  Pinning the spelling once here
keeps every statement below on one side of that line. -/
def derivedTensorCompare (X Y : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    X ⊗ Y ⟶ ((derivedBifunctor (curriedTensor A)).obj X).obj Y :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  ((derivedLocalizedTensorIso A).hom.app X).app Y

include hres in
/-- **`derivedTensorCompare` at the image of a pair of K-flat complexes.**  This is
`CochainComplex.KFlatMonoidal.derivedLocalizedTensorIso_hom_app_app`, re-ascribed. -/
theorem derivedTensorCompare_kFlat {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    derivedTensorCompare A hres
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) =
      derivedMu A hres hK hL ≫ (derivedBifunctorMu A hres hK hL).inv :=
  derivedLocalizedTensorIso_hom_app_app A hres hK hL

include hres in
/-- **`derivedTensorCompare` composed with the descent datum of `derivedBifunctor` is
Mathlib's localized tensorator**, reassociated.  This is the shape in which
`derivedTensorCompare_kFlat` is consumed: the descent datum occurs inverted there and straight
in `CochainComplex.KFlatBifunctor.comparison`, and cancelling the two here, where the
trailing morphism is a variable, keeps both spellings of the object it cancels to out of the
goal. -/
theorem derivedTensorCompare_kFlat_comp {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    ∀ {W : DerivedCategory A}
      (t : DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⊗
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ⟶ W),
      derivedTensorCompare A hres
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) ≫
          (derivedBifunctorMu A hres hK hL).hom ≫ t = derivedMu A hres hK hL ≫ t := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  intro W t
  rw [derivedTensorCompare_kFlat A hres hK hL, Category.assoc, Iso.inv_hom_id_assoc]

/-- Postcomposing both sides of an equation of composites with `t`, reassociated. -/
private theorem comp_assoc_congr {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z}
    {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) {V : C} (t : Z ⟶ V) :
    a ≫ b ≫ t = c ≫ d ≫ t := by
  rw [← Category.assoc, h, Category.assoc]

include hres in
/-- **Naturality of `derivedTensorCompare` in the first variable**, reassociated. -/
theorem derivedTensorCompare_naturality_left {X X' : DerivedCategory A} (f : X ⟶ X')
    (Z : DerivedCategory A) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    ∀ {W : DerivedCategory A} (t : ((derivedBifunctor (curriedTensor A)).obj X').obj Z ⟶ W),
      f ▷ Z ≫ derivedTensorCompare A hres X' Z ≫ t =
        derivedTensorCompare A hres X Z ≫
          ((derivedBifunctor (curriedTensor A)).map f).app Z ≫ t :=
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  fun t ↦ comp_assoc_congr (NatTrans.naturality_app (derivedLocalizedTensorIso A).hom Z f) t

include hres in
/-- **Naturality of `derivedTensorCompare` in the second variable**, reassociated. -/
theorem derivedTensorCompare_naturality_right (X : DerivedCategory A)
    {Y Y' : DerivedCategory A} (g : Y ⟶ Y') :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    ∀ {W : DerivedCategory A} (t : ((derivedBifunctor (curriedTensor A)).obj X).obj Y' ⟶ W),
      X ◁ g ≫ derivedTensorCompare A hres X Y' ≫ t =
        derivedTensorCompare A hres X Y ≫
          ((derivedBifunctor (curriedTensor A)).obj X).map g ≫ t :=
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  fun t ↦ comp_assoc_congr (((derivedLocalizedTensorIso A).hom.app X).naturality g) t

include hres in
/-- **The five factors of `derivedTensorIso`**, with the total tensor complex written in the
monoidal spelling.  Every step is `rfl`: `CategoryTheory.Iso.trans`, `Functor.mapIso` and
`CategoryTheory.MonoidalCategory.tensorIso` all project, `kFlatQ` of `ObjectProperty.isoMk` is
`DerivedCategory.Qh` of the underlying morphism, and `derivedQIso` is an abbreviation. -/
theorem derivedTensorIso_hom_eq {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    (derivedTensorIso A hres hK hL).hom =
      ((derivedQIso A K).inv ⊗ₘ (derivedQIso A L).inv) ≫
        derivedMu A hres hK hL ≫
          DerivedCategory.Qh.map (homotopyMu A K L).hom ≫ (derivedQIso A (K ⊗ L)).hom :=
  rfl

include hres in
/-- **The five factors of `CochainComplex.KFlatBifunctor.comparison`**, with the total tensor
complex written in the monoidal spelling and the homotopy descent datum written as
`homotopyMu`.  Stated after one composition with `derivedTensorCompare`, which is the only
shape it is used in; the ascription of the target to `Q (K ⊗ L)` is what the statement is
for. -/
theorem derivedTensorCompare_comp_comparison_eq {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    letI := derivedMonoidal A hres
    derivedTensorCompare A hres (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
          (comparison (curriedTensor A) K L (kFlatLeft_of_kFlat A hK) hL).hom =
      derivedTensorCompare A hres (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor (curriedTensor A)).map (derivedQIso A K).inv).app
            (DerivedCategory.Q.obj L) ≫
          ((derivedBifunctor (curriedTensor A)).obj
                (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).map
              (derivedQIso A L).inv ≫
            (derivedBifunctorMu A hres hK hL).hom ≫
              DerivedCategory.Qh.map (homotopyMu A K L).hom ≫
                (derivedQIso A (K ⊗ L)).hom :=
  rfl

include hres in
/-- **The comparison of the two derived tensor products carries the K-flat comparison of
`CochainComplex.KFlatBifunctor.derivedBifunctor` back to the K-flat comparison
`derivedTensorIso` of `derivedMonoidal`.**

This is the identity that makes the two comparisons interchangeable: a coherence equation for
one of them is, through it, a coherence equation for the other.  The proof cancels the descent
datum of `derivedBifunctor`, which the two carry in opposite directions, and then the three
`DerivedCategory.quotientCompQhIso` bridges against each other. -/
theorem derivedTensorCompare_comp_comparison {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
    derivedTensorCompare A hres (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        (comparison (curriedTensor A) K L (kFlatLeft_of_kFlat A hK) hL).hom =
      (derivedTensorIso A hres hK hL).hom := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  let := kFlatQLeft_isLocalization (curriedTensor A) (exists_kFlatLeft_quasiIso A hres)
  let := derivedMonoidal A hres
  refine (derivedTensorCompare_comp_comparison_eq A hres hK hL).trans
    (Eq.trans ?_ (derivedTensorIso_hom_eq A hres hK hL).symm)
  refine (cancel_epi ((derivedQIso A K).hom ⊗ₘ (derivedQIso A L).hom)).1 ?_
  rw [tensorHom_def_assoc, derivedTensorCompare_naturality_right A hres,
    derivedTensorCompare_naturality_left A hres,
    ← ((derivedBifunctor (curriedTensor A)).map (derivedQIso A K).hom).naturality_assoc]
  simp only [Iso.app_hom, Iso.app_inv, cancelIso, tensorHom_comp_tensorHom_assoc,
    Iso.hom_inv_id_app, Functor.comp_obj, tensorHom_id, id_whiskerRight, Category.id_comp]
  exact derivedTensorCompare_kFlat_comp A hres hK hL _

end Derived

end CochainComplex.KFlatMonoidal

end
