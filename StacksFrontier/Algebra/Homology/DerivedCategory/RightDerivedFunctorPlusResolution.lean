module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Resolution.Defs.InjectiveResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Computing a bounded-below right derived functor on an injective resolution

Let `T : C ⥤ D` be an additive functor between abelian categories, with `C` having enough
injectives, so that the bounded-below right derived functor `RT : D⁺(C) ⥤ D⁺(D)` and its unit
exist. For an object `A` of `C` and an injective resolution `I` of the complex `A[0]`, the unit
of `RT` at `I` is invertible, and composing it with the image of the resolution map gives a
canonical isomorphism `RT(A[0]) ≅ Q(T(I))`: the derived functor is computed by applying `T`
termwise to the resolution.

## Main definitions

* `DerivedCategory.Plus.quotientCompQhIso`: the localization functor on bounded-below cochain
  complexes factors through the bounded-below homotopy category.
* `DerivedCategory.Plus.singleFunctorIsoCompQh`: the single functor into the bounded-below
  derived category factors through the bounded-below homotopy category.
* `CategoryTheory.Functor.mapSinglePlusIso` and
  `CategoryTheory.Functor.mapSingleFunctorPlusCompQhIso`: an additive functor commutes with
  `A ↦ A[0]`, read in the bounded-below homotopy category and in the bounded-below derived
  category.
* `CategoryTheory.Functor.rightDerivedFunctorPlusInjectiveResolutionIso`: the canonical
  identification of `RT(A[0])` with the image of `T(I)`, for `I` an injective resolution of
  `A[0]`.
* `CochainComplex.InjectiveResolution.qhHom` and `CochainComplex.InjectiveResolution.qhIso`:
  an injective resolution of `A[0]`, read as an isomorphism `A[0] ≅ Qh(I)` in the
  bounded-below derived category.
* `DerivedCategory.Plus.qhHomMk`: a morphism from `A[0]` to a bounded-below cochain complex,
  read as a morphism out of `A[0]` in the bounded-below derived category.
* `CategoryTheory.Functor.mapHomologicalComplexQhIso`: for a bounded-below complex `K`, the
  comparison between the image of `T(K)` under `Q` and under `Qh` after the quotient.
* `CategoryTheory.Functor.mapHomologicalComplexDerivedUnit`: for a bounded-below complex `K`,
  the comparison of `Q(T(K))` with the value of `RT` at the image of `K`.

## Main results

* `CategoryTheory.Functor.rightAcyclic_of_injective`: an injective object is right acyclic.
* `CategoryTheory.Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic`: `T` applied
  termwise to a quasi-isomorphism of bounded-below complexes of right acyclic objects is a
  quasi-isomorphism.
* `CategoryTheory.Functor.mapHomologicalComplexQhIso_hom_naturality` and
  `CategoryTheory.Functor.mapHomologicalComplexQhIso_comp`: that comparison is natural in the
  complex and compatible with composition of functors.
* `CategoryTheory.Functor.mapHomologicalComplexDerivedUnit_naturality`: the comparison with
  the right derived functor is natural in the bounded-below complex.
* `CategoryTheory.Functor.rightDerivedFunctorPlusInjectiveResolutionIso_hom_comp`: the
  identification of `RT(A[0])` with `Q(T(I))` is the one induced by the resolution map.
* `CategoryTheory.Functor.mapSinglePlusIso_inv_app` and
  `CategoryTheory.Functor.mapSingleFunctorPlusCompQhIso_inv_app_eq_qhHomMk`: the comparisons
  of an additive functor with `A ↦ A[0]` are induced by the comparison of cochain complexes.

## Implementation notes

The bounded-below derived category is a full subcategory of the unbounded one, and the
comparisons of the two localization functors and of the two single functors are obtained by
cancelling that embedding on the right of the corresponding unbounded comparison, which is
where their uniqueness comes from. Boundedness of the complexes involved is recorded as a
membership in `CochainComplex.plus`, so the two helper lemmas
`CochainComplex.plus_singleFunctor_obj` and `CochainComplex.plus_mapHomologicalComplex_obj`
produce the memberships for a complex concentrated in degree zero and for the termwise image
of a bounded-below complex.

The bounded-below homotopy and derived categories are full subcategories, so a morphism
between two of their objects can be spelled through either of two definitionally equal
category instances, and `rw` and `simp` match only one of them. The proofs below therefore
pass through explicitly stated intermediate equalities, which are checked at default
transparency, rather than rewriting with the general functoriality lemmas.

## References

* [Stacks Project, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

universe v v' v'' w w' w'' u u' u''

namespace DerivedCategory.Plus

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The localization functor on bounded-below cochain complexes factors through the
bounded-below homotopy category.** This is the bounded-below form of
`DerivedCategory.quotientCompQhIso`. -/
noncomputable def quotientCompQhIso :
    HomotopyCategory.Plus.quotient A ⋙ Qh ≅ Q :=
  Functor.fullyFaithfulCancelRight Plus.ι
    (Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient A) (QhCompιIsoιCompQh A) ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso A) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι A) (DerivedCategory.quotientCompQhIso A))

/-- **The single functor into the bounded-below derived category factors through the
bounded-below homotopy category.** This is the bounded-below form of
`DerivedCategory.singleFunctorIsoCompQh`. -/
noncomputable def singleFunctorIsoCompQh (n : ℤ) :
    singleFunctor A n ≅ HomotopyCategory.Plus.singleFunctor A n ⋙ Qh :=
  Functor.fullyFaithfulCancelRight Plus.ι
    (singleFunctorιIso A n ≪≫ DerivedCategory.singleFunctorIsoCompQh A n ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.Plus.singleFunctorCompιIso A n).symm
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor A n)
        (QhCompιIsoιCompQh A).symm)

end DerivedCategory.Plus

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A complex concentrated in degree zero is bounded below. -/
lemma plus_singleFunctor_obj (X : A) :
    CochainComplex.plus A ((CochainComplex.singleFunctor A 0).obj X) :=
  ⟨0, inferInstance⟩

variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- The termwise image of a bounded-below complex under an additive functor is bounded
below. -/
lemma plus_mapHomologicalComplex_obj (T : A ⥤ B) [T.Additive]
    {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K) :
    CochainComplex.plus B ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨a, _⟩ := (CochainComplex.plus_iff A K).1 hK
  refine (CochainComplex.plus_iff B _).2 ⟨a, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun n hn => T.map_isZero (K.isZero_of_isStrictlyGE a n hn)

end CochainComplex

namespace HomotopyCategory.Plus

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism of bounded-below cochain complexes, read in the bounded-below homotopy
category. -/
noncomputable abbrev quotientHomMk {K L : CochainComplex A ℤ}
    (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L) (g : K ⟶ L) :
    (HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩ ⟶
      (HomotopyCategory.Plus.quotient A).obj ⟨L, hL⟩ :=
  (HomotopyCategory.Plus.quotient A).map (ObjectProperty.homMk g)

/-- **Reading a composite of morphisms of bounded-below cochain complexes in the
bounded-below homotopy category.** -/
lemma quotientHomMk_comp {K L M : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (hL : CochainComplex.plus A L) (hM : CochainComplex.plus A M) (g : K ⟶ L) (g' : L ⟶ M) :
    quotientHomMk hK hL g ≫ quotientHomMk hL hM g' = quotientHomMk hK hM (g ≫ g') :=
  ((HomotopyCategory.Plus.quotient A).map_comp _ _).symm

/-- **A morphism of complexes concentrated in degree zero, read in the bounded-below homotopy
category, is the image of the morphism under the single functor.** -/
lemma quotientHomMk_singleFunctor_map {X Y : A} (u : X ⟶ Y) :
    quotientHomMk (CochainComplex.plus_singleFunctor_obj X)
        (CochainComplex.plus_singleFunctor_obj Y) ((CochainComplex.singleFunctor A 0).map u) =
      (HomotopyCategory.Plus.singleFunctor A 0).map u :=
  rfl

end HomotopyCategory.Plus

namespace DerivedCategory.Plus

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **Composing the localizations of two morphisms of bounded-below cochain complexes.** -/
lemma Qh_map_quotientHomMk_comp {K L M : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (hL : CochainComplex.plus A L) (hM : CochainComplex.plus A M) (g : K ⟶ L) (g' : L ⟶ M) :
    DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk hK hL g) ≫
        DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk hL hM g') =
      DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk hK hM (g ≫ g')) := by
  rw [← Functor.map_comp, HomotopyCategory.Plus.quotientHomMk_comp]

/-- **A morphism from a complex concentrated in degree zero to a bounded-below cochain
complex, read as a morphism out of `X[0]` in the bounded-below derived category.** -/
noncomputable def qhHomMk {K : CochainComplex A ℤ} (X : A) (hK : CochainComplex.plus A K)
    (u : (CochainComplex.singleFunctor A 0).obj X ⟶ K) :
    (DerivedCategory.Plus.singleFunctor A 0).obj X ⟶
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩) :=
  (DerivedCategory.Plus.singleFunctorIsoCompQh A 0).hom.app X ≫
    DerivedCategory.Plus.Qh.map
      (HomotopyCategory.Plus.quotientHomMk (CochainComplex.plus_singleFunctor_obj X) hK u)

/-- **Postcomposing `DerivedCategory.Plus.qhHomMk` with the localization of a morphism of
bounded-below complexes.** -/
lemma qhHomMk_comp {K L : CochainComplex A ℤ} (X : A) (hK : CochainComplex.plus A K)
    (hL : CochainComplex.plus A L) (u : (CochainComplex.singleFunctor A 0).obj X ⟶ K)
    (g : K ⟶ L) :
    qhHomMk X hK u ≫
        DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk hK hL g) =
      qhHomMk X hL (u ≫ g) := by
  have h : DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
          (CochainComplex.plus_singleFunctor_obj X) hK u) ≫
        DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk hK hL g) =
      DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
        (CochainComplex.plus_singleFunctor_obj X) hL (u ≫ g)) :=
    Qh_map_quotientHomMk_comp _ _ _ _ _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (singleFunctorIsoCompQh A 0).hom.app X ≫ z) h)

/-- **Precomposing `DerivedCategory.Plus.qhHomMk` with the image of a morphism under the
single functor.** -/
lemma singleFunctor_map_comp_qhHomMk {K : CochainComplex A ℤ} {X Y : A} (u : X ⟶ Y)
    (hK : CochainComplex.plus A K)
    (v : (CochainComplex.singleFunctor A 0).obj Y ⟶ K) :
    (DerivedCategory.Plus.singleFunctor A 0).map u ≫ qhHomMk Y hK v =
      qhHomMk X hK ((CochainComplex.singleFunctor A 0).map u ≫ v) := by
  have hA : qhHomMk X (CochainComplex.plus_singleFunctor_obj Y)
        ((CochainComplex.singleFunctor A 0).map u) =
      (DerivedCategory.Plus.singleFunctor A 0).map u ≫
        (singleFunctorIsoCompQh A 0).hom.app Y := by
    refine Eq.trans (congrArg (fun m => (singleFunctorIsoCompQh A 0).hom.app X ≫
      DerivedCategory.Plus.Qh.map m)
        (HomotopyCategory.Plus.quotientHomMk_singleFunctor_map (A := A) u)) ?_
    exact ((singleFunctorIsoCompQh A 0).hom.naturality u).symm
  rw [← qhHomMk_comp X (CochainComplex.plus_singleFunctor_obj Y) hK
    ((CochainComplex.singleFunctor A 0).map u) v, hA]
  exact (Category.assoc _ _ _).symm

end DerivedCategory.Plus

namespace CochainComplex.InjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The resolution map of an injective resolution of `X[0]`, read in the bounded-below
derived category.** -/
noncomputable def qhHom (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    (DerivedCategory.Plus.singleFunctor A 0).obj X ⟶
      DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) :=
  (DerivedCategory.Plus.singleFunctorIsoCompQh A 0).hom.app X ≫
    DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
      (CochainComplex.plus_singleFunctor_obj X) I.boundedBelow I.ι)

/-- **The resolution map of an injective resolution of `X[0]` is inverted by localization.**
It is a quasi-isomorphism, and the comparison of the two readings of `X[0]` is an
isomorphism. -/
instance isIso_qhHom (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    IsIso (qhHom X I) := by
  have h : IsIso (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk
      (CochainComplex.plus_singleFunctor_obj X) I.boundedBelow I.ι)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (by
        change QuasiIso I.ι
        infer_instance))
  exact IsIso.comp_isIso' inferInstance h

/-- **An injective resolution of `X[0]`, read in the bounded-below derived category.** The
resolution map becomes an isomorphism `X[0] ≅ Qh(I)` after localization. -/
noncomputable abbrev qhIso (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    (DerivedCategory.Plus.singleFunctor A 0).obj X ≅
      DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) :=
  asIso (qhHom X I)

/-- **The localized resolution map of an injective resolution of `X[0]` is the morphism out
of `X[0]` attached to the resolution map.** -/
lemma qhHom_eq_qhHomMk (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    qhHom X I = DerivedCategory.Plus.qhHomMk X I.boundedBelow I.ι :=
  rfl

end CochainComplex.InjectiveResolution

namespace CategoryTheory.Functor

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]

/-- **The functor induced on bounded-below homotopy categories by an additive functor sends
the localization of a morphism of complexes to the localization of its termwise image.** -/
lemma mapHomotopyCategoryPlus_map_quotientHomMk (T : A ⥤ B) [T.Additive]
    {K L : CochainComplex A ℤ} (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L)
    (g : K ⟶ L) :
    T.mapHomotopyCategoryPlus.map (HomotopyCategory.Plus.quotientHomMk hK hL g) =
      HomotopyCategory.Plus.quotientHomMk
        (CochainComplex.plus_mapHomologicalComplex_obj T hK)
        (CochainComplex.plus_mapHomologicalComplex_obj T hL)
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  apply ObjectProperty.hom_ext
  rfl

/-- **An additive functor commutes with `X ↦ X[0]` on homotopy categories.** -/
noncomputable def mapHomotopyCategorySingleFunctorIso (T : A ⥤ B) [T.Additive] (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ T.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      T ⋙ HomotopyCategory.singleFunctor B n :=
  Functor.isoWhiskerLeft (CochainComplex.singleFunctor A n)
      (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n)
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))

/-- The inverse of `CategoryTheory.Functor.mapHomotopyCategorySingleFunctorIso` is the image
under the quotient of the corresponding comparison of cochain complexes. -/
lemma mapHomotopyCategorySingleFunctorIso_inv_app (T : A ⥤ B) [T.Additive] (n : ℤ) (X : A) :
    (T.mapHomotopyCategorySingleFunctorIso n).inv.app X =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).inv.app X) := by
  have hf : (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((CochainComplex.singleFunctor A n).obj X) = 𝟙 _ := rfl
  have hsplit : (T.mapHomotopyCategorySingleFunctorIso n).inv.app X =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) n).inv.app X) ≫
        (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((CochainComplex.singleFunctor A n).obj X) := rfl
  rw [hsplit, hf]
  exact Category.comp_id _

/-- **An additive functor commutes with `X ↦ X[0]` on bounded-below homotopy
categories.** -/
noncomputable def mapSinglePlusIso (T : A ⥤ B) [T.Additive] :
    HomotopyCategory.Plus.singleFunctor A 0 ⋙ T.mapHomotopyCategoryPlus ≅
      T ⋙ HomotopyCategory.Plus.singleFunctor B 0 :=
  Functor.fullyFaithfulCancelRight (HomotopyCategory.Plus.ι B)
    (T.mapHomotopyCategorySingleFunctorIso 0)

/-- The inverse of `CategoryTheory.Functor.mapSinglePlusIso` is, in the homotopy category,
the image under the quotient of the comparison of cochain complexes. -/
lemma ι_map_mapSinglePlusIso_inv_app (T : A ⥤ B) [T.Additive] (X : A) :
    (HomotopyCategory.Plus.ι B).map (T.mapSinglePlusIso.inv.app X) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app X) := by
  have h : (HomotopyCategory.Plus.ι B).map (T.mapSinglePlusIso.inv.app X) =
      (T.mapHomotopyCategorySingleFunctorIso 0).inv.app X :=
    (HomotopyCategory.Plus.ι B).map_preimage _
  rw [h, mapHomotopyCategorySingleFunctorIso_inv_app]

/-- **The inverse of `CategoryTheory.Functor.mapSinglePlusIso` is the comparison of the
cochain complexes concentrated in degree zero**, read in the bounded-below homotopy
category. -/
lemma mapSinglePlusIso_inv_app (T : A ⥤ B) [T.Additive] (X : A) :
    T.mapSinglePlusIso.inv.app X =
      HomotopyCategory.Plus.quotientHomMk
        (CochainComplex.plus_singleFunctor_obj (T.obj X))
        (CochainComplex.plus_mapHomologicalComplex_obj T
          (CochainComplex.plus_singleFunctor_obj X))
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app X) := by
  apply (HomotopyCategory.Plus.ι B).map_injective
  rw [T.ι_map_mapSinglePlusIso_inv_app]
  rfl

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- **An additive functor commutes with `X ↦ X[0]`, read in the bounded-below derived
category.** The composite `X ↦ Qh(T(X[0]))`, which is the source of the unit of a right
derived functor of `T` at `X[0]`, is `X ↦ T(X)[0]`. -/
noncomputable def mapSingleFunctorPlusCompQhIso (T : A ⥤ B) [T.Additive] :
    HomotopyCategory.Plus.singleFunctor A 0 ⋙ T.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ≅
      T ⋙ DerivedCategory.Plus.singleFunctor B 0 :=
  Functor.isoWhiskerRight T.mapSinglePlusIso DerivedCategory.Plus.Qh ≪≫
    Functor.isoWhiskerLeft T (DerivedCategory.Plus.singleFunctorIsoCompQh B 0).symm

omit [HasDerivedCategory.{w} A] in
/-- The inverse of `CategoryTheory.Functor.mapSingleFunctorPlusCompQhIso` is the comparison of
`T(X)[0]` with `Qh(T(X[0]))` followed by the localization of the comparison of complexes. -/
lemma mapSingleFunctorPlusCompQhIso_inv_app (T : A ⥤ B) [T.Additive] (X : A) :
    T.mapSingleFunctorPlusCompQhIso.inv.app X =
      (DerivedCategory.Plus.singleFunctorIsoCompQh B 0).hom.app (T.obj X) ≫
        DerivedCategory.Plus.Qh.map (T.mapSinglePlusIso.inv.app X) :=
  rfl

omit [HasDerivedCategory.{w} A] in
/-- **The inverse of `CategoryTheory.Functor.mapSingleFunctorPlusCompQhIso` is the morphism
out of `T(X)[0]` attached to the comparison of the complexes concentrated in degree
zero.** -/
lemma mapSingleFunctorPlusCompQhIso_inv_app_eq_qhHomMk (T : A ⥤ B) [T.Additive] (X : A) :
    T.mapSingleFunctorPlusCompQhIso.inv.app X =
      DerivedCategory.Plus.qhHomMk (T.obj X)
        (CochainComplex.plus_mapHomologicalComplex_obj T
          (CochainComplex.plus_singleFunctor_obj X))
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).inv.app X) := by
  refine (T.mapSingleFunctorPlusCompQhIso_inv_app X).trans ?_
  exact congrArg (fun g => (DerivedCategory.Plus.singleFunctorIsoCompQh B 0).hom.app (T.obj X) ≫
    DerivedCategory.Plus.Qh.map g) (T.mapSinglePlusIso_inv_app X)

/-- **For a bounded-below complex `K`, the two readings of the image of `T(K)` in the derived
category agree**: the one obtained by applying `T` termwise and localizing, and the one
obtained by passing to the homotopy category first. -/
noncomputable def mapHomologicalComplexQhIso (T : A ⥤ B) [T.Additive]
    {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K) :
    DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj
        (T.mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩))) ≅
      DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  DerivedCategory.Qh.mapIso
      ((T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso B).app _

omit [HasDerivedCategory.{w} A] in
/-- **The comparison of the two readings of `T(K)` is natural in the bounded-below complex
`K`.** -/
lemma mapHomologicalComplexQhIso_hom_naturality (T : A ⥤ B) [T.Additive]
    {K L : CochainComplex A ℤ}
    (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L) (g : K ⟶ L) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map
          (HomotopyCategory.Plus.quotientHomMk hK hL g))) ≫
        (T.mapHomologicalComplexQhIso hL).hom =
      (T.mapHomologicalComplexQhIso hK).hom ≫
        DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
  (Functor.isoWhiskerRight (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso B)).hom.naturality g

omit [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] in
/-- **The comparison of the two readings of `T(K)` is compatible with composition of
functors**: for `P : 𝒜 ⥤ ℬ` and `T : ℬ ⥤ 𝒞`, the comparison for `T` at `P(K)`, precomposed
with the coherence isomorphism of the induced functors on bounded-below homotopy categories,
is the comparison for `P ⋙ T` at `K`. -/
lemma mapHomologicalComplexQhIso_comp {C : Type u''} [Category.{v''} C] [Abelian C]
    [HasDerivedCategory.{w''} C] (P : A ⥤ B) (T : B ⥤ C) [P.Additive] [T.Additive]
    {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (hPK : CochainComplex.plus B ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ T))).inv.app
            ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩))) ≫
        (T.mapHomologicalComplexQhIso hPK).hom =
      ((P ⋙ T).mapHomologicalComplexQhIso hK).hom := by
  have hid : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ T))).inv.app
      ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    rfl
  have hone : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ T))).inv.app
        ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩))) = 𝟙 _ := by
    rw [hid]
    exact (congrArg DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map_id _)).trans
      (DerivedCategory.Plus.ι.map_id _)
  rw [hone]
  exact (Category.id_comp _).trans rfl

variable [EnoughInjectives A]

/-- **The comparison of the image of `T(K)` in the derived category with the value at `K` of
the bounded-below right derived functor of `T`**, for a bounded-below complex `K`: the
comparison of the two readings of `T(K)` followed by the unit of the right derived functor.
It is invertible as soon as the unit is, which happens when every term of `K` is right
acyclic. -/
noncomputable def mapHomologicalComplexDerivedUnit (T : A ⥤ B) [T.Additive]
    {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K) :
    DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Plus.ι.obj (T.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩))) :=
  (T.mapHomologicalComplexQhIso hK).inv ≫
    DerivedCategory.Plus.ι.map
      (T.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩))

/-- **The comparison with the right derived functor is natural in the bounded-below
complex.** -/
lemma mapHomologicalComplexDerivedUnit_naturality (T : A ⥤ B) [T.Additive]
    {K L : CochainComplex A ℤ} (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L)
    (g : K ⟶ L) :
    DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        T.mapHomologicalComplexDerivedUnit hL =
      T.mapHomologicalComplexDerivedUnit hK ≫
        DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map (HomotopyCategory.Plus.quotientHomMk hK hL g))) := by
  have hunit := T.rightDerivedFunctorPlusUnit.naturality
    (HomotopyCategory.Plus.quotientHomMk hK hL g)
  dsimp only [Functor.comp_map] at hunit
  have hiso : DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
      (T.mapHomologicalComplexQhIso hL).inv =
        (T.mapHomologicalComplexQhIso hK).inv ≫ DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlus.map
            (HomotopyCategory.Plus.quotientHomMk hK hL g))) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (T.mapHomologicalComplexQhIso_hom_naturality hK hL g).symm
  dsimp only [mapHomologicalComplexDerivedUnit]
  rw [← Category.assoc, hiso, Category.assoc, Category.assoc,
    ← DerivedCategory.Plus.ι.map_comp, ← DerivedCategory.Plus.ι.map_comp, hunit]

/-- **An injective object is right acyclic** for any additive functor whose bounded-below
right derived functor exists: the complex `X[0]` is a complex of injective objects, so the
unit of the right derived functor is invertible on it. -/
lemma rightAcyclic_of_injective (T : A ⥤ B) [T.Additive]
    [(T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (X : A) [Injective X] : T.rightAcyclic X := by
  have hinj (j : ℤ) : Injective
      (((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj.as.X j) := by
    rcases eq_or_ne j 0 with rfl | hj
    · exact Injective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X j hj).injective
  show IsIso (T.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
  infer_instance

/-- **A quasi-isomorphism of bounded-below complexes of right acyclic objects stays a
quasi-isomorphism after applying an additive functor termwise.** Both ends are computed by the
right derived functor, on which the map is invertible. -/
@[sga "4½ Etat_0 4.2.3.2" "(1)"]
lemma quasiIso_mapHomologicalComplex_of_rightAcyclic (T : A ⥤ B) [T.Additive]
    [(T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L)
    (hKac : ∀ n, T.rightAcyclic (K.X n)) (hLac : ∀ n, T.rightAcyclic (L.X n)) :
    QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  let Kq := (HomotopyCategory.Plus.quotient A).obj ⟨K, hK⟩
  let Lq := (HomotopyCategory.Plus.quotient A).obj ⟨L, hL⟩
  let ψq : Kq ⟶ Lq := HomotopyCategory.Plus.quotientHomMk hK hL φ
  have : IsIso (T.rightDerivedFunctorPlusUnit.app Kq) :=
    T.isIso_totalRightDerivedUnit_app_of_rightAcyclic K hK hKac
  have : IsIso (T.rightDerivedFunctorPlusUnit.app Lq) :=
    T.isIso_totalRightDerivedUnit_app_of_rightAcyclic L hL hLac
  have hQ : IsIso (DerivedCategory.Plus.Qh.map ψq) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (by
        show QuasiIso φ
        infer_instance))
  have hmap : IsIso ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map ψq) := by
    have hcomp : IsIso (((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map ψq) ≫
        T.rightDerivedFunctorPlusUnit.app Lq) := by
      rw [T.rightDerivedFunctorPlusUnit.naturality ψq]
      dsimp only [Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (T.rightDerivedFunctorPlusUnit.app Lq)
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso B _).1 ?_
  refine (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso B) _).1 ?_
  exact (DerivedCategory.Plus.ι (C := B)).map_isIso
    ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map ψq)

/-- **The canonical identification of a bounded-below right derived functor on `X[0]` with its
value on an injective resolution** of the complex `X[0]`: apply the derived functor to the
localized resolution map, then invert its unit on the complex of injectives. All source, target
and localization universes are independent. -/
noncomputable def rightDerivedFunctorPlusInjectiveResolutionIso (T : A ⥤ B) [T.Additive]
    (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    DerivedCategory.Plus.ι.obj
        (T.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≅
      DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cocomplex) :=
  DerivedCategory.Plus.ι.mapIso
      (T.rightDerivedFunctorPlus.mapIso (CochainComplex.InjectiveResolution.qhIso X I)) ≪≫
    (DerivedCategory.Plus.ι.mapIso (asIso (T.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩)))).symm ≪≫
    T.mapHomologicalComplexQhIso I.boundedBelow

/-- The inverse of
`CategoryTheory.Functor.rightDerivedFunctorPlusInjectiveResolutionIso`, written through the
comparison with the right derived functor. -/
lemma rightDerivedFunctorPlusInjectiveResolutionIso_inv (T : A ⥤ B) [T.Additive] (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    (T.rightDerivedFunctorPlusInjectiveResolutionIso X I).inv =
      T.mapHomologicalComplexDerivedUnit I.boundedBelow ≫
        DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlus.map
          (CochainComplex.InjectiveResolution.qhIso X I).inv) :=
  rfl

/-- **The identification of a right derived functor on `X[0]` with its value on an injective
resolution is the one induced by the resolution map**: composed with the comparison of the
termwise image of the resolution with the right derived functor, it is the image of the
localized resolution map. -/
lemma rightDerivedFunctorPlusInjectiveResolutionIso_hom_comp (T : A ⥤ B) [T.Additive] (X : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj X)) :
    (T.rightDerivedFunctorPlusInjectiveResolutionIso X I).hom ≫
        T.mapHomologicalComplexDerivedUnit I.boundedBelow =
      DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlus.map
        (CochainComplex.InjectiveResolution.qhHom X I)) := by
  rw [← Iso.eq_inv_comp, rightDerivedFunctorPlusInjectiveResolutionIso_inv, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  simp

end CategoryTheory.Functor

end
