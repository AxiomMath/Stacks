module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# Transporting a derived equivalence `D_{P₁} ≌ D_{P₂}` along exact equivalences

Let `L : A₁ ⥤ A₂` and `L' : B₁ ⥤ B₂` be exact functors of abelian categories, and let
`Φ₁ : A₁ ≌ B₁`, `Φ₂ : A₂ ≌ B₂` be equivalences with `L ⋙ Φ₂ ≅ Φ₁ ⋙ L'`. Let `Pᵢ ⊆ Aᵢ` and
`Qᵢ ⊆ Bᵢ` be classes of objects which correspond under `Φᵢ`. Then the functor induced by `L`
between the subcategories `D_{P₁}(A₁) ⊆ D(A₁)` and `D_{P₂}(A₂) ⊆ D(A₂)` of **Stacks 06UP** is an
equivalence as soon as the functor induced by `L'` between `D_{Q₁}(B₁)` and `D_{Q₂}(B₂)` is.

The derived categories carry arbitrary `HasDerivedCategory` instances, independently on the four
categories: this is what lets a statement proved for one model of a derived category — for
instance the standard one of `CategoryTheory.HasDerivedCategory.standard` on a small model of a
site — be read for another.

## Main definitions

* `DerivedCategoryB.mapDerivedCategoryLift`: the functor `D_P(A) ⥤ D_Q(B)` induced by an exact
  functor carrying `P` into `Q`.

## Main results

* `DerivedCategoryB.derivedCategoryB_mapDerivedCategory_obj_iff`: an exact functor reflecting and
  preserving the classes reflects and preserves the corresponding subcategories of the derived
  categories.
* `DerivedCategoryB.isEquivalence_mapDerivedCategoryLift_of_equivalence`: an exact equivalence
  matching the classes induces an equivalence `D_P(A) ≌ D_Q(B)`.
* `DerivedCategoryB.isEquivalence_mapDerivedCategoryLift_of_transport`: **the transport.**

## References

* [Stacks Project, Tag 06UP](https://stacks.math.columbia.edu/tag/06UP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ w₄

namespace DerivedCategoryB

section Lift

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type*} [Category B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (P : ObjectProperty A) (Q : ObjectProperty B) [Q.IsClosedUnderIsomorphisms]

/-- An exact functor carrying `P` into `Q` carries `D_P(A)` into `D_Q(B)`: the cohomology objects
of `F(K)` are the images under `F` of those of `K`. -/
theorem derivedCategoryB_mapDerivedCategory_obj (hF : ∀ M, P M → Q (F.obj M))
    {K : DerivedCategory A} (hK : derivedCategoryB P K) :
    derivedCategoryB Q (F.mapDerivedCategory.obj K) := fun n ↦
  Q.prop_of_iso ((F.mapDerivedCategoryHomologyIso n).app K).symm (hF _ (hK n))

/-- The functor `D_P(A) ⥤ D_Q(B)` induced by an exact functor carrying `P` into `Q`. -/
abbrev mapDerivedCategoryLift (hF : ∀ M, P M → Q (F.obj M)) :
    (derivedCategoryB P).FullSubcategory ⥤ (derivedCategoryB Q).FullSubcategory :=
  (derivedCategoryB Q).lift ((derivedCategoryB P).ι ⋙ F.mapDerivedCategory)
    (fun K ↦ derivedCategoryB_mapDerivedCategory_obj F P Q hF K.property)

/-- An exact functor which matches `P` with `Q` matches `D_P(A)` with `D_Q(B)`. -/
theorem derivedCategoryB_mapDerivedCategory_obj_iff (hPQ : ∀ M, P M ↔ Q (F.obj M))
    (K : DerivedCategory A) :
    derivedCategoryB Q (F.mapDerivedCategory.obj K) ↔ derivedCategoryB P K :=
  ⟨fun h n ↦ (hPQ _).2 (Q.prop_of_iso ((F.mapDerivedCategoryHomologyIso n).app K) (h n)),
    derivedCategoryB_mapDerivedCategory_obj F P Q fun M ↦ (hPQ M).1⟩

end Lift

section Equivalence

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type*} [Category B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (Φ : A ≌ B) [Φ.functor.Additive] [Φ.inverse.Additive]
  (P : ObjectProperty A) (Q : ObjectProperty B) [Q.IsClosedUnderIsomorphisms]
  (hPQ : ∀ M, P M ↔ Q (Φ.functor.obj M))

include hPQ in
/-- **An exact equivalence matching `P` with `Q` induces an equivalence `D_P(A) ≌ D_Q(B)`.**
The induced functor of derived categories is an equivalence, and it matches `D_P(A)` with
`D_Q(B)`; so its corestriction is fully faithful, and essentially surjective because every
object of `D_Q(B)` is the image of an object of `D(A)`, which then lies in `D_P(A)`. -/
theorem isEquivalence_mapDerivedCategoryLift_of_equivalence :
    (mapDerivedCategoryLift Φ.functor P Q (fun M ↦ (hPQ M).1)).IsEquivalence := by
  have : Φ.functor.mapDerivedCategory.IsEquivalence :=
    StacksDraft.DerivedRingIso.isEquivalence_mapDerivedCategory Φ.functor Φ.inverse
      Φ.unitIso Φ.counitIso
  have hff : (mapDerivedCategoryLift Φ.functor P Q (fun M ↦ (hPQ M).1)).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful
      (G := (derivedCategoryB Q).ι)
      (((derivedCategoryB P).fullyFaithfulι.comp
        (Functor.FullyFaithful.ofFullyFaithful Φ.functor.mapDerivedCategory)))
  have := hff.full
  have := hff.faithful
  have : (mapDerivedCategoryLift Φ.functor P Q (fun M ↦ (hPQ M).1)).EssSurj := by
    refine ⟨fun K' ↦ ?_⟩
    let K := Φ.functor.mapDerivedCategory.objPreimage K'.obj
    let e : Φ.functor.mapDerivedCategory.obj K ≅ K'.obj :=
      Φ.functor.mapDerivedCategory.objObjPreimageIso K'.obj
    exact ⟨⟨K, (derivedCategoryB_mapDerivedCategory_obj_iff Φ.functor P Q hPQ K).1
      fun n ↦ Q.prop_of_iso ((DerivedCategory.homologyFunctor B n).mapIso e.symm)
        (K'.property n)⟩, ⟨(derivedCategoryB Q).fullyFaithfulι.preimageIso e⟩⟩
  exact { }

end Equivalence

section Transport

variable {A₁ : Type*} [Category A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type*} [Category A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
  {B₁ : Type*} [Category B₁] [Abelian B₁] [HasDerivedCategory.{w₃} B₁]
  {B₂ : Type*} [Category B₂] [Abelian B₂] [HasDerivedCategory.{w₄} B₂]
  (L : A₁ ⥤ A₂) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (L' : B₁ ⥤ B₂) [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  (Φ₁ : A₁ ≌ B₁) [Φ₁.functor.Additive] [Φ₁.inverse.Additive]
  (Φ₂ : A₂ ≌ B₂) [Φ₂.functor.Additive] [Φ₂.inverse.Additive]
  (α : L ⋙ Φ₂.functor ≅ Φ₁.functor ⋙ L')
  (P₁ : ObjectProperty A₁) (P₂ : ObjectProperty A₂) [P₂.IsClosedUnderIsomorphisms]
  (Q₁ : ObjectProperty B₁) (Q₂ : ObjectProperty B₂)
  [Q₁.IsClosedUnderIsomorphisms] [Q₂.IsClosedUnderIsomorphisms]
  (hP₁ : ∀ M, P₁ M ↔ Q₁ (Φ₁.functor.obj M)) (hP₂ : ∀ M, P₂ M ↔ Q₂ (Φ₂.functor.obj M))
  (hL : ∀ M, P₁ M → P₂ (L.obj M)) (hL' : ∀ M, Q₁ M → Q₂ (L'.obj M))

/-- The square of induced functors on derived categories: `L` followed by `Φ₂` is `Φ₁` followed
by `L'`, after passing to derived categories. -/
def mapDerivedCategorySquareIso :
    L.mapDerivedCategory ⋙ Φ₂.functor.mapDerivedCategory ≅
      Φ₁.functor.mapDerivedCategory ⋙ L'.mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso L Φ₂.functor).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ α ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso Φ₁.functor L'

include α hP₁ hP₂ in
/-- **Transport of a derived equivalence along exact equivalences.** If `L'` induces an
equivalence `D_{Q₁}(B₁) ≌ D_{Q₂}(B₂)`, then `L` induces an equivalence `D_{P₁}(A₁) ≌ D_{P₂}(A₂)`.
The two corestricted functors are intertwined by the corestrictions of `Φ₁` and `Φ₂`, which are
equivalences by `isEquivalence_mapDerivedCategoryLift_of_equivalence`. -/
theorem isEquivalence_mapDerivedCategoryLift_of_transport
    [(mapDerivedCategoryLift L' Q₁ Q₂ hL').IsEquivalence] :
    (mapDerivedCategoryLift L P₁ P₂ hL).IsEquivalence := by
  have := isEquivalence_mapDerivedCategoryLift_of_equivalence Φ₁ P₁ Q₁ hP₁
  have := isEquivalence_mapDerivedCategoryLift_of_equivalence Φ₂ P₂ Q₂ hP₂
  let G := mapDerivedCategoryLift L P₁ P₂ hL
  let G' := mapDerivedCategoryLift L' Q₁ Q₂ hL'
  let F₁ := mapDerivedCategoryLift Φ₁.functor P₁ Q₁ (fun M ↦ (hP₁ M).1)
  let F₂ := mapDerivedCategoryLift Φ₂.functor P₂ Q₂ (fun M ↦ (hP₂ M).1)
  let e : G ⋙ F₂ ≅ F₁ ⋙ G' :=
    (derivedCategoryB Q₂).fullyFaithfulι.whiskeringRight _ |>.preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G (Iso.refl _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Iso.refl (G ⋙ (derivedCategoryB P₂).ι)) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (derivedCategoryB P₁).ι
          (mapDerivedCategorySquareIso L L' Φ₁ Φ₂ α) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Iso.refl (F₁ ⋙ (derivedCategoryB Q₁).ι)) _ ≪≫
        Functor.associator _ _ _)
  have : (G ⋙ F₂).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  exact Functor.isEquivalence_of_comp_right G F₂

end Transport

end DerivedCategoryB

end
