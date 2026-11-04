module

public import StacksFrontier.CategoryTheory.Monoidal.DetectingLaxMonoidalCommShift
public import StacksFrontier.Homology.ConstMapDerivedCategoryMonoidal
public import StacksFrontier.Homology.ConstMapDerivedCategoryTensorator
public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoCommShift
public import StacksFrontier.Homology.KFlat.BifunctorComplexModelsShift
public import StacksFrontier.Homology.MapHomologicalComplexCommShift

/-!
# The tensorator of constant diagrams on derived categories, at K-flat complexes

Let `J` be a category and `D` a monoidal abelian category over which both `CochainComplex D ℤ`
and `CochainComplex (J ⥤ D) ℤ` carry the total tensor product and admit K-flat resolutions, so
that `CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(D)` and `D(J ⥤ D)` with the derived
tensor product and `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` makes

`(Functor.const J).mapDerivedCategory : D(D) ⥤ D(J ⥤ D)`

a monoidal functor.  That monoidal structure is produced by descent along the K-flat
localization, so nothing about its tensorator

`μ : π^{-1}K ⊗^L π^{-1}L ⟶ π^{-1}(K ⊗^L L)`

is visible at a particular pair of objects.  This file computes it at the image of a pair of
K-flat *cochain complexes*, as an explicit composite of

* the comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` of the derived functor with
  the degreewise one, in each variable;
* the K-flat comparison `CochainComplex.KFlatMonoidal.derivedTensorIso` of the derived tensor
  product with the total tensor product of complexes, over `J ⥤ D`;
* the image under `DerivedCategory.Q` of the tensorator of
  `(Functor.const J).mapHomologicalComplex (ComplexShape.up ℤ)`;
* and the two previous ones again, inverted, over `D`.

Every factor of that composite is a transformation of functors of the K-flat complexes which is
known to commute with the shift, which is what the computation is for.

## Main results

* `CategoryTheory.Functor.mu_constMapDerivedCategory_derivedTensorIso`: **the tensorator of
  `(Functor.const J).mapDerivedCategory` at the images of two K-flat complexes, as a commuting
  square between the two K-flat comparisons.**
* `CategoryTheory.Functor.mu_constMapDerivedCategory_eq`: the same identity solved for the
  tensorator, with the tensor product of the two comparisons split into its two whiskerings.
* `CategoryTheory.Functor.constKFlatComplexLift` and `constKFlatComplexLiftLeft`, with
  `constKFlatComplexLiftMonoidal` and the two commutations with the shift: **constant diagrams on
  the K-flat complexes**, a monoidal shift-compatible functor between the full monoidal
  subcategories.
* `CategoryTheory.Functor.mu_constMapHomotopyCategory_comp`: the tensorator of
  `(Functor.const J).mapHomotopyCategory`, with the two comparisons of
  `CategoryTheory.Functor.mapHomotopyCategoryFactors` it carries on the target side cancelled.
* `CategoryTheory.Functor.constMapDerivedCategoryFactorsh_hom_app_comp` and its two companions:
  the comparison over the homotopy category in terms of the comparison over the complexes.

## Implementation notes

**Where the identity comes from.**  `CategoryTheory.Localization.Monoidal.lifting_isMonoidal`
says that the lifting isomorphism of a monoidal structure obtained by
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` is a monoidal natural
transformation.  `CategoryTheory.Functor.constMapDerivedCategoryMonoidal` is such a transport
along the K-flat localization, so its tensorator at the image of a pair of K-flat *objects of the
homotopy category* is `CategoryTheory.Functor.mu_constMapDerivedCategory` with the two inverses
it carries moved to the other side; that is the half of the work done over `K(D)`.  The other
half descends it to complexes, which is where the comparisons
`DerivedCategory.quotientCompQhIso` and `CategoryTheory.Functor.mapHomotopyCategoryFactors`
enter and cancel.

**Why so many of the steps are in term mode, and why the chain is cut into short statements.**
`CategoryTheory.Localization.Monoidal.μ` has its source on the type synonym
`CochainComplex.KFlatMonoidal.DerivedLocalized`, so a composite containing it is type-correct
only at `default` transparency: `rw` and `simp` build motives at a lower transparency and refuse
such a goal outright.  Two devices get past that.  `CochainComplex.KFlatMonoidal.derivedMu` is
that morphism with its type ascribed to `D(A)`, and every statement here that is to be rewritten
uses it, never `Localization.Monoidal.μ`; and where a goal does mix the two spellings the step is
taken as a term, through the abstract `comp_cancel_aux` and `comp_chain_aux`, whose composition
algebra happens in an abstract category where no spelling can intrude and whose instantiation is
left to the unifier.  The same consideration cuts the computation into lemmas with short
statements rather than one chain: each of them pays the elaboration of the `J ⥤ D` graded-object
instances once.

**The two spellings of a constant diagram.**  `((Functor.const J).mapHomotopyCategory _).obj (Q K)`
and `Q (((Functor.const J).mapHomologicalComplex _).obj K)` are the same object of `K(J ⥤ D)`,
but not the same term, so the comparison `CategoryTheory.Functor.mapHomotopyCategoryFactors`
between them -- an isomorphism whose components are identities -- cannot be rewritten away and is
carried explicitly, as it is in
`CategoryTheory.Functor.mu_constMapHomotopyCategory`.  Its passage across the tensorator of the
K-flat localization is the naturality of
`CategoryTheory.Localization.Monoidal.μ`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 08QC](https://stacks.math.columbia.edu/tag/08QC)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v u v₁ u₁ v₂ u₂

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

/-! ### An abstract cancellation -/

/-- Splicing a chain of three identities.  Abstract for the same reason as
`CategoryTheory.comp_cancel_aux`: the composites it is applied to mix `DerivedCategory` with the
type synonym carrying the localized monoidal structure, where no rewriting tactic can act. -/
private lemma comp_chain_aux {C : Type*} [Category* C] {X₁ X₂ X₃ X₄ X₅ Y₂ Y₃ Y₄ Z₂ : C}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (s : X₄ ⟶ X₅) (p : X₁ ⟶ Y₂) (q : Y₂ ⟶ Y₃)
    (r : Y₃ ⟶ X₄) (u : Y₃ ⟶ Y₄) (v : Y₄ ⟶ X₅) (u' : Y₂ ⟶ Z₂) (q' : Z₂ ⟶ Y₄)
    (h1 : a ≫ b ≫ c = p ≫ q ≫ r) (h2 : r ≫ s = u ≫ v) (h3 : q ≫ u = u' ≫ q') :
    a ≫ b ≫ c ≫ s = p ≫ u' ≫ q' ≫ v := by
  rw [← Category.assoc b, ← Category.assoc a, h1, Category.assoc, Category.assoc, h2,
    ← Category.assoc q, h3, Category.assoc]

/-- Cancelling two retractions in the middle of a composite.  Stated abstractly because the
composites it is applied to live partly on the type synonym
`CochainComplex.KFlatMonoidal.DerivedLocalized` and partly on `DerivedCategory`, where no
rewriting tactic can act; applied as a term, the unifier does that identification. -/
private lemma comp_cancel_aux {C : Type*} [Category* C] {S T U V W : C} (p : S ⟶ T) (q : T ⟶ U)
    (r : U ⟶ V) (s : V ⟶ W) (t : W ⟶ V) (u : V ⟶ U) (hst : s ≫ t = 𝟙 V) (hru : r ≫ u = 𝟙 U) :
    (p ≫ q ≫ r ≫ s) ≫ t ≫ u = p ≫ q := by
  rw [Category.assoc, Category.assoc, Category.assoc, reassoc_of% hst, hru, Category.comp_id]


/-! ### The tensorator of the K-flat localization, at the spelling of the type synonym -/

section General

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **The K-flat comparison of the derived tensor product, with its middle factor written as
`CategoryTheory.Localization.Monoidal.μ`.**  This is
`CochainComplex.KFlatMonoidal.derivedTensorIso_hom_eq` with
`CochainComplex.KFlatMonoidal.derivedMu` unfolded: that abbreviation ascribes the composition to
`D(A)`, and the statements it is combined with here are the ones of the type synonym
`CategoryTheory.LocalizedMonoidal`. -/
private lemma derivedTensorIso_hom_locMonMu {K L : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (hL : KFlat (curriedTensor A) L) :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    (derivedTensorIso A hres hK hL).hom =
      ((derivedQIso A K).inv ⊗ₘ (derivedQIso A L).inv) ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
            (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩
            ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L, hL⟩).hom ≫
          DerivedCategory.Qh.map (homotopyMu A K L).hom ≫ (derivedQIso A (K ⊗ L)).hom :=
  derivedTensorIso_hom_eq A hres hK hL

include hres in
/-- **The tensorator of the K-flat localization is natural in both variables**, at the spelling
of the type synonym.  This is `CategoryTheory.Functor.LaxMonoidal.μ_natural` for the monoidal
localization functor `CategoryTheory.Localization.Monoidal.toMonoidalCategory`, whose tensorator
is `CategoryTheory.Localization.Monoidal.μ` and whose action on morphisms is that of
`DerivedCategory.Qh` on the underlying morphisms of `K(A)`. -/
private lemma locMonMu_natural
    {X Y X' Y' : (kFlatObjects (curriedTensor A)).FullSubcategory} (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := kFlatQ_isLocalization (curriedTensor A) hres
    letI := derivedMonoidal A hres
    (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
            (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X Y).hom ≫
        DerivedCategory.Qh.map (f.hom ⊗ₘ g.hom) =
      (DerivedCategory.Qh.map f.hom ⊗ₘ DerivedCategory.Qh.map g.hom) ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor A)) (kFlatQuasiIso (curriedTensor A))
          (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _))) X' Y').hom :=
  let := kFlatQ_isLocalization (curriedTensor A) hres
  (Functor.LaxMonoidal.μ_natural
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor A))
      (kFlatQuasiIso (curriedTensor A))
      (Iso.refl ((kFlatQ (curriedTensor A)).obj (𝟙_ _)))) f g).symm

include hres in
/-- **The K-flat complexes are essentially surjective onto `D(A)`.**  Every object of `D(A)` is
the image of a K-flat object of `K(A)` (`CochainComplex.KFlatBifunctor.kFlatQ_essSurj`), every
K-flat object of `K(A)` is the homotopy class of a K-flat complex
(`CochainComplex.KFlatBifunctor.kFlatQuotient_essSurj`), and the bridge
`CochainComplex.KFlatBifunctor.kFlatQuotientCompQIso` identifies the composite with
`kFlatComplexQ`. -/
private lemma kFlatComplexQ_essSurj : (kFlatComplexQ (curriedTensor A)).EssSurj := by
  let := kFlatQ_isLocalization (curriedTensor A) hres
  have := kFlatQ_essSurj (curriedTensor A)
  exact Functor.essSurj_of_iso (kFlatQuotientCompQIso (curriedTensor A))

/-- K-flatness implies left K-flatness, as an inequality of object properties. -/
private lemma kFlatComplexes_le_kFlatComplexesLeft :
    kFlatComplexes (curriedTensor A) ≤ kFlatComplexesLeft (curriedTensor A) :=
  fun _ hK => kFlatLeft_of_kFlat A hK

/-- The K-flat complexes among the left K-flat ones, as a shift-compatible functor. -/
@[instance_reducible]
private def ιOfLE_kFlatComplexes_commShift :
    (ObjectProperty.ιOfLE (kFlatComplexes_le_kFlatComplexesLeft A)).CommShift ℤ :=
  Functor.CommShift.ofComp
    (ObjectProperty.ιOfLECompιIso (kFlatComplexes_le_kFlatComplexesLeft A)) ℤ

end General

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]
  [SymmetricCategory (CochainComplex D ℤ)] [SymmetricCategory (CochainComplex (J ⥤ D) ℤ)]

/-! ### Constant diagrams on the K-flat cochain complexes -/

/-- Constant diagrams, from the K-flat cochain complexes of `D` to the K-flat cochain complexes
of `J ⥤ D`. -/
def Functor.constKFlatComplexLift :
    (kFlatComplexes (curriedTensor D)).FullSubcategory ⥤
      (kFlatComplexes (curriedTensor (J ⥤ D))).FullSubcategory :=
  (kFlatComplexes (curriedTensor (J ⥤ D))).lift
    ((kFlatComplexes (curriedTensor D)).ι ⋙
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => kFlat_constMapHomologicalComplex K.obj K.property)

/-- Constant diagrams, from the K-flat cochain complexes of `D` to the left K-flat cochain
complexes of `J ⥤ D`. -/
def Functor.constKFlatComplexLiftLeft :
    (kFlatComplexes (curriedTensor D)).FullSubcategory ⥤
      (kFlatComplexesLeft (curriedTensor (J ⥤ D))).FullSubcategory :=
  (kFlatComplexesLeft (curriedTensor (J ⥤ D))).lift
    ((kFlatComplexes (curriedTensor D)).ι ⋙
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))

/-- `Functor.constKFlatComplexLift` commutes with the shift. -/
@[instance_reducible]
def Functor.constKFlatComplexLift_commShift :
    (Functor.constKFlatComplexLift (J := J) (D := D)).CommShift ℤ :=
  Functor.CommShift.ofComp ((kFlatComplexes (curriedTensor (J ⥤ D))).liftCompιIso
    ((kFlatComplexes (curriedTensor D)).ι ⋙
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => kFlat_constMapHomologicalComplex K.obj K.property)) ℤ

/-- `Functor.constKFlatComplexLiftLeft` commutes with the shift. -/
@[instance_reducible]
def Functor.constKFlatComplexLiftLeft_commShift :
    (Functor.constKFlatComplexLiftLeft (J := J) (D := D)).CommShift ℤ :=
  Functor.CommShift.ofComp ((kFlatComplexesLeft (curriedTensor (J ⥤ D))).liftCompιIso
    ((kFlatComplexes (curriedTensor D)).ι ⋙
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => kFlatLeft_of_kFlat _ (kFlat_constMapHomologicalComplex K.obj K.property))) ℤ

/-- **`Functor.constKFlatComplexLift` is a monoidal functor** between the full monoidal
subcategories of K-flat complexes.  The K-flat complexes are a full monoidal subcategory on each
side (`CochainComplex.KFlatMonoidal.kFlatComplexes_isMonoidal`), so this is
`CategoryTheory.ObjectProperty.liftMonoidal` applied to
`CategoryTheory.Functor.constMapHomologicalComplexMonoidal`, exactly as
`CategoryTheory.Functor.constKFlatLiftMonoidal` is for the homotopy categories. -/
@[instance_reducible]
def Functor.constKFlatComplexLiftMonoidal :
    (Functor.constKFlatComplexLift (J := J) (D := D)).Monoidal :=
  letI := Functor.constMapHomologicalComplexMonoidal (J := J) (D := D) (c := ComplexShape.up ℤ)
  ObjectProperty.liftMonoidal _ _ _

/-- **Taking the homotopy class of a K-flat complex commutes with constant diagrams on the
nose.**  Both composites send a K-flat complex `K` to the homotopy class of the constant diagram
at `K`, and `(Functor.const J).mapHomotopyCategory` acts on homotopy classes as
`(Functor.const J).mapHomologicalComplex` acts on complexes, so the two functors are equal. -/
lemma Functor.toKFlatObjects_comp_constKFlatLift :
    toKFlatObjects D ⋙ Functor.constKFlatLift (J := J) (D := D) =
      Functor.constKFlatComplexLift (J := J) (D := D) ⋙ toKFlatObjects (J ⥤ D) :=
  rfl

/-- **The tensorator of `(Functor.const J).mapHomotopyCategory` at the homotopy classes of two
complexes, with the two comparisons of `CategoryTheory.Functor.mapHomotopyCategoryFactors` it
carries on the right cancelled.**  This is
`CategoryTheory.Functor.mu_constMapHomotopyCategory` composed with the image of
`CochainComplex.KFlatMonoidal.homotopyMu` and the comparison at `K ⊗ L`; in this form the
identity involves only the comparison in the two *source* variables, which is what the descent to
the derived categories consumes. -/
lemma Functor.mu_constMapHomotopyCategory_comp (K L : CochainComplex D ℤ) :
    letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
    Functor.LaxMonoidal.μ
            ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ))
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K)
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
              (homotopyMu D K L).hom ≫
            ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app (K ⊗ L) =
      ((((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app K) ⊗ₘ
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app L)) ≫
        (homotopyMu (J ⥤ D)
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L)).hom ≫
          (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).map
            (Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)) K L) := by
  rw [Functor.mu_constMapHomotopyCategory K L]
  simp

/-! ### The tensorator at the images of two K-flat complexes -/

section Derived

variable [HasDerivedCategory.{w} D] [HasDerivedCategory.{w'} (J ⥤ D)]
  (hresD : ∀ G : CochainComplex D ℤ, ∃ (P : CochainComplex D ℤ) (f : P ⟶ G),
    KFlat (curriedTensor D) P ∧ QuasiIso f)
  (hresJD : ∀ G : CochainComplex (J ⥤ D) ℤ, ∃ (P : CochainComplex (J ⥤ D) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f)

/-- The two factorizations of `(Functor.const J).mapDerivedCategory`, over the homotopy
category and over the complexes, differ by the bridge `DerivedCategory.quotientCompQhIso` in
each variable.  This is Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` with the component of
`CategoryTheory.Functor.mapHomotopyCategoryFactors` -- an isomorphism between two spellings of
one object of `K(J ⥤ D)` -- moved to the other side. -/
lemma Functor.constMapDerivedCategoryFactorsh_hom_app_comp (M : CochainComplex D ℤ) :
    (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app M) =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
          ((DerivedCategory.quotientCompQhIso D).hom.app M) ≫
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app M ≫
          (DerivedCategory.quotientCompQhIso (J ⥤ D)).inv.app
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, Category.assoc, Category.assoc,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

include hresD hresJD in
/-- **The tensorator of `(Functor.const J).mapDerivedCategory` at the image of a pair of K-flat
objects of `K(D)`, in the form of a commuting square.**  This is
`CategoryTheory.Functor.mu_constMapDerivedCategory` with the two inverses it carries -- that of
the comparison `CategoryTheory.Functor.mapDerivedCategoryFactorsh` and that of the tensorator of
the K-flat localization of `D` -- moved to the other side, where they cancel.  In this form the
identity says that `mapDerivedCategoryFactorsh` is a *monoidal* natural transformation. -/
private lemma muZ_kFlatObjects (X Y : (kFlatObjects (curriedTensor D)).FullSubcategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := kFlatQ_isLocalization (curriedTensor D) hresD
    letI := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
    letI := Functor.constKFlatLiftMonoidal (J := J) (D := D)
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
            ((kFlatQ (curriedTensor D)).obj X) ((kFlatQ (curriedTensor D)).obj Y) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
              (Localization.Monoidal.μ (kFlatQ (curriedTensor D)) (kFlatQuasiIso (curriedTensor D))
                (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))) X Y).hom ≫
            (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app (X ⊗ Y).obj =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app X.obj ⊗ₘ
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app Y.obj) ≫
        (Localization.Monoidal.μ (kFlatQ (curriedTensor (J ⥤ D)))
              (kFlatQuasiIso (curriedTensor (J ⥤ D)))
              (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _)))
              (Functor.constKFlatLift.obj X) (Functor.constKFlatLift.obj Y)).hom ≫
          (kFlatQ (curriedTensor (J ⥤ D))).map
            (Functor.LaxMonoidal.μ (Functor.constKFlatLift (J := J) (D := D)) X Y) := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := kFlatQ_isLocalization (curriedTensor D) hresD
  let := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
  let := Functor.constKFlatLiftMonoidal (J := J) (D := D)
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  rw [Functor.mu_constMapDerivedCategory hresD hresJD X Y]
  exact comp_cancel_aux _ _ _ _ _ _
    (((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory.mapIso _).inv_hom_id)
    (Iso.inv_hom_id_app _ _)

include hresD hresJD in
/-- **`muZ_kFlatObjects` at the homotopy classes of two K-flat complexes**, with the two
tensorators of the K-flat localizations named by `CochainComplex.KFlatMonoidal.derivedMu` and the
tensorator of `CategoryTheory.Functor.constKFlatLift` replaced by that of
`(Functor.const J).mapHomotopyCategory`.

The point of the restatement is the ascription: `CategoryTheory.Localization.Monoidal.μ` has its
source on the type synonym `CochainComplex.KFlatMonoidal.DerivedLocalized`, so a composite
containing it is type-correct only at `default` transparency and no rewriting tactic can act on
it; `derivedMu` is the same morphism ascribed to `D(A)`. -/
private lemma muZ_kFlatComplexes {K L : CochainComplex D ℤ} (hK : KFlat (curriedTensor D) K)
    (hL : KFlat (curriedTensor D) L) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K))
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L)) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
              (derivedMu D hresD hK hL) ≫
            (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K ⊗
                (HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L) =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K) ⊗ₘ
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L)) ≫
        derivedMu (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
            (kFlat_constMapHomologicalComplex L hL) ≫
          DerivedCategory.Qh.map (Functor.LaxMonoidal.μ
            ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ))
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K)
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L)) := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := kFlatQ_isLocalization (curriedTensor D) hresD
  let := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
  let := Functor.constKFlatLiftMonoidal (J := J) (D := D)
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  have h := muZ_kFlatObjects hresD hresJD
    ⟨(HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K, hK⟩
    ⟨(HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L, hL⟩
  rw [Functor.comp_map, ObjectProperty.ι_map, Functor.mu_constKFlatLift_hom] at h
  exact h

/-- The companion of `CategoryTheory.Functor.constMapDerivedCategoryFactorsh_hom_app_comp`, with
the bridge to the homotopy category on the other side. -/
lemma Functor.constMapDerivedCategoryFactorsh_hom_app_comp' (M : CochainComplex D ℤ) :
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
          ((DerivedCategory.quotientCompQhIso D).hom.app M) ≫
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app M =
      (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app M) ≫
          (DerivedCategory.quotientCompQhIso (J ⥤ D)).hom.app
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) := by
  rw [← Category.assoc, Functor.constMapDerivedCategoryFactorsh_hom_app_comp, Category.assoc,
    Category.assoc, Iso.inv_hom_id_app]
  simp

include hresJD in
/-- **The tensorator of the K-flat localization of `J ⥤ D` commutes with the comparison of the
two spellings of a constant diagram's homotopy class.**  The two objects
`((Functor.const J).mapHomotopyCategory _).obj (Q K)` and
`Q ((Functor.const J).mapHomologicalComplex _).obj K)` are the same object of `K(J ⥤ D)`, so the
tensorator is the same morphism on both sides and this is the naturality of
`CategoryTheory.Localization.Monoidal.μ` at the comparison. -/
private lemma derivedMu_comp_qh_map_mu_constMapHomotopyCategoryFactors
    {K L : CochainComplex D ℤ} (hK : KFlat (curriedTensor D) K)
    (hL : KFlat (curriedTensor D) L) :
    letI := derivedMonoidal (J ⥤ D) hresJD
    derivedMu (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
            (kFlat_constMapHomologicalComplex L hL) ≫
          DerivedCategory.Qh.map
            ((((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).hom.app K) ⊗ₘ
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).hom.app L)) =
      (DerivedCategory.Qh.map
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app K) ⊗ₘ
          DerivedCategory.Qh.map
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app L)) ≫
        derivedMu (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
          (kFlat_constMapHomologicalComplex L hL) :=
  let := derivedMonoidal (J ⥤ D) hresJD
  locMonMu_natural (J ⥤ D) hresJD
    (X := ⟨(HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).obj
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
      kFlat_constMapHomologicalComplex K hK⟩)
    (Y := ⟨(HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).obj
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L),
      kFlat_constMapHomologicalComplex L hL⟩)
    (X' := ⟨(HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).obj
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
      kFlat_constMapHomologicalComplex K hK⟩)
    (Y' := ⟨(HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).obj
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L),
      kFlat_constMapHomologicalComplex L hL⟩)
    (ObjectProperty.homMk
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app K))
    (ObjectProperty.homMk
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app L))

/-- The inverse form of `CategoryTheory.Functor.constMapDerivedCategoryFactorsh_hom_app_comp`. -/
lemma Functor.constMapDerivedCategoryFactorsh_hom_app_comp_inv (M : CochainComplex D ℤ) :
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
          ((DerivedCategory.quotientCompQhIso D).inv.app M) ≫
        (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj M) ≫
          DerivedCategory.Qh.map
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app M) =
      (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app M ≫
        (DerivedCategory.quotientCompQhIso (J ⥤ D)).inv.app
          (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
  rw [Functor.constMapDerivedCategoryFactorsh_hom_app_comp,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The tail of (Z) on the side of the degreewise action**: the image of
`CochainComplex.KFlatMonoidal.homotopyMu` followed by the bridge to `D(D)` and the comparison at
`K ⊗ L`, rewritten through the comparison over the homotopy category.  This is
`CategoryTheory.Functor.constMapDerivedCategoryFactorsh_hom_app_comp'` preceded by the naturality
of `CategoryTheory.Functor.mapDerivedCategoryFactorsh`. -/
lemma Functor.constMapDerivedCategoryFactorsh_homotopyMu (K L : CochainComplex D ℤ) :
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
          (DerivedCategory.Qh.map (homotopyMu D K L).hom) ≫
        ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
            ((DerivedCategory.quotientCompQhIso D).hom.app (K ⊗ L)) ≫
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K ⊗
            (HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L) ≫
        DerivedCategory.Qh.map
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
                (homotopyMu D K L).hom ≫
              ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).hom.app (K ⊗ L)) ≫
          (DerivedCategory.quotientCompQhIso (J ⥤ D)).hom.app
            (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (K ⊗ L)) := by
  have hnat := ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh).hom.naturality
    (homotopyMu D K L).hom
  dsimp only [Functor.comp_map] at hnat
  rw [Functor.constMapDerivedCategoryFactorsh_hom_app_comp' (K ⊗ L), reassoc_of% hnat,
    CategoryTheory.Functor.map_comp DerivedCategory.Qh, Category.assoc]

include hresD hresJD in
/-- **(Z) over the homotopy category**: `muZ_kFlatComplexes` with the comparison of the two
spellings of the constant diagram moved to the source variables, where the descent to the
complexes needs it.  The three identities spliced are `muZ_kFlatComplexes`,
`CategoryTheory.Functor.mu_constMapHomotopyCategory_comp` and
`derivedMu_comp_qh_map_mu_constMapHomotopyCategoryFactors`. -/
private lemma muZ_kFlatComplexes' {K L : CochainComplex D ℤ} (hK : KFlat (curriedTensor D) K)
    (hL : KFlat (curriedTensor D) L) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K))
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L)) ≫
          ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map (derivedMu D hresD hK hL) ≫
            (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
                ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K ⊗
                  (HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L) ≫
              DerivedCategory.Qh.map
                (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
                    (homotopyMu D K L).hom ≫
                  ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                    (ComplexShape.up ℤ)).hom.app (K ⊗ L)) =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj K) ⊗ₘ
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj L)) ≫
        (DerivedCategory.Qh.map
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).hom.app K) ⊗ₘ
            DerivedCategory.Qh.map
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors
                (ComplexShape.up ℤ)).hom.app L)) ≫
          derivedMu (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
              (kFlat_constMapHomologicalComplex L hL) ≫
            DerivedCategory.Qh.map
              ((homotopyMu (J ⥤ D)
                    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj K)
                    (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj L)).hom ≫
                (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ)).map
                  (Functor.LaxMonoidal.μ
                    ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                      (ComplexShape.up ℤ)) K L)) := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  refine comp_chain_aux _ _ _ _ _ _ _ _ _ _ _ (muZ_kFlatComplexes hresD hresJD hK hL) ?_
    (derivedMu_comp_qh_map_mu_constMapHomotopyCategoryFactors hresJD hK hL)
  exact ((CategoryTheory.Functor.map_comp DerivedCategory.Qh _ _).symm.trans
    (congrArg (fun f => DerivedCategory.Qh.map f)
      (Functor.mu_constMapHomotopyCategory_comp K L))).trans
    (CategoryTheory.Functor.map_comp DerivedCategory.Qh _ _)

include hresD hresJD in
/-- **(Z): the tensorator of the derived constant diagram at the images of two K-flat
complexes.** -/
theorem Functor.mu_constMapDerivedCategory_derivedTensorIso
    {K L : CochainComplex D ℤ} (hK : KFlat (curriedTensor D) K)
    (hL : KFlat (curriedTensor D) L) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
            (derivedTensorIso D hresD hK hL).hom ≫
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app K ⊗ₘ
          (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app L) ≫
        (derivedTensorIso (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
            (kFlat_constMapHomologicalComplex L hL)).hom ≫
          DerivedCategory.Q.map (Functor.LaxMonoidal.μ
            ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)) K L) := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  rw [derivedTensorIso_hom_eq D hresD hK hL,
    derivedTensorIso_hom_eq (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
      (kFlat_constMapHomologicalComplex L hL)]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [← reassoc_of% (Functor.LaxMonoidal.μ_natural
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
      ((DerivedCategory.quotientCompQhIso D).inv.app K)
      ((DerivedCategory.quotientCompQhIso D).inv.app L)),
    Functor.constMapDerivedCategoryFactorsh_homotopyMu K L,
    reassoc_of% (muZ_kFlatComplexes' hresD hresJD hK hL)]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [Functor.constMapDerivedCategoryFactorsh_hom_app_comp_inv K,
    Functor.constMapDerivedCategoryFactorsh_hom_app_comp_inv L,
    CategoryTheory.Functor.map_comp DerivedCategory.Qh, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality]

include hresD hresJD in
/-- **(Z) solved for the tensorator**, with the tensor product of the two comparisons split into
its two whiskerings.  This is the componentwise form that the shift compatibility of the
tensorator is read off from. -/
theorem Functor.mu_constMapDerivedCategory_eq {K L : CochainComplex D ℤ}
    (hK : KFlat (curriedTensor D) K) (hL : KFlat (curriedTensor D) L) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
    Functor.LaxMonoidal.μ ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app K ▷
            ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).obj
              (DerivedCategory.Q.obj L)) ≫
        (DerivedCategory.Q.obj
              (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K) ◁
            (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.hom.app L) ≫
          (derivedTensorIso (J ⥤ D) hresJD (kFlat_constMapHomologicalComplex K hK)
              (kFlat_constMapHomologicalComplex L hL)).hom ≫
            DerivedCategory.Q.map (Functor.LaxMonoidal.μ
                ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ))
                K L) ≫
              (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactors.inv.app (K ⊗ L) ≫
                ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).map
                  (derivedTensorIso D hresD hK hL).inv := by
  let := derivedMonoidal D hresD
  let := derivedMonoidal (J ⥤ D) hresJD
  let := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  have hZ := Functor.mu_constMapDerivedCategory_derivedTensorIso hresD hresJD hK hL
  rw [MonoidalCategory.tensorHom_def] at hZ
  rw [← reassoc_of% hZ]
  simp

end Derived

end CategoryTheory

end
