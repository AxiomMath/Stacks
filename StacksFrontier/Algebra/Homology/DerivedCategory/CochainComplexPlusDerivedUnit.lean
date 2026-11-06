module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# The derived-functor unit on bounded-below cochain complexes, as a transformation

For an additive functor `T : 𝒜 ⥤ ℬ` between abelian categories with enough injectives in `𝒜`,
`CategoryTheory.Functor.mapHomologicalComplexDerivedUnit` compares the image in the derived
category of the termwise image `T(K)` of a bounded-below complex with the value at `K` of the
bounded-below right derived functor `RT`. This file assembles those comparisons into a natural
transformation

`T(-) ⋙ Q ⟶ Q ⋙ RT`

of functors on bounded-below cochain complexes, which carries a roof `Q(b) ≫ Q(a)⁻¹` to the roof
of the termwise images.

An object-level injective resolution is also read as an injective resolution of the complex
concentrated in degree zero.

## Main definitions

* `CategoryTheory.InjectiveResolution.toCochainComplex`: an injective resolution of an object,
  read as an injective resolution of the complex concentrated in degree zero.
* `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit`: the derived-functor unit on
  bounded-below cochain complexes, as a natural transformation.

## Main results

* `CategoryTheory.InjectiveResolution.mono_ι'_f`: the resolution map of an object-level
  injective resolution is degreewise a monomorphism.
* `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_roof`: the unit carries a roof
  representing a morphism in the derived category to the roof of the termwise images.
* `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_comp`: the unit at a composite
  functor, followed by the canonical comparison of the composite of the right derived functors,
  is the unit of the second factor followed by its image of the unit of the first.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite

universe v v' v'' w w' w'' u u' u''

namespace CategoryTheory

namespace InjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- An injective resolution of an object, read as an injective resolution of the complex
concentrated in degree zero. -/
def toCochainComplex (Z : A) (J : InjectiveResolution Z) :
    CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj Z) where
  cocomplex := J.cochainComplex
  boundedBelow := ⟨0, inferInstance⟩
  injective := by infer_instance
  ι := J.ι'
  quasiIso := by infer_instance

/-- The underlying complex of `toCochainComplex Z J` is `J.cochainComplex`. -/
@[simp]
lemma toCochainComplex_cocomplex (Z : A) (J : InjectiveResolution Z) :
    (toCochainComplex Z J).cocomplex = J.cochainComplex := rfl

/-- The resolution map of `toCochainComplex Z J` is `J.ι'`. -/
@[simp]
lemma toCochainComplex_ι (Z : A) (J : InjectiveResolution Z) :
    (toCochainComplex Z J).ι = J.ι' := rfl

/-- **The resolution map of an injective resolution is degreewise a monomorphism.** -/
lemma mono_ι'_f (Z : A) (J : InjectiveResolution Z) (n : ℤ) : Mono (J.ι'.f n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hJ : Mono (J.ι.f 0) := mono_of_isLimit_fork J.isLimitKernelFork
    have hι : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv ≫
        J.ι'.f 0) := by
      rw [J.ι'_f_zero, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      exact mono_comp (J.ι.f 0) ((J.cochainComplexXIso 0 0 (by simp)).inv)
    have hcomp : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv ≫ J.ι'.f 0) :=
      mono_comp _ _
    rwa [Iso.hom_inv_id_assoc] at hcomp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Z n hn).mono _

end InjectiveResolution

namespace Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- **The derived-functor unit on bounded-below cochain complexes.** At a bounded-below
complex `K` it compares the image in the bounded-below derived category of the termwise image
`T(K)` with the value at `K` of the bounded-below right derived functor of `T`. -/
def mapCochainComplexPlusDerivedUnit (T : A ⥤ B) [T.Additive] :
    T.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ T.rightDerivedFunctorPlus where
  app K :=
    (DerivedCategory.Plus.quotientCompQhIso B).inv.app (T.mapCochainComplexPlus.obj K) ≫
      T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
      T.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K)
  naturality K L g := by
    have hq := (DerivedCategory.Plus.quotientCompQhIso B).inv.naturality
      (T.mapCochainComplexPlus.map g)
    have hu := T.rightDerivedFunctorPlusUnith.naturality
      ((HomotopyCategory.Plus.quotient A).map g)
    have hp := (DerivedCategory.Plus.quotientCompQhIso A).hom.naturality g
    dsimp only [Functor.comp_map] at hq hu hp ⊢
    rw [← Category.assoc, hq]
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (fun z =>
      (DerivedCategory.Plus.quotientCompQhIso B).inv.app
        (T.mapCochainComplexPlus.obj K) ≫ z) ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ T.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso A).hom.app L)) hu).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z => T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj K) ≫ z)
      (T.rightDerivedFunctorPlus.map_comp _ _).symm).trans ?_
    refine (congrArg (fun z => T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj K) ≫
        T.rightDerivedFunctorPlus.map z) hp).trans ?_
    refine (congrArg (fun z => T.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj K) ≫ z)
      (T.rightDerivedFunctorPlus.map_comp _ _)).trans ?_
    exact (Category.assoc _ _ _).symm

/-- The components of the derived-functor unit on bounded-below cochain complexes. -/
lemma mapCochainComplexPlusDerivedUnit_app (T : A ⥤ B) [T.Additive]
    (K : CochainComplex.Plus A) :
    (mapCochainComplexPlusDerivedUnit T).app K =
      (DerivedCategory.Plus.quotientCompQhIso B).inv.app (T.mapCochainComplexPlus.obj K) ≫
        T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
        T.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K) := rfl

/-- **The derived-functor unit carries a roof to the roof of the termwise images.** A morphism
of the derived category presented as `Q(b) ≫ Q(a)⁻¹` for a quasi-isomorphism `a` is carried by
the unit to the corresponding roof built from the termwise images, provided `T(a)` is a
quasi-isomorphism too. -/
lemma mapCochainComplexPlusDerivedUnit_roof (T : A ⥤ B) [T.Additive]
    {K L M : CochainComplex.Plus A} (a : K ⟶ M) (b : L ⟶ M)
    [IsIso (DerivedCategory.Plus.Q.map a)]
    [IsIso (DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map a))] :
    (mapCochainComplexPlusDerivedUnit T).app L ≫ T.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map b ≫
          CategoryTheory.inv (DerivedCategory.Plus.Q.map a)) =
      DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map b) ≫
        CategoryTheory.inv (DerivedCategory.Plus.Q.map
          (T.mapCochainComplexPlus.map a)) ≫
          (mapCochainComplexPlusDerivedUnit T).app K := by
  have ha := (mapCochainComplexPlusDerivedUnit T).naturality a
  have hb := (mapCochainComplexPlusDerivedUnit T).naturality b
  dsimp only [Functor.comp_map] at ha hb
  rw [T.rightDerivedFunctorPlus.map_comp, ← Category.assoc, ← hb, Category.assoc]
  refine congrArg (fun z => DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map b) ≫ z) ?_
  refine (cancel_epi (DerivedCategory.Plus.Q.map (T.mapCochainComplexPlus.map a))).mp ?_
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ha, Category.assoc,
    ← T.rightDerivedFunctorPlus.map_comp, IsIso.hom_inv_id,
    T.rightDerivedFunctorPlus.map_id]
  exact Category.comp_id _

/-! ### Composing the unit with the comparison of a composite of right derived functors -/

section Composition

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u''} [Category.{v''} C] [Abelian C] [HasDerivedCategory.{w''} C]
  [EnoughInjectives B]

/-- If `m ≫ c = c' ≫ n` and `u ≫ c' = r ≫ s`, then `(i ≫ u ≫ m) ≫ c = i ≫ r ≫ s ≫ n`. -/
private lemma comp_eq_of_naturality_of_fac {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ Y Z : D} (i : X₀ ⟶ X₁) (u : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (c : X₃ ⟶ X₄)
    (c' : X₂ ⟶ Y) (n : Y ⟶ X₄) (r : X₁ ⟶ Z) (s : Z ⟶ Y)
    (hnat : m ≫ c = c' ≫ n) (hfac : u ≫ c' = r ≫ s) :
    (i ≫ u ≫ m) ≫ c = i ≫ r ≫ s ≫ n := by
  rw [Category.assoc, Category.assoc, hnat, reassoc_of% hfac]

/-- If `p ≫ q = 𝟙 Y₀`, then `(i ≫ u ≫ F.map p) ≫ F.map (q ≫ t) = i ≫ u ≫ F.map t`. -/
private lemma comp_map_eq_of_comp_eq_id {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) {X₀ X₁ : E} {Y₀ Y₁ Y₂ : D} (i : X₀ ⟶ X₁) (u : X₁ ⟶ F.obj Y₀)
    (p : Y₀ ⟶ Y₁) (q : Y₁ ⟶ Y₀) (t : Y₀ ⟶ Y₂) (h : p ≫ q = 𝟙 Y₀) :
    (i ≫ u ≫ F.map p) ≫ F.map (q ≫ t) = i ≫ u ≫ F.map t := by
  rw [Category.assoc, Category.assoc, ← F.map_comp, ← Category.assoc p, h, Category.id_comp]

/-- **The derived-functor unit is compatible with the comparison map of a composite.** Let
`t : R(R ∘ T) ⟶ RR ∘ RT` be a transformation whose composite with the unit of `R(R ∘ T)` is
the transformation assembled from the units of `RR` and of `RT`. Then the derived-functor unit
at the composite functor, followed by `t`, is the unit of `RR` at the termwise image `T(K)`
followed by the image under `RR` of the unit of `RT` at `K`. -/
lemma mapCochainComplexPlusDerivedUnit_comp (T : A ⥤ B) (R : B ⥤ C) [T.Additive] [R.Additive]
    (t : (T ⋙ R).rightDerivedFunctorPlus ⟶
      T.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus)
    (ht : (T ⋙ R).rightDerivedFunctorPlusUnith ≫ whiskerLeft DerivedCategory.Plus.Qh t =
      whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ R))).inv
          DerivedCategory.Plus.Qh ≫
        whiskerLeft T.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnith ≫
        whiskerRight T.rightDerivedFunctorPlusUnith R.rightDerivedFunctorPlus)
    (K : CochainComplex.Plus A) :
    (mapCochainComplexPlusDerivedUnit (T ⋙ R)).app K ≫ t.app (DerivedCategory.Plus.Q.obj K) =
      (mapCochainComplexPlusDerivedUnit R).app (T.mapCochainComplexPlus.obj K) ≫
        R.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit T).app K) := by
  set H := (HomotopyCategory.Plus.quotient A).obj K
  set e := (DerivedCategory.Plus.quotientCompQhIso A).hom.app K
  have hnat : (T ⋙ R).rightDerivedFunctorPlus.map e ≫ t.app (DerivedCategory.Plus.Q.obj K) =
      t.app (DerivedCategory.Plus.Qh.obj H) ≫
        R.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlus.map e) := t.naturality e
  have hone : DerivedCategory.Plus.Qh.map
      ((mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ R))).inv.app H) = 𝟙 _ := by
    rw [show (mapHomotopyCategoryPlusCompIso (Iso.refl (T ⋙ R))).inv.app H = 𝟙 _ from
      ObjectProperty.hom_ext _ rfl]
    exact DerivedCategory.Plus.Qh.map_id _
  have hfac := congrArg (fun η : (T ⋙ R).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus => η.app H) ht
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hfac
  rw [hone] at hfac
  have hfac' : (T ⋙ R).rightDerivedFunctorPlusUnith.app H ≫
        t.app (DerivedCategory.Plus.Qh.obj H) =
      R.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj H) ≫
        R.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnith.app H) :=
    hfac.trans (Category.id_comp _)
  refine (comp_eq_of_naturality_of_fac
    ((DerivedCategory.Plus.quotientCompQhIso C).inv.app
      ((T ⋙ R).mapCochainComplexPlus.obj K))
    ((T ⋙ R).rightDerivedFunctorPlusUnith.app H)
    ((T ⋙ R).rightDerivedFunctorPlus.map e)
    (t.app (DerivedCategory.Plus.Q.obj K))
    (t.app (DerivedCategory.Plus.Qh.obj H))
    (R.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlus.map e))
    (R.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj H))
    (R.rightDerivedFunctorPlus.map (T.rightDerivedFunctorPlusUnith.app H))
    hnat hfac').trans ?_
  refine Eq.trans ?_ (comp_map_eq_of_comp_eq_id R.rightDerivedFunctorPlus
    ((DerivedCategory.Plus.quotientCompQhIso C).inv.app
      (R.mapCochainComplexPlus.obj (T.mapCochainComplexPlus.obj K)))
    (R.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient B).obj (T.mapCochainComplexPlus.obj K)))
    ((DerivedCategory.Plus.quotientCompQhIso B).hom.app (T.mapCochainComplexPlus.obj K))
    ((DerivedCategory.Plus.quotientCompQhIso B).inv.app (T.mapCochainComplexPlus.obj K))
    (T.rightDerivedFunctorPlusUnith.app H ≫ T.rightDerivedFunctorPlus.map e)
    ((DerivedCategory.Plus.quotientCompQhIso B).hom_inv_id_app _)).symm
  exact congrArg (fun z => (DerivedCategory.Plus.quotientCompQhIso C).inv.app
      ((T ⋙ R).mapCochainComplexPlus.obj K) ≫
    R.rightDerivedFunctorPlusUnith.app (T.mapHomotopyCategoryPlus.obj H) ≫ z)
    (R.rightDerivedFunctorPlus.map_comp _ _).symm

end Composition

end Functor

end CategoryTheory

end
