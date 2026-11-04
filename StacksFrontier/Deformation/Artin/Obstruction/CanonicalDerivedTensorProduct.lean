module

public import Mathlib
public import StacksFrontier.Deformation.Artin.Obstruction
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# A canonical derived tensor product on `D(A)`

`Deformation.Artin.DerivedTensorProduct A` records a derived tensor product on the derived
category of `A`-modules: a bifunctor, comparisons with the tensor product of complexes
exhibiting it as the total left derived functor in each variable, and the standard exact,
symmetric and unital structure. This file produces such a term for an arbitrary commutative
ring `A`, so that every statement quantified over a `DerivedTensorProduct A` has content.

The term is assembled from `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`,
whose comparison is stated on K-flat representatives rather than as a universal property.
The two universal properties are obtained by transporting that comparison along a chosen
K-flat resolution and recognizing the result as a total left derived functor through
`CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat`. The
second variable is handled by conjugating the first with the canonical symmetry. At the
tensor unit the comparison is replaced by the one coming from the left unitor itself, which
is what makes the required compatibility between the derived and chain-level left unitors
hold on the nose.

## Main definitions

* `Deformation.Artin.canonicalDerivedTensorProduct` — a derived tensor product on `D(A)`,
  for an arbitrary commutative ring `A`.

## References

* [Stacks Project, Section 47.9](https://stacks.math.columbia.edu/tag/0A6P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor MonoidalCategory HomologicalComplex
open CochainComplex.DerivedTensor StacksDraft.TorAmplitude

namespace Deformation.Artin

universe u

attribute [local instance] HasDerivedCategory.standard

section CanonicalTensorAdapter

variable {A : Type u} [CommRing A]

/-- The underlying cochain complex of an object of the homotopy category, as a named
definition rather than the raw `Quotient` projection. Going through a constant keeps the
goals of the constructions below type-correct at `implicit` transparency, where
`HomotopyCategory` does not unfold to `CategoryTheory.Quotient`. -/
private def homotopyAs (X : HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ)) :
    CochainComplex (ModuleCat.{u} A) ℤ := X.as

/-- The image of an isomorphism under a functor. This repeats `CategoryTheory.Functor.mapIso`
so that the accompanying `functorMapIso_hom` is usable as a rewrite rule: the `@[simps]`
lemma for `Functor.mapIso` has its left-hand side already reduced, hence rewrites nothing. -/
private def functorMapIso {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}
    (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  hom := F.map i.hom
  inv := F.map i.inv
  hom_inv_id := by rw [← F.map_comp, i.hom_inv_id, F.map_id]
  inv_hom_id := by rw [← F.map_comp, i.inv_hom_id, F.map_id]

private lemma functorMapIso_hom {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}
    (i : X ≅ Y) : (functorMapIso F i).hom = F.map i.hom := rfl

private lemma tensorRight_inverts (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)).IsInvertedBy
      (tensorRight P ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have h : QuasiIso ((tensorRight P).map f) := quasiIso_tensorRight_map hP f
  have := h
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((tensorRight P).map f)))
private noncomputable abbrev liftedTensor (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : P.KFlat) : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Localization.lift (tensorRight P ⋙ DerivedCategory.Q) (tensorRight_inverts P hP) DerivedCategory.Q
private noncomputable def liftedTensorFactors (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : P.KFlat) : DerivedCategory.Q ⋙ liftedTensor P hP ≅ tensorRight P ⋙ DerivedCategory.Q :=
  Localization.fac _ (tensorRight_inverts P hP) DerivedCategory.Q
/-- `Z` is K-flat, stated about `homotopyAs Z.obj` rather than about the raw projection. -/
private lemma homotopyAs_kFlat (Z : (kFlatHomotopyObjects A).FullSubcategory) :
    (homotopyAs Z.obj).KFlat := Z.property

/-- The derived object of a K-flat object of the homotopy category, compared with the
derived object of its underlying complex. The content is
`DerivedCategory.quotientCompQhIso`; stating it as a definition of this type is what keeps
the naturality square below type-correct at `implicit` transparency. -/
private noncomputable def kFlatQIso (Z : (kFlatHomotopyObjects A).FullSubcategory) :
    DerivedCategory.Qh.obj Z.obj ≅ DerivedCategory.Q.obj (homotopyAs Z.obj) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (homotopyAs Z.obj)

private lemma kFlatQIso_hom_naturality {Z Z' : (kFlatHomotopyObjects A).FullSubcategory}
    (f : Z ⟶ Z') (g : homotopyAs Z.obj ⟶ homotopyAs Z'.obj)
    (hg : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map g = f.hom) :
    DerivedCategory.Qh.map f.hom ≫ (kFlatQIso Z').hom =
      (kFlatQIso Z).hom ≫ DerivedCategory.Q.map g := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} A) g
  rw [hg] at h
  exact h

private lemma kFlatQIso_inv_naturality {Z Z' : (kFlatHomotopyObjects A).FullSubcategory}
    (f : Z ⟶ Z') (g : homotopyAs Z.obj ⟶ homotopyAs Z'.obj)
    (hg : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map g = f.hom) :
    DerivedCategory.Q.map g ≫ (kFlatQIso Z').inv =
      (kFlatQIso Z).inv ≫ DerivedCategory.Qh.map f.hom := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (kFlatQIso_hom_naturality f g hg).symm

private noncomputable def tensorFlatComparison
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    kFlatHomotopyQ A ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj P) ≅
      kFlatHomotopyQ A ⋙ liftedTensor P hP := by
  refine NatIso.ofComponents (fun X =>
    functorMapIso (T.tensor.flip.obj (DerivedCategory.Q.obj P)) (kFlatQIso X) ≪≫
    T.comparison (homotopyAs X.obj) P (homotopyAs_kFlat X) hP ≪≫
    ((liftedTensorFactors P hP).app (homotopyAs X.obj)).symm ≪≫
    functorMapIso (liftedTensor P hP) (kFlatQIso X).symm) ?_
  intro X Y f
  obtain ⟨g, hg⟩ : ∃ g : homotopyAs X.obj ⟶ homotopyAs Y.obj,
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map g = f.hom :=
    ⟨f.hom.out, HomotopyCategory.quotient_map_out _⟩
  have hcmp : (T.tensor.map (DerivedCategory.Q.map g)).app (DerivedCategory.Q.obj P) ≫
      (T.comparison (homotopyAs Y.obj) P (homotopyAs_kFlat Y) hP).hom =
      (T.comparison (homotopyAs X.obj) P (homotopyAs_kFlat X) hP).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom g (𝟙 P)) := by
    have h := T.comparison_naturality g (𝟙 P) (homotopyAs_kFlat X) (homotopyAs_kFlat Y) hP hP
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  have key : (T.tensor.flip.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map g) ≫
      (T.comparison (homotopyAs Y.obj) P (homotopyAs_kFlat Y) hP).hom ≫
        (liftedTensorFactors P hP).inv.app (homotopyAs Y.obj) =
      (T.comparison (homotopyAs X.obj) P (homotopyAs_kFlat X) hP).hom ≫
        (liftedTensorFactors P hP).inv.app (homotopyAs X.obj) ≫
          (liftedTensor P hP).map (DerivedCategory.Q.map g) := by
    have h1 : (T.tensor.flip.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map g) =
        (T.tensor.map (DerivedCategory.Q.map g)).app (DerivedCategory.Q.obj P) := rfl
    rw [h1, reassoc_of% hcmp]
    have h2 : (tensorRight P).map g = HomologicalComplex.tensorHom g (𝟙 P) := rfl
    rw [← h2]
    exact congrArg
      (fun z => (T.comparison (homotopyAs X.obj) P (homotopyAs_kFlat X) hP).hom ≫ z)
      ((liftedTensorFactors P hP).inv.naturality g)
  dsimp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, functorMapIso_hom, Iso.app_hom,
    Iso.app_inv, ObjectProperty.ι_map]
  rw [← Functor.map_comp_assoc, kFlatQIso_hom_naturality f g hg, Functor.map_comp_assoc,
    reassoc_of% key]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, kFlatQIso_inv_naturality f g hg]
private noncomputable def tensorFlatIso (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    T.tensor.flip.obj (DerivedCategory.Q.obj P) ≅ liftedTensor P hP := by
  letI := kFlatHomotopyQ_isLocalization A
  exact (Localization.fullyFaithfulWhiskeringLeft (kFlatHomotopyQ A)
    (kFlatHomotopyQuasiIso A) (DerivedCategory (ModuleCat.{u} A))).preimageIso
      (tensorFlatComparison T P hP)


private noncomputable abbrev termwiseTensorHomotopy (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Tright L ⋙ DerivedCategory.Qh
private noncomputable def quotientCompTermwiseTensorIso (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ) ⋙ termwiseTensorHomotopy L ≅
      TrightCochain L ⋙ DerivedCategory.Q := by
  letI : (TrightCochain L).Additive := TrightCochain_additive L
  exact Functor.isoWhiskerRight
      (eqToIso (descendF_comp_quotient (TrightCochain L)
        (TrightCochain_preservesHomotopyRel L))) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (TrightCochain L)
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))
private noncomputable def compareLeft (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q ⋙
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.flip.obj
        (DerivedCategory.Q.obj L) ⟶ TrightCochain L ⋙ DerivedCategory.Q := by
  letI : (TrightCochain L).Additive := TrightCochain_additive L
  let P := (CochainComplex.KFlat.exists_kFlat_resolution L).choose
  let π := (CochainComplex.KFlat.exists_kFlat_resolution L).choose_spec.choose
  let hP := (CochainComplex.KFlat.exists_kFlat_resolution L).choose_spec.choose_spec.1
  let hπ := (CochainComplex.KFlat.exists_kFlat_resolution L).choose_spec.choose_spec.2.2.1
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  letI : QuasiIso π := hπ
  exact Functor.whiskerLeft DerivedCategory.Q
      (T.tensor.flip.mapIso (asIso (DerivedCategory.Q.map π))).symm.hom ≫
    (Functor.isoWhiskerLeft DerivedCategory.Q (tensorFlatIso T P hP)).hom ≫
    (liftedTensorFactors P hP).hom ≫
      Functor.whiskerRight ((curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip.map π)
        DerivedCategory.Q
private lemma compareLeft_isIso (L K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) :
    IsIso ((compareLeft L).app K) := by
  let P := (CochainComplex.KFlat.exists_kFlat_resolution L).choose
  let π := (CochainComplex.KFlat.exists_kFlat_resolution L).choose_spec.choose
  let hP := (CochainComplex.KFlat.exists_kFlat_resolution L).choose_spec.choose_spec.1
  let hπ := (CochainComplex.KFlat.exists_kFlat_resolution L).choose_spec.choose_spec.2.2.1
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let : QuasiIso π := hπ
  have h1 : IsIso ((Functor.whiskerLeft DerivedCategory.Q
      (T.tensor.flip.mapIso (asIso (DerivedCategory.Q.map π))).symm.hom).app K) := inferInstance
  have h2 : IsIso ((Functor.isoWhiskerLeft DerivedCategory.Q (tensorFlatIso T P hP)).hom.app K) :=
      inferInstance
  have h3 : IsIso ((liftedTensorFactors P hP).hom.app K) := inferInstance
  have hπ' : QuasiIso ((tensorLeft K).map π) :=
    StacksDraft.TorAmplitude.quasiIso_tensorLeft_map K hK π
  have h4 : IsIso (DerivedCategory.Q.map ((tensorLeft K).map π)) := by infer_instance
  show IsIso ((Functor.whiskerLeft DerivedCategory.Q
      (T.tensor.flip.mapIso (asIso (DerivedCategory.Q.map π))).symm.hom).app K ≫
    (Functor.isoWhiskerLeft DerivedCategory.Q (tensorFlatIso T P hP)).hom.app K ≫
    (liftedTensorFactors P hP).hom.app K ≫ DerivedCategory.Q.map ((tensorLeft K).map π))
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (IsIso.comp_isIso' h3 h4))
private theorem compareLeft_isLeftDerived (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.flip.obj
      (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor (compareLeft L)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) :=
  CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat
    (TrightCochain L ⋙ DerivedCategory.Q) (termwiseTensorHomotopy L)
    (quotientCompTermwiseTensorIso L)
    _ (compareLeft L) (fun K hK => compareLeft_isIso L K hK)

private noncomputable abbrev termwiseLeftTensorHomotopy
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomotopyCategory (ModuleCat.{u} A) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Tleft K ⋙ DerivedCategory.Qh

private noncomputable def quotientCompTermwiseLeftTensorIso
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ) ⋙
      termwiseLeftTensorHomotopy K ≅ TleftCochain K ⋙ DerivedCategory.Q := by
  letI : (TleftCochain K).Additive := TleftCochain_additive K
  exact Functor.isoWhiskerRight
      (eqToIso (descendF_comp_quotient (TleftCochain K)
        (TleftCochain_preservesHomotopyRel K))) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (TleftCochain K)
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))

section FlipHelpers
variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D] {F G : C₁ ⥤ C₂ ⥤ D}
  [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ X, (G.obj X).PreservesZeroMorphisms]
private noncomputable def mapBifunctorHomologicalComplexIso
    (e : F ≅ G) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) :
    ((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L ≅
      ((G.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L :=
  Hom.isoOfComponents
    (fun i => Hom.isoOfComponents
      (fun j => (e.app (K.X i)).app (L.X j))
      (fun j j' _ => ((e.hom.app (K.X i)).naturality (L.d j j')).symm))
    (fun i i' _ => by
      ext j
      exact (congr_app (e.hom.naturality (K.d i i')) (L.X j)).symm)
private noncomputable def mapBifunctorIso
    (e : F ≅ G) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [HasMapBifunctor K L F (.up ℤ)] [HasMapBifunctor K L G (.up ℤ)] :
    mapBifunctor K L F (.up ℤ) ≅ mapBifunctor K L G (.up ℤ) :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexIso e K L) (.up ℤ)
private lemma ι_mapBifunctorIso_hom
    (e : F ≅ G) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [HasMapBifunctor K L F (.up ℤ)] [HasMapBifunctor K L G (.up ℤ)]
    (i j n : ℤ) (h : i + j = n) :
    ιMapBifunctor K L F (.up ℤ) i j n h ≫ (mapBifunctorIso e K L).hom.f n =
      (e.hom.app (K.X i)).app (L.X j) ≫ ιMapBifunctor K L G (.up ℤ) i j n h := by
  dsimp only [mapBifunctorIso, HomologicalComplex₂.total.mapIso, ιMapBifunctor]
  exact HomologicalComplex₂.ιTotal_map ..
private lemma mapBifunctorIso_hom_naturality
    (e : F ≅ G) {K K' : CochainComplex C₁ ℤ} {L L' : CochainComplex C₂ ℤ}
    (f : K ⟶ K') (g : L ⟶ L')
    [HasMapBifunctor K L F (.up ℤ)] [HasMapBifunctor K L G (.up ℤ)]
    [HasMapBifunctor K' L' F (.up ℤ)] [HasMapBifunctor K' L' G (.up ℤ)] :
    mapBifunctorMap f g F (.up ℤ) ≫ (mapBifunctorIso e K' L').hom =
      (mapBifunctorIso e K L).hom ≫ mapBifunctorMap f g G (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc,
    ι_mapBifunctorIso_hom, reassoc_of% ι_mapBifunctorIso_hom, ι_mapBifunctorMap]
  simp [← NatTrans.naturality_assoc]
end FlipHelpers

private noncomputable def localTensorLeftIsoRight (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    tensorLeft K ≅ tensorRight K :=
  NatIso.ofComponents
    (fun L => mapBifunctorIso (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} A)) K L ≪≫
      mapBifunctorFlipIso L K (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ))
    (fun {L L'} f => by
      change mapBifunctorMap (𝟙 K) f (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) ≫
          (mapBifunctorIso (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} A)) K L').hom ≫
            (mapBifunctorFlipIso L' K (curriedTensor (ModuleCat.{u} A))
              (ComplexShape.up ℤ)).hom = _
      rw [reassoc_of% mapBifunctorIso_hom_naturality
          (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} A)) (𝟙 K) f,
        mapBifunctorFlipIso_hom_naturality]
      simp only [Iso.trans_hom, Category.assoc]
      rfl)

private noncomputable abbrev unitComplex : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)

private noncomputable def canonicalLeftUnitor :
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
      (Deformation.Artin.ringObject A)) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} A)) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let TS := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct A
  exact (TS.braiding.iso.app (Deformation.Artin.ringObject A)) ≪≫ T.rightUnitor

private noncomputable def compareRightUnit :
    DerivedCategory.Q ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
          (DerivedCategory.Q.obj unitComplex) ⟶
      Deformation.Artin.complexTensorRight A unitComplex := by
  exact Functor.whiskerLeft DerivedCategory.Q canonicalLeftUnitor.hom ≫
    (Functor.rightUnitor DerivedCategory.Q).hom ≫
    (Functor.leftUnitor DerivedCategory.Q).inv ≫
    Functor.whiskerRight
      (MonoidalCategory.leftUnitorNatIso (CochainComplex (ModuleCat.{u} A) ℤ)).inv
      DerivedCategory.Q

private lemma compareRightUnit_isIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (compareRightUnit.app K) := by
  have h1 : IsIso ((Functor.whiskerLeft DerivedCategory.Q
      (canonicalLeftUnitor (A := A)).hom).app K) := inferInstance
  have h2 : IsIso ((Functor.rightUnitor
      (DerivedCategory.Q (C := ModuleCat.{u} A))).hom.app K) := inferInstance
  have h3 : IsIso ((Functor.leftUnitor
      (DerivedCategory.Q (C := ModuleCat.{u} A))).inv.app K) := inferInstance
  have h4 : IsIso ((Functor.whiskerRight
      (MonoidalCategory.leftUnitorNatIso (CochainComplex (ModuleCat.{u} A) ℤ)).inv
      DerivedCategory.Q).app K) := inferInstance
  show IsIso ((Functor.whiskerLeft DerivedCategory.Q (canonicalLeftUnitor (A := A)).hom).app K ≫
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{u} A))).hom.app K ≫
    (Functor.leftUnitor (DerivedCategory.Q (C := ModuleCat.{u} A))).inv.app K ≫
    (Functor.whiskerRight
      (MonoidalCategory.leftUnitorNatIso (CochainComplex (ModuleCat.{u} A) ℤ)).inv
      DerivedCategory.Q).app K)
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (IsIso.comp_isIso' h3 h4))

private theorem compareRightUnit_isLeftDerived :
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
      (DerivedCategory.Q.obj unitComplex)).IsLeftDerivedFunctor compareRightUnit
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) := by
  simpa [Deformation.Artin.DerivedCategoryOfRing, Deformation.Artin.complexTensorRight,
    Deformation.Artin.ringObject, unitComplex, TleftCochain] using
    (CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat.{u, u}
      (TleftCochain unitComplex ⋙ DerivedCategory.Q) (termwiseLeftTensorHomotopy unitComplex)
      (quotientCompTermwiseLeftTensorIso unitComplex)
      _ compareRightUnit (fun K _ => compareRightUnit_isIso K))

private lemma unitLeftUnitor_eq (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (MonoidalCategory.leftUnitorNatIso (CochainComplex (ModuleCat.{u} A) ℤ)).hom.app K =
      (HomologicalComplex.leftUnitor K).hom := by
  rfl

private noncomputable def compareRightRaw (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q ⋙ (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
      (DerivedCategory.Q.obj K) ⟶ TleftCochain K ⋙ DerivedCategory.Q := by
  let T0 := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct A
  exact Functor.whiskerLeft DerivedCategory.Q (T0.braiding.iso.hom.app (DerivedCategory.Q.obj K)) ≫
    compareLeft K ≫
    Functor.whiskerRight (localTensorLeftIsoRight K).inv DerivedCategory.Q

private noncomputable def compareRight (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q ⋙ (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
      (DerivedCategory.Q.obj K) ⟶ TleftCochain K ⋙ DerivedCategory.Q := by
  classical
  by_cases h : K = unitComplex
  · subst K
    exact compareRightUnit
  · exact compareRightRaw K

private lemma compareRight_isIso (K L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.KFlat) :
    IsIso ((compareRight K).app L) := by
  classical
  by_cases h : K = unitComplex
  · subst K
    simpa [compareRight, TleftCochain] using compareRightUnit_isIso L
  · simp only [compareRight, dif_neg h]
    have h1 : IsIso ((Functor.whiskerLeft DerivedCategory.Q
        ((canonicalSymmetricDerivedTensorProduct A).braiding.iso.hom.app
          (DerivedCategory.Q.obj K))).app L) := inferInstance
    have h2 : IsIso ((compareLeft K).app L) := compareLeft_isIso K L hL
    have h3 : IsIso ((Functor.whiskerRight
        (localTensorLeftIsoRight K).inv DerivedCategory.Q).app L) := inferInstance
    show IsIso ((Functor.whiskerLeft DerivedCategory.Q
        ((canonicalSymmetricDerivedTensorProduct A).braiding.iso.hom.app
          (DerivedCategory.Q.obj K))).app L ≫ (compareLeft K).app L ≫
        (Functor.whiskerRight (localTensorLeftIsoRight K).inv DerivedCategory.Q).app L)
    exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

private theorem compareRight_isLeftDerived (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
      (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor (compareRight K)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) :=
  CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat.{u, u}
    (TleftCochain K ⋙ DerivedCategory.Q) (termwiseLeftTensorHomotopy K)
    (quotientCompTermwiseLeftTensorIso K)
    _ (compareRight K) (fun L hL => compareRight_isIso K L hL)

/-- **The canonical derived tensor product on `D(A)`.** This exhibits a term of
`Deformation.Artin.DerivedTensorProduct A` for every commutative ring `A`, built from the
canonical derived tensor product `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`
and its canonical symmetry. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[no_expose]
public noncomputable def canonicalDerivedTensorProduct (A : Type u) [CommRing A] :
    Deformation.Artin.DerivedTensorProduct A := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let TS := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct A
  refine {
    tensor := T.tensor
    comparison_left := compareLeft
    isLeftDerived_left := compareLeft_isLeftDerived
    comparison_right := compareRight
    isLeftDerived_right := by
      intro K
      classical
      by_cases h : K = unitComplex
      · subst K
        simpa [compareRight, unitComplex, Deformation.Artin.DerivedCategoryOfRing,
          Deformation.Artin.ringObject, Deformation.Artin.complexTensorRight,
          TleftCochain] using compareRightUnit_isLeftDerived (A := A)
      · simpa [compareRight, h, Deformation.Artin.complexTensorRight,
          TleftCochain] using compareRight_isLeftDerived K
    add_left := fun L => inferInstance
    add_right := fun K => inferInstance
    commShift_left := T.commShift_left
    commShift_right := T.commShift_right
    triangulated_left := T.exact_left
    triangulated_right := T.exact_right
    braiding := TS.braiding.iso
    leftUnitor := canonicalLeftUnitor (A := A)
    leftUnitor_compatibility := by
      intro K
      change (compareRight (A := A) unitComplex).app K ≫
        DerivedCategory.Q.map (HomologicalComplex.leftUnitor K).hom =
        (canonicalLeftUnitor (A := A)).hom.app (DerivedCategory.Q.obj K)
      have hcmp : compareRight (A := A) unitComplex = compareRightUnit (A := A) := by
        simp [compareRight, unitComplex]
        rfl
      have happ : (compareRightUnit (A := A)).app K =
          (canonicalLeftUnitor (A := A)).hom.app (DerivedCategory.Q.obj K) ≫
            DerivedCategory.Q.map
              ((MonoidalCategory.leftUnitorNatIso
                (CochainComplex (ModuleCat.{u} A) ℤ)).inv.app K) := by
        simp only [compareRightUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.rightUnitor_hom_app]
        exact congrArg
          (fun z => (canonicalLeftUnitor (A := A)).hom.app (DerivedCategory.Q.obj K) ≫ z)
          (Category.id_comp (DerivedCategory.Q.map
            ((MonoidalCategory.leftUnitorNatIso
              (CochainComplex (ModuleCat.{u} A) ℤ)).inv.app K)))
      have h_unitor :
          (MonoidalCategory.leftUnitorNatIso (CochainComplex (ModuleCat.{u} A) ℤ)).inv.app K ≫
            (HomologicalComplex.leftUnitor K).hom = 𝟙 _ := by
        rw [← unitLeftUnitor_eq K]
        simp
      have hmap : DerivedCategory.Q.map
            ((MonoidalCategory.leftUnitorNatIso
              (CochainComplex (ModuleCat.{u} A) ℤ)).inv.app K) ≫
            DerivedCategory.Q.map (HomologicalComplex.leftUnitor K).hom =
          𝟙 (DerivedCategory.Q.obj K) := by
        rw [← Functor.map_comp, h_unitor]
        simp
      rw [hcmp, happ]
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun z => (canonicalLeftUnitor (A := A)).hom.app (DerivedCategory.Q.obj K) ≫ z)
          hmap).trans (Category.comp_id _)) }

end CanonicalTensorAdapter

end Deformation.Artin

end
