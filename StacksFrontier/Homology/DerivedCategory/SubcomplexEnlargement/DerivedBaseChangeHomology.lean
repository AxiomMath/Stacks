module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksFrontier.Algebra.Module.ProjResComplexFlat
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat
public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargement.BoundedSubcomplexes

@[expose] public noncomputable section

/-!
# Cohomology of derived base change

Cohomology of the derived base change of a complex along a ring homomorphism `A →+* B`: its
computation by a projective resolution of `B`, its commutation with filtered colimits, and its
cardinality bound.

## Main results

* `Stacks.SubcomplexEnlargement.derivedBaseChangeHomology_preservesFilteredColimits_ulift`: derived
  base change followed by cohomology preserves filtered colimits.

## Implementation notes

Cohomology of the derived base change of `K` is identified, over `A`, with the cohomology of
`K ⊗_A P` for `P` the chosen projective resolution of `B` as an `A`-module. Both sides are total
left derived functors of `K ↦ H^i(B ⊗_A K)`: the derived one because derived extension of scalars
is absolute under postcomposition, the resolution one because the comparison map it carries is
invertible on K-flat complexes and K-flat complexes resolve every object. The comparison itself is
the augmentation of the resolution followed by the projection formula.

## References

* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SubcomplexEnlargement

universe u v w t

attribute [local instance] HasDerivedCategory.standard

open Cardinal

section Core

open StacksDraft.TorAmplitude CategoryTheory.Functor CategoryTheory.MonoidalCategory

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The chosen projective resolution of a module is a bounded above complex of projectives. -/
private lemma projResComplex_projective {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (n : ℤ) : Projective ((StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M).X n) := by
  change Projective (((ProjectiveResolution.of M).complex.extend
    ComplexShape.embeddingDownNat).X n)
  infer_instance

private instance projResComplex_isStrictlyLE {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M).IsStrictlyLE 0 := by
  change CochainComplex.IsStrictlyLE
    ((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat) 0
  infer_instance


/-- The target ring, viewed as a module over the source ring along `f`. -/
private abbrev baseModule (f : A →+* B) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)

/-- Extension of scalars followed by restriction of scalars is tensoring with `B`. -/
private def extensionUnderlyingIso (f : A →+* B) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft (baseModule f) :=
  NatIso.ofComponents (fun M => Iso.refl _) (by intros; rfl)

/-- Degreewise extension of scalars on cochain complexes. -/
private abbrev extendComplex (f : A →+* B) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise restriction of scalars on cochain complexes. -/
private abbrev restrictComplex (f : A →+* B) :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The single complex `B[0]` of `A`-modules. -/
private abbrev baseSingle (f : A →+* B) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj (baseModule f)

open TotalTensorComplex.SingleTensor in
/-- Tensoring on the left with `B[0]` is degreewise tensoring with `B`. -/
private def singleTensorNatIso (f : A →+* B) :
    (tensorLeft (baseModule f)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      tensorLeft (baseSingle f) :=
  NatIso.ofComponents (fun K => (singleTensorIso (baseModule f) K).symm)
    (fun g => (singleTensorIso_naturality (baseModule f) g).symm)

/-- **The projection formula.** The underlying complex of `A`-modules of the extension of
scalars of `K` is naturally the total tensor product of `B[0]` with `K`. -/
private def projectionFormulaIso (f : A →+* B) :
    tensorLeft (baseSingle f) ≅ extendComplex f ⋙ restrictComplex f :=
  (singleTensorNatIso f).symm ≪≫
    (Functor.mapHomologicalComplexCompIso (extensionUnderlyingIso f)
      (ComplexShape.up ℤ)).symm

/-- Tensoring on the left agrees with tensoring on the right, naturally in the varying
complex. -/
private def tensorFlipNatIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    tensorLeft K ≅ tensorRight K :=
  NatIso.ofComponents (fun L => CochainComplex.DerivedTensor.tensorFlipIso.{u, u} K L)
    (CochainComplex.DerivedTensor.tensorFlipIso_naturality.{u, u} K)

/-- The chosen projective resolution of `B` as an `A`-module. -/
private abbrev baseResolution (f : A →+* B) : CochainComplex (ModuleCat.{u} A) ℤ :=
  StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex (baseModule f)

/-- The ordinary functor `K ↦ H^i(K ⊗_A P)` computed by the resolution `P` of `B`. -/
private abbrev resolutionHomology (f : A →+* B) (i : ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} A :=
  tensorRight (baseResolution f) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i

/-- Termwise extension of scalars, localized, followed by cohomology and restriction. -/
private abbrev derivedTargetHomology (f : A →+* B) (i : ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} A :=
  extendComplex f ⋙ DerivedCategory.Q ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙ ModuleCat.restrictScalars f

/-- Cohomology of the underlying complex of an extension of scalars is the restriction of
scalars of its cohomology over `B`. -/
private def restrictHomologyIso (f : A →+* B) (i : ℤ) :
    restrictComplex f ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i ≅
      DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
        ModuleCat.restrictScalars f :=
  StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (ModuleCat.restrictScalars.{u} f) (ComplexShape.up ℤ) i ≪≫
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).symm
      (ModuleCat.restrictScalars.{u} f) ≪≫
    Functor.associator _ _ _

/-- Everything in the resolution comparison except the augmentation: the flip, the projection
formula and the identification of cohomology after restriction of scalars. -/
private def resolutionComparisonIso (f : A →+* B) (i : ℤ) :
    tensorRight (baseSingle f) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i ≅
      derivedTargetHomology f i :=
  Functor.isoWhiskerRight (tensorFlipNatIso (baseSingle f)).symm
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i) ≪≫
    Functor.isoWhiskerRight (projectionFormulaIso f)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i) ≪≫
    Functor.associator (extendComplex f) (restrictComplex f)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i) ≪≫
    Functor.isoWhiskerLeft (extendComplex f) (restrictHomologyIso f i)

/-- The comparison from the resolution computation to the termwise base change, obtained by
tensoring with the augmentation of the resolution and the projection formula. -/
private def resolutionComparison (f : A →+* B) (i : ℤ) :
    resolutionHomology f i ⟶ derivedTargetHomology f i :=
  Functor.whiskerRight
      ((curriedTensor (CochainComplex (ModuleCat.{u} A) ℤ)).flip.map
        (X := baseResolution f) (ProjectiveResolution.of (baseModule f)).π')
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i) ≫
    (resolutionComparisonIso f i).hom

/-- Cohomology over `B` in degree `i`, viewed over `A`. -/
private abbrev homologyRestrict (f : A →+* B) (i : ℤ) :
    DerivedCategory (ModuleCat.{u} B) ⥤ ModuleCat.{u} A :=
  DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙ ModuleCat.restrictScalars f

/-- Tensoring with the K-flat resolution inverts quasi-isomorphisms. -/
private lemma resolutionHomology_inverts (f : A →+* B) (i : ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)).IsInvertedBy
      (resolutionHomology f i) := by
  intro X Y g hg
  have : QuasiIso g := hg
  have : QuasiIso ((tensorRight (baseResolution f)).map g) :=
    quasiIso_tensorRight_map (FaithfullyFlat.projResComplex_kFlat (baseModule f)) g
  exact (quasiIsoAt_iff_isIso_homologyMap ((tensorRight (baseResolution f)).map g) i).1
    inferInstance

/-- The resolution computation, read on the derived category. -/
private def resolutionDerived (f : A →+* B) (i : ℤ) :
    DerivedCategory (ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  Localization.lift (resolutionHomology f i) (resolutionHomology_inverts f i) DerivedCategory.Q

/-- The resolution computation factors through the derived category. -/
private def resolutionDerivedFac (f : A →+* B) (i : ℤ) :
    DerivedCategory.Q ⋙ resolutionDerived f i ≅ resolutionHomology f i :=
  Localization.fac (resolutionHomology f i) (resolutionHomology_inverts f i) DerivedCategory.Q

/-- The counit exhibiting the resolution computation as a candidate left derived functor of
termwise base change followed by cohomology. -/
private def resolutionCounit (f : A →+* B) (i : ℤ) :
    DerivedCategory.Q ⋙ resolutionDerived f i ⟶ derivedTargetHomology f i :=
  (resolutionDerivedFac f i).hom ≫ resolutionComparison f i

/-- On a K-flat complex the resolution comparison is invertible: the augmentation of the
resolution is a quasi-isomorphism, and tensoring with a K-flat complex preserves those. -/
private lemma isIso_resolutionComparison_app (f : A →+* B) (i : ℤ)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) :
    IsIso ((resolutionComparison f i).app K) := by
  have : QuasiIso ((tensorLeft K).map (ProjectiveResolution.of (baseModule f)).π') :=
    quasiIso_tensorLeft_map K hK (ProjectiveResolution.of (baseModule f)).π'
  have h1 : IsIso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
      (ComplexShape.up ℤ) i).map ((tensorLeft K).map
        (ProjectiveResolution.of (baseModule f)).π')) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  dsimp only [resolutionComparison]
  rw [NatTrans.comp_app]
  exact IsIso.comp_isIso' h1 inferInstance

/-- **Cohomology of derived base change is computed by a projective resolution.** For any
total left derived functor `T` of termwise extension of scalars, the `i`-th cohomology of
`T K`, viewed over `A`, is naturally the `i`-th cohomology of `K ⊗_A P`, where `P` is the
chosen projective resolution of `B` as an `A`-module.

Both sides are total left derived functors of `K ↦ H^i(B ⊗_A K)`: the left side by absoluteness
of derived extension of scalars under postcomposition, the right side because the comparison map
it carries is invertible on K-flat complexes, and K-flat complexes resolve every object. -/
private def derivedBaseChangeHomologyIsoAux (f : A →+* B)
    (T : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
    (hT : T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (i : ℤ) :
    DerivedCategory.Q ⋙ T ⋙ homologyRestrict f i ≅ resolutionHomology f i := by
  haveI := hT
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let H := homologyRestrict f i
  let β : DerivedCategory.Q ⋙ (T ⋙ H) ⟶ derivedTargetHomology f i :=
    (Functor.associator DerivedCategory.Q T H).inv ≫ Functor.whiskerRight α H
  haveI : (T ⋙ H).IsLeftDerivedFunctor β W :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, u}
      f T α H
  let θ := (T ⋙ H).leftDerivedLift β W (resolutionDerived f i) (resolutionCounit f i)
  have hflat (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) :
      IsIso (θ.app (DerivedCategory.Q.obj K)) := by
    have hfac := (T ⋙ H).leftDerived_fac_app β W (resolutionDerived f i)
      (resolutionCounit f i) K
    have hα : IsIso (α.app K) :=
      CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{u, u, u}
        f T α K hK
    have hβ : IsIso (β.app K) := by
      have h : IsIso (H.map (α.app K)) := inferInstance
      change IsIso ((Functor.associator DerivedCategory.Q T H).inv.app K ≫ H.map (α.app K))
      infer_instance
    have hc : IsIso ((resolutionCounit f i).app K) := by
      have h := isIso_resolutionComparison_app f i K hK
      change IsIso ((resolutionDerivedFac f i).hom.app K ≫ (resolutionComparison f i).app K)
      infer_instance
    exact (isIso_comp_right_iff (θ.app (DerivedCategory.Q.obj K)) (β.app K)).mp (hfac ▸ hc)
  have hall (X : DerivedCategory (ModuleCat.{u} A)) : IsIso (θ.app X) := by
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage X)
    have := hp
    have := hflat P hP
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    have hn := θ.naturality e.hom
    have hcomp : IsIso (θ.app (DerivedCategory.Q.obj P) ≫ (T ⋙ H).map e.hom) :=
      inferInstance
    rw [← hn] at hcomp
    exact (isIso_comp_left_iff _ _).mp hcomp
  exact Functor.isoWhiskerLeft DerivedCategory.Q
      (@asIso _ _ _ _ θ (NatIso.isIso_of_isIso_app θ)).symm ≪≫
    resolutionDerivedFac f i

/-- Cohomology of derived base change is computed naturally by a projective resolution
of the target ring, after restriction of scalars. -/
private noncomputable def derivedBaseChangeHomologyIso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (T : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (i : ℤ) :
    DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
        ModuleCat.restrictScalars f ≅
      CategoryTheory.MonoidalCategory.tensorRight
          (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex ((ModuleCat.restrictScalars f).obj
            (ModuleCat.of B B))) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i :=
  derivedBaseChangeHomologyIsoAux f T α (by assumption) i

end Core


/-- The summands contributing to a fixed degree of a tensor total complex. -/
private noncomputable abbrev tensorDegreeSummands
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      Discrete {p : ℤ × ℤ // p.1 + p.2 = i} ⥤ ModuleCat.{u} R :=
  (Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = i} =>
    HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) p.1.1 ⋙
      CategoryTheory.MonoidalCategory.tensorRight (P.X p.1.2))).flip

set_option backward.isDefEq.respectTransparency false in
/-- The degree of a tensor total complex is the coproduct of its tensor summands. -/
private noncomputable def tensorDegreeIso
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    CategoryTheory.MonoidalCategory.tensorRight P ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i ≅
      tensorDegreeSummands P i ⋙ colim :=
  NatIso.ofComponents (fun (K : CochainComplex (ModuleCat.{u} R) ℤ) => by
    let : HasColimit ((tensorDegreeSummands P i).obj K) := inferInstance
    change colimit (Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = i} =>
      ModuleCat.of R (TensorProduct R (K.X p.1.1) (P.X p.1.2)))) ≅
        colimit ((tensorDegreeSummands P i).obj K)
    exact HasColimit.isoOfNatIso (Discrete.natIso (fun p => Iso.refl _))) (by
    intro K L f
    apply colimit.hom_ext
    rintro ⟨p⟩
    dsimp only [id]
    change HomologicalComplex.ιMapBifunctor K P
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)
        p.1.1 p.1.2 i p.2 ≫
      (HomologicalComplex.mapBifunctorMap f (𝟙 P)
        (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℤ)).f i ≫ _ = _
    rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    simp only [HomologicalComplex.ιMapBifunctor, HomologicalComplex₂.ιTotal,
      GradedObject.ιMapObj, HasColimit.ι_isoOfNatIso_hom_assoc,
      HasColimit.ι_isoOfNatIso_hom]
    simp
    rfl)

/-- Tensor-total with a fixed complex preserves colimits. -/
private lemma tensorRightComplex_preservesColimitsOfShape
    {R : Type u} [CommRing R] {J : Type u} [SmallCategory J]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (CategoryTheory.MonoidalCategory.tensorRight P) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i
  have : PreservesColimitsOfShape J (tensorDegreeSummands P i) := by
    apply preservesColimitsOfShape_of_evaluation
    intro p
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) p.as.1.1 ⋙
        CategoryTheory.MonoidalCategory.tensorRight (P.X p.as.1.2))
    infer_instance
  have : PreservesColimitsOfShape J (tensorDegreeSummands P i ⋙ colim) := inferInstance
  exact preservesColimitsOfShape_of_natIso (tensorDegreeIso P i).symm

/-- Derived base change followed by cohomology preserves filtered colimits. -/
private lemma derivedBaseChangeHomology_preservesFilteredColimits
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (T : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    {J : Type u} [SmallCategory J] [IsFiltered J] (i : ℤ) :
    PreservesColimitsOfShape J
      (DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
        ModuleCat.restrictScalars f) := by
  let P := StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i
  have : PreservesColimitsOfShape J (CategoryTheory.MonoidalCategory.tensorRight P) :=
    tensorRightComplex_preservesColimitsOfShape P
  have : PreservesColimitsOfShape J H := homology_preservesFilteredColimits i
  have : PreservesColimitsOfShape J
      (CategoryTheory.MonoidalCategory.tensorRight P ⋙ H) := inferInstance
  have : PreservesColimitsOfShape J
      (DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
        ModuleCat.restrictScalars f) :=
    preservesColimitsOfShape_of_natIso (derivedBaseChangeHomologyIso f T α i).symm
  infer_instance

section RingEquivTransport

set_option backward.isDefEq.respectTransparency false

variable {R : Type t} {S : Type w} [CommRing R] [CommRing S] (e : R ≃+* S)

private lemma restrictScalarsComplex_isEquivalence :
    ((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).IsEquivalence :=
  ((ModuleCat.restrictScalars.{v} e.toRingHom).asEquivalence.mapHomologicalComplex
    (ComplexShape.up ℤ)).isEquivalence_functor

private lemma restrictScalarsLocalizer_isEquivalence :
    ((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
  restrictScalarsComplex_isEquivalence e

private lemma restrictScalarsLocalizer_isInduced :
    ((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsInduced where
  inverseImage_eq := by
    ext K L g
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology g
      (ModuleCat.restrictScalars.{v} e.toRingHom)

private lemma restrictScalarsLocalizer_isLocalizedEquivalence :
    ((ModuleCat.restrictScalars.{v} e.toRingHom).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsLocalizedEquivalence :=
  have := restrictScalarsLocalizer_isEquivalence.{v} e
  have := restrictScalarsLocalizer_isInduced.{v} e
  LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

private lemma restrictScalarsDerived_isEquivalence :
    (ModuleCat.restrictScalars.{v} e.toRingHom).mapDerivedCategory.IsEquivalence := by
  let G := ModuleCat.restrictScalars.{v} e.toRingHom
  have := restrictScalarsLocalizer_isEquivalence.{v} e
  have := restrictScalarsLocalizer_isLocalizedEquivalence.{v} e
  let : CatCommSq (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).isEquivalence
    DerivedCategory.Q DerivedCategory.Q _

end RingEquivTransport

section UliftTransport

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)

/-- Raising the universe of the target ring commutes with extension of scalars. -/
private noncomputable def extendScalarsUliftIso :
    ModuleCat.restrictScalars.{max u v w}
        (ULift.ringEquiv.symm.toRingHom : A →+* ULift.{max v w} A) ⋙
      ModuleCat.extendScalars.{u, v, max v (max u w)} f ⋙
      ModuleCat.restrictScalars.{max u v w}
        (ULift.ringEquiv.toRingHom : ULift.{max u w} B →+* B) ≅
    ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
      (f.ulift.{max v w, max u w}) := by
  let eA := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv.symm : A ≃+* ULift.{max v w} A) :
      ModuleCat.{max u v w} (ULift.{max v w} A) ≌ ModuleCat.{max u v w} A)
  let eB := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{max u w} B ≃+* B) :
      ModuleCat.{max u v w} B ≌ ModuleCat.{max u v w} (ULift.{max u w} B))
  have adj1 := (eA.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} f)).comp eB.toAdjunction
  have adj2 := ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w}
    (f.ulift.{max v w, max u w})
  let i : eB.inverse ⋙ ModuleCat.restrictScalars f ⋙ eA.inverse ≅
      ModuleCat.restrictScalars (f.ulift.{max v w, max u w}) :=
    NatIso.ofComponents (fun M => Iso.refl _) (fun _ => rfl)
  exact (Functor.associator _ _ _).symm ≪≫
    Adjunction.leftAdjointUniq (adj1.ofNatIsoRight i) adj2

/-- Transporting a left derived functor along the universe-raising ring equivalences: some
`T'` on the `ULift`ed rings is a left derived functor of extension of scalars along `f.ulift`
and its cohomology agrees with that of `T` after restricting scalars. -/
private theorem exists_isLeftDerivedFunctor_ulift
    (T : DerivedCategory (ModuleCat.{max u v w} A) ⥤ DerivedCategory (ModuleCat.{max u v w} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ))] (i : ℤ) :
    ∃ (T' : DerivedCategory (ModuleCat.{max u v w} (ULift.{max v w} A)) ⥤
        DerivedCategory (ModuleCat.{max u v w} (ULift.{max u w} B)))
      (α' : DerivedCategory.Q ⋙ T' ⟶
        (ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
          (f.ulift.{max v w, max u w})).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q),
      T'.IsLeftDerivedFunctor α'
        (HomologicalComplex.quasiIso (ModuleCat.{max u v w} (ULift.{max v w} A))
          (ComplexShape.up ℤ)) ∧
      Nonempty (DerivedCategory.Q ⋙ T' ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max u v w} (ULift.{max u w} B)) i ⋙
            ModuleCat.restrictScalars.{max u v w} (f.ulift.{max v w, max u w}) ≅
        (ModuleCat.restrictScalars.{max u v w}
            (ULift.ringEquiv.symm.toRingHom : A →+* ULift.{max v w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙ T ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i ⋙
          ModuleCat.restrictScalars.{max u v w}
            (ULift.ringEquiv.toRingHom : ULift.{max u w} B →+* B) ⋙
          ModuleCat.restrictScalars.{max u v w} (f.ulift.{max v w, max u w})) := by
  let eA : ULift.{max v w} A ≃+* A := ULift.ringEquiv
  let eB : ULift.{max u w} B ≃+* B := ULift.ringEquiv
  let uA := ModuleCat.restrictScalars.{max u v w} eA.symm.toRingHom
  let lB := ModuleCat.restrictScalars.{max u v w} eB.toRingHom
  have := restrictScalarsLocalizer_isEquivalence.{max u v w} eA.symm
  have := restrictScalarsLocalizer_isLocalizedEquivalence.{max u v w} eA.symm
  have := restrictScalarsDerived_isEquivalence.{max u v w} eB
  let E := (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let E' := (ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
    (f.ulift.{max v w, max u w})).mapHomologicalComplex (ComplexShape.up ℤ)
  let Φ := uA.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let T' := uA.mapDerivedCategory ⋙ T ⋙ lB.mapDerivedCategory
  let α₂ : DerivedCategory.Q ⋙ T ⋙ lB.mapDerivedCategory ⟶
      (E ⋙ DerivedCategory.Q) ⋙ lB.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α lB.mapDerivedCategory
  have : lB.mapDerivedCategory.IsRightAdjoint := inferInstance
  have h₂ : (T ⋙ lB.mapDerivedCategory).IsLeftDerivedFunctor α₂
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ)) :=
    inferInstance
  let e₁ : Φ.functor ⋙ (E ⋙ DerivedCategory.Q) ⋙ lB.mapDerivedCategory ≅
      E' ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft Φ.functor (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft E lB.mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
          Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
          NatIso.mapHomologicalComplex (extendScalarsUliftIso.{u, v, w} f) (ComplexShape.up ℤ))
        DerivedCategory.Q
  let α' : DerivedCategory.Q ⋙ T' ⟶ E' ⋙ DerivedCategory.Q :=
    DerivedCategory.Q.whiskerLeft (Iso.refl T').inv ≫
      (DerivedCategory.Q.associator uA.mapDerivedCategory (T ⋙ lB.mapDerivedCategory)).inv ≫
      Functor.whiskerRight uA.mapDerivedCategoryFactors.symm.inv (T ⋙ lB.mapDerivedCategory) ≫
      (Φ.functor.associator DerivedCategory.Q (T ⋙ lB.mapDerivedCategory)).hom ≫
      Φ.functor.whiskerLeft α₂ ≫ e₁.hom
  have hα' : T'.IsLeftDerivedFunctor α'
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} (ULift.{max v w} A))
        (ComplexShape.up ℤ)) :=
    (LocalizerMorphism.isLeftDerivedFunctor_iff_precomp Φ DerivedCategory.Q DerivedCategory.Q
      uA.mapDerivedCategory uA.mapDerivedCategoryFactors.symm α' α₂ e₁ (Iso.refl T') rfl).1 h₂
  let U := ModuleCat.restrictScalars.{max u v w} (f.ulift.{max v w, max u w})
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
  let H' := DerivedCategory.homologyFunctor (ModuleCat.{max u v w} (ULift.{max u w} B)) i
  let G := DerivedCategory.Q ⋙ T ⋙ H
  let e₀ : (DerivedCategory.Q ⋙ uA.mapDerivedCategory ⋙ T) ⋙ lB.mapDerivedCategory ⋙ H' ⋙ U ≅
      (DerivedCategory.Q ⋙ uA.mapDerivedCategory ⋙ T) ⋙ H ⋙ lB ⋙ U :=
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso lB i) U)
  let e₁' : ((uA.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ T) ⋙
        H ⋙ lB ⋙ U ≅
      (DerivedCategory.Q ⋙ uA.mapDerivedCategory ⋙ T) ⋙ H ⋙ lB ⋙ U :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight uA.mapDerivedCategoryFactors.symm T) _
  let e : DerivedCategory.Q ⋙ T' ⋙ H' ⋙ U ≅
      uA.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G ⋙ lB ⋙ U :=
    e₀ ≪≫ e₁'.symm
  exact ⟨T', α', hα', ⟨e⟩⟩

/-- Derived base change followed by cohomology preserves filtered colimits, for rings in
independent universes and modules in a common larger universe. -/
public lemma derivedBaseChangeHomology_preservesFilteredColimits_ulift
    (T : DerivedCategory (ModuleCat.{max u v w} A) ⥤ DerivedCategory (ModuleCat.{max u v w} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ))]
    {J : Type (max u v w)} [SmallCategory J] [IsFiltered J] (i : ℤ) :
    PreservesColimitsOfShape J
      (DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i) := by
  obtain ⟨T', α', hα', ⟨e⟩⟩ := exists_isLeftDerivedFunctor_ulift f T α i
  have hT' := derivedBaseChangeHomology_preservesFilteredColimits
    (f.ulift.{max v w, max u w}) T' α' (J := J) i
  let uA := ModuleCat.restrictScalars.{max u v w}
    (ULift.ringEquiv.symm : A ≃+* ULift.{max v w} A).toRingHom
  let lB := ModuleCat.restrictScalars.{max u v w}
    (ULift.ringEquiv : ULift.{max u w} B ≃+* B).toRingHom
  let U := ModuleCat.restrictScalars.{max u v w} (f.ulift.{max v w, max u w})
  let G := DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
  have := restrictScalarsComplex_isEquivalence.{max u v w}
    (ULift.ringEquiv.symm : A ≃+* ULift.{max v w} A)
  have h₁ : PreservesColimitsOfShape J
      (uA.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G ⋙ lB ⋙ U) :=
    preservesColimitsOfShape_of_natIso e
  let eq := (uA.mapHomologicalComplex (ComplexShape.up ℤ)).asEquivalence
  have : PreservesColimitsOfShape J eq.inverse := inferInstance
  have : PreservesColimitsOfShape J (eq.inverse ⋙ eq.functor ⋙ G ⋙ lB ⋙ U) := by
    change PreservesColimitsOfShape J
      (eq.inverse ⋙ uA.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G ⋙ lB ⋙ U)
    infer_instance
  have h₂ : PreservesColimitsOfShape J (G ⋙ lB ⋙ U) :=
    preservesColimitsOfShape_of_natIso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eq.counitIso (G ⋙ lB ⋙ U) ≪≫ Functor.leftUnitor _)
  have : PreservesColimitsOfShape J lB := ⟨fun {_} => inferInstance⟩
  have : PreservesColimitsOfShape J U := ⟨fun {_} => inferInstance⟩
  have : PreservesColimitsOfShape J (lB ⋙ U) := inferInstance
  have : (lB ⋙ U).ReflectsIsomorphisms := inferInstance
  have : ReflectsColimitsOfShape J (lB ⋙ U) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves G (lB ⋙ U)

end UliftTransport

/-- The chain complex of the functorial free resolution. -/
private noncomputable abbrev freeResolutionComplex {R : Type u} [Ring R] (M : ModuleCat.{u} R) :=
  ((isProjective (ModuleCat.{u} R)).ι.mapHomologicalComplex _).obj
    ((ModuleCat.projectiveResolution R).chainComplex M)

set_option backward.isDefEq.respectTransparency false in
/-- The functorial free resolution, with its augmentation as a projective resolution. -/
private noncomputable def freeProjectiveResolution {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    ProjectiveResolution M := by
  let Λ := ModuleCat.projectiveResolution R
  let ι := (isProjective (ModuleCat.{u} R)).ι
  let e₀ := ι.mapIso (Λ.chainComplexXZeroIso M)
  let e₁ := ι.mapIso (Λ.chainComplexXOneIso M)
  let a := e₀.hom ≫ Λ.π.app M
  have ha : (freeResolutionComplex M).d 1 0 ≫ a = 0 := by
    change ι.map ((Λ.chainComplex M).d 1 0) ≫ a = 0
    rw [Abelian.LeftResolution.map_chainComplex_d_1_0]
    change (e₁.hom ≫ Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι _ ≫ e₀.inv) ≫
      (e₀.hom ≫ Λ.π.app M) = 0
    simp only [Category.assoc, Iso.inv_hom_id_assoc, kernel.condition, comp_zero]
  let S := ShortComplex.mk (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι _) (Λ.π.app M)
    (by simp)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    change Epi (kernel.lift _ (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι _) _)
    have h : kernel.lift (Λ.π.app M) (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι _) (by simp) =
        Λ.π.app (kernel (Λ.π.app M)) := by
      apply (cancel_mono (kernel.ι (Λ.π.app M))).1
      simp
    rw [h]
    infer_instance
  have he : (ShortComplex.mk _ _ ha).Exact := by
    apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk e₁ e₀ (Iso.refl M) ?_ ?_)).mpr hS
    · change ι.map (Λ.chainComplexXOneIso M).hom ≫
        (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι _) =
        ι.map ((Λ.chainComplex M).d 1 0) ≫ ι.map (Λ.chainComplexXZeroIso M).hom
      rw [Abelian.LeftResolution.map_chainComplex_d_1_0]
      simp
    · simp [a, S]
  refine { complex := freeResolutionComplex M
           projective := fun n => ((Λ.chainComplex M).X n).property
           π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨a, ha⟩
           quasiIso := ⟨fun n => ?_⟩ }
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨he, ?_⟩
      change Epi a
      dsimp [a]
      infer_instance
    · exact (freeResolutionComplex M).shape _ _ (by decide)
    · rfl
    · rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact Λ.exactAt_map_chainComplex_succ M n
    · exact ChainComplex.exactAt_succ_single_obj _ _

set_option backward.isDefEq.respectTransparency false in
/-- The terms of the functorial free resolution satisfy the natural infinite cardinal bound. -/
private lemma mk_freeResolutionComplex_term_le
    {R : Type u} [Ring R] (M : ModuleCat.{u} R)
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ) (hM : #M ≤ κ) (n : ℕ) :
    #((freeResolutionComplex M).X n) ≤ κ := by
  let Λ := ModuleCat.projectiveResolution R
  let ι := (isProjective (ModuleCat.{u} R)).ι
  have hfree (N : ModuleCat.{u} R) (hN : #N ≤ κ) : #(ι.obj (Λ.F.obj N)) ≤ κ := by
    change #(N →₀ R) ≤ κ
    exact mk_finsupp_le_of_le hκ (by simpa using hN) (by simpa using hR)
  have hker {N P : ModuleCat.{u} R} (g : N ⟶ P) : #(kernel g : ModuleCat.{u} R) ≤ #N :=
    mk_le_of_injective ((ModuleCat.mono_iff_injective (kernel.ι g)).mp inferInstance)
  change #(ι.obj ((Λ.chainComplex M).X n)) ≤ κ
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [mk_congr (ι.mapIso (Λ.chainComplexXZeroIso M)).toLinearEquiv.toEquiv]
    exact hfree M hM
  | one =>
    rw [mk_congr (ι.mapIso (Λ.chainComplexXOneIso M)).toLinearEquiv.toEquiv]
    exact hfree _ ((hker _).trans (hfree M hM))
  | more n _ hn =>
    rw [mk_congr (ι.mapIso (Λ.chainComplexXIso M n)).toLinearEquiv.toEquiv]
    exact hfree _ ((hker _).trans hn)

/-- Extending a bounded-size complex by zero preserves an infinite cardinal bound. -/
private lemma mk_extend_term_le
    {R : Type u} [Ring R] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (e : c.Embedding c')
    {κ : Cardinal.{v}} (hκ : ℵ₀ ≤ κ) (hK : ∀ i, #(K.X i) ≤ κ) (i' : ι') :
    #((K.extend e).X i') ≤ κ := by
  classical
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    rw [mk_congr (K.extendXIso e hi).toLinearEquiv.toEquiv]
    exact hK i
  · have := ModuleCat.subsingleton_of_isZero (K.isZero_extend_X e i' (by simpa using hi))
    rw [mk_eq_one]
    exact one_le_aleph0.trans hκ

section ResolutionComparison

open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendHomotopyEquiv
    {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {P Q : HomologicalComplex C c} (h : HomotopyEquiv P Q)
    (e : c.Embedding c') [e.IsRelIff] :
    HomotopyEquiv ((e.extendFunctor C).obj P) ((e.extendFunctor C).obj Q) where
  hom := (e.extendFunctor C).map h.hom
  inv := (e.extendFunctor C).map h.inv
  homotopyHomInvId := by
    rw [← (e.extendFunctor C).map_comp, ← (e.extendFunctor C).map_id]
    exact h.homotopyHomInvId.extend e
  homotopyInvHomId := by
    rw [← (e.extendFunctor C).map_comp, ← (e.extendFunctor C).map_id]
    exact h.homotopyInvHomId.extend e

/-- Tensoring with a projective resolution has the expected infinite cardinal bound on homology. -/
private lemma mk_tensor_projectiveResolution_homology_le
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hR : #R ≤ κ)
    (hM : #M ≤ κ) (hK : ∀ j, #(K.X j) ≤ κ) (i : ℤ) :
    #(((CategoryTheory.MonoidalCategory.tensorRight
      (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).obj K).homology i) ≤ κ := by
  let P := (freeProjectiveResolution M).complex.extend ComplexShape.embeddingDownNat
  let e : HomotopyEquiv ((CategoryTheory.MonoidalCategory.tensorLeft K).obj
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).obj
        (ProjectiveResolution.of M).complex))
      ((CategoryTheory.MonoidalCategory.tensorLeft K).obj P) :=
    TotalTensorComplex.tensorHomotopyEquiv (HomotopyEquiv.refl K)
      (extendHomotopyEquiv
        ((ProjectiveResolution.of M).homotopyEquiv (freeProjectiveResolution M))
        ComplexShape.embeddingDownNat)
  change #(((CategoryTheory.MonoidalCategory.tensorLeft K).obj
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).obj
      (ProjectiveResolution.of M).complex)).homology i) ≤ κ
  rw [mk_congr (e.toHomologyIso i).toLinearEquiv.toEquiv]
  apply (mk_homology_le_mk_term _ i).trans
  apply mk_tensorRight_term_le K P hκ hK
  exact mk_extend_term_le _ _ hκ (mk_freeResolutionComplex_term_le M hκ hR hM)

end ResolutionComparison

/-- Derived extension of scalars preserves an infinite cardinal bound on homology. -/
private lemma mk_derivedBaseChange_homology_le
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (T : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (hB : #B ≤ κ)
    (hK : ∀ j, #(K.X j) ≤ κ) (i : ℤ) :
    #((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      (T.obj (DerivedCategory.Q.obj K))) ≤ κ := by
  change #((DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) i ⋙
    ModuleCat.restrictScalars f).obj K) ≤ κ
  rw [mk_congr ((derivedBaseChangeHomologyIso f T α i).app K).toLinearEquiv.toEquiv]
  exact mk_tensor_projectiveResolution_homology_le K
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) hκ hA hB hK i

set_option backward.isDefEq.respectTransparency false in
/-- The uniform homology bound allows independent ring and module universes. -/
lemma mk_derivedBaseChange_homology_le_ulift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (T : DerivedCategory (ModuleCat.{max u v w} A) ⥤ DerivedCategory (ModuleCat.{max u v w} B))
    (α : DerivedCategory.Q ⋙ T ⟶
      (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [T.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max u v w} A) ℤ) {κ : Cardinal.{max u v w}}
    (hκ : ℵ₀ ≤ κ) (hA : lift.{max v w} #A ≤ κ) (hB : lift.{max u w} #B ≤ κ)
    (hK : ∀ j, #(K.X j) ≤ κ) (i : ℤ) :
    #((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
      (T.obj (DerivedCategory.Q.obj K))) ≤ κ := by
  have := extendScalars_additive.{u, v, max v (max u w)} f
  obtain ⟨T', α', hα', ⟨e⟩⟩ := exists_isLeftDerivedFunctor_ulift f T α i
  let uA := ModuleCat.restrictScalars.{max u v w}
    (ULift.ringEquiv.symm : A ≃+* ULift.{max v w} A).toRingHom
  let lB := ModuleCat.restrictScalars.{max u v w}
    (ULift.ringEquiv : ULift.{max u w} B ≃+* B).toRingHom
  let U := ModuleCat.restrictScalars.{max u v w} (f.ulift.{max v w, max u w})
  let G := DerivedCategory.Q ⋙ T ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i
  have := restrictScalarsComplex_isEquivalence.{max u v w}
    (ULift.ringEquiv.symm : A ≃+* ULift.{max v w} A)
  let F := uA.mapHomologicalComplex (ComplexShape.up ℤ)
  let K' := F.objPreimage K
  let eK := F.objObjPreimageIso K
  have hK' (j : ℤ) : #(K'.X j) ≤ κ := by
    change #((F.obj K').X j) ≤ κ
    exact (mk_congr ((HomologicalComplex.eval _ _ j).mapIso eK).toLinearEquiv.toEquiv).le.trans
      (hK j)
  have hT' := mk_derivedBaseChange_homology_le (f.ulift.{max v w, max u w}) T' α'
    K' hκ (by simpa only [mk_uLift] using hA) (by simpa only [mk_uLift] using hB) hK' i
  let eH := e.app K' ≪≫ (G ⋙ lB ⋙ U).mapIso eK
  change #((G ⋙ lB ⋙ U).obj K) ≤ κ
  rw [← mk_congr eH.toLinearEquiv.toEquiv]
  exact hT'

end Stacks.SubcomplexEnlargement

end
