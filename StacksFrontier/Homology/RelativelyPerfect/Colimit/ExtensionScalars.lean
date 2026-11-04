module

public import Mathlib
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.Homology.HomComplex.CochainScalarTower
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Relative.PolynomialRetract
public import StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import StacksFrontier.Homology.RelativelyPerfect.Representative
public import StacksFrontier.Homology.RelativelyPerfect.Triangulated
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Homology.TorAmplitude.Defs
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.Homology.TorAmplitude.Triangle
public import StacksFrontier.RingTheory.Module.DirectLimit.FinitePresentation
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

/-!
# Stage algebras and derived extension of scalars

The stage algebras `Rᵢ ⊗[R₀] A₀` and their structure maps, the K-flat comparison for derived
tensor products, the composition and unit comparisons for derived extension of scalars and their
coherence, derived base change of morphism groups, and the cocone of stage algebras under
`A₀`.

This is part 1 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

/-- The algebra at stage `i`, obtained from `A₀` by base change along `R₀ → Rᵢ`. -/
public abbrev stageAlgebra {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] (i : I) :=
  F.obj i ⊗[R₀] A₀

/-- The canonical map `Rᵢ ⊗[R₀] A₀ → Rⱼ ⊗[R₀] A₀` attached to a map of stages. -/
public def stageMap {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    {i j : I} (f : i ⟶ j) : stageAlgebra F A₀ i →+* stageAlgebra F A₀ j :=
  (Algebra.TensorProduct.map (F.map f).hom (AlgHom.id R₀ A₀)).toRingHom

/-- The canonical map from `A₀` to its base change at stage `i`. -/
public def baseToStageMap {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] (i : I) :
    A₀ →+* stageAlgebra F A₀ i :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The canonical map from a base-changed algebra at a stage to the base change at the
colimit. -/
public def stageToLimitMap {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] (i : I) :
    stageAlgebra F A₀ i →+* c.pt ⊗[R₀] A₀ :=
  (Algebra.TensorProduct.map (c.ι.app i).hom (AlgHom.id R₀ A₀)).toRingHom

/-- The canonical map from `A₀` to its base change to the colimit ring. -/
public def baseToLimitMap {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] :
    A₀ →+* c.pt ⊗[R₀] A₀ :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- The canonical scalar-tower isomorphism for termwise extension of scalars, followed by the
localization functor to the derived category. -/
public def extensionOfScalarsComplexComp
    {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    extensionOfScalarsComplex.{uR, uR, uM} (g.comp f) ≅
      (ModuleCat.extendScalars.{uR, uR, max uM uR} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplex.{uR, uR, uM} g :=
  Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{uR, uM} f g) (ComplexShape.up ℤ))
    DerivedCategory.Q

/-- Derived extension of scalars is invariant under equality of its ring homomorphism. -/
public def derivedExtensionScalarsCongr
    {A B : Type uR} [CommRing A] [CommRing B] {f g : A →+* B} (h : f = g) :
    (totalDerivedExtensionScalars.{uR, uR, uM} f).functor ≅
      (totalDerivedExtensionScalars.{uR, uR, uM} g).functor :=
  eqToIso (congrArg (fun q ↦ (totalDerivedExtensionScalars.{uR, uR, uM} q).functor) h)


/-- Stacks 0DHV in the shape used below: relative perfectness of an object of `D(A)` is
equivalent to being represented by a bounded complex of `A`-modules that are flat over `R` and
finitely presented over `A`. This repackages
`isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation` for a bundled derived tensor
product. -/
private theorem isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation_bundled.{u, v, w}
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (D : KFlatDerivedTensoringDatum.{u, max v w} R)
    (K : DerivedCategory (ModuleCat.{max u v w} A)) :
    IsRelativelyPerfect D.tensor D.comparison D.isLeftDerived K ↔
      ∃ P : CochainComplex (ModuleCat.{max u v w} A) ℤ,
        (∃ a : ℤ, P.IsStrictlyGE a) ∧
        (∃ b : ℤ, P.IsStrictlyLE b) ∧
        (∀ i : ℤ,
          Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i)) ∧
            Module.FinitePresentation A (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  rw [isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, v, w}
    D.tensor D.comparison D.isLeftDerived K]
  constructor
  · rintro ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨e⟩⟩
    exact ⟨P, ⟨a, hGE⟩, ⟨b, hLE⟩, fun i ↦ ⟨hflat i, hfp i⟩, ⟨e.symm⟩⟩
  · rintro ⟨P, ⟨a, hGE⟩, ⟨b, hLE⟩, h, ⟨e⟩⟩
    exact ⟨P, a, b, hGE, hLE, fun i ↦ (h i).1, fun i ↦ (h i).2, ⟨e.symm⟩⟩


/-- Termwise extension along the identity ring homomorphism is the identity. -/
private def extensionScalarsComplexId.{u, v} (R : Type u) [CommRing R] :
    extensionOfScalarsComplexGeneral.{u, v, u} (RingHom.id R) ≅
      DerivedCategory.Q (C := ModuleCat.{max u v} R) := by
  let e := NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsId.{u, max u v} R) (ComplexShape.up ℤ)
  exact Functor.isoWhiskerRight e DerivedCategory.Q
set_option backward.isDefEq.respectTransparency false in
/-- The unit comparison for derived extension of scalars, obtained by uniqueness. -/
private def derivedExtensionScalarsId.{u, v} (R : Type u) [CommRing R] :
    𝟭 (DerivedCategory (ModuleCat.{max u v} R)) ≅
      (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).functor := by
  let D := totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)
  let e : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{max u v} R)) ≅
      extensionOfScalarsComplexGeneral.{u, v, u} (RingHom.id R) :=
    (Functor.rightUnitor _ ) ≪≫ (extensionScalarsComplexId.{u, v} R).symm
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ)) _ e
  change 𝟭 _ ≅ D.functor
  letI : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ)) := D.isLeftDerived
  exact Functor.leftDerivedUnique D.functor (𝟭 _) e.hom D.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ))


/-- The specializations of two derived tensor products to a module are isomorphic. -/
private def tensorWithModuleIso.{u, v} {R : Type u} [CommRing R]
    (D D' : DerivedTensoringDatum.{u, v} R) (M : ModuleCat.{v} R) :
    D.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ≅
      D'.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) := by
  have := D.isLeftDerived M
  have := D'.isLeftDerived M
  exact Functor.leftDerivedUnique _ _ (D.comparison M) (D'.comparison M)
    (HomologicalComplex.quasiIso (ModuleCat.{v} R) (.up ℤ))
/-- Tor amplitude is independent of the choice of derived tensor product. -/
private theorem hasTorAmplitude_iff_of_derivedTensorProduct.{u, v} {R : Type u} [CommRing R]
    (D D' : DerivedTensoringDatum.{u, v} R)
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) :
    HasTorAmplitude D.tensor D.comparison D.isLeftDerived K a b ↔
      HasTorAmplitude D'.tensor D'.comparison D'.isLeftDerived K a b := by
  have key (D D' : DerivedTensoringDatum.{u, v} R)
      (h : HasTorAmplitude D.tensor D.comparison D.isLeftDerived K a b) :
      HasTorAmplitude D'.tensor D'.comparison D'.isLeftDerived K a b := fun M i hi ↦
    (h M i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso
      ((tensorWithModuleIso D' D M).app K))
  exact ⟨key D D', key D' D⟩
/-- Relative perfection is independent of the choice of derived tensor product. -/
private theorem isRelativelyPerfect_iff_of_derivedTensorProduct.{u, v, w} {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (D D' : DerivedTensoringDatum.{u, max u v w} R)
    (K : DerivedCategory (ModuleCat.{max u v w} A)) :
    IsRelativelyPerfect D.tensor D.comparison D.isLeftDerived K ↔
      IsRelativelyPerfect D'.tensor D'.comparison D'.isLeftDerived K := by
  show _ ∧ (∃ a b, _) ↔ _ ∧ (∃ a b, _)
  exact and_congr_right fun _ ↦ exists_congr fun a ↦ exists_congr fun b ↦
    hasTorAmplitude_iff_of_derivedTensorProduct D D' _ a b

section KFlatComparison

universe u v

open MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive


private def tensorLeftIsoTensorModuleRight {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R) :
    tensorLeft N ≅ tensorModuleRight N :=
  NatIso.ofComponents (fun M => (TensorProduct.comm R N M).toModuleIso) (by
    intro X Y f
    ext : 1
    apply TensorProduct.ext'
    intro x y
    rfl)

private lemma quasiIso_tensorModuleRight_map {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    {C D : CochainComplex (ModuleCat.{max u v} R) ℤ} (s : C ⟶ D) [QuasiIso s]
    (hC : C.KFlat) (hD : D.KFlat) :
    QuasiIso (((tensorModuleRight N).mapHomologicalComplex (.up ℤ)).map s) := by
  have ht := CochainComplex.DerivedTensor.quasiIso_tleftCochain_map s hC hD
    ((CochainComplex.singleFunctor _ 0).obj N)
  let e' : TleftCochain ((CochainComplex.singleFunctor _ 0).obj N) ≅
      (tensorModuleRight N).mapHomologicalComplex (.up ℤ) :=
    (CochainComplex.DerivedTensor.KFlatDerived.tensorLeftMapComplexIso.{v, u} N).symm ≪≫
      NatIso.mapHomologicalComplex (tensorLeftIsoTensorModuleRight.{u, v} N) (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e'.app C) (e'.app D) (e'.hom.naturality s).symm)).1 ht

/-- The comparison of a total left derived functor of termwise tensoring by a module is
invertible on K-flat complexes. -/
private theorem isIso_derivedComparison_app_of_kFlat {R : Type u} [CommRing R]
    (N : ModuleCat.{max u v} R)
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (α : DerivedCategory.Q ⋙ L ⟶ tensorRightComplexToDerived N)
    [L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (hP : P.KFlat) :
    IsIso (α.app P) := by
  let T := tensorModuleRight N
  let Uh := T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : HomotopyCategory.quotient _ _ ⋙ Uh ≅
      tensorRightComplexToDerived N :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (T.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso _)
  refine CochainComplex.DerivedTensor.KFlatDerived.isIso_app_of_kFlat.{v, u} _ Uh e ?_ _ α P hP
  intro X Y s hs hX hY
  have : QuasiIso s.out := (HomotopyCategory.quotient_map_mem_quasiIso_iff s.out).1 (by
    rw [HomotopyCategory.quotient_map_out s]
    exact hs)
  have := quasiIso_tensorModuleRight_map.{u, v} N s.out hX hY
  have : IsIso ((tensorRightComplexToDerived N).map s.out) := by
    dsimp
    infer_instance
  have : IsIso ((HomotopyCategory.quotient _ _ ⋙ Uh).map s.out) := by
    rw [← NatIso.naturality_2 e s.out]
    dsimp
    infer_instance
  simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using this

/-- Every derived tensor product satisfies the K-flat computation rule. -/
private def toKFlatDerivedTensorProduct {R : Type u} [CommRing R]
    (D : DerivedTensoringDatum.{u, max u v} R) :
    KFlatDerivedTensoringDatum.{u, v} R where
  __ := D
  comparison_isIso_of_kFlat N P hP := by
    let := D.isLeftDerived N
    exact isIso_derivedComparison_app_of_kFlat.{u, v} N _ (D.comparison N) P hP

end KFlatComparison

/-- Derived extension of scalars is computed termwise on a bounded above complex of flat
modules, since such a complex is K-flat (Stacks 064K). -/
private theorem isIso_comparison_app_of_isStrictlyLE_flat.{u, v, w}
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] {f : R →+* A}
    (D : TotalDerivedExtensionScalars.{u, v, w} f)
    (P : CochainComplex (ModuleCat.{max v u w} R) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Module.Flat R (P.X n)] :
    IsIso (D.comparison.app P) :=
  D.comparison_isIso_of_kFlat P (CochainComplex.KFlat.kFlat_of_flat.{u, max v w} P d)

section DerivedComposition

universe u v

/-- The comparison from the composite of two total derived extensions of scalars to termwise
extension of scalars along the composed ring map, assembled from the two comparisons and the
scalar-tower isomorphism. -/
public def derivedExtensionScalarsCompComparison {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor) ⟶
      extensionOfScalarsComplexGeneral.{u, v, u} (g.comp f) :=
  Functor.whiskerRight (totalDerivedExtensionScalars.{u, u, v} f).comparison
      (totalDerivedExtensionScalars.{u, u, v} g).functor ≫
    Functor.whiskerLeft ((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (totalDerivedExtensionScalars.{u, u, v} g).comparison ≫
    (extensionOfScalarsComplexComp.{u, v} f g).inv

/-- The natural transformation from the composite of two total derived extensions of scalars to
the total derived extension of scalars along the composed ring map, obtained from the universal
property of the latter applied to `derivedExtensionScalarsCompComparison`. -/
public def derivedExtensionScalarsCompHom {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor :=
  (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.leftDerivedLift
    (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _
    (derivedExtensionScalarsCompComparison.{u, v} f g)

/-- `derivedExtensionScalarsCompHom` factors the comparison of
`derivedExtensionScalarsCompComparison` through the comparison of the total derived extension of
scalars along the composed ring map. -/
public theorem derivedExtensionScalarsCompHom_fac {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (derivedExtensionScalarsCompHom.{u, v} f g).app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P =
      (derivedExtensionScalarsCompComparison.{u, v} f g).app P :=
  (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.leftDerived_fac_app
    (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _
    (derivedExtensionScalarsCompComparison.{u, v} f g) P

/-- Every component of `derivedExtensionScalarsCompHom` is invertible: on a K-flat complex all
three comparisons involved are invertible, and every object of the derived category has a K-flat
representative. -/
public theorem isIso_derivedExtensionScalarsCompHom_app {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((derivedExtensionScalarsCompHom.{u, v} f g).app X) := by
  let Df := totalDerivedExtensionScalars.{u, u, v} f
  let Dg := totalDerivedExtensionScalars.{u, u, v} g
  let D := totalDerivedExtensionScalars.{u, u, v} (g.comp f)
  have hα (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : P.KFlat) :
      IsIso ((derivedExtensionScalarsCompHom.{u, v} f g).app (DerivedCategory.Q.obj P)) := by
    have hD := D.comparison_isIso_of_kFlat P hP
    have hfP := Df.comparison_isIso_of_kFlat P hP
    have hgP := Dg.comparison_isIso_of_kFlat
      (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, v} f P hP)
    have hcomp : IsIso ((derivedExtensionScalarsCompComparison.{u, v} f g).app P) := by
      show IsIso (Dg.functor.map (Df.comparison.app P) ≫ Dg.comparison.app _ ≫
        (extensionOfScalarsComplexComp.{u, v} f g).inv.app P)
      have h₁ : IsIso (Dg.functor.map (Df.comparison.app P)) := inferInstance
      have h₂ : IsIso ((extensionOfScalarsComplexComp.{u, v} f g).inv.app P) := inferInstance
      exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' hgP h₂)
    rw [← derivedExtensionScalarsCompHom_fac] at hcomp
    exact IsIso.of_isIso_comp_right _ (D.comparison.app P)
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, v} (DerivedCategory.Q.objPreimage X)
  have := hα P hP
  let e : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  have hn := (derivedExtensionScalarsCompHom.{u, v} f g).naturality e.hom
  have hIso : IsIso ((derivedExtensionScalarsCompHom.{u, v} f g).app
      (DerivedCategory.Q.obj P) ≫ D.functor.map e.hom) := inferInstance
  rw [← hn] at hIso
  exact (isIso_comp_left_iff _ _).mp hIso

/-- The comparison-compatible composition isomorphism for derived extension of scalars. -/
private theorem exists_derivedExtensionScalarsComp :
    let E := fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      totalDerivedExtensionScalars.{u, u, v} f
    ∃ (comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
          (f : A →+* B) (g : B →+* C),
          (E f).functor ⋙ (E g).functor ≅ (E (g.comp f)).functor),
      ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
          (f : A →+* B) (g : B →+* C)
          (Q : CochainComplex (ModuleCat.{max u v} A) ℤ),
        (E g).functor.map ((E f).comparison.app Q) ≫
            (E g).comparison.app
              (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Q) ≫
            (extensionOfScalarsComplexComp.{u, v} f g).inv.app Q =
          (comp f g).hom.app (DerivedCategory.Q.obj Q) ≫
            (E (g.comp f)).comparison.app Q := by
  intro E
  refine ⟨fun f g ↦ @asIso _ _ _ _ (derivedExtensionScalarsCompHom.{u, v} f g)
    (by
      have := fun X ↦ isIso_derivedExtensionScalarsCompHom_app.{u, v} f g X
      exact NatIso.isIso_of_isIso_app _), ?_⟩
  intro A B C _ _ _ f g Q
  exact (derivedExtensionScalarsCompHom_fac.{u, v} f g Q).symm

end DerivedComposition

set_option backward.isDefEq.respectTransparency false in
/-- The derived unit comparison agrees with the ordinary unit on complexes. -/
private theorem derivedExtensionScalarsId_comparison.{u, v} (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (derivedExtensionScalarsId.{u, v} R).hom.app (DerivedCategory.Q.obj P) ≫
      (totalDerivedExtensionScalars.{u, u, v} (RingHom.id R)).comparison.app P =
        (extensionScalarsComplexId.{u, v} R).inv.app P := by
  simp [derivedExtensionScalarsId, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans]

section ScalarExtensionCoherence

universe u v

set_option backward.isDefEq.respectTransparency false in
/-- Associativity for inverse scalar-extension comparisons. -/
private lemma extendScalarsComp_inv_app
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (M : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalars.{u, u, max u v} h).map
        ((ModuleCat.extendScalarsComp.{u, max u v} f g).inv.app M) ≫
      (ModuleCat.extendScalarsComp.{u, max u v} (g.comp f) h).inv.app M =
    (ModuleCat.extendScalarsComp.{u, max u v} g h).inv.app
        ((ModuleCat.extendScalars.{u, u, max u v} f).obj M) ≫
      (ModuleCat.extendScalarsComp.{u, max u v} f (h.comp g)).inv.app M := by
  let e₁ := ModuleCat.extendScalarsComp.{u, max u v} (g.comp f) h ≪≫
    Functor.isoWhiskerRight (ModuleCat.extendScalarsComp.{u, max u v} f g)
      (ModuleCat.extendScalars.{u, u, max u v} h)
  let e₂ := ModuleCat.extendScalarsComp.{u, max u v} f (h.comp g) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, max u v} f)
      (ModuleCat.extendScalarsComp.{u, max u v} g h) ≪≫
    (Functor.associator _ _ _).symm
  have he : e₁ = e₂ := Iso.ext (ModuleCat.extendScalars_assoc.{u, max u v} f g h)
  simpa [e₁, e₂] using congrArg (fun e ↦ e.inv.app M) he

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extension composition comparison at an identity map is the unit. -/
private lemma extendScalarsComp_id_hom_app {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (M : ModuleCat.{max u v} A) :
    (ModuleCat.extendScalarsComp.{u, max u v} f (RingHom.id B)).hom.app M =
      (ModuleCat.extendScalarsId.{u, max u v} B).inv.app ((ModuleCat.extendScalars.{u, u, max u v}
        f).obj M) := by
  ext m
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The right unit law for extension of scalars on complexes. -/
private lemma extensionScalarsComplexComp_id {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (P : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (extensionScalarsComplexId.{u, v} B).inv.app
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (extensionOfScalarsComplexComp.{u, v} f (RingHom.id B)).inv.app P = 𝟙 _ := by
  have he : (extensionScalarsComplexId.{u, v} B).inv.app
        (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P) =
      (extensionOfScalarsComplexComp.{u, v} f (RingHom.id B)).hom.app P := by
    show DerivedCategory.Q.map _ = DerivedCategory.Q.map _
    congr 1
    ext i : 1
    exact (extendScalarsComp_id_hom_app.{u, v} f (P.X i)).symm
  rw [he]
  simp
  rfl

section Coherence
variable
    (comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor)
    (hcomp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ),
      (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P =
        (totalDerivedExtensionScalars.{u, u, v} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P) ≫
          (totalDerivedExtensionScalars.{u, u, v} g).comparison.app
            (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (extensionOfScalarsComplexComp.{u, v} f g).inv.app P)
set_option backward.isDefEq.respectTransparency false in
include hcomp in
/-- Comparison-compatible derived composition satisfies associativity. -/
private theorem derivedExtensionScalarsComp_assoc
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (totalDerivedExtensionScalars.{u, u, v} h).functor.map ((comp f g).hom.app X) ≫
      (comp (g.comp f) h).hom.app X =
      (comp g h).hom.app ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) ≫
        (comp f (h.comp g)).hom.app X := by
  let α : ((totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
    (totalDerivedExtensionScalars.{u, u, v} g).functor) ⋙
    (totalDerivedExtensionScalars.{u, u, v} h).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} (h.comp (g.comp f))).functor :=
    Functor.whiskerRight (comp f g).hom (totalDerivedExtensionScalars.{u, u, v} h).functor ≫
      (comp (g.comp f) h).hom
  let β : ((totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
    (totalDerivedExtensionScalars.{u, u, v} g).functor) ⋙
    (totalDerivedExtensionScalars.{u, u, v} h).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} (h.comp (g.comp f))).functor :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, v} f).functor (comp g h).hom ≫
        (comp f (h.comp g)).hom
  have heq : α = β := by
    apply Functor.leftDerived_ext _ (totalDerivedExtensionScalars.{u, u, v} (h.comp (g.comp
      f))).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) _ α β
    ext P
    dsimp [α, β]
    simp only [Category.id_comp, Category.assoc]
    erw [hcomp (g.comp f) h P, hcomp f (h.comp g) P]
    rw [← Functor.map_comp_assoc, hcomp f g P]
    simp only [Functor.map_comp, Category.assoc]
    erw [← (comp g h).hom.naturality_assoc ((totalDerivedExtensionScalars.{u, u, v}
      f).comparison.app P)]
    erw [reassoc_of% hcomp g h (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex
      (.up ℤ)).obj P)]
    simp only [Functor.comp_map]
    congr 1
    congr 1
    erw [(totalDerivedExtensionScalars.{u, u, v} h).comparison.naturality_assoc
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max u v} f g)
        (.up ℤ)).inv.app P)]
    congr 1
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext i : 1
    exact extendScalarsComp_inv_app.{u, v} f g h (P.X i)
  simpa [α, β] using NatTrans.congr_app heq X
set_option backward.isDefEq.respectTransparency false in
include hcomp in
/-- Comparison-compatible derived composition satisfies the right unit law. -/
private theorem derivedExtensionScalarsComp_id
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedExtensionScalarsId.{u, v} B).hom.app
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) ≫
      (comp f (RingHom.id B)).hom.app X = 𝟙 _ := by
  let α : (totalDerivedExtensionScalars.{u, u, v} f).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor :=
    Functor.whiskerLeft _ (derivedExtensionScalarsId.{u, v} B).hom ≫
      (comp f (RingHom.id B)).hom
  have heq : α = 𝟙 _ := by
    apply Functor.leftDerived_ext _ (totalDerivedExtensionScalars.{u, u, v} f).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) _ α (𝟙 _)
    ext P
    dsimp [α]
    simp only [Category.id_comp, Category.assoc]
    erw [hcomp f (RingHom.id B) P]
    erw [← (derivedExtensionScalarsId.{u, v} B).hom.naturality_assoc
      ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P)]
    erw [reassoc_of% derivedExtensionScalarsId_comparison.{u, v} B
      (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P)]
    rw [extensionScalarsComplexComp_id f P]
    exact Category.comp_id _
  exact NatTrans.congr_app heq X

/-- Extension of scalars on morphisms between two objects descended from a common ring. -/
private def derivedHomBaseChange
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.obj L :=
  Iso.homCongr ((comp f g).app K) ((comp f g).app L)
    ((totalDerivedExtensionScalars.{u, u, v} g).functor.map φ)

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private lemma derivedHomBaseChange_ofHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (P F : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ψ : ((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj F)
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app F)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app F)] :
    derivedHomBaseChange comp f g
      ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P ≫
        DerivedCategory.Q.map ψ ≫
        inv ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app F)) =
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P ≫
        (extensionOfScalarsComplexComp.{u, v} f g).hom.app P ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, max u v} g).mapHomologicalComplex (.up ℤ)).map ψ) ≫
        (extensionOfScalarsComplexComp.{u, v} f g).inv.app F ≫
        inv ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app F) := by
  apply (cancel_mono
    ((totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app F)).mp
  apply (cancel_epi ((comp f g).hom.app (DerivedCategory.Q.obj P))).mp
  dsimp [derivedHomBaseChange, Iso.homCongr]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc,
    IsIso.inv_hom_id, Category.comp_id]
  rw [hcomp f g F, reassoc_of% (hcomp f g P)]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id, Iso.inv_hom_id_app_assoc]
  simpa only [Category.comp_id, Functor.map_comp, Category.assoc, Functor.comp_map,
    extensionOfScalarsComplexGeneral, extensionOfScalarsComplex] using
    congrArg (fun t ↦
    (totalDerivedExtensionScalars.{u, u, v} g).functor.map
        ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P) ≫ t ≫
      (extensionOfScalarsComplexComp.{u, v} f g).inv.app F)
    ((totalDerivedExtensionScalars.{u, u, v} g).comparison.naturality ψ)

set_option backward.isDefEq.respectTransparency false in
include hcomp in
/-- Successive base changes of a derived morphism agree with their composite. -/
private theorem derivedHomBaseChange_comp
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D)
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    derivedHomBaseChange comp (g.comp f) h (derivedHomBaseChange comp f g φ) =
      derivedHomBaseChange comp f (h.comp g) φ := by
  have hi (X : DerivedCategory (ModuleCat.{max u v} A)) :
      (comp (g.comp f) h).inv.app X ≫
        (totalDerivedExtensionScalars.{u, u, v} h).functor.map
          ((comp f g).inv.app X) =
      (comp f (h.comp g)).inv.app X ≫
        (comp g h).inv.app
          ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) := by
    apply (cancel_epi ((comp f (h.comp g)).hom.app X)).mp
    apply (cancel_mono
      ((totalDerivedExtensionScalars.{u, u, v} h).functor.map
        ((comp f g).hom.app X) ≫ (comp (g.comp f) h).hom.app X)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [derivedExtensionScalarsComp_assoc comp hcomp f g h X]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  dsimp [derivedHomBaseChange, Iso.homCongr]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hi K]
  simp only [Category.assoc]
  rw [derivedExtensionScalarsComp_assoc comp hcomp f g h L]
  erw [(comp g h).hom.naturality_assoc φ]
  simp

set_option backward.isDefEq.respectTransparency false in
include hcomp in
/-- Base change along the identity acts identically on derived morphisms. -/
private theorem derivedHomBaseChange_id
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    derivedHomBaseChange comp f (RingHom.id B) φ = φ := by
  have he (X : DerivedCategory (ModuleCat.{max u v} A)) :
      (comp f (RingHom.id B)).inv.app X =
        (derivedExtensionScalarsId.{u, v} B).hom.app
          ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj X) := by
    apply (cancel_mono ((comp f (RingHom.id B)).hom.app X)).mp
    simp only [Iso.inv_hom_id_app, derivedExtensionScalarsComp_id comp hcomp]
    rfl
  dsimp [derivedHomBaseChange, Iso.homCongr]
  rw [he K, ← (derivedExtensionScalarsId.{u, v} B).hom.naturality_assoc φ]
  rw [derivedExtensionScalarsComp_id comp hcomp f L]
  exact Category.comp_id φ

/-- Base change of derived morphisms along a commuting triangle of ring maps. -/
private def derivedHomBaseChangeAlong
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (f' : A →+* C) (h : g.comp f = f')
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    (totalDerivedExtensionScalars.{u, u, v} f').functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f').functor.obj L :=
  let e := comp f g ≪≫ derivedExtensionScalarsCongr.{u, v} h
  Iso.homCongr (e.app K) (e.app L)
    ((totalDerivedExtensionScalars.{u, u, v} g).functor.map φ)

/-- The triangle construction specializes to composition of ring maps. -/
private theorem derivedHomBaseChangeAlong_rfl
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    derivedHomBaseChangeAlong comp f g (g.comp f) rfl φ =
      derivedHomBaseChange comp f g φ := by
  simp [derivedHomBaseChangeAlong, derivedHomBaseChange, Iso.homCongr,
    derivedExtensionScalarsCongr]

set_option backward.isDefEq.respectTransparency false in
include hcomp in
/-- Base change along two commuting triangles is base change along the outer triangle. -/
private theorem derivedHomBaseChangeAlong_comp
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D)
    (f' : A →+* C) (f'' : A →+* D) (hf : g.comp f = f') (hg : h.comp f' = f'')
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    derivedHomBaseChangeAlong comp f' h f'' hg
        (derivedHomBaseChangeAlong comp f g f' hf φ) =
      derivedHomBaseChangeAlong comp f (h.comp g) f''
        (by rw [RingHom.comp_assoc, hf, hg]) φ := by
  subst f'
  subst f''
  rw [derivedHomBaseChangeAlong_rfl, derivedHomBaseChangeAlong_rfl]
  exact (derivedHomBaseChange_comp comp hcomp f g h φ).trans
    (derivedHomBaseChangeAlong_rfl comp f (h.comp g) φ).symm

set_option backward.isDefEq.respectTransparency false in
include hcomp in
/-- The identity triangle induces the identity map of derived Hom sets. -/
private theorem derivedHomBaseChangeAlong_id
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (φ : (totalDerivedExtensionScalars.{u, u, v} f).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, v} f).functor.obj L) :
    derivedHomBaseChangeAlong comp f (RingHom.id B) f (RingHom.id_comp f) φ = φ :=
  (derivedHomBaseChangeAlong_rfl comp f _ φ).trans (derivedHomBaseChange_id comp hcomp f φ)

set_option backward.isDefEq.respectTransparency false in
/-- Derived Hom between two base-changed objects, as a functor of the target ring. -/
private def derivedHomFunctor {A : Type u} [CommRing A]
    (K L : DerivedCategory (ModuleCat.{max u v} A)) :
    Under (CommRingCat.of A) ⥤ Type (max u v + 1) where
  obj B := (totalDerivedExtensionScalars.{u, u, v} B.hom.hom).functor.obj K ⟶
    (totalDerivedExtensionScalars.{u, u, v} B.hom.hom).functor.obj L
  map {B C} g := ↾(derivedHomBaseChangeAlong comp B.hom.hom g.right.hom C.hom.hom
    (congrArg CommRingCat.Hom.hom (Under.w g)))
  map_id B := by
    ext φ
    exact derivedHomBaseChangeAlong_id comp hcomp B.hom.hom φ
  map_comp {B C D} g h := by
    ext φ
    exact (derivedHomBaseChangeAlong_comp comp hcomp B.hom.hom g.right.hom h.right.hom
      C.hom.hom D.hom.hom (congrArg CommRingCat.Hom.hom (Under.w g))
      (congrArg CommRingCat.Hom.hom (Under.w h)) φ).symm

end Coherence

end ScalarExtensionCoherence

/-- The base-changed algebras as a diagram under the starting algebra. -/
private def stageUnderFunctor {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] (F : I ⥤ CommAlgCat.{uR} R₀)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] :
    I ⥤ Under (CommRingCat.of (ULift.{uR} A₀)) where
  obj i := Under.mk (CommRingCat.ofHom
    ((baseToStageMap F A₀ i).comp ULift.ringEquiv.toRingHom))
  map {i j} f := Under.homMk (CommRingCat.ofHom (stageMap F A₀ f)) (by
    apply CommRingCat.hom_ext
    ext a
    simp [stageMap, baseToStageMap, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul])
  map_id i := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext
    simp [stageMap]
  map_comp f g := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    change stageMap F A₀ (f ≫ g) = (stageMap F A₀ g).comp (stageMap F A₀ f)
    ext <;> simp [stageMap, Algebra.TensorProduct.map_tmul]

/-- The canonical cocone of base-changed algebras under the starting algebra. -/
private def stageUnderCocone {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] :
    Cocone (stageUnderFunctor F A₀) where
  pt := Under.mk (CommRingCat.ofHom
    ((baseToLimitMap c A₀).comp ULift.ringEquiv.toRingHom))
  ι.app i := Under.homMk (CommRingCat.ofHom (stageToLimitMap c A₀ i)) (by
    apply CommRingCat.hom_ext
    ext a
    simp [stageUnderFunctor, stageToLimitMap, baseToStageMap, baseToLimitMap,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul])
  ι.naturality i j f := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    change (stageToLimitMap c A₀ j).comp (stageMap F A₀ f) = stageToLimitMap c A₀ i
    ext x
    · simp [stageToLimitMap, stageMap]
    · simp [stageToLimitMap, stageMap]

end PseudoCoherence

end
