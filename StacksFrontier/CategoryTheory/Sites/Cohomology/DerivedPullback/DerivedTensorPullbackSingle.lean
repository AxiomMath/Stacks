module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex

/-!
# The derived tensor product of a module with the derived pullback of a module

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, `𝒢` an `O`-module and `ℱ` an
`O'`-module. If the functor `𝒩 ↦ 𝒢 ⊗_O f^*𝒩` is left exact, then
`𝒢 ⊗^L_O Lf^*ℱ ≅ (𝒢 ⊗_O f^*ℱ)[0]`. A flat resolution `𝒫 ⟶ ℱ` bounded above computes
`Lf^*ℱ` as `f^*𝒫` (Stacks 06YY), which is K-flat (Stacks 0G7E); the derived tensor product is
then `𝒢 ⊗_O f^*𝒫`, and the exact functor `𝒩 ↦ 𝒢 ⊗_O f^*𝒩` carries the quasi-isomorphism
`𝒫 ⟶ ℱ[0]` to a quasi-isomorphism.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedTensorPullbackSingleIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex
  isFlat_pullbackComplex_X kFlat_pullbackComplex)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)
  (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)

/-- The functor `𝒩 ↦ 𝒢 ⊗_O f^*𝒩`. -/
abbrev tensorPullback (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  f.toModulesHom.pullbackModules ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj G

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- `𝒩 ↦ 𝒢 ⊗_O f^*𝒩` is right exact. -/
theorem preservesFiniteColimits_tensorPullback
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesFiniteColimits (tensorPullback f G) := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X.O G
  have : PreservesColimitsOfSize.{0, 0} f.toModulesHom.pullbackModules :=
    (RingedToposHom.pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits
  exact comp_preservesFiniteColimits _ _

omit [Y.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify Y.J (Type u)] in
/-- A module of `O'`-modules has a flat resolution vanishing in positive degrees whose
degreewise pullback computes the derived pullback. -/
theorem exists_flat_resolution_single
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
      (q : P ⟶ (CochainComplex.singleFunctor _ 0).obj F), QuasiIso q ∧ P.IsStrictlyLE 0 ∧
      ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i) := by
  let Pflat : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
    fun M => AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) M
  have : Pflat.ContainsZero := Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize Y.O
  obtain ⟨P, q, -, hq, hPflat, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pflat (fun M => by
      obtain ⟨N, π, hflat, hepi⟩ :=
        Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize Y.O M
      exact ⟨N, hflat, π, hepi⟩) 0).1 ((CochainComplex.singleFunctor _ 0).obj F)
  exact ⟨P, q, hq, hPLE, hPflat⟩

/-- **`𝒢 ⊗^L Lf^*ℱ ≅ (𝒢 ⊗ f^*ℱ)[0]` when `𝒩 ↦ 𝒢 ⊗ f^*𝒩` is left exact.** -/
def derivedTensorPullbackSingleIso
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [PreservesFiniteLimits (tensorPullback f G)]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (TX.tensor.obj ((DerivedCategory.singleFunctor _ 0).obj G)).obj
        ((derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((tensorPullback f G).obj F) := by
  have hP := exists_flat_resolution_single F
  let P := hP.choose
  let q := hP.choose_spec.choose
  have hq : QuasiIso q := hP.choose_spec.choose_spec.1
  haveI : P.IsStrictlyLE 0 := hP.choose_spec.choose_spec.2.1
  have hPflat := hP.choose_spec.choose_spec.2.2
  have := preservesFiniteColimits_tensorPullback f G
  have : PreservesBinaryBiproducts (tensorPullback f G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : (tensorPullback f G).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hPK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P :=
    letI := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize Y.O
    CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ P 0
      (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor_ofSize _)
      (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules_ofSize _) fun i ↦
        Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat_ofSize _ _ (hPflat i) i
  have hfP := kFlat_pullbackComplex f P hPK hPflat
  haveI : QuasiIso (((tensorPullback f G).mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q _
  let e₁ : (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj P) :=
    (derivedPullback f).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F ≪≫
          (@asIso _ _ _ _ (DerivedCategory.Q.map q)
            ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq)).symm) ≪≫
      flatPullbackIso f P hPK hPflat
  let e₂ : HomologicalComplex.mapBifunctor ((CochainComplex.singleFunctor _ 0).obj G)
      ((pullbackComplex f).obj P) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ) ≅
      ((tensorPullback f G).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
    HomologicalComplex.mapBifunctorSingleLeftIso _ G _ ≪≫
      (Functor.mapHomologicalComplexCompIso (F := f.toModulesHom.pullbackModules)
        (G := (Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj G)
        (H := tensorPullback f G) (Iso.refl _) (ComplexShape.up ℤ)).app P
  let e₃ : DerivedCategory.Q.obj (((tensorPullback f G).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((tensorPullback f G).obj F) :=
    @asIso _ _ _ _ (DerivedCategory.Q.map (((tensorPullback f G).mapHomologicalComplex
        (ComplexShape.up ℤ)).map q))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (tensorPullback f G) _ 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app ((tensorPullback f G).obj F)).symm
  exact (TX.tensor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G)).app _ ≪≫
    (TX.tensor.obj _).mapIso e₁ ≪≫ TX.comparisonRight _ _ hfP ≪≫
    DerivedCategory.Q.mapIso e₂ ≪≫ e₃

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
