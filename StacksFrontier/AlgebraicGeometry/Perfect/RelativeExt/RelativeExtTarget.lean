module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.FlatPullbackTensor
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The complex `𝒢 ⊗_{𝒪_X} f^*ℱ` and its boundary maps

Let `f : X ⟶ Y` be a morphism of ringed spaces and `𝒢` a bounded complex of `𝒪_X`-modules
flat over `Y`. For an `𝒪_Y`-module `ℱ`, the complex `𝒢 ⊗_{𝒪_X} f^*ℱ` has terms
`𝒢^n ⊗_{𝒪_X} f^*ℱ` and differentials `d ⊗ 1`. This is the second argument of the `Ext`-groups
of [Stacks, Tag 08IF].

This file identifies `𝒢 ⊗_{𝒪_X} f^*ℱ`, as an object of `D(𝒪_X)`, with the value at `ℱ[0]` of
the functor `Φ = pullbackTensorDerivedFunctor : D(𝒪_Y) ⥤ D(𝒪_X)`, naturally in `ℱ`. It also
proves that, under this identification, the connecting morphism of the distinguished triangle
of a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` maps under `Φ` to the connecting morphism of
the short exact sequence of complexes `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.tensorModuleComplexFunctor`: `ℳ ↦ 𝒢 ⊗_{𝒪_X} ℳ`.
* `Stacks.Cohomology.RelativeExt.relativeExtTargetFunctor`: `ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ`.
* `Stacks.Cohomology.RelativeExt.singleTargetIso`: `Tot(f^*(ℱ[0]) ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ`.
* `Stacks.Cohomology.RelativeExt.relativeExtTargetIso`: `Φ(ℱ[0]) ≅ 𝒢 ⊗ f^*ℱ` in `D(𝒪_X)`.

## Main results

* `Stacks.Cohomology.RelativeExt.shortExact_relativeExtTarget`: a short exact sequence of
  `𝒪_Y`-modules gives a short exact sequence of complexes `𝒢 ⊗ f^*ℱ_•`.
* `Stacks.Cohomology.RelativeExt.map_singleδ_relativeExtTargetIso`: the compatibility of the
  connecting morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing


/-- The category of `𝒪_X`-modules, as sheaves of modules over the ring sheaf of `X.sheaf`; it is
`SheafOfModules (structureSheafRing X)` up to definitional unfolding. -/
abbrev TModules (X : RingedSpace.{u, u}) : Type (u + 1) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)

/-- `⊗_{𝒪_X}` is additive in its first variable. -/
abbrev sheafTensorAdditiveSpace (X : RingedSpace.{u, u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} X.sheaf

/-- `M ⊗_{𝒪_X} -` is additive. -/
abbrev sheafTensorObjAdditiveSpace (X : RingedSpace.{u, u})
    (M : TModules X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive :=
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive X.sheaf M

section TensorComplex

attribute [local instance] sheafTensorAdditiveSpace sheafTensorObjAdditiveSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (G : CochainComplex (TModules X) ℤ)

/-- **The complex `𝒢 ⊗_{𝒪_X} ℳ`**, with terms `𝒢^p ⊗_{𝒪_X} ℳ` and differentials `d ⊗ 1`, as a
functor of the `𝒪_X`-module `ℳ`. -/
def tensorModuleComplexFunctor : TModules X ⥤
    CochainComplex (TModules X) ℤ where
  obj M := CochainComplex.KFlatBifunctor.rowComplex
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) G M
  map {_ _} φ :=
    { f := fun p =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X p)).map φ
      comm' := fun p q _ =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
          (G.d p q)).naturality φ }
  map_id M := HomologicalComplex.hom_f_injective (funext fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X p)).map_id M)
  map_comp φ ψ := HomologicalComplex.hom_f_injective (funext fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X p)).map_comp
      φ ψ)

/-- The functor `ℳ ↦ 𝒢 ⊗_{𝒪_X} ℳ` is additive. -/
instance tensorModuleComplexFunctor_additive : (tensorModuleComplexFunctor G).Additive where
  map_add {_ _ φ ψ} := HomologicalComplex.hom_f_injective (funext fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X p)).map_add)

/-- **The complex `𝒢 ⊗_{𝒪_X} f^*ℱ`**, as a functor of the `𝒪_Y`-module `ℱ`, with `f^*` the
pullback of modules. -/
abbrev relativeExtTargetFunctor : SheafOfModules.{u} (structureSheafRing Y) ⥤
    CochainComplex (TModules X) ℤ :=
  modulePullback f ⋙ tensorModuleComplexFunctor G

/-- The symmetry of the tensor product of `𝒪_X`-modules. -/
abbrev sheafTensorFlip :
    Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip :=
  haveI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  haveI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso X.sheaf

/-- `ℳ ⊗ 𝒢^•` degreewise is `𝒢^• ⊗ ℳ` degreewise, by the symmetry of the tensor product. -/
def flipTensorComplexIso (M : TModules X) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf).obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj G ≅
      (tensorModuleComplexFunctor G).obj M :=
  HomologicalComplex.Hom.isoOfComponents (fun q => ((sheafTensorFlip (X := X)).app M).app (G.X q))
    (fun q q' _ => (((sheafTensorFlip (X := X)).app M).hom.naturality (G.d q q')).symm)

/-- The isomorphism `flipTensorComplexIso` is natural in the `𝒪_X`-module `ℳ`. -/
theorem flipTensorComplexIso_hom_naturality
    {M M' : TModules X}
    (φ : M ⟶ M') :
    (NatTrans.mapHomologicalComplex
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map φ)
        (ComplexShape.up ℤ)).app G ≫ (flipTensorComplexIso G M').hom =
      (flipTensorComplexIso G M).hom ≫ (tensorModuleComplexFunctor G).map φ := by
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  exact NatTrans.congr_app ((sheafTensorFlip (X := X)).hom.naturality φ) (G.X q)

end TensorComplex

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (G : CochainComplex (TModules X) ℤ)

/-- For an `𝒪_Y`-module `𝒩`, the functor `ℳ ↦ f^*𝒩 ⊗ ℳ` preserves zero morphisms. -/
instance pullbackTensorBifunctor_obj_preservesZeroMorphisms
    (N : SheafOfModules.{u} (structureSheafRing Y)) :
    ((pullbackTensorBifunctor f).obj N).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The functor `𝒩 ↦ f^*𝒩 ⊗ -` preserves zero morphisms. -/
instance pullbackTensorBifunctor_preservesZeroMorphisms :
    (pullbackTensorBifunctor f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `Tot(f^*(ℱ[0]) ⊗ 𝒢)` is `f^*ℱ ⊗ 𝒢` degreewise. -/
def singleLeftTensorIso (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (((pullbackTensorBifunctor f).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj G ≅
      (pullbackTensorComplexFunctor f G).obj
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) :=
  @HomologicalComplex.singleLeftIsoMapBifunctor (SheafOfModules.{u} (structureSheafRing Y))
      (SheafOfModules.{u} (structureSheafRing X)) (SheafOfModules.{u} (structureSheafRing X))
      _ _ _ _ _ _ _ (pullbackTensorBifunctor f) _
      (fun M => Functor.preservesZeroMorphisms_of_additive _) F G _ _

/-- The isomorphism `singleLeftTensorIso` is natural in the `𝒪_Y`-module `ℱ`. -/
theorem singleLeftTensorIso_hom_naturality {F F' : SheafOfModules.{u} (structureSheafRing Y)}
    (v : F ⟶ F') :
    (singleLeftTensorIso f G F).hom ≫ (pullbackTensorComplexFunctor f G).map
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map v) =
      (NatTrans.mapHomologicalComplex ((pullbackTensorBifunctor f).map v)
        (ComplexShape.up ℤ)).app G ≫ (singleLeftTensorIso f G F').hom :=
  @HomologicalComplex.singleLeftIsoMapBifunctor_hom_naturality_left
    (SheafOfModules.{u} (structureSheafRing Y))
    (SheafOfModules.{u} (structureSheafRing X)) (SheafOfModules.{u} (structureSheafRing X))
    _ _ _ _ _ _ _ (pullbackTensorBifunctor f) _
    (fun M => Functor.preservesZeroMorphisms_of_additive _) F' G _ F _ _ _ v

/-- `Tot(f^*(ℱ[0]) ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ` at one module. -/
def singleTargetIsoApp (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (pullbackTensorComplexFunctor f G).obj
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≅
      (relativeExtTargetFunctor f G).obj F :=
  (singleLeftTensorIso f G F).symm ≪≫ flipTensorComplexIso G ((modulePullback f).obj F)

/-- **`Tot(f^*(ℱ[0]) ⊗ 𝒢)` is `𝒢 ⊗ f^*ℱ`**, naturally in the `𝒪_Y`-module `ℱ`: the total
complex of a double complex concentrated in one column is that column, and the symmetry of the
tensor product exchanges the two factors. -/
def singleTargetIso :
    CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0 ⋙
        pullbackTensorComplexFunctor f G ≅ relativeExtTargetFunctor f G :=
  NatIso.ofComponents (singleTargetIsoApp f G)
    (fun {F F'} v => by
      have h' : (pullbackTensorComplexFunctor f G).map
            ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map v) ≫
          (singleLeftTensorIso f G F').inv =
        (singleLeftTensorIso f G F).inv ≫ (NatTrans.mapHomologicalComplex
          ((pullbackTensorBifunctor f).map v) (ComplexShape.up ℤ)).app G := by
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, singleLeftTensorIso_hom_naturality]
      change _ ≫ (singleLeftTensorIso f G F').inv ≫
          (flipTensorComplexIso G ((modulePullback f).obj F')).hom =
        ((singleLeftTensorIso f G F).inv ≫
          (flipTensorComplexIso G ((modulePullback f).obj F)).hom) ≫
          (tensorModuleComplexFunctor G).map ((modulePullback f).map v)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (flipTensorComplexIso G ((modulePullback f).obj F')).hom) h').trans
          ((Category.assoc _ _ _).trans
            ((congrArg ((singleLeftTensorIso f G F).inv ≫ ·)
              (flipTensorComplexIso_hom_naturality G ((modulePullback f).map v))).trans
              (Category.assoc _ _ _).symm))))

/-- The functor `ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ` is additive. -/
instance relativeExtTargetFunctor_additive : (relativeExtTargetFunctor f G).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _ _ _
    (tensorModuleComplexFunctor G) (tensorModuleComplexFunctor_additive G)

/-- The functor `ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ`, valued in complexes of
`SheafOfModules (structureSheafRing X)`, is additive. -/
instance relativeExtTargetFunctor_additive' :
    (relativeExtTargetFunctor f G : SheafOfModules.{u} (structureSheafRing Y) ⥤
      CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ).Additive :=
  relativeExtTargetFunctor_additive f G

/-- The functor `ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ`, valued in complexes of
`SheafOfModules (structureSheafRing X)`, preserves zero morphisms. -/
instance relativeExtTargetFunctor_preservesZeroMorphisms' :
    (relativeExtTargetFunctor f G : SheafOfModules.{u} (structureSheafRing Y) ⥤
      CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (relativeExtTargetFunctor_additive f G)

/-- The functor `K ↦ Tot(f^*K ⊗ 𝒢)` on complexes of `𝒪_Y`-modules is additive. -/
instance pullbackTensorComplexFunctor_additive' : (pullbackTensorComplexFunctor f G).Additive :=
  pullbackTensorComplexFunctor_additive f G

/-- `ℱ ↦ 𝒢^q ⊗ f^*ℱ` is `ℱ ↦ f^*ℱ ⊗ 𝒢^q`, by the symmetry of the tensor product. -/
def tensorPullbackFlipIso (M : TModules X) :
    modulePullback f ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M ≅
      Stacks.SheafOfModules.pullbackTensorFunctor f M :=
  Functor.isoWhiskerLeft (modulePullback f) ((sheafTensorFlip (X := X)).app M)

/-- **`ℱ ↦ 𝒢^q ⊗ f^*ℱ` is exact when `𝒢^q` is flat over `Y`.** -/
theorem exact_tensorPullback (M : TModules X) (hM : IsFlatOver f M) :
    PreservesFiniteLimits
        (modulePullback f ⋙
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M) ∧
      PreservesFiniteColimits
        (modulePullback f ⋙
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M) := by
  have hex := Stacks.SheafOfModules.pullbackTensorFunctor_exact f M hM
  exact ⟨@preservesFiniteLimits_of_natIso _ _ _ _ _ _ (tensorPullbackFlipIso f M).symm hex.1,
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (tensorPullbackFlipIso f M).symm hex.2⟩

/-- **A short exact sequence of `𝒪_Y`-modules gives a short exact sequence of complexes
`0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`** when every term of `𝒢` is flat over `Y`. -/
theorem shortExact_relativeExtTarget (hflat : ∀ i : ℤ, IsFlatOver f (G.X i))
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))} (hA : A.ShortExact) :
    (A.map (relativeExtTargetFunctor f G)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q => ?_)
  obtain ⟨h₁, h₂⟩ := exact_tensorPullback f (G.X q) (hflat q)
  have : (modulePullback f ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X q)).Additive :=
    @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X q))
      (sheafTensorObjAdditiveSpace X (G.X q))
  have : PreservesFiniteLimits (modulePullback f ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X q)) := h₁
  have : PreservesFiniteColimits (modulePullback f ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X q)) := h₂
  exact hA.map_of_exact
    (modulePullback f ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X q))

variable {f G}

/-- **`Φ(ℱ[0]) ≅ 𝒢 ⊗ f^*ℱ` in `D(𝒪_X)`**, naturally in the `𝒪_Y`-module `ℱ`, for `𝒢` bounded
and flat over `Y`. -/
def relativeExtTargetIso (hG : IsBoundedFlatOver f G) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0 ⋙
        pullbackTensorDerivedFunctor hG ≅
      relativeExtTargetFunctor f G ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun F => (pullbackTensorDerivedFunctorFactors hG).app
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≪≫
      DerivedCategory.Q.mapIso (singleTargetIsoApp f G F))
    (fun {F F'} v => by
      have h₁ := (pullbackTensorDerivedFunctorFactors hG).hom.naturality
        ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map v)
      have h₂ := congrArg DerivedCategory.Q.map ((singleTargetIso f G).hom.naturality v)
      simp only [Functor.map_comp] at h₂
      change (pullbackTensorDerivedFunctor hG).map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).map v)) ≫
          (pullbackTensorDerivedFunctorFactors hG).hom.app _ ≫
            DerivedCategory.Q.map (singleTargetIsoApp f G F').hom =
        ((pullbackTensorDerivedFunctorFactors hG).hom.app _ ≫
          DerivedCategory.Q.map (singleTargetIsoApp f G F).hom) ≫
            DerivedCategory.Q.map ((relativeExtTargetFunctor f G).map v)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm))))

/-- The functor `Φ = pullbackTensorDerivedFunctor` commutes with the shift. -/
instance pullbackTensorDerivedFunctor_commShift' (hG : IsBoundedFlatOver f G) :
    (pullbackTensorDerivedFunctor hG).CommShift ℤ :=
  pullbackTensorDerivedFunctor_commShift hG

/-- The component of `relativeExtTargetIso` at `ℱ` is the composite of the factorisation
`pullbackTensorDerivedFunctorFactors` at `ℱ[0]` with the image of `singleTargetIsoApp`. -/
theorem relativeExtTargetIso_hom_app (hG : IsBoundedFlatOver f G)
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (relativeExtTargetIso hG).hom.app F =
      (pullbackTensorDerivedFunctorFactors hG).hom.app
          ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≫
        DerivedCategory.Q.map (singleTargetIsoApp f G F).hom := rfl

/-- The image under `K ↦ Tot(f^*K ⊗ 𝒢)` of a short exact sequence of `𝒪_Y`-modules placed in
degree zero is the short exact sequence `𝒢 ⊗ f^*ℱ_•`. -/
def singleShortComplexIso (A : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))) :
    (A.map (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ) 0)).map (pullbackTensorComplexFunctor f G) ≅
      ShortComplex.mk ((relativeExtTargetFunctor f G).map A.f)
        ((relativeExtTargetFunctor f G).map A.g)
          (by exact (A.map (relativeExtTargetFunctor f G)).zero) :=
  ShortComplex.isoMk (singleTargetIsoApp f G A.X₁) (singleTargetIsoApp f G A.X₂)
    (singleTargetIsoApp f G A.X₃) ((singleTargetIso f G).hom.naturality A.f).symm
    ((singleTargetIso f G).hom.naturality A.g).symm

/-- **The boundary maps of [Stacks, Tag 08IF] are compatible.** For a short exact sequence
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of `𝒪_Y`-modules, the image under `Φ` of its connecting morphism
`ℱ₃ ⟶ ℱ₁[1]` in `D(𝒪_Y)` corresponds, under `Φ(ℱ[0]) ≅ 𝒢 ⊗ f^*ℱ`, to the connecting morphism of
the short exact sequence of complexes `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0` in
`D(𝒪_X)`. -/
theorem map_singleδ_relativeExtTargetIso (hG : IsBoundedFlatOver f G)
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))} (hA : A.ShortExact) :
    (pullbackTensorDerivedFunctor hG).map hA.singleδ ≫
        ((pullbackTensorDerivedFunctor hG).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((relativeExtTargetIso hG).hom.app A.X₁)⟦(1 : ℤ)⟧' =
      (relativeExtTargetIso hG).hom.app A.X₃ ≫
        DerivedCategory.triangleOfSESδ (shortExact_relativeExtTarget f G hG.isFlatOver hA) := by
  have hS := hA.map_of_exact
    (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) 0)
  have hΨS : ((A.map (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) 0)).map (pullbackTensorComplexFunctor f G)).ShortExact :=
    (ShortComplex.shortExact_iff_of_iso (singleShortComplexIso A)).2
      (shortExact_relativeExtTarget f G hG.isFlatOver hA)
  have key₁ := map_triangleOfSESδ_pullbackTensorDerivedFunctor hG hS hΨS
  have key₂ := DerivedCategory.triangleOfSESδ_naturality hΨS
    (shortExact_relativeExtTarget f G hG.isFlatOver hA) (singleShortComplexIso A).hom
  rw [relativeExtTargetIso_hom_app, relativeExtTargetIso_hom_app]
  have e₁ := (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
      (1 : ℤ)).map_comp
    ((pullbackTensorDerivedFunctorFactors hG).hom.app
      ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj A.X₁))
    (DerivedCategory.Q.map (singleTargetIsoApp f G A.X₁).hom)
  exact (congrArg (fun t => _ ≫ _ ≫ t) e₁).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) key₁).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) key₂).trans (Category.assoc _ _ _).symm)))))

end Stacks.Cohomology.RelativeExt

end
