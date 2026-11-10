module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalToTensorCommShift
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverDerivedTensorPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToTensorCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorMappingConeDesc
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleOfSESNatTrans

/-!
# `𝒢^• ⊗^L Lf^*ℱ = 𝒢^• ⊗ f^*ℱ` for `𝒢^•` flat over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝒢^•` a complex of `𝒪_X`-modules.  The
canonical maps `𝒢^• ⊗^L Lf^*M ⟶ Lf^*M ⟶ f^*M` and `𝒢^• ⊗^L f^*M ⟶ Tot(𝒢^• ⊗ f^*M)` (Stacks 0FPH)
assemble to a natural transformation, on complexes `M` of `𝒪_Y`-modules,
`𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M` (`AlgebraicGeometry.Space.tensorPullbackComplex`), compatible with
the shifts.  When `𝒢^•` is bounded with terms flat over `Y` it is an isomorphism at every module
`ℱ` placed in degree `0` (the first displayed equalities of the proof of Stacks 0A1M).  That the
functor `ℱ ↦ 𝒢^• ⊗ f^*ℱ` carries short exact sequences of modules to short exact sequences of
complexes, and that the isomorphisms are compatible with the boundary maps of the two
distinguished triangles, is shown in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexShortExact` and
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexTriangle`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackComplexComparison`: `Lf^* ⟶ f^*` on
  complexes.
* `AlgebraicGeometry.Space.tensorPullbackComplexComparison`: `𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable (f : X ⟶ Y)

/-- Degreewise pullback of complexes of modules along `f`, spelled in this file's instance context
(definitionally `AlgebraicGeometry.Space.pullbackComplexSmallEtale f`). -/
abbrev pullbackComplexSmallEtale' :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
    (ComplexShape.up ℤ)

example : pullbackComplexSmallEtale' f = pullbackComplexSmallEtale f := by
  with_reducible_and_instances rfl

/-- **`Lf^* ⟶ f^*` on complexes**: the canonical comparison of the derived pullback with the
degreewise pullback, read on complexes through the two localizations. -/
def smallEtaleDerivedModulePullbackComplexComparison :
    DerivedCategory.Q ⋙ smallEtaleDerivedModulePullback B S hS f ⟶
      pullbackComplexSmallEtale' f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))).inv
      (smallEtaleDerivedModulePullback B S hS f) ≫
    (Functor.associator (HomotopyCategory.quotient
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ))
      DerivedCategory.Qh (smallEtaleDerivedModulePullback B S hS f)).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ))
      (smallEtaleDerivedModulePullbackComparison B S hS f) ≫
    (Functor.associator (HomotopyCategory.quotient
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ))
      ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomotopyCategory
        (ComplexShape.up ℤ)) DerivedCategory.Qh).inv ≫
    Functor.whiskerRight
      ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    (Functor.associator (pullbackComplexSmallEtale' f)
      (HomotopyCategory.quotient
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft (pullbackComplexSmallEtale' f)
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))).hom

/-- The comparison `Lf^* ⟶ f^*` on complexes commutes with the shifts. -/
instance : NatTrans.CommShift (smallEtaleDerivedModulePullbackComplexComparison f) ℤ := by
  let : (HomotopyCategory.quotient (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (ComplexShape.up ℤ)).CommShift ℤ := inferInstance
  let : (DerivedCategory.Qh ⋙ smallEtaleDerivedModulePullback B S hS f).CommShift ℤ :=
    inferInstance
  let : (smallEtaleModulePullbackOnHomotopy B S hS f).CommShift ℤ := inferInstance
  let : NatTrans.CommShift (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  let : NatTrans.CommShift (smallEtaleDerivedModulePullbackComparison B S hS f) ℤ :=
    Functor.IsLeftDerivedFunctor.natTrans_commShift (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedModulePullbackComparison B S hS f) (smallEtaleModuleQuasiIso B S hS Y) ℤ
  unfold smallEtaleDerivedModulePullbackComplexComparison
  infer_instance

variable (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)

/-- `Tot(𝒢^• ⊗ -)` on complexes of `𝒪_X`-modules, in the spelling of
`AlgebraicGeometry.Space.tensorPullbackComplex`. -/
abbrev tensorComplexSmallEtale :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS X).O).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G

section Tensor

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

/-- Two complexes of modules on the small étale site of an algebraic space have a total complex
for the tensor product. -/
local instance hasMapBifunctor_sheafTensor_smallEtaleSite (W : AlgebraicSpaces B S hS)
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS W.1 W.2).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u, u, u, u} _ K₁ K₂

/-- The canonical map `𝒢^• ⊗^L M ⟶ Tot(𝒢^• ⊗ M)` of Stacks 0FPH on an algebraic space, natural
in the complex `M`. -/
def smallEtaleToTensorNatTrans :
    DerivedCategory.Q ⋙ (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G) ⟶
      tensorComplexSmallEtale G ⋙ DerivedCategory.Q :=
  Stacks.SheafOfModules.canonicalToTensorNatTrans (smallEtaleRingedSite B S hS X.1 X.2) G

/-- The canonical map `𝒢^• ⊗^L M ⟶ Tot(𝒢^• ⊗ M)` commutes with the shifts. -/
instance : NatTrans.CommShift (smallEtaleToTensorNatTrans G) ℤ :=
  Stacks.SheafOfModules.canonicalToTensorNatTrans_commShift
    (smallEtaleRingedSite B S hS X.1 X.2) G

variable {G} in
/-- The canonical map `𝒢^• ⊗^L L ⟶ Tot(𝒢^• ⊗ L)` is invertible at a K-flat `L`. -/
theorem isIso_smallEtaleToTensorNatTrans_app
    (L : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedTopos B S hS X).O L) :
    IsIso ((smallEtaleToTensorNatTrans G).app L) :=
  Stacks.SheafOfModules.isIso_canonicalToTensorNatTrans_app_of_kFlat
    (smallEtaleRingedSite B S hS X.1 X.2) G L hL

end Tensor

/-- **`𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M`**, natural in the complex `M` of `𝒪_Y`-modules: the
comparison `Lf^* ⟶ f^*` followed by the canonical map of Stacks 0FPH. -/
def tensorPullbackComplexComparison :
    (DerivedCategory.Q ⋙ smallEtaleDerivedModulePullback B S hS f) ⋙
        (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G) ⟶
      pullbackComplexSmallEtale' f ⋙ (tensorComplexSmallEtale G ⋙ DerivedCategory.Q) :=
  Functor.whiskerRight (smallEtaleDerivedModulePullbackComplexComparison f)
      ((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)) ≫
    (Functor.associator (pullbackComplexSmallEtale' f) DerivedCategory.Q
      ((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))).hom ≫
    Functor.whiskerLeft (pullbackComplexSmallEtale' f) (smallEtaleToTensorNatTrans G)

/-- The comparison `𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M` commutes with the shifts. -/
instance : NatTrans.CommShift (tensorPullbackComplexComparison f G) ℤ := by
  unfold tensorPullbackComplexComparison
  infer_instance

/-- `𝒢^• ⊗ f^*(-)` commutes with the shifts: it is the composite of the degreewise pullback and
of `Tot(𝒢^• ⊗ -)`. -/
instance tensorPullbackComplex_commShift : (tensorPullbackComplex f G).CommShift ℤ :=
  inferInstanceAs ((pullbackComplexSmallEtale' f ⋙ tensorComplexSmallEtale G).CommShift ℤ)

/-- The functor `𝒢^• ⊗ f^*(-)` on complexes is additive. -/
instance tensorPullbackComplex_additive : (tensorPullbackComplex f G).Additive := by
  have : (tensorComplexSmallEtale G).Additive :=
    Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive _ G
  have : (pullbackComplexSmallEtale' f).Additive := inferInstance
  change (pullbackComplexSmallEtale' f ⋙ tensorComplexSmallEtale G).Additive
  infer_instance

/-- The comparison `𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M`, reassociated. -/
def tensorPullbackComplexComparisonAssoc :
    DerivedCategory.Q ⋙ (smallEtaleDerivedModulePullback B S hS f ⋙
        (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)) ⟶
      (pullbackComplexSmallEtale' f ⋙ tensorComplexSmallEtale G) ⋙ DerivedCategory.Q :=
  (Functor.associator DerivedCategory.Q (smallEtaleDerivedModulePullback B S hS f)
      ((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))).inv ≫
    tensorPullbackComplexComparison f G ≫
    (Functor.associator (pullbackComplexSmallEtale' f) (tensorComplexSmallEtale G)
      DerivedCategory.Q).inv

/-- The reassociated comparison `𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M` commutes with the shifts. -/
instance : NatTrans.CommShift (tensorPullbackComplexComparisonAssoc f G) ℤ := by
  let : ((DerivedCategory.Q ⋙ smallEtaleDerivedModulePullback B S hS f) ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).CommShift ℤ :=
    inferInstance
  let : (pullbackComplexSmallEtale' f ⋙ (tensorComplexSmallEtale G ⋙
      DerivedCategory.Q)).CommShift ℤ := inferInstance
  have h0 : NatTrans.CommShift (Functor.associator DerivedCategory.Q
      (smallEtaleDerivedModulePullback B S hS f)
      ((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))).inv ℤ := inferInstance
  have h1 : NatTrans.CommShift (tensorPullbackComplexComparison f G) ℤ := inferInstance
  have h2 : NatTrans.CommShift (Functor.associator (pullbackComplexSmallEtale' f)
      (tensorComplexSmallEtale G) DerivedCategory.Q).inv ℤ := inferInstance
  unfold tensorPullbackComplexComparisonAssoc
  infer_instance

/-- **`𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M`**, with target `𝒢^• ⊗ f^*(-)` in the spelling
`AlgebraicGeometry.Space.tensorPullbackComplex`; natural in the complex `M` and compatible with
the shifts. -/
def tensorPullbackComplexNatTrans :
    DerivedCategory.Q ⋙ (smallEtaleDerivedModulePullback B S hS f ⋙
        (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)) ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q :=
  tensorPullbackComplexComparisonAssoc f G

/-- The natural transformation `𝒢^• ⊗^L Lf^*M ⟶ 𝒢^• ⊗ f^*M` commutes with the shifts. -/
instance : NatTrans.CommShift (tensorPullbackComplexNatTrans f G) ℤ :=
  (inferInstance : NatTrans.CommShift (tensorPullbackComplexComparisonAssoc f G) ℤ)

section QuasiIso

/-- The bifunctor `(𝒢, 𝒩) ↦ 𝒢 ⊗_{𝒪_X} f^*𝒩`. -/
abbrev tensorPullbackBifunctor :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
        SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} (smallEtaleRingedTopos B S hS X).O ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules

/-- The bifunctor `(𝒢, 𝒩) ↦ 𝒢 ⊗ f^*𝒩` is additive in `𝒢`. -/
instance : (tensorPullbackBifunctor f).Additive where
  map_add {_ _ a b} := by
    apply NatTrans.ext
    funext N
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X).O).map (a + b)).app _ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X).O).map a).app _ +
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS X).O).map b).app _
    rw [Functor.map_add, NatTrans.app_add]

/-- For a fixed `𝒪_X`-module `𝒢`, the functor `𝒩 ↦ 𝒢 ⊗ f^*𝒩` is additive. -/
instance (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    ((tensorPullbackBifunctor f).obj M).Additive := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.preservesFiniteColimits_tensorPullback
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f) M
  have : PreservesBinaryBiproducts (Stacks.Cohomology.DerivedPullbackOfToposHom.tensorPullback
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f) M) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  change (Stacks.Cohomology.DerivedPullbackOfToposHom.tensorPullback
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f) M).Additive
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The total complexes of `(𝒢, 𝒩) ↦ 𝒢 ⊗ f^*𝒩` are those of the tensor product. -/
instance hasMapBifunctor_tensorPullbackBifunctor
    (K₁ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (K₂ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ (tensorPullbackBifunctor f) (ComplexShape.up ℤ) :=
  hasMapBifunctor_sheafTensor_smallEtaleRingedTopos B S hS X K₁
    ((pullbackComplexSmallEtale' f).obj K₂)

/-- The total complexes of `(𝒩, 𝒢) ↦ 𝒢 ⊗ f^*𝒩` are transposes of those of the tensor product. -/
instance hasMapBifunctor_tensorPullbackBifunctor_flip
    (K₁ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (K₂ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ (tensorPullbackBifunctor f).flip
      (ComplexShape.up ℤ) :=
  haveI := hasMapBifunctor_sheafTensor_smallEtaleRingedTopos B S hS X K₂
    ((pullbackComplexSmallEtale' f).obj K₁)
  (inferInstance : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS X).O).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K₂).obj ((pullbackComplexSmallEtale' f).obj K₁)).flip.HasTotal
        (ComplexShape.up ℤ))

variable {f} in
/-- **`𝒢^• ⊗ f^*(-)` preserves quasi-isomorphisms** when `𝒢^•` is bounded with terms flat over
`Y`: the terms of `𝒢^•` make `𝒩 ↦ 𝒢ⁿ ⊗ f^*𝒩` exact, so `𝒢^•` is K-flat for the bifunctor
`(𝒩, 𝒢) ↦ 𝒢 ⊗ f^*𝒩` (Stacks 06YQ, bounded case). -/
theorem quasiIso_tensorPullbackComplex_map (a b : ℤ)
    (hGb : ∀ q : ℤ, q < a ∨ b < q → IsZero (G.X q))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {P M : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (q : P ⟶ M) (hq : QuasiIso q) : QuasiIso ((tensorPullbackComplex f G).map q) := by
  have : G.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff (K := G) b).2 fun i hi => hGb i (Or.inr hi)
  have : G.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff (K := G) a).2 fun i hi => hGb i (Or.inl hi)
  have hK : CochainComplex.KFlatBifunctor.KFlat (tensorPullbackBifunctor f).flip G :=
    CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE _ G b a fun n =>
      CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ (G.X n) n fun C hC => by
        have : PreservesFiniteLimits ((tensorPullbackBifunctor f).obj (G.X n)) :=
          preservesFiniteLimits_tensorPullbackFunctor f (G.X n) (hG n)
        have : PreservesFiniteColimits ((tensorPullbackBifunctor f).obj (G.X n)) :=
          Stacks.Cohomology.DerivedPullbackOfToposHom.preservesFiniteColimits_tensorPullback
            (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS f) (G.X n)
        intro i
        exact (hC i).map ((tensorPullbackBifunctor f).obj (G.X n))
  exact CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft (tensorPullbackBifunctor f) G
    ((CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ G).2 hK) q hq

end QuasiIso

/-- **The comparison is invertible at a bounded above complex of flat modules**: such a complex
computes `Lf^*` (Stacks 06YY) and its pullback is K-flat (Stacks 0G7E). -/
theorem isIso_tensorPullbackComplexNatTrans_app_of_isStrictlyLE
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) (n : ℤ)
    [P.IsStrictlyLE n]
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS Y).O) (P.X i)) :
    IsIso ((tensorPullbackComplexNatTrans f G).app P) := by
  have h1 : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.quotient _ _).obj P)) :=
    isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _
      (smallEtaleModuleKFlat_of_isStrictlyLE B S hS Y P n hflat)
  have h2 : IsIso ((smallEtaleToTensorNatTrans G).app ((pullbackComplexSmallEtale' f).obj P)) :=
    isIso_smallEtaleToTensorNatTrans_app _
      (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex_of_isStrictlyLE
        (smallEtaleRingedToposHom B S hS f) P n hflat)
  have hc : IsIso ((smallEtaleDerivedModulePullbackComplexComparison f).app P) := by
    dsimp only [smallEtaleDerivedModulePullbackComplexComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app]
    infer_instance
  dsimp only [tensorPullbackComplexNatTrans, tensorPullbackComplexComparisonAssoc,
    tensorPullbackComplexComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  repeat' (first | exact h2 | apply IsIso.comp_isIso' | apply Functor.map_isIso |
    exact Iso.isIso_inv ((Functor.associator _ _ _).app _) | infer_instance)

variable {f G} in
/-- **`𝒢^• ⊗^L Lf^*(ℱ[0]) ≅ 𝒢^• ⊗ f^*ℱ`** for `𝒢^•` bounded with terms flat over `Y`, at every
`𝒪_Y`-module `ℱ` (the first displayed equalities of the proof of Stacks 0A1M). -/
theorem isIso_tensorPullbackComplexNatTrans_app_single (a b : ℤ)
    (hGb : ∀ q : ℤ, q < a ∨ b < q → IsZero (G.X q))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    IsIso ((tensorPullbackComplexNatTrans f G).app ((CochainComplex.singleFunctor _ 0).obj F)) := by
  obtain ⟨P, q, hq, hP, hPflat⟩ :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.exists_flat_resolution_single
      (Y := smallEtaleRingedTopos B S hS Y) F
  have hP' := isIso_tensorPullbackComplexNatTrans_app_of_isStrictlyLE f G P 0 hPflat
  have hΨ : IsIso (DerivedCategory.Q.map ((tensorPullbackComplex f G).map q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_tensorPullbackComplex_map G a b hGb hG q hq)
  have hQq : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hnat := (tensorPullbackComplexNatTrans f G).naturality q
  have hc : IsIso ((DerivedCategory.Q ⋙ (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))).map q ≫
        (tensorPullbackComplexNatTrans f G).app _) := by
    rw [hnat]
    exact IsIso.comp_isIso' hP' hΨ
  have : IsIso ((DerivedCategory.Q ⋙ (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))).map q) := by
    rw [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ (smallEtaleDerivedModulePullback B S hS f ⋙
      (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G))).map q)
    ((tensorPullbackComplexNatTrans f G).app _)

end AlgebraicGeometry.Space

end
