module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftRightComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftReduction
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPrecompIso
public import StacksFrontier.CategoryTheory.Shift.CommShiftCompOfEqData
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of Tag 079U on K-flat representatives commutes with the shifts

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. This file proves
`Stacks.Cohomology.DerivedPullbackTensor.ModelsComparisonCommShift₂ f`: the comparison
`Lf^*(QM₁ ⊗^L QM₂) ≅ Lf^*(QM₁) ⊗^L Lf^*(QM₂)` of [Stacks, Tag 079U] on pairs of K-flat objects
of the homotopy category, curried, commutes with the shifts in each variable.

By `Stacks.Cohomology.DerivedPullbackTensor.modelsComparisonCommShift₂_of_complexes` it suffices
to restrict both variables along the homotopy quotient from the K-flat cochain complexes. There
the component of `modelsComparison` at a pair `(K₁, K₂)` is
`modelsComparison_hom_app_kFlatQuotient`: `leftComparison` followed by the inverse of
`rightComparison`, conjugated by `kFlatQuotientCompQIso` in each variable. So in each variable
the restriction is a composite of eight shift-compatible one-variable factors:

* the conjugating isomorphisms, by `CategoryTheory.NatTrans.CommShift₂.precompPairIso_commShift₂`
  at the shift compatibility `kFlatQuotientCompQIso_commShift` of the bridge, together with the
  isomorphisms pinning the curried spellings, which are shift-compatible for the transported data
  by `CategoryTheory.Functor.CommShift₂.ofIsoInt_commShift₂`;
* `leftComparison`, by `leftComparisonCommShift₂'`;
* the inverse of `rightComparison`, which is invertible on K-flat complexes, by
  `rightComparisonCommShift₂`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.restrictBothMap_modelsComparison_eq`: the restriction
  of `modelsComparison` to pairs of K-flat complexes as the composite of the eight factors.
* `Stacks.Cohomology.DerivedPullbackTensor.modelsComparisonCommShiftOnComplexes`: the two
  conditions over K-flat complexes.
* `Stacks.Cohomology.DerivedPullbackTensor.modelsComparisonCommShift₂`: the shift compatibility
  of the comparison of [Stacks, Tag 079U] on K-flat representatives.

## Implementation notes

The two comparisons enter one variable at a time, through
`CategoryTheory.NatTrans.CommShift₂.restrictBothMap_app_commShift` and its companions, applied at
the object `ι K₁` exactly as the restriction spells it. Restating their two-variable statements
here, or reading them at `K₁.obj` rather than at `ι.obj K₁`, makes the kernel unfold the
commutation data of the curried bifunctors, and its check then exceeds the default budget.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)
open CochainComplex.KFlatBifunctor (kFlatComplexes kFlatQuotient kFlatQuotient_commShift
  kFlatQuotientCompQIso kFlatQuotientCompQIso_commShift)
open NatTrans.CommShift₂ (restrictBoth restrictBothMap precompPairIso comp_of_eq_data)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The inclusion of the K-flat complexes of `𝒪_Y`-modules into all complexes. -/
abbrev kFlatComplexesιY := (kFlatComplexesY (Y := Y)).ι

/-! ### The eight factors -/

/-- The first factor: the inverse of the pinning isomorphism of the source, restricted along the
homotopy quotient. -/
theorem modelsFactor₁_commShift₂ :
    letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
    letI := curryModelsPullbackOfTensor_commShift₂Int f
    letI := curriedModelsPullbackOfTensor_commShift₂Int f
    NatTrans.CommShift₂Int
      (restrictBothMap (kFlatQuotientY (Y := Y)) (curryModelsPullbackOfTensorIso f).inv) := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curriedModelsPullbackOfTensor_commShift₂Int f
  let := curryModelsPullbackOfTensor_commShift₂Int f
  let := Functor.CommShift₂.ofIsoInt_commShift₂ (curryModelsPullbackOfTensorIso f)
  let := NatTrans.CommShift₂.of_iso_invInt (curryModelsPullbackOfTensorIso f)
  infer_instance

/-- The second factor: the bridge `kFlatQuotientCompQIso` in both variables, on the source. -/
theorem modelsFactor₂_commShift₂ :
    letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
    letI := curriedPullbackOfTensor_commShift₂Int f
    NatTrans.CommShift₂Int (precompPairIso (G := curriedPullbackOfTensor f)
      (kFlatQuotientCompQIso (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf))).hom := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curriedPullbackOfTensor_commShift₂Int f
  let := kFlatQuotientCompQIso_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  infer_instance

/-- The third factor: the pinning isomorphism of the source of `leftComparison`, restricted
to K-flat complexes. -/
theorem modelsFactor₃_commShift₂ :
    letI := curryComplexesPullbackOfTensor_commShift₂Int f
    letI := curriedComplexesPullbackOfTensor_commShift₂Int f
    NatTrans.CommShift₂Int
      (restrictBothMap (kFlatComplexesιY (Y := Y)) (curryComplexesPullbackOfTensorIso f).hom) := by
  let := curriedComplexesPullbackOfTensor_commShift₂Int f
  let := curryComplexesPullbackOfTensor_commShift₂Int f
  let := Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesPullbackOfTensorIso f)
  infer_instance

/-- The fourth factor in the second variable: `leftComparison`, restricted to K-flat complexes,
at a fixed K-flat complex in the first variable. -/
theorem modelsFactor₄_app (K₁ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    letI := curryComplexesPullbackOfTensor_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (leftComparison f))).app K₁) ℤ :=
  let := curryComplexesPullbackOfTensor_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  NatTrans.CommShift₂.restrictBothMap_app_commShift _ _ K₁
    ((leftComparisonCommShift₂' f).commShift_app ((kFlatComplexesιY (Y := Y)).obj K₁))

/-- The fourth factor in the first variable. -/
theorem modelsFactor₄_flipApp (K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    letI := curryComplexesPullbackOfTensor_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (leftComparison f))).flipApp K₂) ℤ :=
  let := curryComplexesPullbackOfTensor_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  NatTrans.CommShift₂.restrictBothMap_flipApp_commShift _ _ K₂
    ((leftComparisonCommShift₂' f).commShift_flipApp ((kFlatComplexesιY (Y := Y)).obj K₂))

/-- `rightComparison` is invertible on pairs of K-flat complexes. -/
instance isIso_restrictBothMap_rightComparison :
    IsIso (restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f))) := by
  have h₂ : ∀ K₁ K₂, IsIso (((restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f))).app K₁).app K₂) := fun K₁ K₂ =>
    isIso_rightComparison_app f K₁.obj K₂.obj K₁.property K₂.property
  have h₁ : ∀ K₁, IsIso ((restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f))).app K₁) := fun K₁ =>
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (h₂ K₁)
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ h₁

/-- The fifth factor in the second variable: the inverse of `rightComparison`, restricted to
K-flat complexes, at a fixed K-flat complex in the first variable. -/
theorem modelsFactor₅_app (K₁ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    letI := curryComplexesTensorOfPullbacks_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((inv (restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f)))).app K₁) ℤ :=
  let := curryComplexesTensorOfPullbacks_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  NatTrans.CommShift₂.restrictBothMap_inv_app_commShift _ _ K₁
    ((rightComparisonCommShift₂ f).commShift_app ((kFlatComplexesιY (Y := Y)).obj K₁))

/-- The fifth factor in the first variable. -/
theorem modelsFactor₅_flipApp (K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    letI := curryComplexesTensorOfPullbacks_commShift₂Int f
    letI := curryComplexesTotalPullback_commShift₂Int f
    NatTrans.CommShift ((inv (restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f)))).flipApp K₂) ℤ :=
  let := curryComplexesTensorOfPullbacks_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  NatTrans.CommShift₂.restrictBothMap_inv_flipApp_commShift _ _ K₂
    ((rightComparisonCommShift₂ f).commShift_flipApp ((kFlatComplexesιY (Y := Y)).obj K₂))

/-- The sixth factor: the inverse of the pinning isomorphism of the source of
`rightComparison`, restricted to K-flat complexes. -/
theorem modelsFactor₆_commShift₂ :
    letI := curryComplexesTensorOfPullbacks_commShift₂Int f
    letI := curriedComplexesTensorOfPullbacks_commShift₂Int f
    NatTrans.CommShift₂Int
      (restrictBothMap (kFlatComplexesιY (Y := Y))
        (curryComplexesTensorOfPullbacksIso f).inv) := by
  let := curriedComplexesTensorOfPullbacks_commShift₂Int f
  let := curryComplexesTensorOfPullbacks_commShift₂Int f
  let := Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesTensorOfPullbacksIso f)
  let := NatTrans.CommShift₂.of_iso_invInt (curryComplexesTensorOfPullbacksIso f)
  infer_instance

/-- The seventh factor: the inverse bridge in both variables, on the target. -/
theorem modelsFactor₇_commShift₂ :
    letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
    letI := curriedTensorOfPullbacks_commShift₂Int f
    NatTrans.CommShift₂Int (precompPairIso (G := curriedTensorOfPullbacks f)
      (kFlatQuotientCompQIso (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).symm).hom := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curriedTensorOfPullbacks_commShift₂Int f
  let := kFlatQuotientCompQIso_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  infer_instance

/-- The eighth factor: the pinning isomorphism of the target, restricted along the homotopy
quotient. -/
theorem modelsFactor₈_commShift₂ :
    letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
    letI := curryModelsTensorOfPullbacks_commShift₂Int f
    letI := curriedModelsTensorOfPullbacks_commShift₂Int f
    NatTrans.CommShift₂Int
      (restrictBothMap (kFlatQuotientY (Y := Y)) (curryModelsTensorOfPullbacksIso f).hom) := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curriedModelsTensorOfPullbacks_commShift₂Int f
  let := curryModelsTensorOfPullbacks_commShift₂Int f
  let := Functor.CommShift₂.ofIsoInt_commShift₂ (curryModelsTensorOfPullbacksIso f)
  infer_instance

/-! ### The assembly -/

/-- `(K, L) ↦ Lf^*(K ⊗^L L)` on a pair of morphisms, through the pinned curried form. -/
theorem pullbackOfTensor_map_prod {K K' L L' : DerivedCategory (Modules Y)} (x : K ⟶ K')
    (y : L ⟶ L') :
    (pullbackOfTensor f).map (x ×ₘ y) =
      ((curriedPullbackOfTensor f).map x).app L ≫ ((curriedPullbackOfTensor f).obj K').map y :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map_comp _ _

/-- `(K, L) ↦ Lf^*K ⊗^L Lf^*L` on a pair of morphisms, through the pinned curried form. -/
theorem tensorOfPullbacks_map_prod {K K' L L' : DerivedCategory (Modules Y)} (x : K ⟶ K')
    (y : L ⟶ L') :
    (tensorOfPullbacks f).map (x ×ₘ y) =
      ((curriedTensorOfPullbacks f).map x).app L ≫ ((curriedTensorOfPullbacks f).obj K').map y :=
  rfl

/-- The right comparison is invertible at a pair of K-flat complexes. -/
instance isIso_rightComparison_app_kFlat (K₁ K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    IsIso ((rightComparison f).app (K₁.obj, K₂.obj)) :=
  isIso_rightComparison_app f K₁.obj K₂.obj K₁.property K₂.property

/-- The components of the inverse of the right comparison on pairs of K-flat complexes. -/
theorem inv_restrictBothMap_rightComparison_app_app
    (K₁ K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    ((inv (restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f)))).app K₁).app K₂ =
      inv ((rightComparison f).app (K₁.obj, K₂.obj)) :=
  IsIso.eq_inv_of_hom_inv_id <| congrArg (fun t => NatTrans.app (NatTrans.app t K₁) K₂)
    (IsIso.hom_inv_id (restrictBothMap (kFlatComplexesιY (Y := Y))
      (Functor.curry.map (rightComparison f))))

/-- The components of the inverse of `curryModelsPullbackOfTensorIso f` are identities. -/
theorem curryModelsPullbackOfTensorIso_inv_app_app (K L) :
    ((curryModelsPullbackOfTensorIso f).inv.app K).app L = 𝟙 _ :=
  rfl

/-- The components of `curryModelsTensorOfPullbacksIso f` are identities. -/
theorem curryModelsTensorOfPullbacksIso_hom_app_app (K L) :
    ((curryModelsTensorOfPullbacksIso f).hom.app K).app L = 𝟙 _ :=
  rfl

/-- The components of `curryComplexesPullbackOfTensorIso f` are identities. -/
theorem curryComplexesPullbackOfTensorIso_hom_app_app (K L : CochainComplex (Modules Y) ℤ) :
    ((curryComplexesPullbackOfTensorIso f).hom.app K).app L = 𝟙 _ :=
  Category.id_comp (𝟙 _)

/-- The components of the inverse of `curryComplexesTensorOfPullbacksIso f` are identities. -/
theorem curryComplexesTensorOfPullbacksIso_inv_app_app (K L : CochainComplex (Modules Y) ℤ) :
    ((curryComplexesTensorOfPullbacksIso f).inv.app K).app L = 𝟙 _ :=
  Category.id_comp (𝟙 _)

/-- A composite of four morphisms against the same composite interleaved with identities. -/
theorem comp_eq_id_comp_interleaved {C : Type*} [Category C] {A B D E F : C} (a : A ⟶ B)
    (l : B ⟶ D) (r : D ⟶ E) (b : E ⟶ F) :
    a ≫ (l ≫ r) ≫ b = 𝟙 A ≫ a ≫ 𝟙 B ≫ l ≫ r ≫ 𝟙 E ≫ b ≫ 𝟙 F := by
  simp

/-- **The restriction of `modelsComparison` to pairs of K-flat complexes is the composite of the
eight factors.** On components this is `modelsComparison_hom_app_kFlatQuotient`: the pinning
isomorphisms have identity components and the two bridges contribute the conjugation by
`kFlatQuotientCompQIso` in each variable. -/
theorem restrictBothMap_modelsComparison_eq :
    restrictBothMap (kFlatQuotientY (Y := Y)) (Functor.curry.map (modelsComparison f).hom) =
      restrictBothMap (kFlatQuotientY (Y := Y)) (curryModelsPullbackOfTensorIso f).inv ≫
        (precompPairIso (G := curriedPullbackOfTensor f)
          (kFlatQuotientCompQIso (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf))).hom ≫
        restrictBothMap (kFlatComplexesιY (Y := Y)) (curryComplexesPullbackOfTensorIso f).hom ≫
        restrictBothMap (kFlatComplexesιY (Y := Y)) (Functor.curry.map (leftComparison f)) ≫
        inv (restrictBothMap (kFlatComplexesιY (Y := Y))
          (Functor.curry.map (rightComparison f))) ≫
        restrictBothMap (kFlatComplexesιY (Y := Y)) (curryComplexesTensorOfPullbacksIso f).inv ≫
        (precompPairIso (G := curriedTensorOfPullbacks f)
          (kFlatQuotientCompQIso (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).symm).hom ≫
        restrictBothMap (kFlatQuotientY (Y := Y)) (curryModelsTensorOfPullbacksIso f).hom := by
  ext K₁ K₂
  change (modelsComparison f).hom.app ((kFlatQuotientY (Y := Y)).obj K₁,
      (kFlatQuotientY (Y := Y)).obj K₂) =
    ((restrictBothMap (kFlatQuotientY (Y := Y)) (curryModelsPullbackOfTensorIso f).inv).app
        K₁).app K₂ ≫
      (((precompPairIso (G := curriedPullbackOfTensor f)
        (kFlatQuotientCompQIso (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf))).hom.app
          K₁).app K₂) ≫
      ((restrictBothMap (kFlatComplexesιY (Y := Y))
        (curryComplexesPullbackOfTensorIso f).hom).app K₁).app K₂ ≫
      ((restrictBothMap (kFlatComplexesιY (Y := Y))
        (Functor.curry.map (leftComparison f))).app K₁).app K₂ ≫
      ((inv (restrictBothMap (kFlatComplexesιY (Y := Y))
        (Functor.curry.map (rightComparison f)))).app K₁).app K₂ ≫
      ((restrictBothMap (kFlatComplexesιY (Y := Y))
        (curryComplexesTensorOfPullbacksIso f).inv).app K₁).app K₂ ≫
      (((precompPairIso (G := curriedTensorOfPullbacks f)
        (kFlatQuotientCompQIso (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).symm).hom.app
          K₁).app K₂) ≫
      ((restrictBothMap (kFlatQuotientY (Y := Y)) (curryModelsTensorOfPullbacksIso f).hom).app
        K₁).app K₂
  simp only [modelsComparison_hom_app_kFlatQuotient, pullbackOfTensor_map_prod,
    tensorOfPullbacks_map_prod, inv_restrictBothMap_rightComparison_app_app,
    NatTrans.CommShift₂.precompPairIso_hom_app_app,
    NatTrans.CommShift₂.restrictBothMap_app_app, curryModelsPullbackOfTensorIso_inv_app_app,
    curryModelsTensorOfPullbacksIso_hom_app_app, curryComplexesPullbackOfTensorIso_hom_app_app,
    curryComplexesTensorOfPullbacksIso_inv_app_app, Functor.curry_map_app_app, Iso.symm_hom]
  exact comp_eq_id_comp_interleaved _ _ _ _

/-- **The second-variable condition over K-flat complexes**: at a fixed K-flat complex `K₁`, the
restriction of `modelsComparison` along the homotopy quotient commutes with the shift in the
second variable. It is the composite of the eight factors at `K₁`. -/
theorem modelsComparison_restrict_app_commShift (K₁ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
    letI := curryModelsPullbackOfTensor_commShift₂Int f
    letI := curryModelsTensorOfPullbacks_commShift₂Int f
    NatTrans.CommShift (Functor.whiskerLeft (kFlatQuotientY (Y := Y))
      ((Functor.curry.map (modelsComparison f).hom).app ((kFlatQuotientY (Y := Y)).obj K₁))) ℤ := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curryModelsPullbackOfTensor_commShift₂Int f
  let := curryModelsTensorOfPullbacks_commShift₂Int f
  change NatTrans.CommShift ((restrictBothMap (kFlatQuotientY (Y := Y))
    (Functor.curry.map (modelsComparison f).hom)).app K₁) ℤ
  rw [restrictBothMap_modelsComparison_eq f]
  exact NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₁_commShift₂ f).commShift_app K₁)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₂_commShift₂ f).commShift_app K₁)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₃_commShift₂ f).commShift_app K₁)
    (NatTrans.commShift_comp_of_eq_data _ _ (modelsFactor₄_app f K₁)
    (NatTrans.commShift_comp_of_eq_data _ _ (modelsFactor₅_app f K₁)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₆_commShift₂ f).commShift_app K₁)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₇_commShift₂ f).commShift_app K₁)
      ((modelsFactor₈_commShift₂ f).commShift_app K₁)))))))

/-- **The first-variable condition over K-flat complexes**, the mirror of
`modelsComparison_restrict_app_commShift`. -/
theorem modelsComparison_restrict_flipApp_commShift
    (K₂ : (kFlatComplexesY (Y := Y)).FullSubcategory) :
    letI := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
    letI := curryModelsPullbackOfTensor_commShift₂Int f
    letI := curryModelsTensorOfPullbacks_commShift₂Int f
    NatTrans.CommShift (Functor.whiskerLeft (kFlatQuotientY (Y := Y))
      ((Functor.curry.map (modelsComparison f).hom).flipApp
        ((kFlatQuotientY (Y := Y)).obj K₂))) ℤ := by
  let := kFlatQuotient_commShift (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
  let := curryModelsPullbackOfTensor_commShift₂Int f
  let := curryModelsTensorOfPullbacks_commShift₂Int f
  change NatTrans.CommShift ((restrictBothMap (kFlatQuotientY (Y := Y))
    (Functor.curry.map (modelsComparison f).hom)).flipApp K₂) ℤ
  rw [restrictBothMap_modelsComparison_eq f]
  exact NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₁_commShift₂ f).commShift_flipApp K₂)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₂_commShift₂ f).commShift_flipApp K₂)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₃_commShift₂ f).commShift_flipApp K₂)
    (NatTrans.commShift_comp_of_eq_data _ _ (modelsFactor₄_flipApp f K₂)
    (NatTrans.commShift_comp_of_eq_data _ _ (modelsFactor₅_flipApp f K₂)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₆_commShift₂ f).commShift_flipApp K₂)
    (NatTrans.commShift_comp_of_eq_data _ _ ((modelsFactor₇_commShift₂ f).commShift_flipApp K₂)
      ((modelsFactor₈_commShift₂ f).commShift_flipApp K₂)))))))

/-- **`ModelsComparisonCommShiftOnComplexes` holds**: its two conjuncts are
`modelsComparison_restrict_app_commShift` and `modelsComparison_restrict_flipApp_commShift`. -/
theorem modelsComparisonCommShiftOnComplexes : ModelsComparisonCommShiftOnComplexes f :=
  ⟨fun K₁ => modelsComparison_restrict_app_commShift f K₁,
    fun K₂ => modelsComparison_restrict_flipApp_commShift f K₂⟩

/-- **The comparison of [Stacks, Tag 079U] on K-flat representatives commutes with the shifts in
both variables.** This is `modelsComparisonCommShift₂_of_complexes` at
`modelsComparisonCommShiftOnComplexes`. -/
theorem modelsComparisonCommShift₂ : ModelsComparisonCommShift₂ f :=
  modelsComparisonCommShift₂_of_complexes f (modelsComparisonCommShiftOnComplexes f)

end Stacks.Cohomology.DerivedPullbackTensor

end
