module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftModels
public import StacksFrontier.CategoryTheory.Functor.TransportBifunctorComparisonCommShift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShiftTwo
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of Tag 079U commutes with the shift in the first variable

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. For a fixed `L ∈ D(𝒪_Y)`, the
canonical isomorphism

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`

of [Stacks, Tag 079U], `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`, is
compatible with the shift in `K`: as a morphism of functors of `K`, between
`(- ⊗^L L) ⋙ Lf^*` and `Lf^* ⋙ (- ⊗^L Lf^*L)`, it is a `CategoryTheory.NatTrans.CommShift`. The
derived tensor products carry `Stacks.Cohomology.DerivedPullbackTensor.derivedTensorCommShift₂Int`
and `Lf^*` its derived-functor shift.

The isomorphism is descended from `modelsComparison` along the localization `kFlatQY` of the
K-flat objects of the homotopy category, in both variables. The shift compatibility is therefore
tested after restricting the first variable along `kFlatQY`
(`CategoryTheory.NatTrans.commShift_of_whiskerLeft`) with the second variable moved to an object
in the image of `kFlatQY`
(`CategoryTheory.Functor.commShift_bifunctorComparisonFlip_of_iso`); there the isomorphism is
the first-variable component of `modelsComparison`, up to the isomorphisms pinning the curried
spellings, which is shift-compatible by `modelsComparisonCommShift₂`.

## Main results

* `derivedPullbackTensorIso_bifunctorComparisonFlip_commShift`: the isomorphism
  `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L`, as a morphism of functors of `K`, commutes with the shifts.

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

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The localization of the K-flat objects of the homotopy category is essentially surjective. -/
instance kFlatQY_essSurj : (kFlatQY (Y := Y)).EssSurj :=
  Localization.essSurj _ (CochainComplex.KFlatBifunctor.kFlatQuasiIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))

/-- A morphism against itself wrapped in identities. -/
theorem eq_id_comp_comp_id {C : Type*} [Category C] {A B : C} (a : A ⟶ B) :
    a = 𝟙 A ≫ a ≫ 𝟙 B := by
  simp

attribute [local instance] kFlatQPair_isLocalization in
/-- At a pair of K-flat objects the comparison of [Stacks, Tag 079U] is `modelsComparison`. -/
theorem derivedPullbackTensorIso_hom_app_kFlatQY (M₁ M₂ :
    (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    (derivedPullbackTensorIso f).hom.app ((kFlatQY (Y := Y)).obj M₁, (kFlatQY (Y := Y)).obj M₂) =
      (modelsComparison f).hom.app (M₁, M₂) := by
  change (Localization.liftNatTrans (kFlatQPair (Y := Y)) (kFlatQuasiIsoPair (Y := Y)) _ _
    (pullbackOfTensor f) (tensorOfPullbacks f) (modelsComparison f).hom).app
      ((kFlatQPair (Y := Y)).obj (M₁, M₂)) = _
  rw [Localization.liftNatTrans_app]
  exact (eq_id_comp_comp_id _).symm

/-- **The comparison at a second argument in the image of `kFlatQY`, restricted along `kFlatQY` in
the first, is the first-variable component of `modelsComparison`**, conjugated by the
isomorphisms pinning the curried spellings, whose components are identities. -/
theorem whiskerLeft_bifunctorComparisonFlip_eq (M₂ :
    (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    Functor.whiskerLeft (kFlatQY (Y := Y))
        (Functor.bifunctorComparisonFlip (derivedPullbackTensorIso f).hom
          ((kFlatQY (Y := Y)).obj M₂)) =
      ((Functor.CommShift₂.flipIso (curryModelsPullbackOfTensorIso f)).app M₂).hom ≫
        (Functor.curry.map (modelsComparison f).hom).flipApp M₂ ≫
          ((Functor.CommShift₂.flipIso (curryModelsTensorOfPullbacksIso f)).app M₂).inv := by
  ext M₁
  change (derivedPullbackTensorIso f).hom.app ((kFlatQY (Y := Y)).obj M₁,
    (kFlatQY (Y := Y)).obj M₂) = _
  rw [derivedPullbackTensorIso_hom_app_kFlatQY]
  exact eq_id_comp_comp_id _

/-- The comparison at a second argument in the image of `kFlatQY`, restricted along `kFlatQY` in
the first, read between the pinned curried spellings, commutes with the shift: it is conjugate to
the first-variable component of `modelsComparison` by isomorphisms which commute with the shift
for the transported data. -/
theorem whiskerLeft_bifunctorComparisonFlip_kFlatQY_commShift_pinned
    (M₂ : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    letI := curriedModelsPullbackOfTensor_commShift₂Int f
    letI := curriedModelsTensorOfPullbacks_commShift₂Int f
    NatTrans.CommShift (show (curriedModelsPullbackOfTensor f).flip.obj M₂ ⟶
      (curriedModelsTensorOfPullbacks f).flip.obj M₂ from
        Functor.whiskerLeft (kFlatQY (Y := Y))
          (Functor.bifunctorComparisonFlip (derivedPullbackTensorIso f).hom
            ((kFlatQY (Y := Y)).obj M₂))) ℤ := by
  let := curriedModelsPullbackOfTensor_commShift₂Int f
  let := curriedModelsTensorOfPullbacks_commShift₂Int f
  let := curryModelsPullbackOfTensor_commShift₂Int f
  let := curryModelsTensorOfPullbacks_commShift₂Int f
  have hθ := (modelsComparisonCommShift₂ f).commShift_flipApp M₂
  have := Functor.CommShift.ofIso_compatibility
    ((Functor.CommShift₂.flipIso (curryModelsPullbackOfTensorIso f)).app M₂) ℤ
  have := Functor.CommShift.ofIso_compatibility
    ((Functor.CommShift₂.flipIso (curryModelsTensorOfPullbacksIso f)).app M₂) ℤ
  exact NatTrans.commShift_of_eq_conj
    ((Functor.CommShift₂.flipIso (curryModelsPullbackOfTensorIso f)).app M₂)
    ((Functor.CommShift₂.flipIso (curryModelsTensorOfPullbacksIso f)).app M₂)
    ((Functor.curry.map (modelsComparison f).hom).flipApp M₂)
    (whiskerLeft_bifunctorComparisonFlip_eq f M₂)

/-- Equal commutation data on the second functor give equal data on the composite. -/
private theorem commShift_comp_congr {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ]
    {d₁ d₂ : G.CommShift ℤ} (h : d₁ = d₂) :
    (letI := d₁; Functor.CommShift.comp F G : (F ⋙ G).CommShift ℤ) =
      (letI := d₂; Functor.CommShift.comp F G) :=
  h ▸ rfl

/-- The flipped commutation datum of the source over the K-flat models, at the composite
spelling. -/
theorem curriedModelsPullbackOfTensor_commShiftFlipObj
    (M₂ : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    letI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
    letI := derivedTensorCommShift₂Int Y
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
    (show (kFlatQY (Y := Y) ⋙
          ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
            ((kFlatQY (Y := Y)).obj M₂) ⋙
          Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)).CommShift ℤ from
        (curriedModelsPullbackOfTensor_commShift₂Int f).commShiftFlipObj M₂) =
      Functor.CommShift.comp _ _ := by
  let := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  let := derivedTensorCommShift₂Int Y
  let : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
  let := derivedPullbackAdditive f
  exact commShift_comp_congr _ _
    (Functor.CommShift₂.postcompInt_commShiftFlipObj (C₁ := DerivedCategory (Modules Y))
      (C₂ := DerivedCategory (Modules Y)) (D := DerivedCategory (Modules Y))
      (D' := DerivedCategory (Modules X))
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      ((kFlatQY (Y := Y)).obj M₂))

/-- The flipped commutation datum of the target over the K-flat models, at the composite
spelling. -/
theorem curriedModelsTensorOfPullbacks_commShiftFlipObj
    (M₂ : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    letI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
    letI := derivedTensorCommShift₂Int X
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
    (show (kFlatQY (Y := Y) ⋙
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
              ((kFlatQY (Y := Y)).obj M₂)))).CommShift ℤ from
        (curriedModelsTensorOfPullbacks_commShift₂Int f).commShiftFlipObj M₂) =
      Functor.CommShift.comp _ _ := by
  let := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  let := derivedTensorCommShift₂Int X
  let : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
  exact commShift_comp_congr _ _
    (Functor.CommShift₂.precomp₁₂_commShiftFlipObj (C' := DerivedCategory (Modules Y))
      (C := DerivedCategory (Modules X)) (D := DerivedCategory (Modules X))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf) CommShift₂Setup.int
      ((kFlatQY (Y := Y)).obj M₂))

/-- The same, read between the composite spellings. -/
theorem whiskerLeft_bifunctorComparisonFlip_kFlatQY_commShift
    (M₂ : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    letI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
    letI := derivedTensorCommShift₂Int Y
    letI := derivedTensorCommShift₂Int X
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
    NatTrans.CommShift (Functor.whiskerLeft (kFlatQY (Y := Y))
      (Functor.bifunctorComparisonFlip (derivedPullbackTensorIso f).hom
        ((kFlatQY (Y := Y)).obj M₂))) ℤ :=
  NatTrans.commShift_of_eq_data (curriedModelsPullbackOfTensor_commShiftFlipObj f M₂)
    (curriedModelsTensorOfPullbacks_commShiftFlipObj f M₂) _
    (whiskerLeft_bifunctorComparisonFlip_kFlatQY_commShift_pinned f M₂)

/-- The comparison at a second argument in the image of `kFlatQY` commutes with the shift in the
first variable. -/
theorem bifunctorComparisonFlip_kFlatQY_commShift
    (M₂ : (CochainComplex.KFlatBifunctor.kFlatObjects
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).FullSubcategory) :
    letI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
    letI := derivedTensorCommShift₂Int Y
    letI := derivedTensorCommShift₂Int X
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
    NatTrans.CommShift (Functor.bifunctorComparisonFlip (derivedPullbackTensorIso f).hom
      ((kFlatQY (Y := Y)).obj M₂)) ℤ := by
  let := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  let := derivedTensorCommShift₂Int Y
  let := derivedTensorCommShift₂Int X
  let : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
  let : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
  exact NatTrans.commShift_of_whiskerLeft (kFlatQY (Y := Y)) _
    (whiskerLeft_bifunctorComparisonFlip_kFlatQY_commShift f M₂)

/-- **[Stacks, Tag 079U]: the comparison `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` commutes with the shift
in `K`**, at every fixed `L`. -/
theorem derivedPullbackTensorIso_bifunctorComparisonFlip_commShift
    (L : DerivedCategory (Modules Y)) :
    letI := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
    letI := derivedTensorCommShift₂Int Y
    letI := derivedTensorCommShift₂Int X
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
    letI : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
        L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
    NatTrans.CommShift (Functor.bifunctorComparisonFlip (derivedPullbackTensorIso f).hom L) ℤ := by
  let := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  let := derivedTensorCommShift₂Int Y
  let := derivedTensorCommShift₂Int X
  let : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj
      L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int Y).commShiftFlipObj L
  let : ∀ L, ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      L).CommShift ℤ := fun L => (derivedTensorCommShift₂Int X).commShiftFlipObj L
  exact Functor.commShift_bifunctorComparisonFlip_of_iso _
    ((kFlatQY (Y := Y)).objObjPreimageIso L).symm
    (bifunctorComparisonFlip_kFlatQY_commShift f ((kFlatQY (Y := Y)).objPreimage L))

end Stacks.Cohomology.DerivedPullbackTensor

end
