module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.HomotopyColimitTensorSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.CategoryTheory.Functor.TensorDualHomTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidualNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHomMap

/-!
# Derived Homs out of duals of a system of perfect objects

Let `X` be an algebraic space and `E : ℕ ⥤ D(𝒪_X)` a system of perfect objects. With
`Lₙ = Eₙ^∨`, read on the equi-universe model of `X`, there is an isomorphism
`Eₙ ⊗^L K ≅ R𝓗om(Lₙ, K)` natural in `n` and in `K` (Stacks 08JJ, with the double-dual map
`Eₙ ⟶ Eₙ^∨∨`, which is invertible for `Eₙ` perfect). Hence part (1) of Stacks 0CRW follows from
part (2):

`RΓ(U, Lf^*K) = hocolim RHom_X(Lₙ, K)` functorially in `K ∈ D_QCoh(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleTensorDualHomTrans`: `E ⊗^L K ⟶ R𝓗om(E^∨, K)`, natural in
  `E` and `K`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleTensorDualHomTrans_app_of_isPerfect`.
* `AlgebraicGeometry.Space.exists_isHomotopyColimitCocone_derivedHom_of_tensor`.

## References

* [Stacks Project, Tag 0CRW](https://stacks.math.columbia.edu/tag/0CRW)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`E ⊗^L K ⟶ R𝓗om(E^∨, K)`, natural in `E` and `K`**, for `E^∨` the dual of `E` read on the
equi-universe model `M` of `X`: through the derived equivalence `e : D(𝒪_X) ≌ D(𝒪_M)`, the
comparison of the derived tensor products, the commutativity constraint, the double-dual map
and the map of Stacks 08JJ. -/
def smallEtaleTensorDualHomTrans (X : AlgebraicSpaces B S hS) :
    smallEtaleDerivedTensor B S hS X ⟶
      ((smallEtaleModelDerivedEquivalence B S hS X).functor ⋙
        ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)).flip.obj
          (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))).rightOp ⋙
        (smallEtaleModelDerivedEquivalence B S hS X).inverse.op) ⋙
      smallEtaleDerivedSheafHom B S hS X :=
  Functor.tensorDualHomTransport (smallEtaleModelDerivedEquivalence B S hS X)
    (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedStructureSheaf (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedTensorIso B S hS X)
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (smallEtaleModelRingedSite B S hS X.1 X.2)
      (RingedSite.canonicalRingedSiteDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2))).hom
    (RingedSite.derivedBidualTrans (smallEtaleModelRingedSite B S hS X.1 X.2)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2)))
    (RingedSite.derivedDualTensorSheafHomTrans (smallEtaleModelRingedSite B S hS X.1 X.2))

/-- **`E ⊗^L - ≅ R𝓗om(E^∨, -)` for `E` perfect** (Stacks 08JJ): the component of
`smallEtaleTensorDualHomTrans` at a perfect object is invertible. -/
theorem isIso_smallEtaleTensorDualHomTrans_app_of_isPerfect (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    IsIso ((smallEtaleTensorDualHomTrans X).app E) := by
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  let e := smallEtaleModelDerivedEquivalence B S hS X
  have hP := isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE
  exact (NatTrans.isIso_iff_isIso_app _).2 fun K ↦
    Functor.isIso_tensorDualHomTransportApp _ _ _ _ _ _ _ _ _ E K
    ((((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso M
      (RingedSite.canonicalRingedSiteDerivedTensorProduct M)).app (e.functor.obj E)).app
        (e.functor.obj K)).isIso_hom)
    (RingedSite.isIso_derivedBidual_of_isPerfect M
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct M) _ hP)
    (RingedSite.isIso_derivedDualTensorSheafHomMap_of_isPerfect M _ _
      (RingedSite.isPerfect_derivedDual M _ hP))

/-- **Stacks 0CRW (1) from (2).** Let `p : X ⟶ Spec A`, `q : U ⟶ Spec A` and `f : U ⟶ X` be
morphisms of algebraic spaces, `E` a system of perfect objects of `D(𝒪_X)` and
`ιₙ : RΓ(X, Eₙ ⊗^L -) ⟶ RΓ(U, Lf^* -)` natural maps exhibiting
`RΓ(U, Lf^*K) = hocolim RΓ(X, Eₙ ⊗^L K)` for every `K ∈ D_QCoh(𝒪_X)`. Then there is an inverse
system `L` of perfect objects (the duals `Lₙ = Eₙ^∨`) and natural maps
`RHom_X(Lₙ, -) ⟶ RΓ(U, Lf^* -)` exhibiting `RΓ(U, Lf^*K) = hocolim RHom_X(Lₙ, K)` for every such
`K`. -/
theorem exists_isHomotopyColimitCocone_derivedHom_of_tensor
    {U X : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (f : U ⟶ X)
    (p : X ⟶ schemeSpace T)
    (q : U ⟶ schemeSpace T)
    (E : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (E.obj n))
    (ι : ∀ n, (smallEtaleDerivedTensor B S hS X).obj (E.obj n) ⋙
        derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T ⟶
          smallEtaleDerivedModulePullback B S hS f ⋙ derivedModulePushforward B S hS q ⋙
            representedAffineDerivedSections B S hS T)
    (hι : ∀ K, QcohDerived B S hS X K →
        IsHomotopyColimitCocone
          (E ⋙ (smallEtaleDerivedTensor B S hS X).flip.obj K ⋙
            derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T)
          fun n ↦ (ι n).app K) :
    ∃ L : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (L.obj n)) ∧
      ∃ ι' : ∀ n, (smallEtaleDerivedSheafHom B S hS X).obj (op (L.obj (op n))) ⋙
          derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T ⟶
            smallEtaleDerivedModulePullback B S hS f ⋙ derivedModulePushforward B S hS q ⋙
              representedAffineDerivedSections B S hS T,
        ∀ K, QcohDerived B S hS X K →
          IsHomotopyColimitCocone
            (L.rightOp ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj K ⋙
              derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T)
            fun n ↦ (ι' n).app K := by
  let e := smallEtaleModelDerivedEquivalence B S hS X
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  let G := e.functor ⋙ ((RingedSite.derivedSheafHomBifunctor M).flip.obj
    (RingedSite.derivedStructureSheaf M)).rightOp ⋙ e.inverse.op
  let L : ℕᵒᵖ ⥤ DerivedCategory (Modules.{u, u} B S hS X.1 X.2) := (E ⋙ G).leftOp
  let RΓp := derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T
  have : ∀ n, IsIso ((Functor.whiskerLeft E (smallEtaleTensorDualHomTrans X)).app n) :=
    fun n ↦ isIso_smallEtaleTensorDualHomTrans_app_of_isPerfect X (E.obj n) (hE n)
  have : IsIso (Functor.whiskerLeft E (smallEtaleTensorDualHomTrans X)) :=
    NatIso.isIso_of_isIso_app _
  let Φ := asIso (Functor.whiskerLeft E (smallEtaleTensorDualHomTrans X))
  refine ⟨L, fun n ↦ isPerfect_smallEtaleModelDerivedEquivalence_inverse_obj B S hS X _
      (RingedSite.isPerfect_derivedDual M _
        (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X _ (hE n.unop))),
    fun n ↦ Functor.whiskerRight (Φ.app n).inv RΓp ≫ ι n, fun K hK ↦ ?_⟩
  let sys : L.rightOp ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj K ⋙ RΓp ≅
      E ⋙ (smallEtaleDerivedTensor B S hS X).flip.obj K ⋙ RΓp :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight Φ ((evaluation _ _).obj K)).symm RΓp
  exact (hι K hK).of_iso sys

end AlgebraicGeometry.Space

end
