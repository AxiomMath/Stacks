module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectQuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointAmplitude
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointFlatProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelQuasiCompactTerminal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# The direct image of a perfect object to the point has finite Tor dimension

Let `T` be an affine object of the big fppf site, `R = Γ(T, 𝒪_T)`, and `f : X ⟶ T` a flat
morphism from a quasi-compact and quasi-separated algebraic space, read as the morphism of ringed
topoi `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model. For a perfect object `E` of
the model, `Rf_*E` has finite Tor dimension over the punctual ringed topos: this is the
Tor-amplitude half of the proof of [Stacks, Tag 0DKJ], the step of [Stacks, Tag 0CTM] that holds
over an arbitrary ring.

The argument is the source's.

* `X` being quasi-compact, the terminal object of the model is quasi-compact, so the perfect `E`
  has Tor amplitude in a fixed interval `[a, b]` (Stacks 08FZ, 08G8).
* By the projection formula for the flat `f` against a module in degree zero
  (`AlgebraicGeometry.Space.flatProjectionFormulaSingleIso`, Stacks 08IN),
  `Rf_*E ⊗^L_R M ≅ Rf_*(E ⊗^L (𝒪_X ⊗_R M))`; the right side lies in degrees `≥ a` because
  `E ⊗^L (𝒪_X ⊗_R M)` does and `Rf_*` does not lower a lower bound.
* `E` has quasi-coherent cohomology in degrees `≤ b`, so `Rf_*E` lies in degrees `≤ b + N` for the
  uniform bound `N` of
  `AlgebraicGeometry.Space.exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing`, and the
  derived tensor product with a module in degree zero is right t-exact.

So `Rf_*E` has Tor amplitude in `[a, b + N]`.

## Main results

* `AlgebraicGeometry.Space.exists_hasTorAmplitude_of_isPerfect_spacesEtaleModel`: a perfect
  object of the model of a quasi-compact space has Tor amplitude in a fixed interval.
* `AlgebraicGeometry.Space.exists_hasTorAmplitude_derivedPushforward_spacesEtaleModelToBaseRing`:
  `Rf_*E` has finite Tor dimension over the point.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

/-! ### The tensor instances on a diagonal ringed site, with their universes pinned -/

/-- `⊗_O` is additive in the first variable, on a ringed site whose morphisms, structure sheaf
and modules share the universe of its objects. This is
`Stacks.SheafOfModules.Tensor.sheafTensor_additive` with its universes pinned, which instance
search cannot do while they are metavariables. -/
theorem sheafTensor_additive_ringedSite (Z : RingedSite.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} Z.O

/-- `⊗_O` is additive in the second variable, universes pinned. -/
theorem sheafTensor_obj_additive_ringedSite (Z : RingedSite.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : RingedSite.Modules.{u, u, u} Z) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} Z.O M

/-- Total tensor complexes exist, universes pinned. -/
theorem hasMapBifunctor_sheafTensor_ringedSite (Z : RingedSite.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} Z) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor Z.O K L

attribute [local instance high] sheafTensor_additive_ringedSite sheafTensor_obj_additive_ringedSite
  hasMapBifunctor_sheafTensor_ringedSite

/-! ### Bounds across the module equivalence of the model -/

section Bounds

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The comparison of the model with `D(𝒪_X)` carries a vanishing homology object to one. -/
private theorem isZero_homology_mapDerivedCategory_spacesEtaleModelModulesEquiv
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj K)) :=
  ((spacesEtaleModelModulesEquiv B S hS X).functor.map_isZero h).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (spacesEtaleModelModulesEquiv B S hS X).functor i).app K)

/-- The comparison of the model with `D(𝒪_X)` preserves lower bounds. -/
theorem isGE_mapDerivedCategory_spacesEtaleModelModulesEquiv
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) (a : ℤ) (hK : K.IsGE a) :
    ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj K).IsGE a := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  exact fun i hi => isZero_homology_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X K i
    (hK i hi)

/-- The comparison of the model with `D(𝒪_X)` preserves upper bounds. -/
theorem isLE_mapDerivedCategory_spacesEtaleModelModulesEquiv
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) (b : ℤ) (hK : K.IsLE b) :
    ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj K).IsLE b := by
  rw [DerivedCategory.isLE_iff] at hK ⊢
  exact fun i hi => isZero_homology_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X K i
    (hK i hi)

/-- **A perfect object of the spaces-étale model of a quasi-compact space has Tor amplitude in a
fixed interval.** Perfect objects locally have finite Tor dimension (Stacks 08G8), and the
terminal object of the model is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompactObject_spacesEtaleModelTerminal`), so finitely many
intervals, hence one, suffice (Stacks 08FZ). -/
theorem exists_hasTorAmplitude_of_isPerfect_spacesEtaleModel
    (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    ∃ a b : ℤ, a ≤ b ∧ Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
        (spacesEtaleModelRingedTopos B S hS X).toRingedSite) E a b := by
  open Stacks.SheafOfModules.DerivedTensorProduct in
  exact (hasFiniteTorDimension_iff _ _).1
    (hasFiniteTorDimension_of_locallyHasFiniteTorDimension
      (spacesEtaleModelRingedTopos B S hS X).toRingedSite _ _ E
      (locallyHasFiniteTorDimension_of_isPerfect_anyUniverse.{u, u + 1}
        (X := (spacesEtaleModelRingedTopos B S hS X).toRingedSite)
        (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1} _) E hE)
      _ (isTerminal_spacesEtaleModelTerminal B S hS X)
      (isQuasiCompactObject_spacesEtaleModelTerminal B S hS X hX))

end Bounds

/-! ### Tor amplitude of the direct image to the point -/

section Point

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  {T : BigFppfOver B S hS}

/-- **The direct image of a perfect object to the point has finite Tor dimension.** Let `T` be
affine, `R = Γ(T, 𝒪_T)` and `f : X ⟶ T` flat with `X` quasi-compact and quasi-separated, read as
the morphism `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model. For every perfect
object `E` of the model, `Rf_*E` has Tor amplitude in some interval `[a, b']` over the punctual
ringed topos: if `E` has Tor amplitude in `[a, b]` then `[a, b + N]` works, `N` the uniform
upper bound of `Rf_*` on `D_QCoh`. -/
theorem exists_hasTorAmplitude_derivedPushforward_spacesEtaleModelToBaseRing
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    ∃ a b : ℤ, a ≤ b ∧ Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
        (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite)
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)
      a b := by
  obtain ⟨a, b, hab, hamp⟩ :=
    exists_hasTorAmplitude_of_isPerfect_spacesEtaleModel B S hS X hXqc E hE
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing B S hS X
    (baseRingHomOfMap f) hZ hXqc hXqs
  have hEq : qcohDerivedProp B S hS X
      ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E) :=
    derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS X.1 X.2 _
      (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X E hE)
  have hK : ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
      E).IsLE (b + N) :=
    hN E hEq b (isLE_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X E b
      (Stacks.SheafOfModules.DerivedTensorProduct.isLE_of_hasTorAmplitude
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
          (spacesEtaleModelRingedTopos B S hS X).toRingedSite) E hamp))
  refine ⟨a, max (b + N) a, le_max_right _ _, fun F i hi => ?_⟩
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · let eqv := (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of (baseRing B S hS T))).trans
      (pointModuleCatEquiv (R := baseRing B S hS T))
    let M := eqv.functor.obj F
    let G := (spacesEtaleModelModulesEquiv B S hS X).inverse.obj
      ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj M)
    have hGE : (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (spacesEtaleModelRingedTopos B S hS X).O).obj E).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)).IsGE a := by
      rw [DerivedCategory.isGE_iff]
      intro j hj
      exact (hamp G j fun h => not_le.2 hj h.1).of_iso
        ((DerivedCategory.homologyFunctor _ j).mapIso
          (((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso.{u + 1, u}
            (spacesEtaleModelRingedTopos B S hS X).toRingedSite).app E).app
              ((DerivedCategory.singleFunctor _ 0).obj G)).symm)
    have hpush := isGE_derivedPushforward_spacesEtaleModelToBaseRing B S hS X
      (baseRingHomOfMap f) _ a
      (isGE_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X _ a hGE)
    let e := ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso.{u + 1, u}
        (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite).app
          ((derivedPushforward
            (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)).app
            ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).O).obj
          ((derivedPushforward
            (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (eqv.unitIso.app F)) ≪≫
      flatProjectionFormulaSingleIso B S hS hZ hXqc hXqs f hflat hT E hEq M
    exact ((DerivedCategory.isGE_iff _ a).1 hpush i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)
  · exact (DerivedCategory.isLE_iff _ (b + N + 0)).1
      (Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
          (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite)
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)
        ((DerivedCategory.singleFunctor _ 0).obj F) (b + N) 0) i
      (by omega)

end Point

end AlgebraicGeometry.Space

end
