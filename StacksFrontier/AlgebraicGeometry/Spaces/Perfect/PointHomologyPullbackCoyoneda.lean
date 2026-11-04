module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PointDerivedTensorHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.ProjectionFormulaDualHom
public import StacksFrontier.Homology.PseudoCoherent.RingPowerComplexCriterion
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# Cohomology of `Rf_*P^∨ ⊗^L K` over the point as maps out of a perfect object

Let `f : X ⟶ (pt, R)` be a morphism of ringed topoi presented by a morphism of sites, let `P` be
a perfect object of `D(𝒪_X)` and suppose that the projection-formula map of Stacks 0B56 at
`P^∨` is invertible. Write `L = Rf_*P^∨`. This file identifies, naturally in `K ∈ D(pt, R)`,

  `Hⁱ(L ⊗^L K) ≅ Hom_{D(𝒪_X)}(P, Lf^*(K[i]))`,

the cohomology being read in `D(R)` through `AlgebraicGeometry.Space.pointDerivedEquiv`. It is
the computation of `Hⁱ(RΓ(X, P^∨) ⊗^L_R M)` used in the proof of Stacks 0CTM:

* `Hom(P, Lf^*K) ≅ Hom(𝒪, L ⊗^L K)` naturally in `K` (Stacks 08JJ, the adjunction `Lf^* ⊣ Rf_*`
  and the projection formula), the first part of
  `Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaIso` which needs no
  perfectness of `L`;
* `Hⁱ(M) ≅ Hom_{D(R)}(R[-i], M)` for every `M ∈ D(R)`, `R` being projective (Stacks 06XS and the
  truncation triangle, `DerivedCategory.homologyFromSingleAddEquiv`);
* `L ⊗^L -` commutes with shifts.

## Main results

* `Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaTensorIso`.
* `AlgebraicGeometry.Space.moduleCatSingleCoyonedaHomologyIso`: `Hom_{D(R)}(R[-q], -) ≅ Hᵠ(-)`.
* `AlgebraicGeometry.Space.pointHomologyShiftCoyonedaIso`:
  `Hⁱ(pointDerivedEquiv M) ≅ Hom(𝒪, M[i])`.
* `AlgebraicGeometry.Space.pointHomologyTensorPullbackCoyonedaIso`.

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace Stacks.Cohomology.ProjectionFormulaDualHom

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{u}]
  [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Y.C, (Y.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : Y.C, (Y.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [(sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **Maps out of a perfect object into a derived pullback are maps out of the structure sheaf
into a tensor product with `Rf_*P^∨`.** Let `P` be perfect on `X` and let the projection-formula
map of Stacks 0B56 at `P^∨` be invertible at every `K`. Then
`Hom(P, Lf^*K) ≅ Hom(𝒪_Y, Rf_*P^∨ ⊗^L K)`, naturally in `K`: Stacks 08JJ on `X`, the adjunction
`Lf^* ⊣ Rf_*` with `Lf^*𝒪_Y = 𝒪_X`, and the projection formula. -/
def derivedPullbackCoyonedaTensorIso
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hP : X.toRingedSite.IsPerfect P)
    (hpf : ∀ K, IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos
      (derivedDual X.toRingedSite P) K)) :
    derivedPullback f ⋙ coyoneda.obj (op P) ≅
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O).obj
          ((derivedPushforward f).obj (derivedDual X.toRingedSite P)) ⋙
        coyoneda.obj (op (derivedStructureSheaf Y.toRingedSite)) :=
  Functor.isoWhiskerLeft (derivedPullback f) (coyonedaDualTensorIso X.toRingedSite P hP).symm ≪≫
    Functor.isoWhiskerLeft (derivedPullback f)
      (Functor.isoWhiskerLeft _ (coyoneda.mapIso
        (Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso f hmos).op)) ≪≫
    Functor.isoWhiskerLeft (derivedPullback f) (Functor.isoWhiskerLeft _
      ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).compCoyonedaIso.app
        (op (derivedStructureSheaf Y.toRingedSite)))) ≪≫
    Functor.isoWhiskerLeft (derivedPullback f) (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (projectionFormulaNatIso f hmos _ hpf) _

end Stacks.Cohomology.ProjectionFormulaDualHom

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance high] sheafTensor_additive_ringedSite sheafTensor_obj_additive_ringedSite

section Point

variable {R : Type u} [CommRing R]

/-- **`R[-q]` corepresents `Hᵠ` on `D(R)`**: `Hom_{D(R)}(R[-q], M) ≅ Hᵠ(M)` naturally in `M`, the
ring being a projective module (`DerivedCategory.homologyFromSingleAddEquiv`) and maps out of
`R` being elements. -/
def moduleCatSingleCoyonedaHomologyIso (q : ℤ) :
    coyoneda.obj (op ((DerivedCategory.singleFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R))) ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) q ⋙ forget (ModuleCat.{u} R) ⋙
        uliftFunctor.{u + 1} :=
  haveI : Projective (ModuleCat.of R R) :=
    (IsProjective.iff_projective (R := R) (P := ModuleCat.of R R)).1 inferInstance
  NatIso.ofComponents
    (fun M => ((DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of R R) M q).toEquiv.trans
      ((ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R R _).toEquiv).trans
        Equiv.ulift.symm)).toIso)
    (fun {M M'} g => by
      ext a
      exact congrArg ULift.up (congrArg (fun φ => φ.hom (1 : R))
        (DerivedCategory.homologyFromSingleAddEquiv_comp (ModuleCat.of R R) M q a g)))

/-- `R` placed in degree `-q`, carried to the point, is the structure sheaf placed in degree zero
and shifted by `-q`. -/
def pointDerivedEquivInverseSingleIso (q : ℤ) :
    (DerivedCategory.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0 ⋙
        shiftFunctor _ (-q)).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (pointRingedTopos (CommRingCat.of R)).O)) ≅
      (pointDerivedEquiv (R := R)).inverse.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)) :=
  let e := baseRingPointModulesEquiv (R := R)
  let hunit : e.inverse.obj (ModuleCat.of R R) ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos (CommRingCat.of R)).O) :=
    e.inverse.mapIso ((show ModuleCat.of R (Shrink.{u} R) ≅ ModuleCat.of R R from
        (Shrink.linearEquiv R R).toModuleIso).symm ≪≫
        baseRingPointModulesEquivUnitIso.symm) ≪≫ e.unitIso.symm.app _
  ((DerivedCategory.singleFunctors (pointRingedTopos (CommRingCat.of R)).Modules).shiftIso
      (-q) q 0 (by omega)).app _ ≪≫
    (DerivedCategory.singleFunctor _ q).mapIso hunit.symm ≪≫
    ((e.inverse.mapDerivedCategorySingleFunctor q).app (ModuleCat.of R R)).symm

/-- **`Hⁱ(pointDerivedEquiv M) ≅ Hom(𝒪, M[i])`, naturally in `M ∈ D(pt, R)`**: in `D(R)` the
cohomology is corepresented by `R[-i]`
(`AlgebraicGeometry.Space.moduleCatSingleCoyonedaHomologyIso`), which corresponds to `𝒪[0][-i]`
on the point. -/
def pointHomologyShiftCoyonedaIso (i : ℤ) :
    (pointDerivedEquiv (R := R)).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) i ⋙
        forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1} ≅
      shiftFunctor (DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) i ⋙
        coyoneda.obj (op (RingedSite.derivedStructureSheaf
          (pointRingedTopos (CommRingCat.of R)).toRingedSite)) :=
  let A := (DerivedCategory.singleFunctor (ModuleCat.{u} R) i).obj (ModuleCat.of R R)
  let D := DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules
  Functor.isoWhiskerLeft (pointDerivedEquiv (R := R)).functor
      (moduleCatSingleCoyonedaHomologyIso i).symm ≪≫
    ((pointDerivedEquiv (R := R)).symm.toAdjunction.compCoyonedaIso.app (op A)).symm ≪≫
    coyoneda.mapIso (pointDerivedEquivInverseSingleIso i).op ≪≫
    (shiftEquiv D i).symm.toAdjunction.compCoyonedaIso.app
      (op (RingedSite.derivedStructureSheaf (pointRingedTopos (CommRingCat.of R)).toRingedSite))

end Point

section Spaces

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

attribute [local instance] hasCoproducts_derivedCategory_point
  hasCoproducts_derivedCategory_spacesEtaleModel

/-- **`Hⁱ(RΓ(X, P^∨) ⊗^L K) ≅ Hom(P, Lf^*(K[i]))`, naturally in `K ∈ D(pt, R)`.** Let
`f : X ⟶ T` be flat with `T` affine and `X` quasi-compact and quasi-separated, `R = Γ(T, 𝒪_T)`,
and let `P` be perfect on the spaces-étale model of `X`. With `L = Rf_*P^∨` (the derived direct
image along `X ⟶ (pt, R)`), the `i`-th cohomology of `L ⊗^L K`, read in `D(R)`, is
`Hom(P, Lf^*(K[i]))`. -/
def pointHomologyTensorPullbackCoyonedaIso (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hP : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect P) (i : ℤ) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    (pointDerivedTensor (R := baseRing B S hS T)).obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
          (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite P)) ⋙
        (pointDerivedEquiv (R := baseRing B S hS T)).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing B S hS T)) i ⋙
        forget (ModuleCat.{u} (baseRing B S hS T)) ⋙ uliftFunctor.{u + 1} ≅
      shiftFunctor _ i ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
        coyoneda.obj (op P) :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  let f' := spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
  let hmos := isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
  let L := (derivedPushforward f').obj
    (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite P)
  let TL := (pointDerivedTensor (R := baseRing B S hS T)).obj L
  let O := coyoneda.obj (op (RingedSite.derivedStructureSheaf
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite))
  have hpf : ∀ K, IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap f'
      hmos (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite P) K) :=
    fun K => isIso_projectionFormulaMap_spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
      hZ hXqc hXqs _
      (derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS X.1 X.2 _
        (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X _
          (RingedSite.isPerfect_derivedDual _ _ hP))) K
  Functor.isoWhiskerLeft TL (pointHomologyShiftCoyonedaIso i) ≪≫
    (Functor.associator TL (shiftFunctor _ i) O).symm ≪≫
    Functor.isoWhiskerRight (TL.commShiftIso i).symm O ≪≫
    Functor.associator (shiftFunctor _ i) TL O ≪≫
    Functor.isoWhiskerLeft (shiftFunctor _ i)
      (Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaTensorIso f' hmos P hP
        hpf).symm

/-- **`RΓ(X, P^∨)` is pseudo-coherent once `M ↦ Hom(P, Lf^*(M[0][i]))` commutes with products of
copies of `R`.** Let `f : X ⟶ T` be flat with `T` affine and `X` quasi-compact and
quasi-separated, `R = Γ(T, 𝒪_T)`, and let `P` be perfect on the spaces-étale model of `X`. If for
every set `A` and every `i` the functor `M ↦ Hom(P, Lf^*(M[0][i]))` on `R`-modules preserves the
product `∏_A R`, then the image of `L = Rf_*P^∨` in `D(R)` is pseudo-coherent.

`L` is bounded above, so it is represented by a bounded above complex `E` of projective modules,
and `Hⁱ(E ⊗_R M) ≅ Hⁱ(L ⊗^L M[0]) ≅ Hom(P, Lf^*(M[0][i]))` naturally in `M`
(`AlgebraicGeometry.Space.pointDerivedTensorHomologyIso`,
`AlgebraicGeometry.Space.pointHomologyTensorPullbackCoyonedaIso`); the criterion
`StacksDraft.PseudoCoherence.isPseudoCoherent_of_preservesLimit_homology_tensor` applies. -/
theorem isPseudoCoherent_pointDerivedEquiv_derivedPushforward_derivedDual_of_preservesLimit
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hP : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect P)
    (hprod : letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
      ∀ (A : Type u) (i : ℤ),
        PreservesLimit (Discrete.functor fun _ : A => ModuleCat.of (baseRing B S hS T)
            (baseRing B S hS T))
          ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
            DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
            derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
            coyoneda.obj (op P))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
          (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite P))) := by
  let := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  let R := baseRing B S hS T
  let e := baseRingPointModulesEquiv (R := R)
  let L := (derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
    (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite P)
  obtain ⟨c, hc⟩ :=
    exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing_of_isPerfect B S hS hZ hXqc hXqs
      (baseRingHomOfMap f) _ (RingedSite.isPerfect_derivedDual _ _ hP)
  obtain ⟨K₀, hK₀, ⟨eK₀⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE L c
  let K₁ := (e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀
  have : CochainComplex.IsStrictlyLE K₁ c := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => e.functor.map_isZero (K₀.isZero_of_isStrictlyLE c n hn)
  obtain ⟨E, b, π, hEb, hEp, hπ⟩ := StacksDraft.TorAmplitude.exists_projective_resolution K₁ c
  have hflatE : ∀ n, Module.Flat R (E.X n) := fun n =>
    have := (IsProjective.iff_projective (R := R) (P := E.X n)).2 (hEp n)
    inferInstance
  -- `L ≅ Q(E')` on the point, `E'` the complex `E` carried to the point.
  let iE : DerivedCategory.Q.obj E ≅ (pointDerivedEquiv (R := R)).functor.obj L :=
    (asIso (DerivedCategory.Q.map π)) ≪≫
      ((e.functor.mapDerivedCategoryFactors).app K₀).symm ≪≫
      (pointDerivedEquiv (R := R)).functor.mapIso eK₀.symm
  let j : DerivedCategory.Q.obj ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅
      L :=
    (e.inverse.mapDerivedCategoryFactors.app E).symm ≪≫
      e.inverse.mapDerivedCategory.mapIso iE ≪≫ ((pointDerivedEquiv (R := R)).unitIso.app L).symm
  refine StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    (StacksDraft.PseudoCoherence.isPseudoCoherent_of_preservesLimit_homology_tensor E b hEp
      (fun A i => ?_)) iE
  let G := e.inverse ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    (pointDerivedTensor (R := R)).obj (DerivedCategory.Q.obj
      ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) ⋙
    (pointDerivedEquiv (R := R)).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) i
  let U := forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1}
  have iG : G ⋙ U ≅ e.inverse ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
      derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
      coyoneda.obj (op P) :=
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight ((pointDerivedTensor (R := R)).mapIso j)
          ((pointDerivedEquiv (R := R)).functor ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} R) i ⋙ U) ≪≫
        pointHomologyTensorPullbackCoyonedaIso hZ f hflat hT hXqc hXqs P hP i))
  have := hprod A i
  have : PreservesLimit (Discrete.functor fun _ : A => ModuleCat.of R R) (G ⋙ U) :=
    preservesLimit_of_natIso _ iG.symm
  have : PreservesLimit (Discrete.functor fun _ : A => ModuleCat.of R R) G :=
    preservesLimit_of_reflects_of_preserves G U
  exact preservesLimit_of_natIso _ (pointDerivedTensorHomologyIso E b hflatE i).symm

end Spaces

end AlgebraicGeometry.Space

end
