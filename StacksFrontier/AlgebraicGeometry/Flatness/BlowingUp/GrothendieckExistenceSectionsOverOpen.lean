module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLeray
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelMaps
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Restriction
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting

/-!
# The comparison map of Stacks 0CTG

In Situation [Stacks, Tag 0CTC], let `K` be the object of [Stacks, Tag 0CTD] and `U ⊆ X` an open,
with `Uₙ = U ∩ Xₙ`. [Stacks, Tag 0CTG] identifies `RΓ(U, K) ⊗_A^𝐋 Aₙ` with `RΓ(Uₙ, ℱₙ)` in
`D(Aₙ)`. This file constructs the canonical map between the two:

`RΓ(U, K) ⟶ RΓ(U, iₙ,* ℱₙ) ≅ RΓ(Uₙ, ℱₙ)` in `D(A)`,

the first map induced by the canonical map `K ⟶ iₙ,* ℱₙ`
(`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelMap`), the second the `A`-linear
Leray identification for the closed immersion `Uₙ ⟶ U` over `Spec Aₙ ⟶ Spec A`, and then its
adjoint `RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` in `D(Aₙ)`.

## Main definitions

* `ExistenceSituation.sectionsOver`: `RΓ(U, -)`, the
  `A`-linear derived sections over `U`, as restriction to `U` followed by `A`-linear derived
  global sections.
* `ExistenceSituation.levelSectionsOver`: `RΓ(Uₙ, ℱₙ)`.
* `ExistenceSituation.sectionsOverPushforwardIso`:
  `RΓ(U, iₙ,* ℱₙ) ≅ RΓ(Uₙ, ℱₙ)` in `D(A)`.
* `ExistenceSituation.sectionsOverComparison`: the
  comparison map of [Stacks, Tag 0CTG].

## Implementation notes

The derived base-change map of `D(A)` the comparison is the adjoint of, and the flat derived
pullback `ExistenceSituation.derivedPullbackSingleIsoOfFlat` recorded for comparison with derived
pullback to `U`, are available at the standard model of the derived categories only, so each
declaration that touches derived categories here is stated at that model, scoped to the
declaration.

## References

* [Stacks Project, Tag 0CTG](https://stacks.math.columbia.edu/tag/0CTG)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.CoherentTFAE (isQuasicoherent_isFiniteType_of_isFinitePresentation)
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- `Uₙ = U ∩ Xₙ`, the inverse image of `U` under `iₙ : Xₙ ⟶ X`. -/
abbrev levelOpen (U : S.X.left.Opens) (n : ℕ) : (schemeAt S.system S.X n).Opens :=
  (S.closedImmersion n) ⁻¹ᵁ U

/-- The closed immersion `Uₙ ⟶ U`, the restriction of `iₙ`. -/
abbrev levelOpenImmersion (U : S.X.left.Opens) (n : ℕ) :
    (S.levelOpen U n).toScheme ⟶ U.toScheme :=
  S.closedImmersion n ∣_ U

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ(U, -) : D(𝒪_X) ⥤ D(A)`, the `A`-linear derived sections over an open `U`: restriction to
`U` (an exact functor, read on derived categories) followed by the `A`-linear derived global
sections of `U`. Stated at the standard model. -/
abbrev sectionsOver (U : S.X.left.Opens) :
    DerivedCategory S.X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙
    derivedGlobalSectionsOver (U.ι ≫ S.X.hom)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ(Uₙ, ℱₙ)`, an object of `D(Aₙ)`: the `Aₙ`-linear derived global sections of `Uₙ` of the
restriction of `ℱₙ`, placed in degree zero. Stated at the standard model. -/
abbrev levelSectionsOver (U : S.X.left.Opens) (n : ℕ) :
    DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))) :=
  (derivedGlobalSectionsOver ((S.levelOpen U n).ι ≫
      pullback.snd S.X.hom (baseProjection S.system n))).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pullback (S.levelOpen U n).ι).obj (S.F n)))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The derived pullback along a flat morphism of a module placed in degree zero is its pullback
placed in degree zero. Stated at the standard model, at which
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat` is available. -/
def derivedPullbackSingleIsoOfFlat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (M : Y.Modules) :
    (derivedPullback f.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj M) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pullback f).obj M) :=
  (derivedPullback f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app M) ≪≫
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat f.toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isFlat_toShHom f) _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom)
        (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso
      ((Adjunction.leftAdjointUniq
        (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
        (Scheme.Modules.pullbackPushforwardAdjunction f)).app M)

/-- `Uₙ ⟶ U` is a closed immersion, as a restriction of the closed immersion `iₙ`. -/
instance isClosedImmersion_levelOpenImmersion (U : S.X.left.Opens) (n : ℕ) :
    IsClosedImmersion (S.levelOpenImmersion U n) := by
  have := S.closedSchemeProjection n
  infer_instance

/-- Pushforward along `Uₙ ⟶ U` is exact. -/
instance preservesFiniteColimits_pushforward_levelOpenImmersion (U : S.X.left.Opens) (n : ℕ) :
    PreservesFiniteColimits (Scheme.Modules.pushforward (S.levelOpenImmersion U n)) :=
  inferInstanceAs (PreservesFiniteColimits
    (RingedSpaceModuleAdjunction.modulePushforward (S.levelOpenImmersion U n).toLRSHom.toShHom))

/-- The level open immersion as the restriction `resLE` of the closed immersion `Xₙ ⟶ X`. -/
theorem resLE_eq_levelOpenImmersion (U : S.X.left.Opens) (n : ℕ) :
    (S.closedImmersion n).resLE U (S.levelOpen U n) le_rfl = S.levelOpenImmersion U n := by
  simp [Scheme.Hom.resLE]

/-- `(iₙ,* ℱₙ)|_U = (Uₙ ⟶ U)_* (ℱₙ|_{Uₙ})`. -/
def restrictLevelPushforwardIso (U : S.X.left.Opens) (n : ℕ) :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward (S.closedImmersion n)).obj
        (S.F n)) ≅
      (Scheme.Modules.pushforward (S.levelOpenImmersion U n)).obj
        ((Scheme.Modules.pullback (S.levelOpen U n).ι).obj (S.F n)) :=
  haveI := S.closedSchemeProjection n
  haveI := S.finitelyPresented n
  haveI : (S.F n).IsQuasicoherent :=
    (isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ (S.finitelyPresented n)).1
  restrictPushforwardIso (S.closedImmersion n) (S.F n) U (S.levelOpen U n) rfl ≪≫
    (Scheme.Modules.pushforwardCongr (S.resLE_eq_levelOpenImmersion U n)).app _ ≪≫
    (Scheme.Modules.pushforward (S.levelOpenImmersion U n)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (S.levelOpen U n).ι).app (S.F n))

/-- The square of the level open immersion over the ring map `A ⟶ Aₙ`. -/
theorem levelOpenImmersion_comp (U : S.X.left.Opens) (n : ℕ) :
    S.levelOpenImmersion U n ≫ (U.ι ≫ S.X.hom) =
      ((S.levelOpen U n).ι ≫ pullback.snd S.X.hom (baseProjection S.system n)) ≫
        Spec.map (CommRingCat.ofHom (limit.π S.system (op n)).hom) := by
  have hc : S.closedImmersion n ≫ S.X.hom =
      pullback.snd S.X.hom (baseProjection S.system n) ≫ baseProjection S.system n :=
    pullback.condition
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hc, Category.assoc]
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Derived pullback along an open immersion is restriction**: for an open `V` of a scheme `Y`,
`Lι^* ≅ D(ι^*)`, the derived pullback along `V ⟶ Y` is the functor induced on derived categories by
the exact functor `M ↦ M|_V`. Both lift `K(ι^*) ⋙ Qh` through `Qh`: the derived pullback because
`ι` is flat, the induced functor by construction, and the degreewise pullback is restriction.
Stated at the standard model, at which the derived pullback is available. -/
def derivedPullbackOpenRestrictIso {Y : Scheme.{u}} (V : Y.Opens) :
    (derivedPullback V.ι.toLRSHom.toShHom :
        DerivedCategory Y.Modules ⥤ DerivedCategory V.toScheme.Modules) ≅
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory :=
  have hadd : (Scheme.Modules.restrictFunctor V.ι).Additive := inferInstance
  have hlim : PreservesFiniteLimits (Scheme.Modules.restrictFunctor V.ι) := inferInstance
  have hcolim : PreservesFiniteColimits (Scheme.Modules.restrictFunctor V.ι) := inferInstance
  @Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ _ _ _ _ _ _ _
    (RingedSpaceModuleAdjunction.modulePullback V.ι.toLRSHom.toShHom)
    (Scheme.Modules.restrictFunctor V.ι) inferInstance hadd hlim hcolim
    (derivedPullback V.ι.toLRSHom.toShHom) (derivedPullbackComparison V.ι.toLRSHom.toShHom)
    inferInstance
    (Adjunction.leftAdjointUniq
        (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction V.ι.toLRSHom.toShHom)
        (Scheme.Modules.pullbackPushforwardAdjunction V.ι) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm)

/-- The square `Uₙ ⟶ Xₙ ⟶ X` equals `Uₙ ⟶ U ⟶ X`, as morphisms of ringed spaces. -/
theorem levelOpen_square (U : S.X.left.Opens) (n : ℕ) :
    (S.levelOpen U n).ι.toLRSHom.toShHom ≫ (S.closedImmersion n).toLRSHom.toShHom =
      (S.levelOpenImmersion U n).toLRSHom.toShHom ≫ U.ι.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k => k.toLRSHom.toShHom) (morphismRestrict_ι (S.closedImmersion n) U).symm

/-- The square `Uₙ ⟶ Xₙ ⟶ X`, `Uₙ ⟶ U ⟶ X` is cartesian. -/
theorem isPullback_levelOpen (U : S.X.left.Opens) (n : ℕ) :
    IsPullback (S.levelOpen U n).ι (S.levelOpenImmersion U n) (S.closedImmersion n) U.ι :=
  (isPullback_morphismRestrict (S.closedImmersion n) U).flip

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Flat base change along `U ⟶ X` for the closed immersion `Xₙ ⟶ X`** ([Stacks, Tag 08IB]):
the derived base change map `L(U ⟶ X)^* Riₙ,*(ℱₙ[0]) ⟶ R(Uₙ ⟶ U)_* L(Uₙ ⟶ Xₙ)^*(ℱₙ[0])` is
invertible, `U ⟶ X` being flat. Stated at the standard model. -/
theorem isIso_derivedBaseChangeMap_levelOpen (U : S.X.left.Opens) (n : ℕ) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      (S.levelOpen U n).ι.toLRSHom.toShHom (S.levelOpenImmersion U n).toLRSHom.toShHom
      (S.closedImmersion n).toLRSHom.toShHom U.ι.toLRSHom.toShHom (S.levelOpen_square U n)
      ((DerivedCategory.singleFunctor _ 0).obj (S.F n))) := by
  have := S.closedSchemeProjection n
  have := S.finitelyPresented n
  refine derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ (S.isPullback_levelOpen U n)
    inferInstance inferInstance (torIndependent_of_flat_right _ _) _ _ fun j => ?_
  by_cases hj : j = 0
  · subst hj
    exact (SheafOfModules.isQuasicoherent.{u} _).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (isQuasicoherent_isFiniteType_of_isFinitePresentation
        _ (S.finitelyPresented n)).1
  · exact (isQuasicoherent_isFiniteType_of_isFinitePresentation
      _ (isFinitePresentation_of_isZero _
        (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hj))).1

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ(U, iₙ,* ℱₙ) = RΓ(Uₙ, ℱₙ)`**, the right-hand side read over `A` by restriction of
scalars along `A ⟶ Aₙ`: restriction to `U` is derived pullback along `U ⟶ X`, `iₙ,* ℱₙ[0]` is
`Riₙ,*(ℱₙ[0])`, flat base change ([Stacks, Tag 08IB]) carries it to `R(Uₙ ⟶ U)_*(ℱₙ|_{Uₙ}[0])`,
and the `A`-linear Leray identification for the closed immersion `Uₙ ⟶ U`
(`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso`) finishes.
Stated at the standard model. -/
def sectionsOverPushforwardIso (U : S.X.left.Opens) (n : ℕ) :
    (S.sectionsOver U).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ≅
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelSectionsOver U n) :=
  haveI := S.closedSchemeProjection n
  (derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).mapIso
      ((derivedPullbackOpenRestrictIso U).symm.app (S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ≪≫
        (derivedPullback U.ι.toLRSHom.toShHom).mapIso
          ((closedImmersionDerivedPushforwardSingleIso (S.closedImmersion n)).app (S.F n)) ≪≫
        @asIso _ _ _ _ (Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap
          (derivedAdjunction (S.closedImmersion n).toLRSHom.toShHom)
          (derivedAdjunction (S.levelOpenImmersion U n).toLRSHom.toShHom)
          (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.levelOpenImmersion U n).toLRSHom.toShHom
            (S.closedImmersion n).toLRSHom.toShHom U.ι.toLRSHom.toShHom (S.levelOpen_square U n))
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.closedImmersion n).toLRSHom.toShHom)
          ((DerivedCategory.singleFunctor _ 0).obj (S.F n)))
          (S.isIso_derivedBaseChangeMap_levelOpen U n) ≪≫
        (derivedPushforward (S.levelOpenImmersion U n).toLRSHom.toShHom).mapIso
          (derivedPullbackSingleIsoOfFlat (S.levelOpen U n).ι (S.F n))) ≪≫
    (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpenImmersion U n)
      (U.ι ≫ S.X.hom) ((S.levelOpen U n).ι ≫ pullback.snd S.X.hom (baseProjection S.system n))
      (limit.π S.system (op n)).hom (S.levelOpenImmersion_comp U n)).app _

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The factors of `sectionsOverPushforwardIso`. -/
theorem sectionsOverPushforwardIso_hom (U : S.X.left.Opens) (n : ℕ) :
    (S.sectionsOverPushforwardIso U n).hom =
      (derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).map
        ((derivedPullbackOpenRestrictIso U).inv.app (S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ≫
        (derivedPullback U.ι.toLRSHom.toShHom).map
          ((@closedImmersionDerivedPushforwardSingleIso _ _ (S.closedImmersion n)
            (S.closedSchemeProjection n)).hom.app (S.F n)) ≫
        Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap
          (derivedAdjunction (S.closedImmersion n).toLRSHom.toShHom)
          (derivedAdjunction (S.levelOpenImmersion U n).toLRSHom.toShHom)
          (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.levelOpenImmersion U n).toLRSHom.toShHom
            (S.closedImmersion n).toLRSHom.toShHom U.ι.toLRSHom.toShHom (S.levelOpen_square U n))
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.closedImmersion n).toLRSHom.toShHom)
          ((DerivedCategory.singleFunctor _ 0).obj (S.F n)) ≫
        (derivedPushforward (S.levelOpenImmersion U n).toLRSHom.toShHom).map
          (derivedPullbackSingleIsoOfFlat (S.levelOpen U n).ι (S.F n)).hom) ≫
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpenImmersion U n)
      (U.ι ≫ S.X.hom) ((S.levelOpen U n).ι ≫ pullback.snd S.X.hom (baseProjection S.system n))
      (limit.π S.system (op n)).hom (S.levelOpenImmersion_comp U n)).hom.app _ :=
  rfl

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `sectionsOverPushforwardIso` after restriction to `U` is identified with derived pullback
along `U ⟶ X`: the comparison `derivedPullbackOpenRestrictIso` cancels. -/
theorem map_derivedPullbackOpenRestrictIso_hom_comp_sectionsOverPushforwardIso_hom
    (U : S.X.left.Opens) (n : ℕ) :
    (derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).map
        ((derivedPullbackOpenRestrictIso U).hom.app (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)) ≫
      (S.sectionsOverPushforwardIso U n).hom =
    (derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).map
        ((derivedPullback U.ι.toLRSHom.toShHom).map
          ((@closedImmersionDerivedPushforwardSingleIso _ _ (S.closedImmersion n)
            (S.closedSchemeProjection n)).hom.app (S.F n)) ≫
        Stacks.Cohomology.DerivedBaseChange.Mate.derivedBaseChangeMap
          (derivedAdjunction (S.closedImmersion n).toLRSHom.toShHom)
          (derivedAdjunction (S.levelOpenImmersion U n).toLRSHom.toShHom)
          (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.levelOpenImmersion U n).toLRSHom.toShHom
            (S.closedImmersion n).toLRSHom.toShHom U.ι.toLRSHom.toShHom (S.levelOpen_square U n))
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
            (S.levelOpen U n).ι.toLRSHom.toShHom (S.closedImmersion n).toLRSHom.toShHom)
          ((DerivedCategory.singleFunctor _ 0).obj (S.F n)) ≫
        (derivedPushforward (S.levelOpenImmersion U n).toLRSHom.toShHom).map
          (derivedPullbackSingleIsoOfFlat (S.levelOpen U n).ι (S.F n)).hom) ≫
      (derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso (S.levelOpenImmersion U n)
      (U.ι ≫ S.X.hom) ((S.levelOpen U n).ι ≫ pullback.snd S.X.hom (baseProjection S.system n))
      (limit.π S.system (op n)).hom (S.levelOpenImmersion_comp U n)).hom.app _ := by
  rw [sectionsOverPushforwardIso_hom]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (((derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).map_comp _ _).symm.trans
      (congrArg (derivedGlobalSectionsOver (U.ι ≫ S.X.hom)).map
        (Iso.hom_inv_id_app_assoc _ _ _))))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The map `RΓ(U, K) ⟶ RΓ(Uₙ, ℱₙ)` of `D(A)` induced by the map `K ⟶ iₙ,* ℱₙ` which is the
universal map `ε : K ⟶ L` followed by the projection of a derived-limit cone `p` of `L`. Stated at
the standard model. -/
def sectionsOverToLevel (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (U : S.X.left.Opens) (n : ℕ) :
    (S.sectionsOver U).obj d.K ⟶
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelSectionsOver U n) :=
  (S.sectionsOver U).map (S.levelMap d p n) ≫ (S.sectionsOverPushforwardIso U n).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The comparison of [Stacks, Tag 0CTG].** The map `RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` of
`D(Aₙ)` adjoint, under derived extension of scalars along `A ⟶ Aₙ`, to
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.sectionsOverToLevel`. Stated at the
standard model. -/
def sectionsOverComparison (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (U : S.X.left.Opens) (n : ℕ) :=
  StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison (limit.π S.system (op n)).hom
    (S.sectionsOverToLevel d p U n)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
