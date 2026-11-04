module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePerfectTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.SheafHomFinitelyPresentedPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedPullbackOfADual
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.IsPerfectComparison

/-!
# Grothendieck's existence theorem: `RHom` out of a perfect complex into `K`, part (2)

In Situation [Stacks, Tag 0CTC] let `K` be as in [Stacks, Tag 0CTD] and let `E` be a perfect
object of `D(𝒪_X)`. This file proves part (2) of [Stacks, Tag 0CTE]: `N = RHom_X(E, K)` is a
perfect object of `D(A)`, and `RHom_{Xₙ}(E|_{Xₙ}, ℱₙ) ≅ N ⊗^𝐋_A Aₙ`.

## The proof

The source: "To see that (1) holds, translate it into (2) using Cohomology, Lemma 08DQ"; the
translation works in both directions, and this file runs it from (1) to (2). By
[Stacks, Tag 08DQ], `R𝓗om(E, M) ≅ E^∨ ⊗^𝐋 M ≅ M ⊗^𝐋 E^∨` for perfect `E`, with `E^∨` perfect, so
`N ≅ RΓ(X, K ⊗^𝐋 E^∨)`; and `Liₙ^*(E^∨) ≅ (Liₙ^*E)^∨`
(`Stacks.SheafOfModules.derivedPullbackDerivedDualIso`), so the level objects of part (1) for
`E^∨` are `RΓ(Xₙ, ℱₙ ⊗^𝐋 (Eₙ)^∨) ≅ RHom_{Xₙ}(Eₙ, ℱₙ)`. Part (1) at `E^∨` then gives part (2).

`RHom_X(E, -)` is realized as `RΓ_A(X, R𝓗om(E, -))`, as in
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.globalSectionsSheafHom`.

## Implementation notes

The statements are at `CategoryTheory.HasDerivedCategory.standard`, scoped to each declaration,
as for part (1).

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.SheafOfModules (derivedSheafHom derivedDual)
open StacksDraft.DerivedInverseLimit

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `R𝓗om(E, M) ≅ M ⊗^𝐋 E^∨` on a scheme `Y` for a perfect `E` ([Stacks, Tag 08DQ]), in the order
of part (1) of [Stacks, Tag 0CTE]. -/
def sheafHomIsoTensorDual {Y : Scheme.{u}} (E : DerivedCategory Y.Modules)
    (hE : RingedSpace.IsPerfect (X := Y.toRingedSpace) E) (M : DerivedCategory Y.Modules) :
    ((derivedSheafHom Y.sheaf).obj (op E)).obj M ≅
      ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj M).obj (derivedDual Y.sheaf E) :=
  sheafHomIsoDerivedDualTensor E hE M ≪≫ tensorBraidingIso _ (derivedDual Y.sheaf E) M

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RHom_{Xₙ}(E|_{Xₙ}, ℱₙ) = RΓ_{Aₙ}(Xₙ, R𝓗om(Eₙ, ℱₙ))`, an object of `D(Aₙ)`. -/
def levelSheafHom (n : ℕ) (E : DerivedCategory S.X.left.Modules) :
    DerivedCategory (ModuleCat.{u} ↑(S.system.obj (op n))) :=
  (derivedGlobalSectionsOver (S.levelStructure n)).obj
    (((derivedSheafHom (schemeAt S.system S.X n).sheaf).obj (op ((S.levelPullback n).obj E))).obj
      (S.levelSheafStandard n))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- `RΓ(Xₙ, ℱₙ ⊗^𝐋 Liₙ^*(E^∨)) ≅ RHom_{Xₙ}(Eₙ, ℱₙ)`: the level object of part (1) of
[Stacks, Tag 0CTE] for the dual `E^∨` is the level object of part (2) for `E`, by
`Liₙ^*(E^∨) ≅ (Liₙ^*E)^∨` and [Stacks, Tag 08DQ] on `Xₙ`. -/
def levelTensorDualIso (n : ℕ) (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    S.levelTensor n (derivedDual S.X.left.sheaf E) ≅ S.levelSheafHom n E :=
  have hEn : RingedSpace.IsPerfect (X := (schemeAt S.system S.X n).toRingedSpace)
      ((S.levelPullback n).obj E) :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE
  (derivedGlobalSectionsOver (S.levelStructure n)).mapIso
    (((derivedTensorProductFunctor (schemeAt S.system S.X n).toRingedSpace.sheaf).obj
        (S.levelSheafStandard n)).mapIso
      (Stacks.SheafOfModules.derivedPullbackDerivedDualIso (S.closedImmersion n).toLRSHom.toShHom E
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect
          S.X.left.toRingedSpace E hE)
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect
          (schemeAt S.system S.X n).toRingedSpace ((S.levelPullback n).obj E) hEn)) ≪≫
      (sheafHomIsoTensorDual ((S.levelPullback n).obj E) hEn (S.levelSheafStandard n)).symm)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

namespace AlgebraicGeometry.GrothendieckExistence

attribute [local instance 10000] HasDerivedCategory.standard in
/-- Invertibility of the derived base-change map adjoint to `g` is unchanged by composing `g`
with isomorphisms on either side. -/
theorem isIso_derivedBaseChangeComparison_iso_comp_comp {R R' : Type u} [CommRing R]
    [CommRing R'] (φ : R →+* R') {M M' : DerivedCategory (ModuleCat.{u} R)}
    {L L' : DerivedCategory (ModuleCat.{u} R')} (a : M' ≅ M)
    (g : M ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj L) (b : L ≅ L')
    (hg : IsIso (derivedBaseChangeComparison.{u, u, u} φ g)) :
    IsIso (derivedBaseChangeComparison.{u, u, u} φ
      (a.hom ≫ g ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map b.hom)) := by
  dsimp only [derivedBaseChangeComparison]
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  dsimp only [derivedBaseChangeComparison] at hg
  infer_instance

end AlgebraicGeometry.GrothendieckExistence


namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- The perfectness of `E^∨`, in the spelling of part (1) of [Stacks, Tag 0CTE]. -/
theorem isPerfect_derivedDual (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace)
      (derivedDual S.X.left.sheaf E) :=
  (AlgebraicGeometry.RingedSpace.isPerfect_iff_perfectComplexes_isPerfect.{u, u + 1} _).1
    (isPerfect_derivedDual_scheme E hE)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The canonical isomorphism of [Stacks, Tag 0CTE] (2)**, before base change:
`RHom_X(E, K) ⟶ RHom_{Xₙ}(Eₙ, ℱₙ)` read over `A`. It is the canonical map of part (1) for `E^∨`,
`RΓ(X, K ⊗^𝐋 E^∨) ⟶ RΓ(Xₙ, ℱₙ ⊗^𝐋 (E^∨)ₙ)` (induced by `levelMap`), transported along the
identifications `R𝓗om(E, -) ≅ - ⊗^𝐋 E^∨` of [Stacks, Tag 08DQ] on `X` and on `Xₙ`. -/
def DerivedLimitQCoh.sheafHomLevelMap (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ) :
    (derivedGlobalSectionsOver S.X.hom).obj
        (((derivedSheafHom S.X.left.sheaf).obj (op E)).obj d.K) ⟶
      (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.obj
        (S.levelSheafHom n E) :=
  (derivedGlobalSectionsOver S.X.hom).map (sheafHomIsoTensorDual E hE d.K).hom ≫
    ((derivedGlobalSectionsOver S.X.hom).map
      (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
        (S.levelMap d p n)).app (derivedDual S.X.left.sheaf E)) ≫
      (S.levelTensorRestrictionIso n (derivedDual S.X.left.sheaf E)
        (S.isPerfect_derivedDual E hE)).hom) ≫
    (ModuleCat.restrictScalars (S.limitProjection n)).mapDerivedCategory.map
      (S.levelTensorDualIso n E hE).hom

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTE] (2) from part (1) at `E^∨`**, given the compatibility of the system
isomorphism for `E^∨` with the transitions. -/
theorem DerivedLimitQCoh.isPerfect_and_isIso_baseChange_sheafHom_of (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p)
    (hComm : ∀ n : ℕ, (derivedGlobalSectionsOver S.X.hom).map
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
          (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)).app
            (derivedDual S.X.left.sheaf E)) ≫
        (S.levelTensorRestrictionIso n (derivedDual S.X.left.sheaf E)
          (S.isPerfect_derivedDual E hE)).hom =
      (S.levelTensorRestrictionIso (n + 1) (derivedDual S.X.left.sheaf E)
          (S.isPerfect_derivedDual E hE)).hom ≫
        S.towerTransition (fun m => S.levelTensor m (derivedDual S.X.left.sheaf E))
          (fun m => S.levelTensorTransition m (derivedDual S.X.left.sheaf E)) n) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver S.X.hom).obj
        (((derivedSheafHom S.X.left.sheaf).obj (op E)).obj d.K)) ∧
      ∀ n : ℕ, IsIso (derivedBaseChangeComparison (S.limitProjection n)
        (DerivedLimitQCoh.sheafHomLevelMap S d E hE p n)) := by
  have hEd := isPerfect_derivedDual_scheme E hE
  obtain ⟨h1, h2⟩ :=
    DerivedLimitQCoh.isPerfect_and_isIso_baseChange_of S d (derivedDual S.X.left.sheaf E)
    (S.isPerfect_derivedDual E hE) p hp
    (fun n => S.isIso_derivedBaseChangeComparison_levelTensorTransition n _ hEd) hComm
  refine ⟨StacksDraft.Perfect.isPerfect_of_iso
    ((derivedGlobalSectionsOver S.X.hom).mapIso (sheafHomIsoTensorDual E hE d.K)) h1,
    fun n => ?_⟩
  exact isIso_derivedBaseChangeComparison_iso_comp_comp (S.limitProjection n)
    ((derivedGlobalSectionsOver S.X.hom).mapIso (sheafHomIsoTensorDual E hE d.K)) _
    (S.levelTensorDualIso n E hE) (h2 n)

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation


namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **Stacks Project, Tag 0CTE, part (2).** In Situation [Stacks, Tag 0CTC] let `K` be as in
[Stacks, Tag 0CTD] and let `E` be a perfect object of `D(𝒪_X)`. Then
`N = RHom_X(E, K) = RΓ_A(X, R𝓗om(E, K))` is a perfect object of `D(A)`, and there is a canonical
isomorphism `N ⊗^𝐋_A Aₙ ≅ RHom_{Xₙ}(E|_{Xₙ}, ℱₙ)` in `D(Aₙ)` for every `n`, with `E|_{Xₙ}` the
derived pullback: the derived base change of
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh.sheafHomLevelMap`,
built from a cone `p` exhibiting `L = R lim ℱₙ`, is invertible.

As in the source, part (2) and part (1) are translated into each other by
[Stacks, Tag 08DQ]; here part (2) is read off part (1) at `E^∨`. Stated at
`HasDerivedCategory.standard` (scoped to this declaration). -/
@[stacks 0CTE "(2)"]
theorem DerivedLimitQCoh.isPerfect_and_isIso_sheafHomBaseChange (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver S.X.hom).obj
        (((derivedSheafHom S.X.left.sheaf).obj (op E)).obj d.K)) ∧
      ∀ (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩),
        S.IsDerivedLimitCone p → ∀ n : ℕ,
          IsIso (derivedBaseChangeComparison (S.limitProjection n)
            (DerivedLimitQCoh.sheafHomLevelMap S d E hE p n)) := by
  obtain ⟨p₀, hp₀⟩ := DerivedLimitQCoh.exists_isDerivedLimitCone S d
  have key := fun p (hp : S.IsDerivedLimitCone p) =>
    DerivedLimitQCoh.isPerfect_and_isIso_baseChange_sheafHom_of S d E hE p hp
      (fun n => S.levelTensorRestrictionIso_comm n _ (S.isPerfect_derivedDual E hE))
  exact ⟨(key p₀ hp₀).1, fun p hp => (key p hp).2⟩

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
