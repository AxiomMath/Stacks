module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.SupportedPushforwardReflect
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportCompactOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect

/-!
# The projection formula for an object supported over a quasi-compact open

Let `f : X ⟶ S` be a morphism of schemes and let `N ∈ D(𝒪_X)` have quasi-coherent cohomology
sheaves supported on a closed subset `T` of `X`. For quasi-compact quasi-separated `f`, the
projection-formula morphism `Rf_*N ⊗^𝐋 M ⟶ Rf_*(N ⊗^𝐋 Lf^*M)` of [Stacks, Tag 0B53] is invertible
for `M` with quasi-coherent cohomology ([Stacks, Tag 08EU]). When `f` is not quasi-compact but `T`
lies in a quasi-compact open `U` whose inclusion `ι : U ⟶ X` and the composite `g = ι ≫ f` are
quasi-compact and quasi-separated (for instance `f` locally of finite type over a Noetherian base
and `T` proper over `S`), the two sides are nevertheless identified, through `U`.

Write `N_U = N|_U`. Then `N ≅ Rι_*N_U` because `N` is supported on `T ⊆ U`
([Stacks, Tag 08DF] part (1)), and there are two natural transformations of functors of `M`

* `Rf_*N ⊗^𝐋 M ≅ Rg_*N_U ⊗^𝐋 M ⟶ Rg_*(N_U ⊗^𝐋 Lg^*M)`, the projection-formula morphism of `g`;
* `Rf_*(N ⊗^𝐋 Lf^*M) ≅ Rf_*(Rι_*N_U ⊗^𝐋 Lf^*M) ⟶ Rf_*Rι_*(N_U ⊗^𝐋 Lι^*Lf^*M) ≅
  Rg_*(N_U ⊗^𝐋 Lg^*M)`, the projection-formula morphism of `ι` pushed forward along `f`.

Both are natural on all of `D(𝒪_S)` and both are invertible at every `M` with quasi-coherent
cohomology, by [Stacks, Tag 08EU] for `g` and for `ι`. The pair is a zigzag rather than a single
transformation.

## Main definitions

* `Stacks.Cohomology.SupportedProjectionFormula.forwardLeg` and
  `Stacks.Cohomology.SupportedProjectionFormula.backwardLeg`: the two transformations.

## Main results

* `Stacks.Cohomology.SupportedProjectionFormula.isIso_forwardLeg_app` and
  `Stacks.Cohomology.SupportedProjectionFormula.isIso_backwardLeg_app`: both are invertible at
  objects with quasi-coherent cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPullback derivedPushforward derivedPushforwardCompIso)
open Stacks.Cohomology.DerivedProjectionFormula (projectionFormulaMap)
open Stacks.Cohomology.ProjectionFormulaPerfect (projectionFormulaTransformation)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open ExtensionByZeroModules (jStar)

universe u

namespace Stacks.Cohomology.SupportedProjectionFormula

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)

/-- `D(𝒪_X)` at the spelling of [Stacks, Tag 0B53]. -/
abbrev DX (X : Scheme.{u}) :=
  DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The restriction `N|_U` of an object of `D(𝒪_X)` to an open subscheme. -/
abbrev restrictedObject (N : DX X) : DX U.toScheme :=
  (jStar U (structureSheafRing X.toRingedSpace)).mapDerivedCategory.obj N

variable {T : Set X} (hT : IsClosed T) (hTU : T ⊆ U) (N : DX X)
  (hN : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
    (structureSheafRing X.toRingedSpace) T N)

/-- The common target of the two legs: `M ↦ Rg_*(N_U ⊗^𝐋 Lg^*M)` for `g = ι ≫ f`. -/
abbrev legTarget : DX S ⥤ DX S :=
  derivedPullback (U.ι ≫ f).toLRSHom.toShHom ⋙
    (derivedTensorProductFunctor U.toScheme.toRingedSpace.sheaf).obj (restrictedObject U N) ⋙
      derivedPushforward (U.ι ≫ f).toLRSHom.toShHom

include hT hTU hN in
/-- **The forward leg**: `Rf_*N ⊗^𝐋 M ≅ Rg_*N_U ⊗^𝐋 M ⟶ Rg_*(N_U ⊗^𝐋 Lg^*M)`, the
projection-formula morphism of `g = ι ≫ f` after the identification `Rf_*N ≅ Rg_*N_U` of
[Stacks, Tag 08DF] and Leray. -/
def forwardLeg :
    (derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj N) ⟶ legTarget f U N :=
  (derivedTensorProductFunctor S.toRingedSpace.sheaf).map
      (Stacks.AlgebraicGeometry.SupportedPushforwardReflect.derivedPushforwardRestrictCompIso
        f U hT hTU N hN).hom ≫
    projectionFormulaTransformation (U.ι ≫ f).toLRSHom.toShHom (restrictedObject U N)

/-- The tensor factor `N_U ⊗^𝐋 -` on `D(𝒪_U)`. -/
abbrev tensorRestricted : DX U.toScheme ⥤ DX U.toScheme :=
  (derivedTensorProductFunctor U.toScheme.toRingedSpace.sheaf).obj (restrictedObject U N)

include hT hTU hN in
/-- First factor of the backward leg: `Rf_*(N ⊗^𝐋 Lf^*M) ≅ Rf_*(Rι_*N_U ⊗^𝐋 Lf^*M)`. -/
def backwardLegRestrict :
    derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj N ⋙
          derivedPushforward f.toLRSHom.toShHom ⟶
      derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
          ((derivedPushforward U.ι.toLRSHom.toShHom).obj (restrictedObject U N)) ⋙
          derivedPushforward f.toLRSHom.toShHom :=
  Functor.whiskerLeft (derivedPullback f.toLRSHom.toShHom)
    (Functor.whiskerRight ((derivedTensorProductFunctor X.toRingedSpace.sheaf).map
      (Stacks.AlgebraicGeometry.SupportedPushforwardReflect.derivedRestrictionIso
        U hT hTU N hN).hom) (derivedPushforward f.toLRSHom.toShHom))

/-- Second factor of the backward leg: the projection-formula morphism of `ι : U ⟶ X` at `N_U`,
pushed forward along `f`. -/
def backwardLegProjection :
    derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
          ((derivedPushforward U.ι.toLRSHom.toShHom).obj (restrictedObject U N)) ⋙
          derivedPushforward f.toLRSHom.toShHom ⟶
      derivedPullback f.toLRSHom.toShHom ⋙
        (derivedPullback U.ι.toLRSHom.toShHom ⋙ tensorRestricted U N ⋙
          derivedPushforward U.ι.toLRSHom.toShHom) ⋙
          derivedPushforward f.toLRSHom.toShHom :=
  Functor.whiskerLeft (derivedPullback f.toLRSHom.toShHom)
    (Functor.whiskerRight
      (projectionFormulaTransformation U.ι.toLRSHom.toShHom (restrictedObject U N))
      (derivedPushforward f.toLRSHom.toShHom))

/-- Third factor of the backward leg: `Rf_* ∘ Rι_* ≅ R(ι ≫ f)_*`. -/
def backwardLegPushforwardComp :
    (derivedPullback f.toLRSHom.toShHom ⋙ derivedPullback U.ι.toLRSHom.toShHom) ⋙
        tensorRestricted U N ⋙
          (derivedPushforward U.ι.toLRSHom.toShHom ⋙ derivedPushforward f.toLRSHom.toShHom) ⟶
      (derivedPullback f.toLRSHom.toShHom ⋙ derivedPullback U.ι.toLRSHom.toShHom) ⋙
        tensorRestricted U N ⋙ derivedPushforward (U.ι ≫ f).toLRSHom.toShHom :=
  Functor.whiskerLeft
    ((derivedPullback f.toLRSHom.toShHom ⋙ derivedPullback U.ι.toLRSHom.toShHom) ⋙
      tensorRestricted U N)
    (derivedPushforwardCompIso U.ι.toLRSHom.toShHom f.toLRSHom.toShHom).hom

/-- Fourth factor of the backward leg: `Lι^* ∘ Lf^* ≅ L(ι ≫ f)^*`. -/
def backwardLegPullbackComp :
    (derivedPullback f.toLRSHom.toShHom ⋙ derivedPullback U.ι.toLRSHom.toShHom) ⋙
        tensorRestricted U N ⋙ derivedPushforward (U.ι ≫ f).toLRSHom.toShHom ⟶
      legTarget f U N :=
  Functor.whiskerRight
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      U.ι.toLRSHom.toShHom f.toLRSHom.toShHom).hom
    (tensorRestricted U N ⋙ derivedPushforward (U.ι ≫ f).toLRSHom.toShHom)

include hT hTU hN in
/-- **The backward leg**: `Rf_*(N ⊗^𝐋 Lf^*M) ≅ Rf_*(Rι_*N_U ⊗^𝐋 Lf^*M) ⟶
Rf_*Rι_*(N_U ⊗^𝐋 Lι^*Lf^*M) ≅ Rg_*(N_U ⊗^𝐋 Lg^*M)`: the projection-formula morphism of the
inclusion `ι : U ⟶ X` at `N_U`, pushed forward along `f`, between the identification
`N ≅ Rι_*N_U` of [Stacks, Tag 08DF] and the two composition isomorphisms. -/
def backwardLeg :
    derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj N ⋙
          derivedPushforward f.toLRSHom.toShHom ⟶ legTarget f U N :=
  backwardLegRestrict f U hT hTU N hN ≫ backwardLegProjection f U N ≫
    backwardLegPushforwardComp f U N ≫ backwardLegPullbackComp f U N

/-! ### Invertibility at objects with quasi-coherent cohomology -/

/-- Objects of `D(𝒪_X)` all of whose cohomology sheaves are quasi-coherent. -/
abbrev HasQuasicoherentCohomology {X : Scheme.{u}} (M : DX X) : Prop :=
  ∀ j : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj M).IsQuasicoherent

variable {N}

include hT hTU hN in
/-- **The forward leg is invertible at objects with quasi-coherent cohomology** when
`g = ι ≫ f` is quasi-compact and quasi-separated. -/
theorem isIso_forwardLeg_app [QuasiCompact (U.ι ≫ f)] [QuasiSeparated (U.ι ≫ f)]
    (hNq : HasQuasicoherentCohomology N) (M : DX S) (hM : HasQuasicoherentCohomology M) :
    IsIso ((forwardLeg f U hT hTU N hN).app M) := by
  have := Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent
    (U.ι ≫ f) (restrictedObject U N)
    (fun j ↦ Stacks.AlgebraicGeometry.SupportedPushforwardReflect.isQuasicoherent_homology_jStar
      U j N (hNq j)) M hM
  dsimp only [forwardLeg, NatTrans.comp_app,
    Stacks.Cohomology.ProjectionFormulaPerfect.projectionFormulaTransformation_app]
  infer_instance

include hT hTU hN in
/-- **The backward leg is invertible at objects with quasi-coherent cohomology** when the
inclusion `ι : U ⟶ X` is quasi-compact and quasi-separated. -/
theorem isIso_backwardLeg_app [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (hNq : HasQuasicoherentCohomology N) (M : DX S) (hM : HasQuasicoherentCohomology M) :
    IsIso ((backwardLeg f U hT hTU N hN).app M) := by
  have := Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent
    U.ι (restrictedObject U N)
    (fun j ↦ Stacks.AlgebraicGeometry.SupportedPushforwardReflect.isQuasicoherent_homology_jStar
      U j N (hNq j))
    ((derivedPullback f.toLRSHom.toShHom).obj M)
    (fun j ↦ Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel f M hM j)
  have h₁ : IsIso ((backwardLegRestrict f U hT hTU N hN).app M) := by
    dsimp only [backwardLegRestrict, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have h₂ : IsIso ((backwardLegProjection f U N).app M) := by
    dsimp only [backwardLegProjection, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Stacks.Cohomology.ProjectionFormulaPerfect.projectionFormulaTransformation_app]
    infer_instance
  have h₃ : IsIso ((backwardLegPushforwardComp f U N).app M) :=
    ((derivedPushforwardCompIso U.ι.toLRSHom.toShHom f.toLRSHom.toShHom).app _).isIso_hom
  have h₄ : IsIso ((backwardLegPullbackComp f U N).app M) :=
    ((tensorRestricted U N ⋙ derivedPushforward (U.ι ≫ f).toLRSHom.toShHom).mapIso
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        U.ι.toLRSHom.toShHom f.toLRSHom.toShHom).app M)).isIso_hom
  rw [backwardLeg, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
  infer_instance

end Stacks.Cohomology.SupportedProjectionFormula

end
