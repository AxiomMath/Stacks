module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialCompatibility
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianFractionFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySpellingBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages

/-!
# The right-hand vertical arrow of the comparison square of Stacks 0G85

Let `X` be a scheme, `T ⊆ X` a closed subset with inclusion `i : T ⟶ X`, and `ℱ` a sheaf of
`𝒪_X`-modules. The target of the Gysin map of [Stacks, Tag 0G83] is `i_*ℋ ᶜ_T(ℱ)`, written
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`. This file makes the local cohomology
sheaf `i_*ℋ ⁿ_T(ℱ)` functorial along morphisms of the underlying sheaves of abelian groups, which
need not be `𝒪_X`-linear, both in the spelling of the target of the Gysin map and in the spelling
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf` in which
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` takes its values. It also proves the
comparison square of step (ii) of [Stacks, Tag 0G85] for `𝒪_X`-linear morphisms.

## Main definitions

* `abelianClosedPushforward`: the direct image of sheaves of abelian groups along the inclusion of
  a closed subset.
* `pushforwardLocalCohomologyForgetIso`: the underlying abelian sheaf of `i_*ℋ ⁿ_T(ℱ[0])` is the
  abelian `i_*ℋ ⁿ_T(ℱ_ab)`, naturally in `ℱ` ([Stacks, Tag 0G74] part (2)).
* `pushforwardLocalCohomologyAbelianMap`: the action of `i_*ℋ ⁿ_T` on a morphism of the
  underlying abelian sheaves, which need not be `𝒪_X`-linear.
* `gysinTargetAbelianMap`: the same action with its source and target spelled exactly as
  `AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`, the target of the Gysin map.
* `supportCohomologySheafForgetIso` and `supportCohomologySheafAbelianMap`: the same isomorphism
  and the same action in the `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` spelling.
* `supportCohomologySheafFunctorLocalCohomologyIso`: `supportCohomologySheafFunctor` is `i_*` of
  Mathlib's classical right derived functor `Rⁿ H_T`.
* `cokernelLastDifMap`: the morphism induced on the Čech cokernel of [Stacks, Tag 0G7Q] by an
  `𝒪_X`-linear morphism of coefficient modules.

## Main results

* `localCohomologyPushforwardFunctor_eq`: the Gysin map's local cohomology functor is
  `localCohomologySheafOfComplexFunctor` followed by the direct image.
* `pushforwardLocalCohomologyAbelianMap_map`, `gysinTargetAbelianMap_map`,
  `supportCohomologySheafAbelianMap_map`: on the underlying morphism of abelian sheaves of a
  morphism of `X.Modules`, each abelian action is the underlying morphism of the functorial action.
* `pushforwardLocalCohomologyAbelianMap_id`, `supportCohomologySheafAbelianMap_id`: unitality.
* `cokernelLastDifAb_mapPresheaf`: the abelian functoriality of the Čech cokernel extends the
  `𝒪_X`-linear one.
* `cokernelLastDifMap_comp_cokernelLastDifToSupport`: the identification
  `Coker(lastDif f ℱ) ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7L] is natural along `𝒪_X`-linear
  morphisms.
* `cokernelLastDifToSupport_abelian_square_mapPresheaf`: the comparison square of step (ii) of
  [Stacks, Tag 0G85] for an `𝒪_X`-linear morphism of coefficient modules.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G84](https://stacks.math.columbia.edu/tag/0G84)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.ModulePushforwardComparison (modulePushforwardCompToSheafIso)
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Perfect.GysinAbelianSquare

attribute [local instance 10000] HasDerivedCategory.standard

/-- Sheaves of modules over `structureSheafRing Y` on a ringed space `Y` form an abelian
category. -/
local instance abelian_sheafOfModules_ringSheaf (Y : RingedSpace.{u, u}) :
    Abelian (_root_.SheafOfModules.{u} (structureSheafRing Y)) :=
  _root_.SheafOfModules.instAbelian _

/-- The direct image of modules over `structureSheafRing` along a morphism of ringed spaces is
additive. -/
local instance additive_modulePushforward {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z) :
    (modulePushforward g).Additive :=
  RingedSpaceModuleAdjunction.modulePushforward_additive g

/-! ### The direct image of abelian sheaves along the inclusion of a closed subset -/

/-- The direct image of sheaves of abelian groups along the inclusion `i : T ⟶ X` of a closed
subset: `(i_*𝒢)(V) = 𝒢(i⁻¹V)`. -/
public abbrev abelianClosedPushforward (Y : RingedSpace.{u, u}) (T : Set Y.carrier) :
    Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} :=
  (opensMap (closedSubsetInclusion Y T)).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y.carrier)
    (Opens.grothendieckTopology (closedSubsetRingedSpace Y T).carrier)

/-- The abelian local cohomology sheaf of [Stacks, Tag 0G74] pushed forward from the closed
subset, as a functor of the coefficient abelian sheaf: `𝒢 ↦ i_*ℋ ⁿ_T(𝒢)`, with `ℋ ⁿ_T` Mathlib's
classical right derived functor of abelian sections supported on `T`. -/
public abbrev abelianLocalCohomologyPushforward (Y : RingedSpace.{u, u}) (T : Set Y.carrier)
    (hT : IsClosed T) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} :=
  ClosedImmersionSheaves.localCohomologySheafFunctor T hT n ⋙ abelianClosedPushforward Y T

variable {X : Scheme.{u}}

/-! ### The Gysin map's local cohomology functor factors through the `T`-side one -/

/-- The Gysin map's spelling `ℱ ↦ i_*ℋ ⁿ_T(ℱ[0])` of the local cohomology sheaf is
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctor` on `T` followed by the
direct image from `T` to `X`. -/
public theorem localCohomologyPushforwardFunctor_eq {T : Set X} (hT : IsClosed T) (n : ℤ) :
    GysinLocalCohomology.localCohomologyPushforwardFunctor hT n =
      localCohomologySheafOfComplexFunctor X.toRingedSpace T hT n ⋙
        modulePushforward (closedSubsetInclusion X.toRingedSpace T) := rfl

/-! ### Stacks 0G74 part (2) for the Gysin map's target -/

/-- The underlying sheaf of abelian groups of `i_*ℋ ⁿ_T(ℱ[0])`, with the local cohomology sheaf
taken as the degree-`n` cohomology sheaf of `R𝓗_T(ℱ[0])` in the unbounded derived category — the
spelling of the target of `AlgebraicGeometry.Scheme.Hom.gysinMap` — is the abelian direct image of
the abelian local cohomology sheaf `ℋ ⁿ_T(ℱ_ab)`, naturally in `ℱ`. -/
@[stacks 0G74 "part (2) at the GYSIN MAP'S TARGET: the underlying abelian sheaf of \
i_*H^n_T(F) is i_*^ab H^n_T(F_ab), naturally in F, which is what lets H^n_T act on a morphism \
that is additive but not O_X-linear. No hypotheses beyond IsClosed T"]
public def pushforwardLocalCohomologyForgetIso {T : Set X} (hT : IsClosed T) (n : ℕ) :
    GysinLocalCohomology.localCohomologyPushforwardFunctor hT (n : ℤ) ⋙ abelianSheaf X ≅
      abelianSheaf X ⋙ abelianLocalCohomologyPushforward X.toRingedSpace T hT n :=
  Functor.isoWhiskerLeft (localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (n : ℤ))
      (modulePushforwardCompToSheafIso (closedSubsetInclusion X.toRingedSpace T)) ≪≫
    Functor.isoWhiskerRight (localCohomologySheafOfComplexForgetIso X.toRingedSpace T hT n)
      (abelianClosedPushforward X.toRingedSpace T)

/-! ### The abelian action on the Gysin map's target -/

/-- `i_*ℋ ⁿ_T` in the Gysin map's spelling, acting on a morphism of the underlying abelian
sheaves: given `𝒪_X`-modules `ℱ` and `𝒢` and a morphism `ψ : ℱ_ab ⟶ 𝒢_ab` of the underlying
sheaves of abelian groups, not required to be `𝒪_X`-linear, the morphism
`(i_*ℋ ⁿ_T(ℱ[0]))_ab ⟶ (i_*ℋ ⁿ_T(𝒢[0]))_ab` obtained by applying the abelian functor
`𝒢 ↦ i_*ℋ ⁿ_T(𝒢)` to `ψ` and conjugating by `pushforwardLocalCohomologyForgetIso`. -/
public def pushforwardLocalCohomologyAbelianMap {T : Set X} (hT : IsClosed T) (n : ℕ)
    {F G : X.Modules} (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G) :
    (abelianSheaf X).obj
        ((GysinLocalCohomology.localCohomologyPushforwardFunctor hT (n : ℤ)).obj F) ⟶
      (abelianSheaf X).obj
        ((GysinLocalCohomology.localCohomologyPushforwardFunctor hT (n : ℤ)).obj G) :=
  (pushforwardLocalCohomologyForgetIso hT n).hom.app F ≫
    (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).map ψ ≫
      (pushforwardLocalCohomologyForgetIso hT n).inv.app G

/-- The abelian action extends the `𝒪_X`-linear one: on the underlying morphism of abelian
sheaves of a morphism `φ : ℱ ⟶ 𝒢` of `𝒪_X`-modules, `pushforwardLocalCohomologyAbelianMap` is the
underlying morphism of abelian sheaves of the functorial action of `i_*ℋ ⁿ_T` on `φ`. -/
public theorem pushforwardLocalCohomologyAbelianMap_map {T : Set X} (hT : IsClosed T) (n : ℕ)
    {F G : X.Modules} (φ : F ⟶ G) :
    pushforwardLocalCohomologyAbelianMap hT n ((abelianSheaf X).map φ) =
      (abelianSheaf X).map
        ((GysinLocalCohomology.localCohomologyPushforwardFunctor hT (n : ℤ)).map φ) :=
  NatIso.naturality_2 (pushforwardLocalCohomologyForgetIso hT n) φ

/-- The abelian action of `i_*ℋ ⁿ_T` sends the identity to the identity. -/
public theorem pushforwardLocalCohomologyAbelianMap_id {T : Set X} (hT : IsClosed T) (n : ℕ)
    (F : X.Modules) :
    pushforwardLocalCohomologyAbelianMap hT n (𝟙 ((abelianSheaf X).obj F)) = 𝟙 _ := by
  simp [pushforwardLocalCohomologyAbelianMap]

/-- The abelian action on the target of the Gysin map, with that target spelled exactly as
`AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology`: here `T` is the common zero locus of
the equations and the degree is their number. -/
public def gysinTargetAbelianMap {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) {F G : X.Modules}
    (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G) :
    (abelianSheaf X).obj (AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f F) ⟶
      (abelianSheaf X).obj (AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f G) :=
  pushforwardLocalCohomologyAbelianMap (isClosed_equationsClosedSet f) (d + 1) ψ

/-- The abelian action on the target of the Gysin map extends the `𝒪_X`-linear one. -/
public theorem gysinTargetAbelianMap_map {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) {F G : X.Modules}
    (φ : F ⟶ G) :
    gysinTargetAbelianMap f ((abelianSheaf X).map φ) =
      (abelianSheaf X).map
        ((GysinLocalCohomology.localCohomologyPushforwardFunctor
          (isClosed_equationsClosedSet f) (((d + 1 : ℕ)) : ℤ)).map φ) :=
  pushforwardLocalCohomologyAbelianMap_map (isClosed_equationsClosedSet f) (d + 1) φ

/-! ### The cohomology sheaf after the direct image as a classical derived functor -/

/-- The degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])`, in the spelling of
`Stacks.Perfect.SupportedFraction.supportCohomologySheaf`, is the direct image of Mathlib's
classical right derived functor `Rⁿ H_T` applied to `ℱ`, naturally in `ℱ`. -/
public def supportCohomologySheafFunctorLocalCohomologyIso {T : Set X} (hT : IsClosed T) (n : ℕ) :
    supportCohomologySheafFunctor hT (n : ℤ) ≅
      localCohomologySheafFunctor X.toRingedSpace T hT n ⋙
        modulePushforward (closedSubsetInclusion X.toRingedSpace T) :=
  GysinLocalCohomology.supportCohomologySheafFunctorIso hT (n : ℤ) ≪≫
    Functor.isoWhiskerRight (localCohomologySheafOfComplexFunctorIso X.toRingedSpace T hT n)
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T))

/-! ### The abelian action in the spelling of the comparison of Stacks 0G7L -/

/-- [Stacks, Tag 0G74] part (2) in the spelling of the target of
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport`: the underlying sheaf of abelian
groups of the degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])` is the abelian direct image of the
abelian local cohomology sheaf `ℋ ⁿ_T(ℱ_ab)`, naturally in `ℱ`. -/
public def supportCohomologySheafForgetIso {T : Set X} (hT : IsClosed T) (n : ℕ) :
    supportCohomologySheafFunctor hT (n : ℤ) ⋙ abelianSheaf X ≅
      abelianSheaf X ⋙ abelianLocalCohomologyPushforward X.toRingedSpace T hT n :=
  Functor.isoWhiskerRight (GysinLocalCohomology.supportCohomologySheafFunctorIso hT (n : ℤ))
      (abelianSheaf X) ≪≫
    pushforwardLocalCohomologyForgetIso hT n

/-- The action of `i_*ℋ ⁿ_T` on a morphism of the underlying abelian sheaves, in the spelling of
the target of `Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport`. -/
public def supportCohomologySheafAbelianMap {T : Set X} (hT : IsClosed T) (n : ℕ)
    {F G : X.Modules} (ψ : (abelianSheaf X).obj F ⟶ (abelianSheaf X).obj G) :
    (abelianSheaf X).obj (supportCohomologySheaf hT F (n : ℤ)) ⟶
      (abelianSheaf X).obj (supportCohomologySheaf hT G (n : ℤ)) :=
  (supportCohomologySheafForgetIso hT n).hom.app F ≫
    (abelianLocalCohomologyPushforward X.toRingedSpace T hT n).map ψ ≫
      (supportCohomologySheafForgetIso hT n).inv.app G

/-- The abelian action extends the `𝒪_X`-linear one, in the spelling of the target of the
comparison of [Stacks, Tag 0G7L]: on the underlying morphism of abelian sheaves of a morphism of
`X.Modules` it is the underlying morphism of `supportCohomologySheafMap`. -/
public theorem supportCohomologySheafAbelianMap_map {T : Set X} (hT : IsClosed T) (n : ℕ)
    {F G : X.Modules} (φ : F ⟶ G) :
    supportCohomologySheafAbelianMap hT n ((abelianSheaf X).map φ) =
      (abelianSheaf X).map (supportCohomologySheafMap hT φ (n : ℤ)) :=
  NatIso.naturality_2 (supportCohomologySheafForgetIso hT n) φ

/-- The abelian action sends the identity to the identity. -/
public theorem supportCohomologySheafAbelianMap_id {T : Set X} (hT : IsClosed T) (n : ℕ)
    (F : X.Modules) :
    supportCohomologySheafAbelianMap hT n (𝟙 ((abelianSheaf X).obj F)) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_id (abelianSheaf X) F, supportCohomologySheafAbelianMap_map,
    show supportCohomologySheafMap hT (𝟙 F) (n : ℤ) = 𝟙 _ from
      (supportCohomologySheafFunctor hT (n : ℤ)).map_id F,
    CategoryTheory.Functor.map_id]

/-! ### The comparison square of step (ii) of Stacks 0G85, in the `𝒪_X`-linear case -/

section LinearCase

variable {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))

/-- The last differential of the extended alternating Čech complex commutes with the maps induced
on the Čech terms by an `𝒪_X`-linear morphism of coefficient modules. -/
public theorem lastDif_comp_prodMap {F G : X.Modules} (φ : F ⟶ G) :
    lastDif f F ≫ prodMap f φ d = (cplxMap f φ).f d ≫ lastDif f G := by
  have h := (cplxMap f φ).comm d (d + 1)
  rw [cplx_d_lastDif, cplx_d_lastDif] at h
  exact h.symm

/-- The morphism induced on the Čech cokernel of [Stacks, Tag 0G7Q] by an `𝒪_X`-linear morphism
of coefficient modules. -/
public def cokernelLastDifMap {F G : X.Modules} (φ : F ⟶ G) :
    cokernel (lastDif f F) ⟶ cokernel (lastDif f G) :=
  cokernel.map (lastDif f F) (lastDif f G) ((cplxMap f φ).f d) (prodMap f φ d)
    (lastDif_comp_prodMap f φ)

/-- The defining property of `cokernelLastDifMap`: it is compatible with the canonical
epimorphisms onto the two cokernels. -/
public theorem cokernelπ_comp_cokernelLastDifMap {F G : X.Modules} (φ : F ⟶ G) :
    cokernel.π (lastDif f F) ≫ cokernelLastDifMap f φ =
      prodMap f φ d ≫ cokernel.π (lastDif f G) :=
  cokernel.π_desc _ _ _

/-- The abelian functoriality of the Čech cokernel extends the `𝒪_X`-linear one: on the
underlying morphism of abelian presheaves of a morphism of `X.Modules`,
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` is the underlying abelian-sheaf morphism of
`cokernelLastDifMap`. -/
public theorem cokernelLastDifAb_mapPresheaf {F G : X.Modules} (φ : F ⟶ G) :
    AbelianFraction.cokernelLastDifAb f (Scheme.Modules.Hom.mapPresheaf φ) =
      (abelianSheaf X).map (cokernelLastDifMap f φ) := by
  refine (AbelianFraction.cokernelLastDifAb_unique f _ _ ?_).symm
  rw [AbelianFraction.prodTermAb_mapPresheaf, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, cokernelπ_comp_cokernelLastDifMap]

/-- The identification `Coker(lastDif f ℱ) ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7L] is natural in
the coefficient module, along `𝒪_X`-linear morphisms. -/
public theorem cokernelLastDifMap_comp_cokernelLastDifToSupport {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) :
    cokernelLastDifMap f φ ≫ cokernelLastDifToSupport f G hT hTf =
      cokernelLastDifToSupport f F hT hTf ≫
        supportCohomologySheafMap hT φ ((d + 1 : ℕ) : ℤ) := by
  refine (cancel_epi (cokernel.π (lastDif f F))).mp ?_
  have hL : cokernel.π (lastDif f F) ≫
        cokernelLastDifMap f φ ≫ cokernelLastDifToSupport f G hT hTf =
      cechCocycleClass f G d (prodMap f φ d) (comp_difSucc_top f G (prodMap f φ d)) ≫
        cechHomologyToSupport f G hT hTf (d + 1) := by
    rw [← Category.assoc, cokernelπ_comp_cokernelLastDifMap, Category.assoc]
    exact comp_cokernelπ_comp_cokernelLastDifToSupport f G hT hTf (prodMap f φ d)
  have hR : cokernel.π (lastDif f F) ≫ cokernelLastDifToSupport f F hT hTf =
      cechCocycleClass f F d (𝟙 (prodTerm f F d))
          (comp_difSucc_top f F (𝟙 (prodTerm f F d))) ≫
        cechHomologyToSupport f F hT hTf (d + 1) := by
    rw [← Category.id_comp (cokernel.π (lastDif f F) ≫ cokernelLastDifToSupport f F hT hTf)]
    exact comp_cokernelπ_comp_cokernelLastDifToSupport f F hT hTf (𝟙 (prodTerm f F d))
  have hR2 : cokernel.π (lastDif f F) ≫ cokernelLastDifToSupport f F hT hTf ≫
        supportCohomologySheafMap hT φ ((d + 1 : ℕ) : ℤ) =
      cechCocycleClass f G d (prodMap f φ d) (comp_difSucc_top f G (prodMap f φ d)) ≫
        cechHomologyToSupport f G hT hTf (d + 1) := by
    rw [← Category.assoc, hR, Category.assoc,
      ← homologyMap_cplxMap_comp_cechHomologyToSupport f φ hT hTf (d + 1), ← Category.assoc,
      cechCocycleClass_top_comp_homologyMap_cplxMap f φ (𝟙 (prodTerm f F d))]
    exact congrArg (fun ψ => ψ ≫ cechHomologyToSupport f G hT hTf (d + 1))
      (cechCocycleClass_congr f G d _ _ (Category.id_comp (prodMap f φ d)))
  exact hL.trans hR2.symm

/-- The comparison square of step (ii) of [Stacks, Tag 0G85], for an `𝒪_X`-linear morphism of
coefficient modules: the square

`Coker(lastDif f ℱ) ⟶ i_*ℋ ᶜ_T(ℱ)` over `Coker(lastDif f 𝒢) ⟶ i_*ℋ ᶜ_T(𝒢)`,

with horizontal arrows the underlying abelian-sheaf morphisms of
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport`, left vertical arrow
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` and right vertical arrow
`supportCohomologySheafAbelianMap`, commutes when the morphism of abelian sheaves is the underlying
morphism of a morphism `φ : ℱ ⟶ 𝒢` of `X.Modules`. -/
public theorem cokernelLastDifToSupport_abelian_square_mapPresheaf {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) :
    (abelianSheaf X).map (cokernelLastDifToSupport f F hT hTf) ≫
        supportCohomologySheafAbelianMap hT (d + 1) ((abelianSheaf X).map φ) =
      AbelianFraction.cokernelLastDifAb f (Scheme.Modules.Hom.mapPresheaf φ) ≫
        (abelianSheaf X).map (cokernelLastDifToSupport f G hT hTf) := by
  rw [supportCohomologySheafAbelianMap_map, cokernelLastDifAb_mapPresheaf,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cokernelLastDifMap_comp_cokernelLastDifToSupport]

end LinearCase

end Stacks.Perfect.GysinAbelianSquare

end
