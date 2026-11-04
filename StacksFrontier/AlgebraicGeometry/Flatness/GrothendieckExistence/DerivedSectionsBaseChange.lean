module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.OpenSections
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.RestrictionIsomorphism
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over a quasi-compact open in derived existence

In Situation [Stacks, Tag 0DIB] let `K` be as in [Stacks, Tag 0DIC]. For every quasi-compact open
`U ⊆ X` with `Uₙ = U ∩ Xₙ`, [Stacks, Tag 0DIF] asserts

`RΓ(U, K) ⊗^𝐋_A Aₙ = RΓ(Uₙ, Kₙ)` in `D(Aₙ)`.

## Main definitions

* `DerivedExistenceSituation.openRestrictionMap`: for a map `c : Liₙ^*K ⟶ Kₙ`, the `A`-linear map
  `RΓ(U, K) ⟶ RΓ(Uₙ, Kₙ)` which pulls a class back along `Uₙ ⟶ U` and then applies `c` on `Uₙ`.
  Its adjoint `RΓ(U, K) ⊗^𝐋_A Aₙ ⟶ RΓ(Uₙ, Kₙ)` is the comparison of the tag.

## Main results

* `DerivedExistenceSituation.isIso_derivedBaseChangeComparison_openRestrictionMap`: for
  `K ∈ D_QCoh(𝒪_X)` the comparison is an isomorphism as soon as `c` is one, by flat base change on
  `U`.
* `DerivedExistenceSituation.isIso_derivedBaseChangeComparison_derivedSections`:
  [Stacks, Tag 0DIF], for `K` the object of [Stacks, Tag 0DIC] and `c` the canonical map
  `K|_{Xₙ} ⟶ Kₙ`.

## Implementation notes

The source writes `RΓ(U, -)` as a homotopy colimit of the functors `RΓ(X, - ⊗^𝐋 Eₘ)` for perfect
`Eₘ` ([Stacks, Tag 0CRR], a result relying on Noetherian approximation and the countability results
of [Stacks, Tag 0CRQ]), which is not in the library. Instead, the canonical map `K|_{Xₙ} ⟶ Kₙ` is
an isomorphism (`DerivedExistenceSituation.isIso_restrictionMap`), because by [Stacks, Tag 0DID]
and flat base change it becomes one after `RΓ(Xₙ, - ⊗^𝐋 E|_{Xₙ})` for every perfect `E`, and those
functors detect isomorphisms in `D_QCoh(𝒪_{Xₙ})` through a perfect generator of `D_QCoh(𝒪_X)`
([Stacks, Tag 09IS], [Stacks, Tag 08DQ], [Stacks, Tag 08EU]); then the comparison is flat base
change for `U ⟶ Spec A` followed by an isomorphism.

## References

* [Stacks Project, Tag 0DIF](https://stacks.math.columbia.edu/tag/0DIF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open StacksDraft.DerivedInverseLimit (derivedBaseChangeComparison)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory
  ModuleCat.hasDerivedCategory

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u}) (U : S.X.left.Opens) (n : ℕ)

/-- The square `Uₙ ⟶ U ⟶ X = Uₙ ⟶ Xₙ ⟶ X` of ringed spaces. -/
theorem levelOpenInclusion_comp_ι :
    (S.levelOpenInclusion U n).toLRSHom.toShHom ≫ U.ι.toLRSHom.toShHom =
      (S.levelOpen U n).ι.toLRSHom.toShHom ≫ S.levelInclusion n := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun t => t.toLRSHom.toShHom) (morphismRestrict_ι (schemeProjection S.system S.X n) U)

/-- The restriction to `Uₙ` of a map `c : Liₙ^*K ⟶ Kₙ`, read as a map out of the pullback of
`K|_U` along `Uₙ ⟶ U`. -/
def levelOpenRestriction
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))
    (c : (derivedPullback (S.levelInclusion n)).obj K ⟶ S.K n) :
    (derivedPullback (S.levelOpenInclusion U n).toLRSHom.toShHom).obj
        ((derivedPullback U.ι.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback (S.levelOpen U n).ι.toLRSHom.toShHom).obj (S.K n) :=
  (derivedPullbackCompIsoCanonical _ _).hom.app K ≫
    eqToHom (congrArg (fun t => (derivedPullback t).obj K) (S.levelOpenInclusion_comp_ι U n)) ≫
    (derivedPullbackCompIsoCanonical _ _).inv.app K ≫
    (derivedPullback (S.levelOpen U n).ι.toLRSHom.toShHom).map c

/-- The restriction to `Uₙ` of an isomorphism `c : Liₙ^*K ⟶ Kₙ` is an isomorphism. -/
instance (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))
    (c : (derivedPullback (S.levelInclusion n)).obj K ⟶ S.K n) [IsIso c] :
    IsIso (S.levelOpenRestriction U n K c) := by
  have := Functor.map_isIso (derivedPullback (S.levelOpen U n).ι.toLRSHom.toShHom) c
  dsimp only [levelOpenRestriction]
  infer_instance

/-- **The restriction map `RΓ(U, K) ⟶ RΓ(Uₙ, Kₙ)`** attached to a map `c : Liₙ^*K ⟶ Kₙ`: derived
global sections of `K|_U` pulled back along `Uₙ ⟶ U`
(`AlgebraicGeometry.LerayOver.pullbackSectionsMap`), followed by derived global sections on `Uₙ`
of the restriction of `c`. It is `A`-linear, the target being restricted along `A ⟶ Aₙ`. -/
def openRestrictionMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))
    (c : (derivedPullback (S.levelInclusion n)).obj K ⟶ S.K n) :
    (LerayOver.sections (S.openStructure U)).obj
        ((derivedPullback U.ι.toLRSHom.toShHom).obj K) ⟶
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        ((LerayOver.sections (S.levelOpenStructure U n)).obj
          ((derivedPullback (S.levelOpen U n).ι.toLRSHom.toShHom).obj (S.K n))) :=
  LerayOver.pullbackSectionsMap (limit.π S.system (op n)).hom (S.openStructure U)
      (S.levelOpenStructure U n) (S.levelOpenInclusion U n)
      (S.levelOpenInclusion_comp_openStructure U n)
      ((derivedPullback U.ι.toLRSHom.toShHom).obj K) ≫
    (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.map
      ((LerayOver.sections (S.levelOpenStructure U n)).map
        (S.levelOpenRestriction U n K c))

/-- **The comparison of [Stacks, Tag 0DIF] is an isomorphism once `c` is.** For a quasi-compact
open `U` and `K ∈ D_QCoh(𝒪_X)`, the comparison is the base-change map of derived global sections of
`K|_U` along `A ⟶ Aₙ`, which is invertible by flat base change since `U` is flat, quasi-compact
and quasi-separated over `A` and `Uₙ = U ×_{Spec A} Spec Aₙ`, followed by derived global sections
of the restriction of `c` to `Uₙ`. -/
theorem isIso_derivedBaseChangeComparison_openRestrictionMap
    (hU : IsCompact (U : Set S.X.left))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)) i).obj K).IsQuasicoherent)
    (c : (derivedPullback (S.levelInclusion n)).obj K ⟶ S.K n) [IsIso c] :
    IsIso (derivedBaseChangeComparison (limit.π S.system (op n)).hom
      (S.openRestrictionMap U n K c)) := by
  have := S.quasiCompact_openStructure U hU
  have h := LerayOver.isIso_derivedBaseChangeComparison_pullbackSectionsMap
    (limit.π S.system (op n)).hom (S.openStructure U) (S.levelOpenStructure U n)
    (S.levelOpenInclusion U n) (S.isPullback_levelOpen U n)
    ((derivedPullback U.ι.toLRSHom.toShHom).obj K)
    (fun i => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel U.ι K hK i)
  have := Functor.map_isIso (LerayOver.sections (S.levelOpenStructure U n))
    (S.levelOpenRestriction U n K c)
  rw [openRestrictionMap, StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison_comp_map]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h this

/-- In Situation [Stacks, Tag 0DIB] let `K` be as in [Stacks, Tag 0DIC]. For any quasi-compact
open `U ⊆ X` we have `RΓ(U, K) ⊗^𝐋_A Aₙ = RΓ(Uₙ, Kₙ)` in `D(Aₙ)`, where `Uₙ = U ∩ Xₙ`.

Here `K` is `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject`,
`RΓ(U, K)` is the `A`-linear derived global sections of `K|_U`, `RΓ(Uₙ, Kₙ)` the `Aₙ`-linear
derived global sections of `Kₙ|_{Uₙ}`, and the identification is the canonical map
`RΓ(U, K) ⊗^𝐋_A Aₙ ⟶ RΓ(Uₙ, Kₙ)`: the adjoint of
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.openRestrictionMap`, which pulls
derived sections back along `Uₙ ⟶ U` and applies the canonical map `K|_{Xₙ} ⟶ Kₙ` adjoint to the
projection `K ⟶ R(iₙ)_* Kₙ`. -/
@[stacks 0DIF]
theorem isIso_derivedBaseChangeComparison_derivedSections (hU : IsCompact (U : Set S.X.left)) :
    IsIso (derivedBaseChangeComparison (limit.π S.system (op n)).hom
      (S.openRestrictionMap U n S.limitObject (S.restrictionMap n))) :=
  S.isIso_derivedBaseChangeComparison_openRestrictionMap U n hU S.limitObject
    S.isQuasicoherent_homology_limitObject (S.restrictionMap n)

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

end
