module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The weighted trace as a natural transformation

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `w` be an
integer-valued function on `X`. Part (1) of Stacks 0GKH says that the trace maps
`Tr_{f, w, F} : f_! f^{-1}F ⟶ F` of Stacks 0GKG are functorial in `F`, which is proved as
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_naturality`: every naturality square
commutes. This file packages that into the statement that a family of trace maps, one for each
abelian sheaf, *is* a natural transformation `f_! f^{-1} ⟶ id`, which is the form in which the
derived version of part (3) consumes it.

## Main definitions

* `AlgebraicGeometry.SmallEtale.weightedTraceFamilyNatTrans` — a family of morphisms
  `f_! f^{-1}F ⟶ F`, one for each abelian sheaf `F` on the small étale site of `Y`, each with the
  behaviour on geometric stalks which characterises the trace map of Stacks 0GKG, is a natural
  transformation.

## Main results

* `AlgebraicGeometry.SmallEtale.weightedTraceFamilyNatTrans_app` — its component at a sheaf is
  the given trace map.
* `AlgebraicGeometry.SmallEtale.weightedTraceFamilyNatTrans_unique` — two such families agree, by
  the uniqueness half of Stacks 0GKG.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **A family of weighted trace maps is a natural transformation.** Given, for each abelian
sheaf `F` on the small étale site of `Y`, a morphism `τ F : f_! f^{-1}F ⟶ F` with the behaviour
on geometric stalks which characterises the trace map of Stacks 0GKG, the family is a natural
transformation `f_! f^{-1} ⟶ id`. Naturality is part (1) of Stacks 0GKH. -/
@[sga "4 XVII 6.2.5"]
public def weightedTraceFamilyNatTrans (w : X.obj → ℤ)
    (τ : ∀ F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v},
      (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
    (hτ : ∀ F, HasWeightedTraceStalks.{u, v} B f w F (τ F)) :
    abPullback.{u, v} B f ⋙ fShriekFunctor.{u, v} B f ⟶
      𝟭 (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) where
  app F := τ F
  naturality _ _ φ := hasWeightedTraceStalks_naturality.{u, v} B f w φ (hτ _) (hτ _)

/-- The component of the natural transformation at a sheaf is the given trace map. -/
@[simp]
public theorem weightedTraceFamilyNatTrans_app (w : X.obj → ℤ)
    (τ : ∀ F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v},
      (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
    (hτ : ∀ F, HasWeightedTraceStalks.{u, v} B f w F (τ F))
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    (weightedTraceFamilyNatTrans.{u, v} B f w τ hτ).app F = τ F :=
  rfl

/-- Two families of weighted trace maps define the same natural transformation: by the
uniqueness half of Stacks 0GKG the characterisation on geometric stalks determines at most one
morphism for each sheaf. -/
public theorem weightedTraceFamilyNatTrans_unique (w : X.obj → ℤ)
    (τ τ' : ∀ F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v},
      (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
    (hτ : ∀ F, HasWeightedTraceStalks.{u, v} B f w F (τ F))
    (hτ' : ∀ F, HasWeightedTraceStalks.{u, v} B f w F (τ' F)) :
    weightedTraceFamilyNatTrans.{u, v} B f w τ hτ =
      weightedTraceFamilyNatTrans.{u, v} B f w τ' hτ' :=
  NatTrans.ext (funext fun F =>
    hasWeightedTraceStalks_unique.{u, v} B f w F (hτ F) (hτ' F))

end AlgebraicGeometry.SmallEtale

end
