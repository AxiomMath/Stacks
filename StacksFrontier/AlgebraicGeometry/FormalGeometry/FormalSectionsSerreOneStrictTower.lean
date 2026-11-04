module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitDescent
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMilnorTriangle
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences

/-!
# Stacks 0BLX for a strictified complement, granted that the unit-induced comparison is invertible

`Stacks.Algebraization.completedComplementIsFormalSections_of_forall_exists` reduces Stacks 0BLX
to exhibiting, for one localization triangle datum, a derived limit of the tower
`n ↦ D.complement.obj (M/IⁿM)` sitting at the derived `I`-adic completion of `D.complement.obj M`
with projections normalized against the completion unit.

This file supplies that for a complement functor of the form `G ⋙ DerivedCategory.Q` — the shape
the Čech datum has, with `G = Stacks.LocalCohomology.cechConeFunctor f`. For such a complement the
tower is the image under `Q` of a tower of cochain complexes, so
`DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi` already computes a derived limit of
it with *pinned* projections, at `Q.obj (limit (idealPowerQuotientTower I M ⋙ G))`, as soon as the
tower's transition maps are epimorphisms.

What remains between that and Stacks 0BLX is a single invertibility. The complex-level comparison
`G.obj M ⟶ limit (idealPowerQuotientTower I M ⋙ G)` is the limit lift of the cone `G` carries the
adic quotient cone to; its image under `Q` lands in a derived complete object, so it descends
along the completion unit to a canonical map

`(G ⋙ Q).obj M ^∧ ⟶ Q.obj (limit (idealPowerQuotientTower I M ⋙ G))`

— `Stacks.Algebraization.completionDescent`, the *unit-induced* comparison. Granted that this map
is invertible, the derived limit transports to the completion and the normalization clause follows
from the defining clause of the descent together with `limit.lift_π`. Nothing else is left: every
other compatibility is a complex-level identity.

The invertibility is genuinely the remaining content, and it must be asserted of the unit-induced
map specifically. A map matching the projections is not enough: for any `η`, the map
`𝟙 + η ≫ δ⟦-1⟧` built from the connecting morphism of the Milnor triangle matches the same
projections and is not in general invertible. That is why the hypothesis here is `IsIso` of
`completionDescent`, which is pinned by a universal property, rather than of some map agreeing
with the projections.

## Main results

* `exists_normalized_isDerivedLimitWithProjections_of_isIso_completionDescent`: for a strictified
  complement with epimorphic tower transitions and a derived complete strict limit, invertibility
  of the unit-induced comparison gives a derived limit of the tower at the completion whose
  projections are normalized against the completion unit.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- **The complex-level comparison of a strictified complement with its adic quotient tower**: the
limit lift of the cone that `G` carries the adic quotient cone
`Stacks.LocalCohomology.idealPowerQuotientCone` to.

Its characterizing clause is
`Stacks.Algebraization.strictTowerComparison_comp_limit_π`: composing with the level-`n`
projection of the limit returns `G.map` of the level-`n` quotient map `M ⟶ M/IⁿM`. -/
public def strictTowerComparison (I : Ideal A) (M : ModuleCat.{u} A)
    (G : ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ) :
    G.obj M ⟶ limit (idealPowerQuotientTower.{u, u} I M ⋙ G) :=
  limit.lift (idealPowerQuotientTower.{u, u} I M ⋙ G)
    (G.mapCone (idealPowerQuotientCone.{u, u} I M))

/-- **The characterizing clause of `Stacks.Algebraization.strictTowerComparison`.** -/
public theorem strictTowerComparison_comp_limit_π (I : Ideal A) (M : ModuleCat.{u} A)
    (G : ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕᵒᵖ) :
    strictTowerComparison I M G ≫ limit.π (idealPowerQuotientTower.{u, u} I M ⋙ G) n =
      G.map ((idealPowerQuotientCone.{u, u} I M).π.app n) :=
  limit.lift_π _ n

/-- **Stacks 0BLX for a strictified complement, granted the unit-induced comparison.** Let the
complement functor be `G ⋙ DerivedCategory.Q`, let the tower of cochain complexes
`idealPowerQuotientTower I M ⋙ G` have epimorphic transition maps, and let the image under `Q` of
its ordinary inverse limit be derived `I`-complete. If the unit-induced comparison
`Stacks.Algebraization.completionDescent` of the complex-level comparison
`Stacks.Algebraization.strictTowerComparison` is invertible, then the derived `I`-adic completion
of `(G ⋙ Q).obj M` is a derived limit of the tower `n ↦ (G ⋙ Q).obj (M/IⁿM)` with projections
normalized against the completion unit.

The derived limit transports along the invertible comparison by
`NoetherianAdicCompletion.isDerivedLimitWithProjections_of_iso`, and the normalization clause is
the defining clause of the descent followed by `limit.lift_π`. -/
public theorem exists_normalized_isDerivedLimitWithProjections_of_isIso_completionDescent
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
    (G : ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    [∀ n : ℕ, Epi ((idealPowerQuotientTower.{u, u} I M ⋙ G).map (homOfLE (Nat.le_succ n)).op)]
    (hcomplete : IsDerivedComplete I
      (DerivedCategory.Q.obj (limit (idealPowerQuotientTower.{u, u} I M ⋙ G))))
    (hiso : IsIso (completionDescent I hI hcomplete
      (DerivedCategory.Q.map (strictTowerComparison I M G)))) :
    ∃ _h : HasProduct (fun n : ℕ ↦
        (idealPowerQuotientTower.{u, u} I M ⋙ G ⋙ DerivedCategory.Q).obj ⟨n⟩),
      ∃ π : ∀ n : ℕ, (adicCompletionFunctor A I hI).obj ((G ⋙ DerivedCategory.Q).obj M) ⟶
          (idealPowerQuotientTower.{u, u} I M ⋙ G ⋙ DerivedCategory.Q).obj ⟨n⟩,
        NoetherianAdicCompletion.IsDerivedLimitWithProjections
            (idealPowerQuotientTower.{u, u} I M ⋙ G ⋙ DerivedCategory.Q)
            ((adicCompletionFunctor A I hI).obj ((G ⋙ DerivedCategory.Q).obj M)) π ∧
          ∀ n : ℕ, (adicCompletionUnit A I hI).app ((G ⋙ DerivedCategory.Q).obj M) ≫ π n =
            (G ⋙ DerivedCategory.Q).map ((idealPowerQuotientCone.{u, u} I M).π.app ⟨n⟩) := by
  have := hiso
  set d := completionDescent I hI hcomplete (DerivedCategory.Q.map (strictTowerComparison I M G))
  obtain ⟨hprod, hlim⟩ := DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi
    (idealPowerQuotientTower.{u, u} I M ⋙ G)
  refine ⟨hprod, fun n ↦ d ≫
    DerivedCategory.Q.map (limit.π (idealPowerQuotientTower.{u, u} I M ⋙ G) ⟨n⟩), ?_, ?_⟩
  · exact NoetherianAdicCompletion.isDerivedLimitWithProjections_of_iso hlim (asIso d) fun _ ↦ rfl
  · intro n
    rw [← Category.assoc, completionDescent_unit, ← Functor.map_comp,
      strictTowerComparison_comp_limit_π]
    rfl

end Stacks.Algebraization

end
