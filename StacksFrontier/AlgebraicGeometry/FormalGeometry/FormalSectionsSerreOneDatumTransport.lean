module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneRealization
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Uniqueness

/-!
# Stacks 0BLX need only be proved for one localization triangle datum

`Stacks.Algebraization.CompletedComplementIsFormalSections` quantifies over *every*
`Stacks.LocalCohomology.LocalizationTriangleData` of the ideal `J`. That is the shape the proof
of Stacks 0EIF consumes, but it is not the shape in which the statement can be proved: a datum
is an abstract functor `complement` subject only to a distinguished triangle and a degree-zero
sections equivalence, so nothing about derived sections on `V = Spec A ∖ V(J)` is available for
it, while the concrete Čech datum
`Stacks.LocalCohomology.localizationTriangleData` is a mapping cone one can compute with.

This file closes that gap. By `Stacks.LocalCohomology.complementIso` the `complement` functors of
any two data are naturally isomorphic, and the derived-limit property transports along a natural
isomorphism of towers (`NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofNatIso`) and
along an isomorphism of the limit object
(`NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofIso`). What needs checking is that the
*normalization* clause transports as well, and it does: the comparison commutes with the
completion unit by naturality of the unit, and with the reduction maps `M ⟶ M/IⁿM` by naturality
of the comparison itself.

So it suffices to exhibit one datum per `(A, I, J, M)` for which the conclusion holds.

## Main results

* `Stacks.Algebraization.completedComplementIsFormalSections_of_forall_exists` — **the
  reduction**: if for every Noetherian `A`, every pair of ideals `I`, `J` and every finite module
  `M` *some* localization triangle datum of `J` satisfies the derived-limit-with-normalized-
  projections conclusion, then `Stacks.Algebraization.CompletedComplementIsFormalSections` holds.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **Stacks 0BLX need only be proved for one localization triangle datum.** The conclusion of
`Stacks.Algebraization.CompletedComplementIsFormalSections` for one datum of `J` implies it for
every datum of `J`, because the `complement` functors of two data are canonically naturally
isomorphic (`Stacks.LocalCohomology.complementIso`) and both the derived-limit property and the
normalization of its projections transport along that isomorphism. -/
public theorem completedComplementIsFormalSections_of_forall_exists
    (h : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
      (M : ModuleCat.{u} A) [Module.Finite A M],
      ∃ D : LocalizationTriangleData.{u, u} A J J.fg_of_isNoetherianRing,
        ∃ _h : HasProduct (fun n : ℕ ↦
            (idealPowerQuotientTower.{u, u} I M ⋙ D.complement).obj ⟨n⟩),
          ∃ π : ∀ n : ℕ, (adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj
              (D.complement.obj M) ⟶ (idealPowerQuotientTower.{u, u} I M ⋙ D.complement).obj ⟨n⟩,
            NoetherianAdicCompletion.IsDerivedLimitWithProjections
                (idealPowerQuotientTower.{u, u} I M ⋙ D.complement)
                ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj
                  (D.complement.obj M)) π ∧
              ∀ n : ℕ, (adicCompletionUnit A I I.fg_of_isNoetherianRing).app
                  (D.complement.obj M) ≫ π n =
                D.complement.map ((idealPowerQuotientCone.{u, u} I M).π.app ⟨n⟩)) :
    CompletedComplementIsFormalSections.{u} := by
  intro A _ _ I J M _ D'
  obtain ⟨D, hprod, π, hlim, hnorm⟩ := h A I J M
  have e : D.complement ≅ D'.complement := complementIso D D'
  -- the two towers are isomorphic, by whiskering the comparison
  let eT : idealPowerQuotientTower.{u, u} I M ⋙ D.complement ≅
      idealPowerQuotientTower.{u, u} I M ⋙ D'.complement :=
    Functor.isoWhiskerLeft (idealPowerQuotientTower.{u, u} I M) e
  have hprod' : HasProduct
      (fun n : ℕ ↦ (idealPowerQuotientTower.{u, u} I M ⋙ D'.complement).obj ⟨n⟩) :=
    hasLimit_of_iso
      (F := Discrete.functor
        (fun n : ℕ ↦ (idealPowerQuotientTower.{u, u} I M ⋙ D.complement).obj ⟨n⟩))
      (Discrete.natIso fun n ↦ eT.app ⟨n.as⟩)
  refine ⟨hprod', ?_⟩
  -- transport the derived limit, first along the tower isomorphism, then along the object one
  have hlim₂ := (hlim.ofNatIso eT).ofIso
    ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).mapIso (e.app M))
  refine ⟨_, hlim₂, ?_⟩
  intro n
  -- the normalization clause transports: unit naturality, the given clause, then the
  -- naturality of the comparison at the reduction `M ⟶ M/IⁿM`
  have hu := ((adicCompletionUnit A I I.fg_of_isNoetherianRing).naturality (e.inv.app M)).symm
  have hna := e.hom.naturality ((idealPowerQuotientCone.{u, u} I M).π.app ⟨n⟩)
  simp only [eT, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.mapIso_inv,
    Iso.app_inv, Functor.id_map, Functor.const_obj_obj] at hu hna ⊢
  rw [← Category.assoc, hu, Category.assoc, ← Category.assoc _ (π n), hnorm n]
  exact (Iso.inv_comp_eq (e.app M)).2 hna

end Stacks.Algebraization

end
