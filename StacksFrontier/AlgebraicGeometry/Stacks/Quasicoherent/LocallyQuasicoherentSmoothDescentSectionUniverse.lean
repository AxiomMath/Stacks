module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocalitySectionUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent

/-!
# Smooth descent of local quasi-coherence, at a free section universe

`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent` is
**Stacks 075Y** for modules whose sections lie in the universe of the structure sheaf. This file
proves it with the universe of the sections free.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective'`: **Stacks 075Y,
  with the universe of the sections free.**

## Implementation notes

Local quasi-coherence itself (**Stacks 06WJ**) is stated for an arbitrary section universe, and so
are the inverse image, the identification of **Stacks 075D** part (3) used here, and the
étale-locality of the second clause of **Stacks 06WJ** at a free section universe,
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover'`. The
reading at section universe `u + 1` is the one the higher direct images of **Stacks 06WE**
produce and the one hypothesis (3) of **Stacks 076Z** asks for.

## References

* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 075Y, with the universe of the sections free.** Let `f j : 𝒵 j ⟶ 𝒳` be a family of
smooth 1-morphisms of algebraic stacks over `S` with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a
sheaf of `𝒪_𝒳`-modules on `𝒳_étale`. If every inverse image `f j^{-1} F` is locally
quasi-coherent, then so is `F`.

`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isSmooth_jointlySurjective` is this statement
at the universe of the structure sheaf, and is where the tag is registered; the reading at
section universe `u + 1` is the one the higher direct images of **Stacks 06WE** produce. -/
theorem isLocallyQuasicoherent_of_isSmooth_jointlySurjective'
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, m} B S hS (f j)).obj F)) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F := by
  classical
  refine ⟨hF, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS _ _ x F hF, ?_⟩⟩
  obtain ⟨I, W, e, a, hetale, hcov, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS f hsmooth hjs
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  choose zz αα hαα using hlift
  exact isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover'
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids x F hF
    (fun i => (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj (zz i)) αα
    (fun i => etale_map_left_of_isHomLift B S hS 𝒳.val.val.p _ (hetale i) (αα i) (hαα i))
    (fun t => (hcov t).imp fun i hi =>
      range_map_left_of_isHomLift B S hS 𝒳.val.val.p (αα i) (hαα i) hi)
    (fun i => isQuasicoherentOnSite_restrictModuleToSmallEtale_image.{u, u + 1, u, u + 1, u, m}
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f (a i)).hom)
      (isFibredOneMorphism_homFunctor_comp B S hS (f (a i)).hom) F hF (hlqc (a i)) (zz i))

end AlgebraicGeometry.Stack

end
