module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PullbackTube
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChangeReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FibrewiseSoftPullback

/-!
# Fibrewise softness of `h^{-1} J` for a base change in a locally quasi-compact Zariski situation

Let `S` be a locally quasi-compact Zariski situation, `f : X ⟶ Y` a morphism of its site and
`j : U ⟶ Y` another one, and let `U ×_Y X` be their fibre product, with projections
`f' = pullback.fst j f` and `h = pullback.snd j f`. Let `J` be a flasque abelian sheaf on the
space underlying `X`. If the fibres of `f` are quasi-compact and its points are separated, then
the restriction of `h^{-1} J` to every fibre of `f'` is soft. This is the fibrewise hypothesis of
`Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` and of
`Stacks.Topology.isZero_rightDerived_pushforward_of_isSoft_fiber`.

## Main results

* `isSoft_restrictionFunctorUnivLE_fiber_snd_of_isFlasque` (in the namespace
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation`): the fibrewise softness of `h^{-1} J`.

## Implementation notes

The projection `h` carries the fibre of `f'` over a point homeomorphically onto the fibre of `f`
over its image, by `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_sitePullback_homeo`,
and softness of the restriction of a flasque sheaf transports along that homeomorphism by
`Stacks.Topology.isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque`.

The coefficient universe is independent of the universe of the site: the hypothesis is
`UnivLE.{u, t}`.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe t u w

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

variable {X Y : S.category} (f : X ⟶ Y) {U : S.category} (j : U ⟶ Y)

/-- For `J` a flasque abelian sheaf on `X`, `f' = pullback.fst j f` and `h = pullback.snd j f`
the two projections of the fibre product `U ×_Y X`, the fibres of `f` quasi-compact and the
points of `f` separated, the restriction of `h^{-1} J` to every fibre of `f'` is soft. -/
theorem isSoft_restrictionFunctorUnivLE_fiber_snd_of_isFlasque [UnivLE.{u, t}]
    (J : ((siteToTop S).obj X).Sheaf AddCommGrpCat.{t}) [TopCat.Sheaf.IsFlasque J]
    (hcpt : ∀ y : (siteToTop S).obj Y,
      IsCompact ((((siteToTop S).map f).hom :
        (siteToTop S).obj X → (siteToTop S).obj Y) ⁻¹' ({y} : Set _)))
    (hsep : IsSeparatedMap
      (((siteToTop S).map f).hom : (siteToTop S).obj X → (siteToTop S).obj Y))
    (w : (siteToTop S).obj U) :
    IsSoft ((restrictionFunctorUnivLE.{t} ((siteToTop S).obj (Limits.pullback j f))
      ((((siteToTop S).map (Limits.pullback.fst j f)).hom :
        (siteToTop S).obj (Limits.pullback j f) → (siteToTop S).obj U) ⁻¹' ({w} : Set _))).obj
      ((inverseImageUnivLE.{t} ((siteToTop S).map (Limits.pullback.snd j f))).obj J)) := by
  obtain ⟨e, he⟩ := exists_sitePullback_homeo S f j
  exact isSoft_restrictionFunctorUnivLE_fiber_of_isFlasque.{t}
    ((siteToTop S).map f) ((siteToTop S).map j)
    ((siteToTop S).map (Limits.pullback.fst j f))
    ((siteToTop S).map (Limits.pullback.snd j f)) e he J hcpt hsep w

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
