module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# The direct image of abelian sheaves preserves injectives, in any coefficient universe

For a continuous map `g : X ⟶ Y` of topological spaces in `TopCat.{s}` the direct image `g_*` of
sheaves of abelian groups in `AddCommGrpCat.{t}` preserves injective objects whenever
`UnivLE.{s, t}`, because its left adjoint `g^{-1}` is exact. This is applied to the direct image
of the derived apparatus of [Stacks, Tag 0DCU], at the coefficient universe `max (u + 1) v`.

## Main results

All in the namespace `Stacks.Topology`.

* `preservesFiniteLimits_opensMapOpLan`: the left Kan extension along `(Opens.map g).op` of
  presheaves of abelian groups in any dominating universe is left exact.
* `preservesFiniteLimits_sheafPullbackOpensMap`: hence `g^{-1}` is left exact.
* `preservesInjectiveObjects_sheafPushforwardOpensMap`: hence `g_*` preserves injectives.

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `preservesInjectiveObjects_topologicalPushforward`: the direct image `topologicalPushforward`
  preserves injective abelian sheaves.
* `isZero_zariskiRightDerivedPresheaf_pushforward_opensToSlice`: for `J` injective and `p > 0` the
  cohomology presheaf of `π_Y^{-1}(f_* J)` on the big site over `Y` vanishes at every object
  coming from an open subset of `Y`.

## Implementation notes

`Stacks.Cohomology.Leray.pushforward_preservesInjectiveObjects` and
`Stacks.Cohomology.SpectralLimit.preservesInjectiveObjects_sheafPushforward` fix the coefficient
universe to that of the spaces, because `CategoryTheory.lan_preservesFiniteLimits_of_flat` does;
the proofs here use the general-universe `Stacks.Topology.lan_preservesFiniteLimits_of_flat`
instead. For the same reason `Functor.sheafPullbackConstruction.preservesFiniteLimits` is used
rather than the `Functor.SmallCategories` instance of the same name, which does not apply here.

The two `HasSheafify` instances of `preservesInjectiveObjects_topologicalPushforward` are
transported by `inferInstanceAs`: the topologies `Opens.grothendieckTopology X.obj` and
`Opens.grothendieckTopology ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X)`
are definitionally but not syntactically equal, so instance search does not cross between them.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Topology

universe t s

variable {X Y : TopCat.{s}} (g : X ⟶ Y) [UnivLE.{s, t}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{t}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{t}]

omit [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{t}]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{t}] in
/-- Under `UnivLE.{s, t}`, the left Kan extension along `(Opens.map g).op` of presheaves of
abelian groups in `AddCommGrpCat.{t}` preserves finite limits. -/
theorem preservesFiniteLimits_opensMapOpLan :
    PreservesFiniteLimits ((Opens.map g).op.lan :
      ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{t}) ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{t})) := by
  have : PreservesFilteredColimitsOfSize.{s, s} (forget AddCommGrpCat.{t}) :=
    preservesFilteredColimitsOfSize_of_univLE.{t, t, s, s} _
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat (Opens.map g) (fun Z => ?_)
  have : IsFiltered (CostructuredArrow (Opens.map g).op Z) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (Opens.map g) (Opposite.unop Z))
  infer_instance

/-- Under `UnivLE.{s, t}`, the inverse image along `g` of sheaves of abelian groups in
`AddCommGrpCat.{t}` preserves finite limits. -/
theorem preservesFiniteLimits_sheafPullbackOpensMap :
    PreservesFiniteLimits ((Opens.map g).sheafPullback AddCommGrpCat.{t}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
  have := preservesFiniteLimits_opensMapOpLan.{t} g
  Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Under `UnivLE.{s, t}`, the direct image along `g` of sheaves of abelian groups in
`AddCommGrpCat.{t}` preserves injective objects. -/
theorem preservesInjectiveObjects_sheafPushforwardOpensMap :
    ((Opens.map g).sheafPushforwardContinuous AddCommGrpCat.{t}
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_sheafPullbackOpensMap.{t} g
  have : ((Opens.map g).sheafPullback AddCommGrpCat.{t}
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Opens.map g).sheafAdjunctionContinuous AddCommGrpCat.{t}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))

namespace LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]

omit [UnivLE.{s, t}] in
/-- The direct image `topologicalPushforward S f` along the underlying continuous map of a
morphism of the site preserves injective sheaves of abelian groups in
`AddCommGrpCat.{max (u + 1) v}`. -/
theorem preservesInjectiveObjects_topologicalPushforward :
    (topologicalPushforward.{u, w, v} S f).PreservesInjectiveObjects := by
  have hY : HasSheafify (Opens.grothendieckTopology
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj Y))
      AddCommGrpCat.{max (u + 1) v} :=
    inferInstanceAs (HasSheafify (Opens.grothendieckTopology Y.obj)
      AddCommGrpCat.{max (u + 1) v})
  have hX : HasSheafify (Opens.grothendieckTopology
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X))
      AddCommGrpCat.{max (u + 1) v} :=
    inferInstanceAs (HasSheafify (Opens.grothendieckTopology X.obj)
      AddCommGrpCat.{max (u + 1) v})
  exact preservesInjectiveObjects_sheafPushforwardOpensMap.{max (u + 1) v}
    ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)

variable [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})]

omit [UnivLE.{s, t}] in
/-- For `J` injective on the small Zariski site of `X` and `p > 0`, the `p`-th cohomology
presheaf of `π_Y^{-1}(f_* J)` on the big site over `Y` is zero at every object coming from a
subset of `Y` that is open. -/
theorem isZero_zariskiRightDerivedPresheaf_pushforward_opensToSlice
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    [Injective J] (p : ℕ) (hp : 0 < p) (V : Opens Y.obj) :
    IsZero ((((sheafToPresheaf (S.zariskiTopology.over Y)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).obj
        ((topologicalPushforward.{u, w, v} S f).obj J))).obj
          (op ((S.opensToSlice Y).1.obj V))) :=
  have : Injective ((topologicalPushforward.{u, w, v} S f).obj J) :=
    (preservesInjectiveObjects_topologicalPushforward.{u, w, v} S f).injective_obj ‹Injective J›
  isZero_zariskiRightDerivedPresheaf_inverseImage_opensToSlice.{u, w, v} S Y _ p hp V

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology

end
