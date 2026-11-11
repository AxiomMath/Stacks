module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceSize
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.CategoryTheory.Sites.OverPullbackPushforward

/-!
# Étale objects lift across a base change that is a thickening

Let `B` be a big fppf site, `S` and `Z` objects of it, `z : Z ⟶ S`, and `U` an object of the
big fppf category over `S` such that the first projection `U ×_S Z ⟶ U` is a thickening. Then
every étale `V ⟶ U ×_S Z` is dominated, near any of its points, by the base change
`T ×_S Z` of an étale `T ⟶ U`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_etale_lift_baseChange_of_isThickening`: given an étale
  `e : V ⟶ U ×_S Z` and a point `v` of `V`, there is an étale `t : T ⟶ U` whose image contains
  the image of `v` in `U`, and a morphism `k : T ×_S Z ⟶ V` with `k ≫ e` the base change of `t`.

## Implementation notes

The scheme `T` is the étale lift of `V` across the thickening `U ×_S Z ⟶ U` given by Stacks 039R
with size control,
`Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective`, so
that `T ×_U (U ×_S Z) ≅ V` over `U ×_S Z`; the morphism `k` is the canonical map
`T ×_S Z ⟶ T ×_U (U ×_S Z)` followed by this isomorphism.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Étale objects lift across a thickening base change.** Let `z : Z ⟶ S` be a morphism of
the big fppf site and `U` an object over `S` whose first projection `U ×_S Z ⟶ U` is a
thickening. For an étale `e : V ⟶ U ×_S Z` and a point `v` of `V` there is an étale
`t : T ⟶ U` whose image contains the image of `v` in `U`, together with `k : T ×_S Z ⟶ V`
such that `k ≫ e` is the base change `T ×_S Z ⟶ U ×_S Z` of `t`. -/
theorem exists_etale_lift_baseChange_of_isThickening {Z : Scheme.{u}} (hZ : B.Contains Z)
    (z : B.obj hZ ⟶ B.obj hS) (U : BigFppfOver B S hS)
    (hU : Stacks.Thickenings.IsThickening (B.inclusion.map (Sheaf.baseChangeFst z U).left))
    {V : BigFppfOver B S hS} (e : V ⟶ (Over.map z).obj ((Over.pullback z).obj U))
    (he : Etale ((BigFppfOver.toScheme B S hS).map e))
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ (T : BigFppfOver B S hS) (t : T ⟶ U) (k : (Over.map z).obj ((Over.pullback z).obj T) ⟶ V),
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧
      (BigFppfOver.toScheme B S hS).map (e ≫ Sheaf.baseChangeFst z U) v ∈
        Set.range ((BigFppfOver.toScheme B S hS).map t) ∧
      k ≫ e = (Over.map z).map ((Over.pullback z).map t) := by
  obtain ⟨hci, hsurj⟩ := hU
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (Sheaf.baseChangeFst z U)) := hci
  obtain ⟨T, t, ht, ι, hι⟩ :=
    Stacks.Etale.exists_bigFppfOver_etale_pullback_iso_of_isClosedImmersion_of_surjective B S hS
      (Sheaf.baseChangeFst z U) hsurj V ((BigFppfOver.toScheme B S hS).map e) he
  have hw : (BigFppfOver.toScheme B S hS).map (Sheaf.baseChangeFst z T) ≫
      (BigFppfOver.toScheme B S hS).map t =
      (BigFppfOver.toScheme B S hS).map ((Over.map z).map ((Over.pullback z).map t)) ≫
      (BigFppfOver.toScheme B S hS).map (Sheaf.baseChangeFst z U) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Sheaf.baseChangeFst_naturality]
  have hV : B.inclusion.map V.hom = (BigFppfOver.toScheme B S hS).map e ≫
      B.inclusion.map ((Over.map z).obj ((Over.pullback z).obj U)).hom := by
    rw [← Over.w e, Functor.map_comp]
    rfl
  have hTZ : B.inclusion.map ((Over.map z).obj ((Over.pullback z).obj T)).hom =
      (BigFppfOver.toScheme B S hS).map ((Over.map z).map ((Over.pullback z).map t)) ≫
      B.inclusion.map ((Over.map z).obj ((Over.pullback z).obj U)).hom := by
    rw [← Over.w ((Over.map z).map ((Over.pullback z).map t)), Functor.map_comp]
    rfl
  obtain ⟨k, hk⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (pullback.lift _ _ hw ≫ ι.hom)
    (by rw [hV, hTZ, Category.assoc, ← Category.assoc ι.hom, hι, pullback.lift_snd_assoc])
  refine ⟨T, t, k, ht, ⟨pullback.fst ((BigFppfOver.toScheme B S hS).map t)
    ((BigFppfOver.toScheme B S hS).map (Sheaf.baseChangeFst z U)) (ι.inv v), ?_⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, pullback.condition, Functor.map_comp, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, ← hι, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply ι.inv,
      Iso.inv_hom_id]
    rfl
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hk, Category.assoc, hι, pullback.lift_snd]

end AlgebraicGeometry.BigFppfOver
