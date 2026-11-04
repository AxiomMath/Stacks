module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.StarCoverReducible
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic

/-!
# Lifting invertible modules along a composite, and the surjective factorization

[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) asserts that `Pic X → Pic Z` is
surjective for a closed immersion `i : Z ⟶ X` into a scheme with Noetherian underlying space of
dimension at most one. The property "every invertible module on the source is the pullback of an
invertible module on the target" is named here, for one morphism at a time, as
`Stacks.AlgebraicGeometry.Tag09NY.LiftsInvertibleModules`, and the basic fact about it is that it
is **closed under composition**: the comparison `f^*g^* ≅ (g ∘ f)^*` is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, which is available in Tag 09NY's own
`RingedSpaceModuleAdjunction.modulePullback` spelling because the two functors agree by `rfl`.

Composition is what turns the already-proved **surjective** case of Tag 09NY
(`Stacks.LiftInvertible.exists_modulePullback_iso_of_surjective`) into a reduction tool: if `i`
factors as `Z ⟶ W ⟶ X` with `W ⟶ X` a *surjective* closed immersion, then Tag 09NY for `i`
follows from Tag 09NY for `Z ⟶ W`. Only the topology of `X` is used, so the intermediate scheme
`W` may be as non-reduced as one likes.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag09NY.LiftsInvertibleModules`: Tag 09NY's conclusion for a
  single morphism.

## Main results

* `Stacks.AlgebraicGeometry.Tag09NY.LiftsInvertibleModules.comp`: the property composes.
* `Stacks.LiftInvertible.picPullbackSurjective_of_surjective`: the surjective case of Tag
  09NY, read as this property.
* `Stacks.LiftInvertible.picPullbackSurjective_comp_of_surjective`: **the reduction**. For a
  surjective closed immersion `k : W ⟶ X` into a Noetherian `X` of dimension at most one, Tag
  09NY for `j ≫ k` follows from Tag 09NY for `j`.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_factorization`: the same conclusion written
  in Tag 09NY's own `∃`-form, for a morphism presented as a composite.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

open Stacks.AlgebraicGeometry.Tag09NY (LiftsInvertibleModules)

namespace Stacks.LiftInvertible

/-- **The surjective case of Tag 09NY, as `LiftsInvertibleModules`.** This is
`Stacks.LiftInvertible.exists_modulePullback_iso_of_surjective` with its module and
invertibility arguments turned into the binders of the predicate. -/
theorem picPullbackSurjective_of_surjective {X W : Scheme.{u}} (k : W ⟶ X)
    [IsClosedImmersion k] (hsurj : Function.Surjective k.base) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) : LiftsInvertibleModules k :=
  fun L hL =>
    let ⟨M, hM, h⟩ := exists_modulePullback_iso_of_surjective k hsurj hdim L hL
    ⟨M, hM, h⟩

/-- **Tag 09NY reduces along a surjective closed immersion.** Let `X` have Noetherian underlying
space of dimension at most one, let `k : W ⟶ X` be a closed immersion which is **onto**, and let
`j : Z ⟶ W` be any morphism for which Tag 09NY's conclusion holds. Then Tag 09NY's conclusion
holds for `j ≫ k`.

So a closed subscheme `Z ⊆ X` may be enlarged to any closed subscheme `W` with the **same
underlying space as `X`** at no cost: the work is entirely transferred to `Z ⟶ W`. Nothing is
assumed about `W` beyond that; in particular `W` is allowed to be non-reduced, which is what
makes this usable when `X` is.

The tag is withheld: `j` is a hypothesis here, not a conclusion. -/
theorem picPullbackSurjective_comp_of_surjective {X W Z : Scheme.{u}} (j : Z ⟶ W) (k : W ⟶ X)
    [IsClosedImmersion k] (hsurj : Function.Surjective k.base) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (hj : LiftsInvertibleModules j) :
    LiftsInvertibleModules (j ≫ k) :=
  LiftsInvertibleModules.comp k j (picPullbackSurjective_of_surjective k hsurj hdim) hj

/-- **Tag 09NY for a morphism presented as a composite through a surjective closed immersion**,
written in Tag 09NY's own `∃`-form.

The tag is withheld: the factorization and `LiftsInvertibleModules j` are not hypotheses of Tag
09NY. -/
theorem exists_modulePullback_iso_of_factorization {X W Z : Scheme.{u}} (j : Z ⟶ W) (k : W ⟶ X)
    [IsClosedImmersion k] (hsurj : Function.Surjective k.base) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (hj : LiftsInvertibleModules j)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback (j ≫ k).toLRSHom.toShHom).obj M ≅ L) :=
  let ⟨M, hM, h⟩ := picPullbackSurjective_comp_of_surjective j k hsurj hdim hj L hL
  ⟨M, hM, h⟩

end Stacks.LiftInvertible

end
