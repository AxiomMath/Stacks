module

public import StacksFrontier.AlgebraicGeometry.Modules.StalkFreePullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange

/-!
# A free stalk over a flat base morphism is flat over the base

A module whose stalk at a point is free over the local ring of the source there is flat over
the base at that point, as soon as the morphism itself is flat: freeness gives flatness over
the local ring of the source, flatness of the morphism gives flatness of that local ring over
the local ring of the target, and flatness is transitive.

The case the flattening theorem [Stacks, Tag 0815] uses is a finite coproduct of copies of the
structure sheaf, whose stalks are finite free: its pullback along one projection of a fibre
product is flat over the other projection.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_free_stalk`: the statement of the first paragraph.
* `AlgebraicGeometry.isFlatOver_pullback_coproductUnit`: the statement of the second.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **A module with free stalk is flat over a flat base morphism there.** Freeness makes the
stalk flat over the local ring of the source; flatness of the morphism makes that local ring
flat over the local ring of the target; and flatness composes. -/
theorem isFlatOverAt_of_free_stalk {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (F : X.Modules)
    (x : X) (hF : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    have := hF
    inferInstance
  change Module.Flat (S.presheaf.stalk (f x)) (F.presheaf.stalk x)
  exact Module.Flat.trans (S.presheaf.stalk (f x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- **A finite coproduct of copies of the structure sheaf, pulled back to a fibre product, is
flat over the other projection.** Its stalks are free, and the other projection is flat, being
a base change of a flat morphism. -/
theorem isFlatOver_pullback_coproductUnit {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [Flat f] (r : ℕ) :
    IsFlatOver (pullback.snd f g).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f g)).obj
        (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules)) := by
  have : Flat (pullback.snd f g) := inferInstance
  exact fun y ↦ isFlatOverAt_of_free_stalk (pullback.snd f g) _ y
    (Stacks.StalkFreeBridge.free_stalk_pullback (pullback.fst f g) _ y
      (Stacks.StalkFreeBridge.free_stalk_coproductUnit r (pullback.fst f g y)))

end AlgebraicGeometry

end
