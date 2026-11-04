module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion

/-!
# Descent of flatness along a surjective flat morphism

If `f : X ⟶ Y` is surjective and flat and the composite `X ⟶ Y ⟶ S` is flat, then `Y ⟶ S` is
flat. Flatness is checked on local rings, and at a point of `Y` chosen in the image of `f` the
stalk map of `f` is a flat local homomorphism of local rings, hence faithfully flat, so
flatness of the composite descends to the first map of the tower of local rings.

## Main results

* `AlgebraicGeometry.flat_of_comp_of_surjective_flat` descends flatness of schemes along a
  surjective flat morphism.

## References

* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02JZ (second global consequence).** If `f : X ⟶ Y`
is surjective and flat and `X` is flat over `S`, then `Y` is flat over `S`. -/
@[stacks 02JZ "descent of scheme flatness"]
public theorem flat_of_comp_of_surjective_flat
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] [Flat f] [Flat (f ≫ q)] : Flat q := by
  refine (Flat.iff_flat_stalkMap q).2 fun y => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  let A := S.presheaf.stalk (q (f x))
  let B := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  let h : A →+* B := (q.stalkMap (f x)).hom
  let g : B →+* C := (f.stalkMap x).hom
  have hcomp : ((f ≫ q).stalkMap x).hom = g.comp h := by
    simpa [h, g, RingHom.comp_apply] using
      congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f q x)
  let : Algebra A B := h.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp h).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat B C := Flat.stalkMap f x
  have : IsLocalHom (algebraMap B C) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Flat A C := RingHom.flat_algebraMap_iff.mp <| by
    rw [RingHom.algebraMap_toAlgebra (g.comp h), ← hcomp]
    exact Flat.stalkMap (f ≫ q) x
  exact RingHom.flat_algebraMap_iff.mpr
    (Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat C)

end AlgebraicGeometry
