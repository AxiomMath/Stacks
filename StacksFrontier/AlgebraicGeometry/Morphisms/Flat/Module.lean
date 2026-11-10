module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Composition of flatness for a module

Let `X ⟶ Y ⟶ Z` be morphisms of ringed spaces. If a module on `X` is flat over `Y` at a point
and `Y` is flat over `Z` at its image, then the module is flat over `Z` at that point. This is
transitivity of flatness for the tower of stalks.

## Main results

* `AlgebraicGeometry.IsFlatOverAt.comp` gives the composition property for flatness of a module
  at a point.

## Implementation notes

The stalkwise predicates apply to arbitrary ringed spaces and modules. Neither quasi-coherence
nor the scheme structure is needed for this composition property.

## References

* [Stacks Project, Tag 01U6](https://stacks.math.columbia.edu/tag/01U6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace IsFlatOverAt

/-- Flatness of a module over a ringed space at a point is transitive along a
flat morphism of target ringed spaces. -/
@[stacks 01U6]
public lemma comp {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) (x : X)
    (hF : AlgebraicGeometry.IsFlatOverAt f F x)
    (hY : AlgebraicGeometry.IsFlatAt g (f.hom.base x)) :
    AlgebraicGeometry.IsFlatOverAt (f ≫ g) F x := by
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x
  let R := Z.presheaf.stalk ((f ≫ g).hom.base x)
  let S := Y.presheaf.stalk (f.hom.base x)
  let ρ : R →+* S := (g.hom.stalkMap (f.hom.base x)).hom
  let σ : S →+* X.presheaf.stalk x := (f.hom.stalkMap x).hom
  let τ : R →+* X.presheaf.stalk x := ((f ≫ g).hom.stalkMap x).hom
  let _ : Module S N := Module.compHom _ σ
  let _ : Algebra R S := ρ.toAlgebra
  let _ : Module R N := Module.compHom _ τ
  have hmaps : τ = σ.comp ρ := congrArg (·.hom) (PresheafedSpace.stalkMap.comp f.hom g.hom x)
  let _ : IsScalarTower R S N := ⟨fun r s n => by
    change σ (ρ r * s) • n = τ r • (σ s • n)
    simp [hmaps, map_mul, RingHom.comp_apply, mul_smul]⟩
  change Module.Flat S N at hF
  change Module.Flat R S at hY
  exact Module.Flat.trans R S N

end IsFlatOverAt

end AlgebraicGeometry
