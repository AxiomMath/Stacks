module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantStalkTorsion
public import StacksFrontier.RingTheory.OrderOfVanishing.ExteriorTorsionQuotient

/-!
# The colength of the stalk of the determinant comparison map

At a point whose local ring is a discrete valuation ring, the cokernel of the stalk of the
determinant comparison map `σ(f, r)` of [Stacks, Tag 0B3T] has length at most `min s r`, where
`s` bounds the cokernel of the stalk of `f` and `r` is the rank of the torsion-free quotients.

This is the determinant bound of
`StacksFrontier.RingTheory.OrderOfVanishing.ExteriorTorsionQuotient` transported to the stalk of
the determinant module by `AlgebraicGeometry.Scheme.Modules.detStalkTorsionEquiv`. Fed into
`AlgebraicGeometry.exists_pow_le_tensorIso_of_surjective_stalk_off` it bounds the exponent of
the Cartier twist of the tag's second assertion.

## Main results

* `Stacks.ModuleStalk.map_eq_stalkHom`: the two stalk-map constructions of the library agree, at
  the `Stacks.ModuleStalk.map` spelling.
* `AlgebraicGeometry.length_quotient_range_map_detMap_le_min`: **the colength bound.**

## Implementation notes

`Stacks.ModuleStalk.map` and `Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom` have the same
type up to `rfl` — `modStalk` unfolds to `TopCat.Presheaf.stalk` and `ringStalk X.sheaf` to
`X.presheaf.stalk` — but are not definitionally equal as maps, the stalk colimit not being
exposed. Both send a germ to the germ of its image, so a germ chase identifies them, exactly as
`Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom_eq_stalkMapL` does for the third spelling.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.ModuleStalk

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **The two stalk-map constructions of the library agree.** `Stacks.ModuleStalk.map` and
`Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom` both send a germ to the germ of its
image. -/
public theorem map_eq_stalkHom (φ : M ⟶ N) (x : X) (m : M.presheaf.stalk x) :
    map φ x m = stalkHom φ x m := by
  obtain ⟨W, hxW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  rw [map_apply, mapFun_germ]
  exact (stalkHom_germAt φ x W hxW t).symm

end Stacks.ModuleStalk

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}} {F F' : X.Modules} (f : F ⟶ F') (r s : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
  [IsDomain (ringStalk X.sheaf x)] [IsLocalRing (ringStalk X.sheaf x)]
  [IsDiscreteValuationRing (ringStalk X.sheaf x)]
  [Module.Finite (ringStalk X.sheaf x) (modStalk F x)]
  [Module.Finite (ringStalk X.sheaf x) (modStalk F' x)]

/-- The stalk of the determinant comparison map read through `detStalkTorsionEquiv` is the map
induced by `⋀^r (f_x)` on torsion-free quotients. -/
theorem detStalkTorsionEquiv_comp_stalkHom_detMap :
    (detStalkTorsionEquiv F' r x).toLinearMap ∘ₗ stalkHom (detMap f (r : ℤ)) x
      = (Stacks.OrderOfVanishing.torsionQuotientMap
          (exteriorPower.map r (stalkHom f x))).comp (detStalkTorsionEquiv F r x).toLinearMap :=
  LinearMap.ext fun Phi => detStalkTorsionEquiv_stalkHom_detMap f r x Phi

/-- The image of the stalk of the determinant comparison map, read through
`detStalkTorsionEquiv`, is the image of the induced map on torsion-free quotients. -/
theorem map_range_stalkHom_detMap :
    Submodule.map (detStalkTorsionEquiv F' r x).toLinearMap
        (LinearMap.range (stalkHom (detMap f (r : ℤ)) x))
      = LinearMap.range (Stacks.OrderOfVanishing.torsionQuotientMap
          (exteriorPower.map r (stalkHom f x))) := by
  rw [← LinearMap.range_comp, detStalkTorsionEquiv_comp_stalkHom_detMap, LinearMap.range_comp,
    LinearMap.range_eq_top.2 (detStalkTorsionEquiv F r x).surjective, Submodule.map_top]

open Stacks.OrderOfVanishing in
/-- **The cokernel of the stalk of the determinant comparison map `σ(f, r)` of
[Stacks, Tag 0B3T] has length at most `min s r`** at a point whose local ring is a discrete
valuation ring, given that the cokernel of the stalk of `f` there is `κ ^ s` and that the
torsion-free quotients of the stalks of `F` and `F'` have rank `r`. -/
theorem length_quotient_range_stalkHom_detMap_le_min
    (e : (modStalk F' x ⧸ LinearMap.range (stalkHom f x))
      ≃ₗ[ringStalk X.sheaf x] (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf x)))
    (hr : Module.finrank (ringStalk X.sheaf x)
      (modStalk F x ⧸ Submodule.torsion (ringStalk X.sheaf x) (modStalk F x)) = r)
    (hr' : Module.finrank (ringStalk X.sheaf x)
      (modStalk F' x ⧸ Submodule.torsion (ringStalk X.sheaf x) (modStalk F' x)) = r) :
    Module.length (ringStalk X.sheaf x)
        (modStalk (reflexiveHull (exteriorPower F' (r : ℤ))) x ⧸
          LinearMap.range (stalkHom (detMap f (r : ℤ)) x))
      ≤ (min s r : ℕ) := by
  rw [(Submodule.Quotient.equiv _ _ (detStalkTorsionEquiv F' r x)
    (map_range_stalkHom_detMap f r x)).length_eq]
  exact length_quotient_range_torsionQuotientMap_exteriorPower_le_min_of_finrank
    (stalkHom f x) e hr hr'

/-- **The colength bound at the `Stacks.ModuleStalk.map` spelling of the stalk map**, which is
the one `AlgebraicGeometry.exists_pow_le_tensorIso_of_surjective_stalk_off` takes. -/
theorem length_quotient_range_map_detMap_le_min
    (e : (modStalk F' x ⧸ LinearMap.range (stalkHom f x))
      ≃ₗ[ringStalk X.sheaf x] (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf x)))
    (hr : Module.finrank (ringStalk X.sheaf x)
      (modStalk F x ⧸ Submodule.torsion (ringStalk X.sheaf x) (modStalk F x)) = r)
    (hr' : Module.finrank (ringStalk X.sheaf x)
      (modStalk F' x ⧸ Submodule.torsion (ringStalk X.sheaf x) (modStalk F' x)) = r) :
    Module.length (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u})
            (reflexiveHull (exteriorPower F' (r : ℤ))).presheaf x ⧸
          LinearMap.range (Stacks.ModuleStalk.map (detMap f (r : ℤ)) x))
      ≤ (min s r : ℕ) := by
  rw [show LinearMap.range (Stacks.ModuleStalk.map (detMap f (r : ℤ)) x)
      = LinearMap.range (stalkHom (detMap f (r : ℤ)) x) from
    congrArg LinearMap.range (LinearMap.ext (Stacks.ModuleStalk.map_eq_stalkHom _ x))]
  exact length_quotient_range_stalkHom_detMap_le_min f r s x e hr hr'

end AlgebraicGeometry

end
