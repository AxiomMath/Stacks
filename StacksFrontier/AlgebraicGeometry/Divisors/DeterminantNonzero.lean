module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantStalkIso
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact

/-!
# The determinant comparison map is nonzero

A morphism of modules `f : F ⟶ F'` on a scheme induces the determinant comparison map
`detMap f r`. It is nonzero as soon as there is one point at which the stalk of the determinant of
`F` is nontrivial and the stalk map of `f` is onto with torsion kernel, or bijective.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isDomain_ringStalk`: the local ring of an integral
  scheme is a domain, in the `ringStalk` spelling.
* `Stacks.AlgebraicGeometry.ReflexiveModules.isLocalRing_ringStalk`: the local ring of a scheme
  is a local ring, in the `ringStalk` spelling.
* `Stacks.AlgebraicGeometry.ReflexiveModules.ne_zero_of_injective_stalkHom`: a morphism with an
  injective stalk map at a point with nontrivial stalk is nonzero.
* `AlgebraicGeometry.Scheme.Modules.nontrivial_modStalk_det`: the stalk of the determinant is
  nontrivial when the double dual of `⋀^r (F_x)` is.
* `AlgebraicGeometry.Scheme.Modules.detMap_ne_zero_of_surjective_of_ker_le_torsion`: the
  determinant comparison map is nonzero, given a point where the stalk of the determinant is
  nontrivial and the stalk map is onto with torsion kernel.
* `AlgebraicGeometry.Scheme.Modules.detMap_ne_zero_of_bijective_stalkHom`: the same, at a point
  where the stalk map is bijective.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- The local ring of an integral scheme is a domain, in the `ringStalk` spelling. -/
public instance isDomain_ringStalk [IsIntegral X] (x : X) : IsDomain (ringStalk X.sheaf x) :=
  inferInstanceAs (IsDomain (X.presheaf.stalk x))

/-- The local ring of a scheme is a local ring, in the `ringStalk` spelling. -/
public instance isLocalRing_ringStalk (x : X) : IsLocalRing (ringStalk X.sheaf x) :=
  inferInstanceAs (IsLocalRing (X.presheaf.stalk x))

/-- A morphism of modules with an injective stalk map at a point whose stalk is nontrivial is
nonzero. -/
public theorem ne_zero_of_injective_stalkHom {E F : X.Modules} (f : E ⟶ F) (x : X)
    [Nontrivial (modStalk E x)] (h : Function.Injective (stalkHom f x)) : f ≠ 0 := by
  intro hf
  obtain ⟨a, b, hab⟩ := exists_pair_ne (modStalk E x)
  exact hab (h (by rw [hf, stalkHom_zero]; simp))

end Stacks.AlgebraicGeometry.ReflexiveModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F F' : X.Modules} (f : F ⟶ F') (r : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]

/-- The stalk of the determinant of `F` is nontrivial as soon as the double dual of
`⋀^r (F_x)` is. -/
public theorem nontrivial_modStalk_det
    [Nontrivial (Module.Dual (ringStalk X.sheaf x) (Module.Dual (ringStalk X.sheaf x)
      (⋀[ringStalk X.sheaf x]^r (modStalk F x))))] :
    Nontrivial (modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x) :=
  (detStalkEquiv F r x).toEquiv.nontrivial

/-- The determinant comparison map is nonzero, given one point where the stalk of the
determinant of `F` is nontrivial and the stalk map of `f` is onto with torsion kernel. -/
public theorem detMap_ne_zero_of_surjective_of_ker_le_torsion
    [IsDomain (ringStalk X.sheaf x)]
    [Nontrivial (modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x)]
    (h : Function.Surjective (stalkHom f x))
    (hker : LinearMap.ker (stalkHom f x) ≤
      Submodule.torsion (ringStalk X.sheaf x) (modStalk F x)) :
    detMap f (r : ℤ) ≠ 0 :=
  ne_zero_of_injective_stalkHom (detMap f (r : ℤ)) x
    (bijective_stalkHom_detMap_of_surjective_of_ker_le_torsion f r x h hker).1

/-- The determinant comparison map is nonzero, given one point where the stalk of the
determinant of `F` is nontrivial and the stalk map of `f` is bijective. -/
public theorem detMap_ne_zero_of_bijective_stalkHom
    [Nontrivial (modStalk (reflexiveHull (exteriorPower F (r : ℤ))) x)]
    (h : Function.Bijective (stalkHom f x)) : detMap f (r : ℤ) ≠ 0 :=
  ne_zero_of_injective_stalkHom (detMap f (r : ℤ)) x (bijective_stalkHom_detMap f r x h).1

end AlgebraicGeometry.Scheme.Modules

end
