module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantStalkColength
public import StacksFrontier.LinearAlgebra.ExteriorPower.DualTorsionKernel

/-!
# The determinant comparison map is a stalk isomorphism where the morphism is

At a point where the stalk map of `f : F ⟶ F'` is bijective — or, over a domain, merely
surjective with torsion kernel — so is the stalk map of the determinant comparison map
`σ(f, r)` of [Stacks, Tag 0B3T].

## Main results

* `AlgebraicGeometry.Scheme.Modules.bijective_stalkHom_detMap`: the stalk of `σ(f, r)` is
  bijective where the stalk of `f` is.
* `AlgebraicGeometry.Scheme.Modules.bijective_stalkHom_detMap_of_surjective_of_ker_le_torsion`:
  the same conclusion from a surjective `f_x` with torsion kernel, over a domain.
* `AlgebraicGeometry.surjective_mapFun_detMap_of_bijective_stalkHom` and
  `AlgebraicGeometry.surjective_mapFun_detMap_of_surjective_of_ker_le_torsion`: the stalk map
  `Stacks.ModuleStalk.mapFun` of `σ(f, r)` is surjective under the same hypotheses.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

section Algebra

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- The `n`-th exterior power of a bijective linear map is bijective. -/
private theorem bijective_exteriorPower_map (n : ℕ) {u : M →ₗ[R] N}
    (hu : Function.Bijective u) : Function.Bijective (exteriorPower.map n u) :=
  ⟨exteriorPower.map_injective (LinearEquiv.ofBijective u hu).symm (by ext; simp),
    exteriorPower.map_surjective hu.2⟩

/-- The transpose of a bijective linear map is bijective. -/
private theorem bijective_transpose {u : M →ₗ[R] N} (hu : Function.Bijective u) :
    Function.Bijective (Module.Dual.transpose (R := R) u) :=
  (LinearEquiv.ofBijective u hu).dualMap.bijective

end Algebra

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F F' : X.Modules} (f : F ⟶ F') (r : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]

/-- The stalk of `σ(f, r)` is bijective as soon as the double transpose of `⋀^r (f_x)` is. -/
private theorem bijective_stalkHom_detMap_of_bijective_transpose
    (hT : Function.Bijective (Module.Dual.transpose
      (Module.Dual.transpose (exteriorPower.map r (stalkHom f x))))) :
    Function.Bijective (stalkHom (detMap f (r : ℤ)) x) := by
  have hcomp : (detStalkEquiv F' r x) ∘ (stalkHom (detMap f (r : ℤ)) x)
      = (Module.Dual.transpose (Module.Dual.transpose (exteriorPower.map r (stalkHom f x))))
        ∘ (detStalkEquiv F r x) :=
    funext fun Phi => detStalkEquiv_stalkHom_detMap f r x Phi
  have hbij : Function.Bijective ((detStalkEquiv F' r x) ∘ (stalkHom (detMap f (r : ℤ)) x)) := by
    rw [hcomp]
    exact hT.comp (detStalkEquiv F r x).bijective
  exact (Function.Bijective.of_comp_iff' (detStalkEquiv F' r x).bijective _).mp hbij

/-- If the stalk map of `f` at `x` is bijective, so is the stalk map of `σ(f, r)`. -/
theorem bijective_stalkHom_detMap (h : Function.Bijective (stalkHom f x)) :
    Function.Bijective (stalkHom (detMap f (r : ℤ)) x) :=
  bijective_stalkHom_detMap_of_bijective_transpose f r x
    (bijective_transpose (bijective_transpose (bijective_exteriorPower_map r h)))

/-- If the stalk of `X` at `x` is a domain and the stalk map of `f` at `x` is surjective with
torsion kernel, then the stalk map of `σ(f, r)` at `x` is bijective. -/
theorem bijective_stalkHom_detMap_of_surjective_of_ker_le_torsion
    [IsDomain (ringStalk X.sheaf x)] (h : Function.Surjective (stalkHom f x))
    (hker : LinearMap.ker (stalkHom f x) ≤
      Submodule.torsion (ringStalk X.sheaf x) (modStalk F x)) :
    Function.Bijective (stalkHom (detMap f (r : ℤ)) x) :=
  bijective_stalkHom_detMap_of_bijective_transpose f r x
    (exteriorPower.bijective_dualMap_dualMap_map_of_surjective_of_ker_le_torsion r h hker)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}} {F F' : X.Modules} (f : F ⟶ F') (r : ℕ) (x : X)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]

omit [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation] in
/-- If the stalk map of `σ(f, r)` at `x` is bijective, its `Stacks.ModuleStalk.mapFun` is
surjective. -/
private theorem surjective_mapFun_detMap_of_bijective_stalkHom_detMap
    (h : Function.Bijective (stalkHom (detMap f (r : ℤ)) x)) :
    Function.Surjective (Stacks.ModuleStalk.mapFun (detMap f (r : ℤ)) x) := by
  intro m
  obtain ⟨n, hn⟩ := h.2 m
  exact ⟨n, (Stacks.ModuleStalk.map_eq_stalkHom (detMap f (r : ℤ)) x n).trans hn⟩

/-- The stalk map `Stacks.ModuleStalk.mapFun` of `σ(f, r)` at `x` is surjective if the stalk map
of `f` at `x` is bijective. -/
theorem surjective_mapFun_detMap_of_bijective_stalkHom
    (h : Function.Bijective (stalkHom f x)) :
    Function.Surjective (Stacks.ModuleStalk.mapFun (detMap f (r : ℤ)) x) :=
  surjective_mapFun_detMap_of_bijective_stalkHom_detMap f r x
    (bijective_stalkHom_detMap f r x h)

/-- The stalk map `Stacks.ModuleStalk.mapFun` of `σ(f, r)` at `x` is surjective if the stalk of
`X` at `x` is a domain and the stalk map of `f` at `x` is surjective with torsion kernel. -/
theorem surjective_mapFun_detMap_of_surjective_of_ker_le_torsion
    [IsDomain (ringStalk X.sheaf x)] (h : Function.Surjective (stalkHom f x))
    (hker : LinearMap.ker (stalkHom f x) ≤
      Submodule.torsion (ringStalk X.sheaf x) (modStalk F x)) :
    Function.Surjective (Stacks.ModuleStalk.mapFun (detMap f (r : ℤ)) x) :=
  surjective_mapFun_detMap_of_bijective_stalkHom_detMap f r x
    (bijective_stalkHom_detMap_of_surjective_of_ker_le_torsion f r x h hker)

end AlgebraicGeometry

end
