module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleMorphismDivisor
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Hull

/-!
# The comparison map of determinant line bundles, and the divisor it cuts out

Let `X` be a scheme and `f : F ⟶ F'` a morphism of `𝒪_X`-modules. Functoriality of the `r`-th
exterior power in the module argument, followed by functoriality of the reflexive hull, gives a
canonical morphism

`σ(f, r) : (⋀^r F)^∨∨ ⟶ (⋀^r F')^∨∨`

of the two determinant modules. This is the map `σ` of the proof of [Stacks, Tag 0B3T]. When `X`
is integral and both determinant modules are invertible, a nonzero `σ` exhibits the second as a
twist of the first by an effective Cartier divisor.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.detMap`: the morphism `σ(f, r)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.detMap_id` and `detMap_comp`: functoriality, and
  `AlgebraicGeometry.Scheme.Modules.isIso_detMap`: `σ` of an isomorphism is an isomorphism,
  which is what makes `σ` nonzero on the open where `F` and `F'` agree.
* `AlgebraicGeometry.exists_isEffectiveCartierDivisor_tensorIso_detMap`: a nonzero
  comparison map between invertible determinant modules on an integral scheme exhibits the
  second as `𝒪_X(D)` times the first, for an effective Cartier divisor `D`.

## Implementation notes

The exterior power is the graded piece of the exterior algebra of
`AlgebraicGeometry.Scheme.Modules.exteriorPower`, whose functoriality in the module argument is
`AlgebraicGeometry.Scheme.Modules.exteriorPowerMap`, built from the universal property; the hull
is `Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveHull` with
`Stacks.AlgebraicGeometry.ReflexiveModules.doubleDualMap` for its action on morphisms. The two
functorialities compose, so `detMap` is a functor in `f` for each fixed `r` and nothing has to
be reproved about it. The name is `detMap` and not `detComparison`: the latter is taken, by the
unrelated comparison `Stacks.SheafOfModules.TopWedge.detComparison` of the top wedge of a short
exact sequence.

**Which reflexive-hull development.** `Stacks.AlgebraicGeometry.ReflexiveModules` of
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/`, not `Stacks.AlgebraicGeometry.ReflexiveHull` of
`StacksFrontier/AlgebraicGeometry/ReflexiveHullAdjunction/`: the former is the one carrying
`doubleDualMap` with its functoriality, which is what `σ` is built from, and the one whose
`dualSheaf` is `Stacks.SheafOfModules.dualSheaf` of the internal hom, so that the evaluation
pairing and the twist of
`StacksFrontier/AlgebraicGeometry/Divisors/InvertibleMorphismDivisor.lean` apply to it unchanged.

**No `@[stacks]` attribute.** Functoriality of the exterior power and of the hull is not a clause
of any tag — see the note in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerFunctorial.lean` — and the corollary
is the divisor-producing step of the proof of Tag 0B3T, not one of that tag's assertions: it
produces the zero scheme of `σ`, and neither identifies it with a multiple of the given divisor
nor bounds the multiple.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (reflexiveHull doubleDualMap doubleDualMap_id
  doubleDualMap_comp)

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F F' F'' : X.Modules}

/-- **The comparison map of determinant modules** attached to a morphism `f : F ⟶ F'`: the
reflexive hull of the `r`-th exterior power of `f`. This is the map `σ` of [Stacks, Tag
0B3T]. -/
def detMap (f : F ⟶ F') (r : ℤ) :
    reflexiveHull (exteriorPower F r) ⟶ reflexiveHull (exteriorPower F' r) :=
  doubleDualMap (exteriorPowerMap f r)

/-- The comparison map of the identity is the identity. -/
@[simp] theorem detMap_id (F : X.Modules) (r : ℤ) :
    detMap (𝟙 F) r = 𝟙 (reflexiveHull (exteriorPower F r)) := by
  rw [detMap, exteriorPowerMap_id, doubleDualMap_id]

/-- The comparison map of a composite is the composite of the comparison maps. -/
theorem detMap_comp (f : F ⟶ F') (g : F' ⟶ F'') (r : ℤ) :
    detMap (f ≫ g) r = detMap f r ≫ detMap g r := by
  rw [detMap, exteriorPowerMap_comp, doubleDualMap_comp, detMap, detMap]

/-- **The comparison map of an isomorphism is an isomorphism.** This is what makes `σ` nonzero
in [Stacks, Tag 0B3T]: it is invertible over the open on which the two modules agree. -/
instance isIso_detMap (f : F ⟶ F') [IsIso f] (r : ℤ) : IsIso (detMap f r) := by
  refine ⟨detMap (inv f) r, ?_, ?_⟩
  · rw [← detMap_comp, IsIso.hom_inv_id, detMap_id]
  · rw [← detMap_comp, IsIso.inv_hom_id, detMap_id]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Stacks.SheafOfModules Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] {F F' : X.Modules} (r : ℤ)

/-- **A nonzero comparison map of invertible determinant modules is a twist by an effective
Cartier divisor.** With `L = (⋀^r F)^∨∨` and `L' = (⋀^r F')^∨∨` invertible on an integral
scheme, a nonzero `σ(f, r)` gives an effective Cartier divisor `D` with `𝒪_X(D) ⊗ L ≅ L'`.

This is the divisor-producing step of the proof of [Stacks, Tag 0B3T]; the tag's identification
of `D` with a multiple `k D₀` of the given divisor, and the bound `k ≤ min(s, r)`, are not
proved here. -/
theorem exists_isEffectiveCartierDivisor_tensorIso_detMap (f : F ⟶ F')
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (reflexiveHull (exteriorPower F r))]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (reflexiveHull (exteriorPower F' r))]
    (hf : detMap f r ≠ 0) :
    ∃ D : X.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
          (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' D))).obj
            ((reflexiveHull (exteriorPower F r)))) ≅
          reflexiveHull (exteriorPower F' r)) :=
  exists_isEffectiveCartierDivisor_tensorIso_of_ne_zero _ _ hf

end AlgebraicGeometry

end
