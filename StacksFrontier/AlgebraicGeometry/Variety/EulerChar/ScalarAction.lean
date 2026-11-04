module
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Natural
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic

/-!
# The scalar action on the cohomology of a scheme over a field

For a scheme `X` with a structure morphism `f : X ⟶ Spec k`, the `k`-vector space structure of
`AlgebraicGeometry.cohomologyOverField k f F n` is the one induced by the functoriality of
cohomology: multiplying a class by `a ∈ k` is applying `Hⁿ(X, -)` to the endomorphism
"multiplication by `a`" of the module `F`.

This is what makes an additive comparison of `Hⁿ(X, F)` with another cohomology theory
`k`-linear as soon as the comparison is natural in the module: the action of `a` is the image of
a morphism of modules on both sides.

## Main results

* `AlgebraicGeometry.cohomologyOverField_smul_eq`: `a • x = Hⁿ(X, a • 𝟙 F) x`, for the linear
  structure `AlgebraicGeometry.modulesLinear` of `X.Modules` over the base field, the right-hand
  side being the right derived functor of global sections applied to `a • 𝟙 F`.

## Implementation notes

The statement is `Stacks.Cohomology.AffineComparison.rightDerived_map_baseSmul_hom` read in the
`AlgebraicGeometry.cohomologyOverField` spelling; the two differ only in that the definition of
`cohomologyOverField` restricts scalars along `f.appLE ⊤ ⊤` where that lemma uses `f.appTop`, and
those agree by `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The `k`-action on `Hⁿ(X, F)` is `Hⁿ(X, -)` of multiplication by the scalar.** For `X` over a
field `k` and `a ∈ k`, multiplying a class of `Hⁿ(X, F)` by `a` is applying
`Hⁿ(X, -)` to the endomorphism `a • 𝟙 F`, the scalar acting on the module sheaves of `X` through
the structure morphism. -/
theorem cohomologyOverField_smul_eq (F : X.Modules) (n : ℕ) (a : k)
    (x : cohomologyOverField k f F n) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    a • x = (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n).map
      (a • 𝟙 F)).hom x := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  have h := Stacks.Cohomology.AffineComparison.rightDerived_map_baseSmul_hom (Over.mk f) F n a x
  have e : (Over.mk f).hom.appTop = f.appLE ⊤ ⊤ (by simp) := Scheme.Hom.app_eq_appLE f
  rw [e] at h
  exact h.symm

end AlgebraicGeometry

end
