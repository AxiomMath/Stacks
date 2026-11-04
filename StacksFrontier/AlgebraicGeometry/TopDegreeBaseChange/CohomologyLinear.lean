module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# Cohomology of a scheme over a base ring is additive and linear over that ring

The proof of [Stacks, Tag 0EX3] (b) reduces to an affine base, `Y' = Spec R'`, and there runs
`Stacks.EilenbergWatts.iso` on an endofunctor of `ModuleCat R'` whose cohomological factor is
`(Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerived d`. Eilenberg-Watts asks
for four properties of that endofunctor; this file supplies the two that are about the
cohomological factor alone, namely that it is additive and `R'`-linear.

Both come from `CategoryTheory.Functor.additive_rightDerived` and
`CategoryTheory.Functor.linear_rightDerived` once the *undervied* global sections functor is
known to be additive and `R`-linear. Additivity of that is
`Stacks.Cohomology.AffineBase.moduleGlobalSections_additive`; linearity is
`linear_moduleGlobalSections` below, and it holds for a reason that is a definitional
coincidence rather than an argument: the `R`-action on morphisms of module sheaves is
multiplication by `AlgebraicGeometry.baseRingToSections` open by open
(`AlgebraicGeometry.baseScalar`), so at the open `⊤` it is already multiplication by the image
of `r` in `Γ(X, ⊤)`, which is what the `R`-action on `ModuleCat Γ(X, ⊤)` is too.

## Main results

* `Stacks.Cohomology.AffineBase.baseSectionsAlgebra`: `Γ(X, ⊤)` is an `R`-algebra when `X` is a
  scheme over `Spec R`. This is what makes `ModuleCat Γ(X, ⊤)` an `R`-linear category, hence
  what makes `R`-linearity of a functor into it a meaningful statement.
* `Stacks.Cohomology.AffineBase.linear_moduleGlobalSections`: global sections is `R`-linear.
* `Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`: **the second
  hypothesis of `Stacks.EilenbergWatts.iso`, for the cohomology functor of a scheme over a
  base ring.** The first, additivity, needs no base ring and is found by instance search, through
  `CategoryTheory.Functor.additive_rightDerived`.

## Implementation notes

The two linear structures are passed as `letI` in the statements, as they are in
`AlgebraicGeometry.quasicoherentIntegralTransform_isLinearOverBase`: neither is a global
instance, because both depend on the structure morphism `X ⟶ Spec R` and not only on `X`.

`linear_moduleGlobalSections` is proved through `CategoryTheory.Functor.linear_iff`, which
reduces linearity to the value on `r • 𝟙 M`, and then through a `have` whose declared type
spells the multiplication at `Γ(X, ⊤)`. The declared type is doing real work: the module
structure on `(moduleGlobalSections X).obj M` is found over
`X.ringCatSheaf.obj.obj (op ⊤)`, and the goal asks for it over `Γ(X, ⊤)`; the two are the same
type but instance search does not see through the abbreviation, so the scalar action has to be
named at the spelling the goal uses.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped ModuleCat.Algebra

namespace Stacks.Cohomology.AffineBase

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

/-- **The functions on a scheme over `Spec R` form an `R`-algebra**, by the structure morphism
read at the open `⊤`. This is the algebra structure that makes `ModuleCat Γ(X, ⊤)` an
`R`-linear category. -/
@[instance_reducible]
noncomputable def baseSectionsAlgebra : Algebra R Γ(X.left, ⊤) :=
  RingHom.toAlgebra (AlgebraicGeometry.baseRingToSections R X (op ⊤))

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-- **Global sections of module sheaves on a scheme over `Spec R` is `R`-linear.** The
`R`-action on a morphism of module sheaves is multiplication by the image of the scalar in the
functions on each open; at `⊤` that is exactly the `R`-action on `ModuleCat Γ(X, ⊤)`. -/
theorem linear_moduleGlobalSections :
    letI := AlgebraicGeometry.modulesLinear R X
    letI := baseSectionsAlgebra R X
    Functor.Linear R (moduleGlobalSections X.left) := by
  rw [Functor.linear_iff]
  intro M r
  have key : (moduleGlobalSections X.left).map (r • 𝟙 M) =
      ModuleCat.ofHom (LinearMap.lsmul Γ(X.left, ⊤)
        ((moduleGlobalSections X.left).obj M) (algebraMap R Γ(X.left, ⊤) r)) := by
    apply ModuleCat.hom_ext
    rfl
  rw [key, ModuleCat.lsmul_eq_smul_id]
  rfl

/-- **The second hypothesis of `Stacks.EilenbergWatts.iso` for the cohomology functor of a
scheme over `Spec R`**: cohomology is `R`-linear. This is the hypothesis that makes the
Eilenberg-Watts comparison factor through a tensor product over `R`, so it is the one the
affine case of [Stacks, Tag 0EX3] (b) cannot do without. -/
theorem linear_rightDerived_moduleGlobalSections (d : ℕ) :
    letI := AlgebraicGeometry.modulesLinear R X
    letI := baseSectionsAlgebra R X
    Functor.Linear R ((moduleGlobalSections X.left).rightDerived d) := by
  let := AlgebraicGeometry.modulesLinear R X
  let := baseSectionsAlgebra R X
  have := linear_moduleGlobalSections R X
  infer_instance

end Stacks.Cohomology.AffineBase

end
