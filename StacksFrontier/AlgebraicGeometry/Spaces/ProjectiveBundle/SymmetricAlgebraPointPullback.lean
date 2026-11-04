module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackSymmetric
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra

/-!
# The symmetric algebra of a module on an algebraic space, restricted to a scheme point

Let `ℰ` be an `𝒪_X`-module on an algebraic space `X` and `g : T ⟶ X` a scheme point. The
restriction `g^*Sym(ℰ)` of the symmetric algebra of `ℰ`, the pullback of sheaves of graded
algebras along the morphism of small étale ringed topoi of `g`, is the symmetric algebra of the
restricted module `g^*ℰ`: the comparison `Sym(g^*ℰ) ⟶ g^*Sym(ℰ)` extending the pullback of the
generator is an isomorphism in every degree.

## Main definitions

* `AlgebraicGeometry.Space.symmetricAlgebraPointPullbackHom`: the comparison.

## Main results

* `AlgebraicGeometry.Space.isIso_symmetricAlgebraPointPullbackHom_app`: it is an isomorphism in
  every degree.
* `AlgebraicGeometry.Space.symmetricAlgebraGen_comp_symmetricAlgebraPointPullbackHom_app_one`:
  it carries the generator to the pullback of the generator.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : SheafOfModules.{u} (structureRingSheaf B S hS X)) (T : BigFppfOver B S hS)
  (g : yoneda.obj T ⟶ X.1)

/-- **The comparison `Sym(g^*ℰ) ⟶ g^*Sym(ℰ)`** at a scheme point `g`: the unital homomorphism
out of the symmetric algebra of `g^*ℰ` extending the pullback of the generator of `Sym(ℰ)`. -/
noncomputable def symmetricAlgebraPointPullbackHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (symmetricAlgebra B S hS (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E))
      (etalePointAlgebra (symmetricAlgebra B S hS X E) T g) :=
  Stacks.Sheaves.GradedAlgebraEssentiallySmall.symmetricPullbackHom
    (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS (pointHom g)) (symmetricAlgebraGen B S hS X E)
    (fun V x y => eq_of_heq (symmetricAlgebra_mul_comm B S hS X E 1 1 V x y))
    (symmetricAlgebraGen B S hS (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E))
    (isSymmetricAlgebra_symmetricAlgebra B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E))

/-- **The comparison `Sym(g^*ℰ) ⟶ g^*Sym(ℰ)` is an isomorphism in every degree.** -/
instance isIso_symmetricAlgebraPointPullbackHom_app (n : ℤ) :
    IsIso ((symmetricAlgebraPointPullbackHom E T g).app n) :=
  Stacks.Sheaves.GradedAlgebraEssentiallySmall.isIso_symmetricPullbackHom_app
    (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS (pointHom g)) (symmetricAlgebraGen B S hS X E)
    (isSymmetricAlgebra_symmetricAlgebra B S hS X E)
    (fun V x y => eq_of_heq (symmetricAlgebra_mul_comm B S hS X E 1 1 V x y))
    (symmetricAlgebraGen B S hS (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E))
    (isSymmetricAlgebra_symmetricAlgebra B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E))
    (fun V x y => eq_of_heq (symmetricAlgebra_mul_comm B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E) 1 1 V x y)) n

/-- The comparison carries the generator of `Sym(g^*ℰ)` to the pullback of the generator of
`Sym(ℰ)`. -/
theorem symmetricAlgebraGen_comp_symmetricAlgebraPointPullbackHom_app_one :
    symmetricAlgebraGen B S hS (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E) ≫
        (symmetricAlgebraPointPullbackHom E T g).app 1 =
      (modulePullback B S hS (pointHom g)).map (symmetricAlgebraGen B S hS X E) :=
  Stacks.Sheaves.GradedAlgebraEssentiallySmall.gen_comp_symmetricPullbackHom_app_one
    (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
    (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS (pointHom g)) (symmetricAlgebraGen B S hS X E)
    (fun V x y => eq_of_heq (symmetricAlgebra_mul_comm B S hS X E 1 1 V x y))
    (symmetricAlgebraGen B S hS (yonedaSpace B S hS T) ((modulePullback B S hS (pointHom g)).obj E))
    (isSymmetricAlgebra_symmetricAlgebra B S hS (yonedaSpace B S hS T)
      ((modulePullback B S hS (pointHom g)).obj E))

end AlgebraicGeometry.Space

end
