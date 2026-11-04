module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekQuasiFinite
import StacksCore.Tactic.StacksAttribute

/-!
# The upper shriek of an étale morphism is the inverse image

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`. The
direct image with compact support `j_!` of Stacks 0F6R agrees with extension by zero of Stacks
03S3, by Stacks 0F6Q, and extension by zero is by definition the left adjoint of `j^{-1}`. So
`j^!`, the right adjoint of `j_!`, is `j^{-1}`.

## Main results

* `AlgebraicGeometry.SmallEtale.abelianExtensionByZeroIsoFShriek` — extension by zero along
  `j` is the direct image with compact support of `j`.
* `AlgebraicGeometry.SmallEtale.fShriekAdjunctionRestriction` — the adjunction
  `j_! ⊣ j^{-1}` for the direct image with compact support.
* `AlgebraicGeometry.SmallEtale.etaleUpperShriekIsoRestriction` — **Stacks 0F5A**,
  `j^! = j^{-1}`.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}` for the scheme universe `u`, which is the
universe at which Stacks 0F6Q is available; the upper shriek of Stacks 0F59, stated at
`AddCommGrpCat.{max (u + 1) v}`, is instantiated at `v = u + 1`.

## References

* [Stacks Project, Tag 0F5A](https://stacks.math.columbia.edu/tag/0F5A)
* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- Extension by zero along an étale morphism `j : U ⟶ X` is the direct image with compact
support of `j`: the comparison map `j_{p!} ⟶ f_{p!}` of Stacks 0F6Q is an isomorphism after
sheafification. -/
public def abelianExtensionByZeroIsoFShriek :
    abelianExtensionByZero B X hX U ≅ fShriekFunctor.{u, u + 1} B U.obj.hom :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ _ (etaleExtensionToFiniteSupport_sheafify_isIso B X hX U F))
    (fun φ => (Functor.whiskerRight (etaleExtensionToFiniteSupport B X hX U)
      (presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})).naturality φ)

/-- The direct image with compact support of an étale morphism `j : U ⟶ X` is left adjoint to
restriction along `j`, being extension by zero. -/
public def fShriekAdjunctionRestriction :
    fShriekFunctor.{u, u + 1} B U.obj.hom ⊣ abelianRestriction B X hX U :=
  (abelianExtensionByZeroAdjunction B X hX U).ofNatIsoLeft
    (abelianExtensionByZeroIsoFShriek B X hX U)

/-- **Stacks 0F5A.** For an étale morphism `j : U ⟶ X` the upper shriek `j^!` on abelian étale
sheaves is the inverse image `j^{-1}`: both are right adjoint to `j_!`. -/
@[stacks 0F5A "j^! = j^{-1} for an étale morphism"]
public def etaleUpperShriekIsoRestriction :
    fUpperShriekFunctor.{u, u + 1} B U.obj.hom ≅ abelianRestriction B X hX U :=
  (fShriekAdjunction.{u, u + 1} B U.obj.hom).rightAdjointUniq
    (fShriekAdjunctionRestriction B X hX U)

end AlgebraicGeometry.SmallEtale

end
