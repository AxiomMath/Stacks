module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# Extension by zero in the two models of the small étale site

Let `B` be a big étale site containing a scheme `X` and let `U` be an object of the small étale
site of Tag 021B of `X`, with structure morphism `j : U ⟶ X`. Extension by zero along `j` exists
in both models of the small étale site: on Mathlib's site `X.smallEtaleTopology` it is the left
adjoint of restriction along `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose j` (for instance
`Stacks.EtaleCohomology.etaleModuleExtensionByZero`), and on the site of Tag 021B it is the left
adjoint of restriction along `AlgebraicGeometry.smallEtalePostcompose` (for instance
`AlgebraicGeometry.abelianExtensionByZero` and `AlgebraicGeometry.moduleExtensionByZero`). This
file shows that the equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sheaf
categories carry the one to the other.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toEtaleSiteRestrictionIso` — restriction along `j` commutes with
  restriction along the dense subsite inclusions `AlgebraicGeometry.SmallEtale.toEtaleSite`.
* `AlgebraicGeometry.SmallEtale.sheafEquivExtensionByZeroIso` — **extension by zero commutes with
  the equivalences of the two sheaf categories**, for arbitrary chosen left adjoints of the two
  restriction functors and an arbitrary coefficient category. It is proved in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.SmallEtaleSitePresentation`,
  imported here.

## Implementation notes

The square of sites
```
U_{021B} --postcompose--> X_{021B}
   |                         |
toEtaleSite              toEtaleSite
   v                         v
 U_étale  --compose j-->  X_étale
```
commutes on the nose: both composites send a scheme `V ⟶ U` below the size cutoff of `B` to
`V ⟶ U ⟶ X` in Mathlib's small étale site of `X`. So the square of restriction functors commutes
on the nose as well, and the comparison of extensions by zero is
`CategoryTheory.Adjunction.leftAdjointUniq` for the two composite adjunctions, as in
`AlgebraicGeometry.SmallEtale.toEtaleSitePullbackBaseChangeIso` for base change. The two left
adjoints are arguments, as there: each consumer uses its own representative (the sheaf pullback
of Mathlib, at whatever sheafification instance it was built with).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (A : Type u') [Category.{v'} A]

/-- **Restriction along an étale morphism commutes with the passage between the two models of the
small étale site.** For `U` in the small étale site of Tag 021B of `X`, with structure morphism
`j`, restriction along `j` on Mathlib's site followed by restriction along the embedding
`AlgebraicGeometry.SmallEtale.toEtaleSite` of `U` is restriction along the embedding of `X`
followed by restriction along `j` on the site of Tag 021B. The two composite functors of sites
agree on the nose, hence so do the two composites of restrictions. -/
public def toEtaleSiteRestrictionIso :
    (@Scheme.Etale.smallEtaleCompose U.obj.left.1 X (B.inclusion.map U.obj.hom)
        U.property).sheafPushforwardContinuous A
        U.obj.left.1.smallEtaleTopology X.smallEtaleTopology ⋙
      (toEtaleSite B U.obj.left.1 U.obj.left.property).sheafPushforwardContinuous A
        (topology B U.obj.left.1 U.obj.left.property) U.obj.left.1.smallEtaleTopology ≅
    (toEtaleSite B X hX).sheafPushforwardContinuous A (topology B X hX) X.smallEtaleTopology ⋙
      (smallEtalePostcompose B X hX U).sheafPushforwardContinuous A
        (topology B U.obj.left.1 U.obj.left.property) (topology B X hX) :=
  Iso.refl _

end AlgebraicGeometry.SmallEtale

end
