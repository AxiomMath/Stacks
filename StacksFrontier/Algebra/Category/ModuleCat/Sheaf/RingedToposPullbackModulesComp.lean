module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Adjunction.Mates
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of sheaves of modules along a composite of morphisms of ringed topoi

Let `X ⟶ Y ⟶ Z` be morphisms of ringed topoi in the sense of Stacks 01D3, i.e.
`AlgebraicGeometry.RingedToposHom`s. The direct image of sheaves of modules composes,
`(g ∘ f)_* ≅ f_* ⋙ g_*`
(`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`). This file draws the adjoint
consequence: the pullback composes the other way round,

`(g ∘ f)^* ≅ g^* ⋙ f^*`,

by uniqueness of left adjoints. No computation is involved — both sides are left adjoint to
`f_* ⋙ g_*`, the left-hand side by the composition isomorphism for direct images and the
right-hand side because adjunctions compose.

The consequence this is wanted for is **Stacks 05V5**: the stalk of a pullback. A point `p` of
`Sh(C)` presented as a morphism of ringed topoi out of a ringed point
(`Stacks.Sheaves.RingedPoint.RingedPointSituation`) makes `(f^*F)_p` the pullback along the
composite `pt_p ⟶ X ⟶ Y`, and the point `q = f ∘ p` makes `F_q ⊗_{O_{D,q}} O_{C,p}` the
pullback along `pt_p ⟶ pt_q ⟶ Y`; the two composites agree, so the two pullbacks do.
`pullbackModulesSquareIso` below is that argument, with the commutativity of the square as its
hypothesis.

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`: the pullback of sheaves of modules
  along a composite is the composite of the pullbacks. Together with
  `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` this is **Stacks 03D8**.
* `AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom`: that comparison
  is the canonical one, its mate under the adjunctions of Stacks 03D7 being the inverse of the
  comparison of direct images.
* `Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`
  (`StacksFrontier/CategoryTheory/Adjunction/Mates.lean`): the general fact behind it. Given
  adjunctions `L ⊣ R`, `L' ⊣ R'` and an isomorphism `e : R ≅ R'`, the comparison of the two
  left adjoints produced by `CategoryTheory.Adjunction.leftAdjointUniq` has conjugate `e.inv`.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesSquareIso`: **the formula of Stacks 05V5.**
  For a commutative square of morphisms of ringed topoi, pulling back along the top and then
  down the left is pulling back down the right and then along the bottom.

## What this file does not contain

`pullbackModulesSquareIso` is the *formula* of Stacks 05V5 and not the whole of that tag. The
tag also asserts that the square exists: that a point `p` of `Sh(C)` and the point
`q = f ∘ p` of `Sh(D)` (`CategoryTheory.MorphismOfTopoi.compPoint`) are joined by a morphism of
ringed points `pt_p ⟶ pt_q` making the square commute. Neither that morphism nor the
commutativity is constructed here, and neither exists anywhere in the tree. The obstruction is
recorded for the next reader because it is structural rather than mathematical:
`Stacks.Sheaves.RingedPoint.RingedPointSituation.toRingedToposHom` is a
`Stacks.Sheaves.RingedToposModules.RingedToposHom` — the four-field morphism of ringed topoi,
carrying both forms of the structure map and their adjunction — whereas the composition
`AlgebraicGeometry.RingedToposHom.comp` used here is defined for the two-field morphism. There
is a conversion from the two-field form to the four-field one
(`AlgebraicGeometry.RingedToposHom.toModulesHom`) but none in the other direction, and no
composition for the four-field form. So the tag is part-qualified here, and the two pieces this
route would still need are: a composition for
`Stacks.Sheaves.RingedToposModules.RingedToposHom` (whose `fSharp_adjunct` field is the one
real obligation), and the morphism of ringed points over `q = f ∘ p`.

That this route is unavailable does *not* leave Stacks 05V5 unproved. The tag is discharged by a
different argument, which needs no
ringed-point square: `Stacks.Sheaves.StalkPullback.pointStalkFunctorIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkPullbackAtAPoint.lean`) proves
`(f^*𝓕)_p ≅ 𝓕_q ⊗_{𝒪'_q} 𝒪_p` for an arbitrary morphism of ringed topoi and an arbitrary point
of the source, with `q = f ∘ p` constructed from `f` and `p` by Stacks 00YA — composing the
point with the underlying morphism of topoi at the level of topos points, where the four-field
structure's missing composition is not in the way.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The pullback of sheaves of modules along a composite of morphisms of ringed topoi is the
composite of the pullbacks**, `(g ∘ f)^* ≅ g^* ⋙ f^*`.

Both sides are left adjoint to `f_* ⋙ g_*`: the left-hand side by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` transported across its adjunction,
the right-hand side because adjunctions compose. So they agree by uniqueness of left
adjoints. -/
@[stacks 03D6 "part (2), pseudo-functoriality: the pullback of a composite of morphisms of
ringed topoi is the composite of the pullbacks"]
def pullbackModulesCompIso (f : RingedToposHom X Y) (g : RingedToposHom Y Z) :
    (g.comp f).toModulesHom.pullbackModules ≅
      g.toModulesHom.pullbackModules ⋙ f.toModulesHom.pullbackModules :=
  ((pullbackAdjPushforwardModules (g.comp f)).ofNatIsoRight
      (pushforwardModulesCompIso f g)).leftAdjointUniq
    ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))

/-- **The formula of Stacks 05V5.** Let

```
  P ⟶ X
  ↓     ↓
  Q ⟶ Y
```

be a commutative square of morphisms of ringed topoi — the hypothesis `h` says that the two
composites `P ⟶ Y` agree. Then pulling a sheaf of `O_Y`-modules back along the bottom and then
down the right is the same as pulling it back down the left and then along the top:

`f^* ⋙ π^* ≅ ρ^* ⋙ γ^*`.

Stacks 05V5 is this applied to the square whose left column is a point `p` of `Sh(C)`, whose
right column is the point `q = f ∘ p` of `Sh(D)`, and whose bottom row is the induced morphism
of ringed points: the left-hand composite is then `F ↦ (f^*F)_p` and the right-hand one is
`F ↦ F_q ⊗_{O_{D,q}} O_{C,p}`. The square itself is not constructed here — see the
module docstring. -/
@[stacks 05V5 "the formula, for a commutative square of morphisms of ringed topoi; the
square over a point `p` and the point `q = f ∘ p` is not constructed"]
def pullbackModulesSquareIso {P : RingedTopos.{v, u, w}} {Q : RingedTopos.{v', u', w'}}
    [P.J.HasSheafCompose (forget RingCat.{w})]
    [P.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [P.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify P.J AddCommGrpCat.{w}] [P.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Q.J.HasSheafCompose (forget RingCat.{w'})]
    [Q.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [Q.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
    [HasWeakSheafify Q.J AddCommGrpCat.{w'}] [Q.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    (f : RingedToposHom X Y) (π : RingedToposHom P X) (ρ : RingedToposHom Q Y)
    (γ : RingedToposHom P Q) (h : f.comp π = ρ.comp γ) :
    f.toModulesHom.pullbackModules ⋙ π.toModulesHom.pullbackModules ≅
      ρ.toModulesHom.pullbackModules ⋙ γ.toModulesHom.pullbackModules :=
  (pullbackModulesCompIso π f).symm ≪≫
    eqToIso (congrArg (fun m : RingedToposHom P Y => m.toModulesHom.pullbackModules) h) ≪≫
    pullbackModulesCompIso γ ρ

/-- **Stacks 03D8.** The comparison `(g ∘ f)^* ≅ g^* ⋙ f^*` of pullbacks of sheaves of modules
is the *canonical* one: its mate under the adjunctions `f^* ⊣ f_*` and `g^* ⊣ g_*` of
Stacks 03D7 is the inverse of the comparison `(g ∘ f)_* ≅ f_* ⋙ g_*` of direct images. This is
what pins down the normalization of the inverse-image comparison, the direct-image one being
normalized by `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso_underlying`. -/
@[stacks 03D8 "pullback canonicity"]
theorem conjugateEquiv_pullbackModulesCompIso_hom (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) :
    conjugateEquiv ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))
        (pullbackAdjPushforwardModules (g.comp f)) (pullbackModulesCompIso f g).hom =
      (pushforwardModulesCompIso f g).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-! ## The rest of the covering set of Stacks 03D8

Stacks 03D8 asserts the two canonical isomorphisms `(g ∘ f)_* ≅ g_* ∘ f_*` and
`(g ∘ f)^* ≅ f^* ∘ g^*` for composable morphisms of ringed topoi. Both are already proved —
the first in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPushforwardComp.lean`, together with
the normalization of its underlying map, and the second above — so they are recorded against
the tag here rather than restated. -/

add_to_stacks 03D8 "pushforward"
  AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso

add_to_stacks 03D8 "pushforward canonicity"
  AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso_underlying

add_to_stacks 03D8 "pullback"
  AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso

end AlgebraicGeometry.RingedToposHom

end
