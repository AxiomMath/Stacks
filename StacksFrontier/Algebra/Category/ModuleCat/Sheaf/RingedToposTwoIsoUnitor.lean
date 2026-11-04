module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId

/-!
# The unitors of the 2-category of ringed topoi

`AlgebraicGeometry.RingedToposHom.comp` composes morphisms of ringed topoi and
`AlgebraicGeometry.RingedToposHom.id` is the identity for it.  This file supplies the two
2-isomorphisms saying so: composing a morphism with the identity of its source, or with the
identity of its target, gives back a morphism 2-isomorphic to it.  Together with
`AlgebraicGeometry.RingedToposHom.TwoIso.associator`, `.whiskerLeft` and `.whiskerRight` these
are what lets a diagram of composites be rearranged, which is how a conjugation by an
identification of ringed topoi is undone.

Both are 2-isomorphisms of the strictest possible kind: the direct image of either composite is
the direct image of the morphism *on the nose* — the direct image of the identity morphism of
topoi is `𝟭`, and `CategoryTheory.Functor.id_comp` and `.comp_id` hold by definition — so the
underlying isomorphism of direct images is `CategoryTheory.Iso.refl`, and all that has to be
checked is the structure-map equation.  That reduces, by
`AlgebraicGeometry.RingedToposHom.forgetFSharp_comp`, to the structure map of the identity being
the identity on underlying sheaves of sets, which is
`AlgebraicGeometry.RingedToposHom.forgetRing_map_id_fSharp`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.compId`: the 2-isomorphism `f ∘ 1_A ≅ f`, where `A`
  is the source of `f`.
* `AlgebraicGeometry.RingedToposHom.TwoIso.idComp`: the 2-isomorphism `1_B ∘ f ≅ f`, where `B`
  is the target of `f`.

## Main results

* `AlgebraicGeometry.RingedToposHom.forgetFSharp_id`: the structure map of the identity morphism
  of a ringed topos, read on underlying sheaves of sets, is the identity.

## Implementation notes

The two names are read off the *application* `AlgebraicGeometry.RingedToposHom.comp g f`, which
is `g` after `f`: `compId` is the case where the second argument is an identity and `idComp` the
case where the first one is.  In the diagrammatic order of a bicategory, `compId` is therefore
the *left* unitor `1_A ≫ f ≅ f` and `idComp` the *right* unitor `f ≫ 1_B ≅ f`; the names follow
the order the arguments are written in here, as `CategoryTheory.Functor.comp_id` and `.id_comp`
do for functors.

`AlgebraicGeometry.RingedToposHom.comp` and `CategoryTheory.MorphismOfTopoi.comp` are made
locally reducible, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposTwoMorphism.lean`, so that the direct
image of a composite reduces to the composite of the direct images at `implicit` transparency
and `CategoryTheory.Iso.refl` can be offered for the underlying isomorphism.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- The structure map of the identity morphism of a ringed topos, read on underlying sheaves of
sets as in `AlgebraicGeometry.RingedToposHom.forgetFSharp`, is the identity. -/
theorem forgetFSharp_id :
    forgetFSharp (RingedToposHom.id A) = 𝟙 (A.forgetRing.obj A.O) :=
  forgetRing_map_id_fSharp A

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

namespace TwoIso

/-- **Composing a morphism of ringed topoi with the identity of its source changes nothing.**
The direct image of the composite is the direct image of `f`, and the structure map of the
composite is the structure map of `f` followed by the direct image of the identity on the source
structure sheaf. -/
noncomputable def compId (f : RingedToposHom A B) :
    TwoIso (f.comp (RingedToposHom.id A)) f where
  e := Iso.refl f.toToposHom.pushforward
  commutes := by
    refine (Category.comp_id _).trans ?_
    refine (forgetFSharp_comp f (RingedToposHom.id A)).trans ?_
    exact (congrArg (fun m ↦ forgetFSharp f ≫ m)
        ((congrArg f.toToposHom.pushforward.map forgetFSharp_id).trans
          (f.toToposHom.pushforward.map_id _))).trans
      (Category.comp_id _)

/-- **Composing a morphism of ringed topoi with the identity of its target changes nothing.**
The direct image of the composite is the direct image of `f`, and the structure map of the
composite is the identity followed by the structure map of `f`. -/
noncomputable def idComp (f : RingedToposHom A B) :
    TwoIso ((RingedToposHom.id B).comp f) f where
  e := Iso.refl f.toToposHom.pushforward
  commutes := by
    refine (Category.comp_id _).trans ?_
    refine (forgetFSharp_comp (RingedToposHom.id B) f).trans ?_
    exact (congrArg
        (fun m ↦ m ≫ (RingedToposHom.id B).toToposHom.pushforward.map (forgetFSharp f))
        forgetFSharp_id).trans
      (Category.id_comp _)

end TwoIso

end AlgebraicGeometry.RingedToposHom

end
