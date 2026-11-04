module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId

/-!
# The round trips of an invertible morphism of ringed topoi, as 2-isomorphisms

Let `f : (Sh(𝒞), 𝒪_X) ⟶ (Sh(𝒟), 𝒪_Y)` be a morphism of ringed topoi whose direct image is an
equivalence and whose structure map is invertible, so that
`AlgebraicGeometry.RingedToposHom.inverse` is defined. This file identifies both round trips with
the identity morphism of [Stacks, Tag 01D3] part (3), as 2-isomorphisms in the sense of
[Stacks, Tag 04IC].

Neither round trip is an *equality*: the direct image of `f ∘ f^{-1}` is `f^{-1} ⋙ f_*`, which is
only isomorphic to the identity functor — through the unit of `f^{-1} ⊣ f_*` — and the inverse
image carries a choice besides. A 2-isomorphism is exactly the right amount of agreement, and it
is what the invariance statements of this directory consume.

## The two sides are not symmetric in the available API

For `f ∘ f^{-1}` everything is in place: `f^{-1} ⋙ f_* ≅ 𝟭` is
`AlgebraicGeometry.RingedToposHom.inverseImageCompPushforwardIsoId`, which is `asIso` of the unit,
and the structure map of the composite is that unit on underlying sheaves of sets, by
`AlgebraicGeometry.RingedToposHom.forgetRing_map_comp_inverse_fSharp`. So the `commutes` field is
one application of `CategoryTheory.Iso.hom_inv_id_app`.

For `f^{-1} ∘ f` nothing was available, and the `commutes` field has to be computed: the structure
map of the composite is the inverse of the inverse-image form of `f^♯` followed by `f^{-1}` of the
direct-image form, and composing the second of those with the counit returns the first, by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget` — which is the adjunctness of the two
forms of the structure map. What is left is `inv h ≫ h = 𝟙`.

## Main results

* `AlgebraicGeometry.RingedToposHom.compInverseTwoIsoId`: `f ∘ f^{-1} ≅ id`, 2-isomorphically.
* `AlgebraicGeometry.RingedToposHom.inverseCompTwoIsoId`: `f^{-1} ∘ f ≅ id`, 2-isomorphically.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]

/-- **The round trip `Y ⟶ X ⟶ Y` of an invertible morphism of ringed topoi is 2-isomorphic to the
identity.** The underlying isomorphism of direct images is the inverse of the unit of
`f^{-1} ⊣ f_*`, by `AlgebraicGeometry.RingedToposHom.inverseImageCompPushforwardIsoId`, and the
`commutes` field is `AlgebraicGeometry.RingedToposHom.forgetRing_map_comp_inverse_fSharp`
followed by the cancellation of that unit against its inverse. -/
def compInverseTwoIsoId : TwoIso (f.comp (inverse f)) (RingedToposHom.id Y) where
  e := (asIso f.toToposHom.adj.unit).symm
  commutes :=
    (congrArg
      (fun m ↦ m ≫ (asIso f.toToposHom.adj.unit).symm.hom.app (Y.forgetRing.obj Y.O))
      (forgetRing_map_comp_inverse_fSharp f)).trans
      (((asIso f.toToposHom.adj.unit).hom_inv_id_app (Y.forgetRing.obj Y.O)).trans
        (forgetRing_map_id_fSharp Y).symm)

/-- **The round trip `X ⟶ Y ⟶ X` of an invertible morphism of ringed topoi is 2-isomorphic to the
identity.** The underlying isomorphism of direct images is the counit of `f^{-1} ⊣ f_*`, which is
invertible because the direct image is an equivalence.

The `commutes` field is the computation described in the module documentation: the structure map
of the composite is `inv (f^♯)^{-1}` followed by `f^{-1}` of `f^♯`, and composing the latter with
the counit gives back `(f^♯)^{-1}`, by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`. -/
def inverseCompTwoIsoId : TwoIso ((inverse f).comp f) (RingedToposHom.id X) where
  e := @asIso _ _ _ _ _ (MorphismOfTopoi.isIso_adj_counit f.toToposHom)
  commutes :=
    (congrArg (fun m ↦ m ≫ f.toToposHom.adj.counit.app (X.forgetRing.obj X.O))
        (forgetFSharp_comp (inverse f) f)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ forgetFSharp (inverse f) ≫ m)
            (fSharpInverseImage_forget f).symm).trans
          (((X.forgetRing.map_comp (inv f.fSharpInverseImage) f.fSharpInverseImage).symm.trans
              ((congrArg X.forgetRing.map (IsIso.inv_hom_id f.fSharpInverseImage)).trans
                (X.forgetRing.map_id X.O))).trans
            (forgetRing_map_id_fSharp X).symm)))

end AlgebraicGeometry.RingedToposHom

end
