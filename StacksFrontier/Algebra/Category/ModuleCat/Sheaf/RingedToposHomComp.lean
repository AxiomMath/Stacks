module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
import StacksCore.Tactic.StacksAttribute

/-!
# The structure map of a composite of morphisms of ringed topoi, in adjunct form

A morphism of ringed topoi (Stacks 01D3) carries its structure map in direct-image form,
`f♯ : O_Z ⟶ f_*O_X`, so composing two of them needs the comparison
`(f ∘ g)_* ≅ f_* ∘ g_*` on sheaves of commutative rings. That comparison is obtained from the
corresponding comparison for inverse images — which is
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorComp`, an isomorphism that is the
identity on underlying sheaves of sets — by uniqueness of right adjoints.

## Main definitions

* `Stacks.Sheaves.ToposPushforward.inverseImageCommRingComp`: the inverse image of sheaves of
  commutative rings along a composite of morphisms of topoi is the iterated inverse image.
* `AlgebraicGeometry.RingedToposHom.compFSharpInverseImage`: the inverse-image form of the
  structure map of a composite of morphisms of ringed topoi.
* `AlgebraicGeometry.RingedToposHom.compFSharp`: its direct-image form, i.e. the structure map
  of the composite, as the adjunct of `compFSharpInverseImage`.

## Main results

* `Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingComp_hom` and `.._inv`: the
  inverse-image comparison is the identity on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.compFSharp_inverseImage`: the inverse-image form of
  `compFSharp` is `compFSharpInverseImage`, i.e. the composite of the two inverse-image forms
  read through the comparison.
* `AlgebraicGeometry.RingedToposHom.forget_map_compFSharpInverseImage` and
  `.forget_map_compFSharp`: both forms of the structure map of a composite, after forgetting the
  ring operations. They are stated here, where the three ringed topoi are abstract, because every
  statement about a commutative triangle of ringed topoi needs them and the terms are small
  here.

## Implementation notes

The composition of morphisms of ringed topoi itself is
`AlgebraicGeometry.RingedToposHom.comp`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPushforwardComp.lean`, which builds its
structure map as the source's own `g♯ ≫ g_*f♯` followed by the comparison, at three independent
sections universes. What this file supplies is the *adjunct* presentation of the same structure
map: `compFSharp` is built from the inverse-image forms and only then transported across the
adjunction. The two agree, but the adjunct form is what
`Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv` computes on
underlying sheaves of sets, which is what every compatibility statement about a commutative
triangle of ringed topoi needs. The identification of the two forms is not proved here.

The three ringed topoi share the universe of the sections of their structure sheaves. That is
forced by `pullbackCommRingSheafFunctorComp`, whose three sites take their sheaves of commutative
rings in one universe; the sites themselves keep independent universes.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

universe w vE uE vF uF vG uG

section Comp

variable {E : Type uE} [Category.{vE} E] {F : Type uF} [Category.{vF} F]
  {G : Type uG} [Category.{vG} G]
  {JE : GrothendieckTopology E} {JF : GrothendieckTopology F} {JG : GrothendieckTopology G}
  [JE.HasSheafCompose (forget RingCat.{w})] [JF.HasSheafCompose (forget RingCat.{w})]
  [JG.HasSheafCompose (forget RingCat.{w})]
  [JE.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JF.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JG.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (g : MorphismOfTopoi (Sheaf JF (Type w)) (Sheaf JG (Type w)))
  (f : MorphismOfTopoi (Sheaf JE (Type w)) (Sheaf JF (Type w)))

/-- The inverse image of sheaves of commutative rings along a composite of morphisms of topoi is
the iterated inverse image. -/
noncomputable def inverseImageCommRingComp :
    inverseImageCommRingFunctor g ⋙ inverseImageCommRingFunctor f ≅
      inverseImageCommRingFunctor (g.comp f) :=
  pullbackCommRingSheafFunctorComp JF JE g.inverseImage f.inverseImage

variable [JE.HasSheafCompose (forget CommRingCat.{w})]
  [JG.HasSheafCompose (forget CommRingCat.{w})]

/-- The inverse-image comparison is the identity on underlying sheaves of sets. -/
@[simp] theorem forget_map_inverseImageCommRingComp_hom (O : Sheaf JG CommRingCat.{w}) :
    (sheafCompose JE (forget CommRingCat.{w})).map ((inverseImageCommRingComp g f).hom.app O) =
      𝟙 ((sheafCompose JE (forget CommRingCat.{w})).obj
        ((inverseImageCommRingFunctor (g.comp f)).obj O)) :=
  forget_map_pullbackCommRingSheafComp_hom JF JE g.inverseImage f.inverseImage O

/-- The inverse of the inverse-image comparison is also the identity on underlying sheaves of
sets. -/
@[simp] theorem forget_map_inverseImageCommRingComp_inv (O : Sheaf JG CommRingCat.{w}) :
    (sheafCompose JE (forget CommRingCat.{w})).map ((inverseImageCommRingComp g f).inv.app O) =
      𝟙 ((sheafCompose JE (forget CommRingCat.{w})).obj
        ((inverseImageCommRingFunctor (g.comp f)).obj O)) :=
  have h : (sheafCompose JE (forget CommRingCat.{w})).map
        ((inverseImageCommRingComp g f).hom.app O) ≫
      (sheafCompose JE (forget CommRingCat.{w})).map
        ((inverseImageCommRingComp g f).inv.app O) = 𝟙 _ :=
    ((sheafCompose JE (forget CommRingCat.{w})).map_comp _ _).symm.trans
      ((congrArg (sheafCompose JE (forget CommRingCat.{w})).map
          ((inverseImageCommRingComp g f).hom_inv_id_app O)).trans
        ((sheafCompose JE (forget CommRingCat.{w})).map_id _))
  ((congrArg (fun m ↦ m ≫ (sheafCompose JE (forget CommRingCat.{w})).map
        ((inverseImageCommRingComp g f).inv.app O))
      (forget_map_inverseImageCommRingComp_hom g f O)).symm.trans h).symm.trans
    (Category.id_comp _).symm |>.symm

end Comp

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.ToposPushforward

universe w v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (F : RingedToposHom Y Z) (G : RingedToposHom X Y)

/-- The inverse-image form of the structure map of a composite of morphisms of ringed topoi: the
inverse image of the structure map of the outer morphism, followed by the structure map of the
inner one, read through the comparison of the iterated inverse image with the inverse image along
the composite. -/
noncomputable def compFSharpInverseImage :
    (inverseImageCommRingFunctor (F.toToposHom.comp G.toToposHom)).obj Z.O ⟶ X.O :=
  (inverseImageCommRingComp F.toToposHom G.toToposHom).inv.app Z.O ≫
    (inverseImageCommRingFunctor G.toToposHom).map F.fSharpInverseImage ≫ G.fSharpInverseImage

/-- The structure map of a composite of morphisms of ringed topoi, in direct-image form: the
adjunct of `compFSharpInverseImage`. -/
noncomputable def compFSharp :
    Z.O ⟶ (pushforwardCommRingFunctor (F.toToposHom.comp G.toToposHom)).obj X.O :=
  (commRingImageAdjunction (F.toToposHom.comp G.toToposHom)).homEquiv Z.O X.O
    (compFSharpInverseImage F G)

/-- The inverse-image form of `compFSharp` is `compFSharpInverseImage`. -/
@[simp] theorem compFSharp_inverseImage :
    ((commRingImageAdjunction (F.toToposHom.comp G.toToposHom)).homEquiv Z.O X.O).symm
        (compFSharp F G) = compFSharpInverseImage F G :=
  ((commRingImageAdjunction (F.toToposHom.comp G.toToposHom)).homEquiv Z.O X.O).symm_apply_apply _

section Forget

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [Z.J.HasSheafCompose (forget CommRingCat.{w})]

/-- The inverse-image form of the structure map of a composite, after forgetting the ring
operations: the comparison of the iterated inverse image with the inverse image along the
composite is the identity there, so only the two structure maps remain. -/
theorem forget_map_compFSharpInverseImage :
    (sheafCompose X.J (forget CommRingCat.{w})).map (compFSharpInverseImage F G) =
      G.toToposHom.inverseImage.map
          ((sheafCompose Y.J (forget CommRingCat.{w})).map F.fSharpInverseImage) ≫
        (sheafCompose X.J (forget CommRingCat.{w})).map G.fSharpInverseImage :=
  ((sheafCompose X.J (forget CommRingCat.{w})).map_comp _ _).trans
    ((congrArg (fun m ↦ m ≫ (sheafCompose X.J (forget CommRingCat.{w})).map
          ((inverseImageCommRingFunctor G.toToposHom).map F.fSharpInverseImage ≫
            G.fSharpInverseImage))
        (forget_map_inverseImageCommRingComp_inv F.toToposHom G.toToposHom Z.O)).trans
      ((Category.id_comp _).trans
        (((sheafCompose X.J (forget CommRingCat.{w})).map_comp _ _).trans
          (congrArg (fun m ↦ m ≫ (sheafCompose X.J (forget CommRingCat.{w})).map
              G.fSharpInverseImage)
            (underlyingRingSheaf_map_pullbackCommRingSheafMap X.J (Φ := G.toToposHom.inverseImage)
              F.fSharpInverseImage)))))

omit [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The structure map of a composite, after forgetting the ring operations: the adjunct of its
inverse-image form. -/
theorem forget_map_compFSharp :
    (sheafCompose Z.J (forget CommRingCat.{w})).map (compFSharp F G) =
      (F.toToposHom.comp G.toToposHom).adj.unit.app
          ((sheafCompose Z.J (forget CommRingCat.{w})).obj Z.O) ≫
        (F.toToposHom.comp G.toToposHom).pushforward.map
          ((sheafCompose X.J (forget CommRingCat.{w})).map (compFSharpInverseImage F G)) :=
  (forget_map_commRingImageAdjunction_homEquiv (F.toToposHom.comp G.toToposHom) Z.O X.O
      (compFSharpInverseImage F G)).trans
    (Adjunction.homEquiv_apply (F.toToposHom.comp G.toToposHom).adj _ _ _)

end Forget

end AlgebraicGeometry.RingedToposHom

end
