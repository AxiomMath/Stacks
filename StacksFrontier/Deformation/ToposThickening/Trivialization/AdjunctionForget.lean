module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The commutative-ring image adjunction on underlying sheaves of sets

The adjunction `f⁻¹ ⊣ f_*` for sheaves of commutative rings along a morphism of topoi,
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, is obtained from the ring-valued
adjunction by restriction along the fully faithful inclusion of sheaves of commutative rings.
This file computes its unit, its counit and the inverse of its hom-set bijection on *underlying
sheaves of sets*, where they are the unit, the counit and the hom-set bijection of the
adjunction `f⁻¹ ⊣ f_*` of sheaves of sets.

Two consequences are recorded: the inverse-image form of the structure map of a morphism of
ringed topoi is the geometric adjunct of its direct-image form, and the direct image of sheaves
of commutative rings is an equivalence whenever the direct image of sheaves of sets is.

## Main results

* `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_unit_forget` and
  `.commRingImageAdjunction_counit_forget`: the unit and counit are those of `f⁻¹ ⊣ f_*`.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`: on underlying sheaves of sets,
  the inverse-image form of the structure map is the adjunct of the direct-image form, written
  through the counit. This is the result that
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposHom.lean` describes in its module
  documentation; it is named `_forget` rather than `_hom` because in this repository `_hom`
  denotes an iso's `.hom` component.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`: the same with the
  adjunct written through the hom-set bijection of `f⁻¹ ⊣ f_*`.  This is the form to use when a
  computation needs the hom-set bijection rather than the counit.

There is no separate lemma saying that the inverse hom-set bijection of the ring-valued
adjunction is that of `f⁻¹ ⊣ f_*`.  The usable statements are
`fSharpInverseImage_forget_homEquiv` just named, together with the unit and counit lemmas above,
out of which a hom-set statement is recovered by `CategoryTheory.Adjunction.homEquiv_counit`.
* `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor_isEquivalence`: the direct image
  of sheaves of commutative rings along a morphism of topoi whose direct image of sheaves of
  sets is an equivalence is itself an equivalence.

## Implementation notes

The two comparison isomorphisms that `commRingImageAdjunction` restricts along,
`Stacks.Sheaves.ToposPullback.forgetCommRingSheafCompPullbackIso`, have identity components;
`forgetCommRingSheafCompPullbackIso_hom_app` and `_inv_app` record that, which is what collapses
`CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` and
`.map_restrictFullyFaithful_counit_app` to the ring-valued unit and counit.

That the direct image is an equivalence is deduced from the adjunction rather than transported:
`sheafCompose J (forget CommRingCat)` reflects isomorphisms, because `forget CommRingCat` does,
so it suffices that the unit and counit be isomorphisms on underlying sheaves of sets, which is
what the lemmas above reduce them to.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

/-- Forgetting commutativity commutes with the inverse image by the identity. -/
@[simp]
lemma forgetCommRingSheafCompPullbackIso_hom_app (A : Sheaf K CommRingCat.{ww'}) :
    (forgetCommRingSheafCompPullbackIso J Φ).hom.app A =
      𝟙 ((Stacks.forgetCommRingSheaf K ⋙ pullbackRingSheafFunctor J Φ).obj A) :=
  rfl

/-- The inverse comparison is also the identity. -/
@[simp]
lemma forgetCommRingSheafCompPullbackIso_inv_app (A : Sheaf K CommRingCat.{ww'}) :
    (forgetCommRingSheafCompPullbackIso J Φ).inv.app A =
      𝟙 ((pullbackCommRingSheafFunctor J Φ ⋙ Stacks.forgetCommRingSheaf J).obj A) :=
  rfl

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- Forgetting commutativity carries the unit of the commutative-ring image adjunction to the
unit of the ring image adjunction. -/
lemma commRingImageAdjunction_unit_forgetCommRing (O : Sheaf K CommRingCat.{ww'}) :
    (Stacks.forgetCommRingSheaf K).map ((commRingImageAdjunction f).unit.app O) =
      ringUnit f (SheafOfModules.Tensor.ringSheaf O) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app (ringImageAdjunction f)
    (fullyFaithfulForgetCommRingSheaf K) (fullyFaithfulForgetCommRingSheaf J)
    (forgetCommRingSheafCompPullbackIso J f.inverseImage)
    (forgetCommRingSheafCompPullbackIso K f.pushforward) O
  rw [forgetCommRingSheafCompPullbackIso_hom_app,
    forgetCommRingSheafCompPullbackIso_hom_app] at h
  refine h.trans ?_
  have e : (pushforwardRingFunctor f).map
        (𝟙 ((Stacks.forgetCommRingSheaf K ⋙ pullbackRingSheafFunctor J f.inverseImage).obj O)) ≫
        𝟙 ((Stacks.forgetCommRingSheaf J ⋙ pullbackRingSheafFunctor K f.pushforward).obj
          ((inverseImageCommRingFunctor f).obj O)) =
      𝟙 ((pushforwardRingFunctor f).obj
        ((Stacks.forgetCommRingSheaf K ⋙ pullbackRingSheafFunctor J f.inverseImage).obj O)) :=
    (Category.comp_id _).trans ((pushforwardRingFunctor f).map_id _)
  exact (congrArg
    (fun m ↦ (ringImageAdjunction f).unit.app (SheafOfModules.Tensor.ringSheaf O) ≫ m) e).trans
    (Category.comp_id _)

/-- Forgetting commutativity carries the counit of the commutative-ring image adjunction to the
counit of the ring image adjunction. -/
lemma commRingImageAdjunction_counit_forgetCommRing (O : Sheaf J CommRingCat.{ww}) :
    (Stacks.forgetCommRingSheaf J).map ((commRingImageAdjunction f).counit.app O) =
      ringCounit f (SheafOfModules.Tensor.ringSheaf O) := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app (ringImageAdjunction f)
    (fullyFaithfulForgetCommRingSheaf K) (fullyFaithfulForgetCommRingSheaf J)
    (forgetCommRingSheafCompPullbackIso J f.inverseImage)
    (forgetCommRingSheafCompPullbackIso K f.pushforward) O
  rw [forgetCommRingSheafCompPullbackIso_inv_app,
    forgetCommRingSheafCompPullbackIso_inv_app] at h
  refine h.trans ?_
  have e : (inverseImageRingFunctor f).map
        (𝟙 ((pullbackCommRingSheafFunctor K f.pushforward ⋙
          Stacks.forgetCommRingSheaf K).obj O)) ≫
        ringCounit f (SheafOfModules.Tensor.ringSheaf O) =
          ringCounit f (SheafOfModules.Tensor.ringSheaf O) :=
    (congrArg (fun m ↦ m ≫ ringCounit f (SheafOfModules.Tensor.ringSheaf O))
      ((inverseImageRingFunctor f).map_id _)).trans (Category.id_comp _)
  exact (Category.id_comp _).trans e

/-- On underlying sheaves of sets, the unit of the commutative-ring image adjunction is the unit
of `f⁻¹ ⊣ f_*`. -/
@[simp]
lemma commRingImageAdjunction_unit_forget (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose K (forget CommRingCat.{ww'})).map ((commRingImageAdjunction f).unit.app O) =
      f.adj.unit.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) := by
  show (sheafCompose K (forget RingCat.{ww'})).map
      ((Stacks.forgetCommRingSheaf K).map ((commRingImageAdjunction f).unit.app O)) = _
  rw [commRingImageAdjunction_unit_forgetCommRing]
  exact Stacks.Sheaves.RingedToposModules.ringSheafMap_ringUnit f
    (SheafOfModules.Tensor.ringSheaf O)

/-- On underlying sheaves of sets, the counit of the commutative-ring image adjunction is the
counit of `f⁻¹ ⊣ f_*`. -/
@[simp]
lemma commRingImageAdjunction_counit_forget (O : Sheaf J CommRingCat.{ww}) :
    (sheafCompose J (forget CommRingCat.{ww})).map ((commRingImageAdjunction f).counit.app O) =
      f.adj.counit.app ((sheafCompose J (forget CommRingCat.{ww})).obj O) := by
  show (sheafCompose J (forget RingCat.{ww})).map
      ((Stacks.forgetCommRingSheaf J).map ((commRingImageAdjunction f).counit.app O)) = _
  rw [commRingImageAdjunction_counit_forgetCommRing]
  exact ringSheafMap_ringCounit f (SheafOfModules.Tensor.ringSheaf O)

/-- If the direct image of a morphism of topoi is an equivalence, so is the induced direct image
of sheaves of commutative rings. The unit and counit of `commRingImageAdjunction` are
isomorphisms because they are so on underlying sheaves of sets, and
`sheafCompose _ (forget CommRingCat)` reflects isomorphisms. -/
lemma pushforwardCommRingFunctor_isEquivalence (hf : f.pushforward.IsEquivalence) :
    (pushforwardCommRingFunctor f).IsEquivalence := by
  have : f.pushforward.IsEquivalence := hf
  have : f.inverseImage.IsEquivalence := f.adj.isEquivalence_left_of_isEquivalence_right
  have : ∀ R : Sheaf K CommRingCat.{ww'},
      IsIso ((commRingImageAdjunction f).unit.app R) := fun R ↦
    have : IsIso (f.adj.unit.app ((sheafCompose K (forget CommRingCat.{ww'})).obj R)) :=
      inferInstance
    have : IsIso ((sheafCompose K (forget CommRingCat.{ww'})).map
        ((commRingImageAdjunction f).unit.app R)) := by
      rw [commRingImageAdjunction_unit_forget]
      assumption
    isIso_of_reflects_iso _ (sheafCompose K (forget CommRingCat.{ww'}))
  have : ∀ R : Sheaf J CommRingCat.{ww},
      IsIso ((commRingImageAdjunction f).counit.app R) := fun R ↦
    have : IsIso (f.adj.counit.app ((sheafCompose J (forget CommRingCat.{ww})).obj R)) :=
      inferInstance
    have : IsIso ((sheafCompose J (forget CommRingCat.{ww})).map
        ((commRingImageAdjunction f).counit.app R)) := by
      rw [commRingImageAdjunction_counit_forget]
      assumption
    isIso_of_reflects_iso _ (sheafCompose J (forget CommRingCat.{ww}))
  exact (commRingImageAdjunction f).toEquivalence.isEquivalence_inverse

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry

namespace RingedToposHom

open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- **The adjunctness of the two forms of the structure map**, described in the module
documentation of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposHom.lean`. On underlying
sheaves of
sets, the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map of a morphism of ringed topoi
is the adjunct, under `f⁻¹ ⊣ f_*` for sheaves of sets, of the direct-image form. -/
lemma fSharpInverseImage_forget (f : RingedToposHom X Y) :
    X.forgetRing.map f.fSharpInverseImage =
      f.toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp) ≫
        f.toToposHom.adj.counit.app (X.forgetRing.obj X.O) := by
  have h1 : f.fSharpInverseImage =
      (inverseImageCommRingFunctor f.toToposHom).map f.fSharp ≫
        (commRingImageAdjunction f.toToposHom).counit.app X.O :=
    (commRingImageAdjunction f.toToposHom).homEquiv_counit Y.O X.O f.fSharp
  have h2 : X.forgetRing.map ((inverseImageCommRingFunctor f.toToposHom).map f.fSharp) =
      f.toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp) :=
    underlyingRingSheaf_map_pullbackCommRingSheafMap X.J (Φ := f.toToposHom.inverseImage) f.fSharp
  rw [h1, CategoryTheory.Functor.map_comp, h2, commRingImageAdjunction_counit_forget]
  rfl

/-- The same statement with the adjunct written through the hom-set bijection of
`f⁻¹ ⊣ f_*`. -/
lemma fSharpInverseImage_forget_homEquiv (f : RingedToposHom X Y) :
    X.forgetRing.map f.fSharpInverseImage =
      (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O)).symm
        (Y.forgetRing.map f.fSharp) :=
  (fSharpInverseImage_forget f).trans
    (f.toToposHom.adj.homEquiv_counit (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O)
      (Y.forgetRing.map f.fSharp)).symm

end RingedToposHom

end AlgebraicGeometry
