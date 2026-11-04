module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.CommRingModuleData
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedTopos

/-!
# Forgetting the ring operations of the adjunction of Stacks 00YV

The inverse image of a sheaf of commutative rings along a finite-product-preserving functor of
sheaves of sets, `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`, carries the transported ring
structure on the *same* underlying sheaf of sets: its sections over an object are by construction
the sections of the image of the underlying sheaf of sets of the given sheaf of rings. Forgetting
the ring operations therefore commutes with the inverse image on the nose, and this file carries
that fact up to the adjunction `f⁻¹ ⊣ f_*` on sheaves of commutative rings of Stacks 00YV: both
the unit and the hom-set bijection of the commutative-ring adjunction become those of the
set-level adjunction after forgetting the ring operations.

The comparison isomorphisms themselves are
`Stacks.Sheaves.ToposPullback.forgetPullbackCommRingSheafIso`,
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingForgetIso` (both in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/CommRingPullback.lean`) and
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingForgetIso` (in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforwardModules/CommRingModuleData.lean`),
all of which are the identity in each component.

## Main results

* `Stacks.Sheaves.ToposPullback.forget_pullbackCommRingSheaf`: the underlying sheaf of sets of an
  inverse image of a sheaf of commutative rings *is* the image of the underlying sheaf of sets.
* `Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_unit_app` and
  `Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv`: forgetting the
  ring operations carries the unit and the hom-set bijection of Stacks 00YV on sheaves of
  commutative rings to those of `f⁻¹ ⊣ f_*` on sheaves of sets.
* `Stacks.Sheaves.ToposPushforward.forgetRing_map_commRingImageAdjunction_unit_app`: the same
  statement about the unit, with the forgetful functor spelled as that of a ringed topos.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section Forget

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- Forgetting the ring operations of the inverse image of a sheaf of commutative rings gives the
image of the underlying sheaf of sets, on the nose. -/
theorem forget_pullbackCommRingSheaf (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).obj (pullbackCommRingSheaf J Φ O) =
      Φ.obj ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  rfl

end Forget

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section Forget

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

omit [J.HasSheafCompose (forget CommRingCat.{ww})] in
/-- Forgetting the ring operations carries the unit of the adjunction of Stacks 00YV on sheaves of
commutative rings to the unit of `f⁻¹ ⊣ f_*` on sheaves of sets.

The proof is in term mode throughout. The two comparison isomorphisms appearing in Mathlib's
formula for the unit of `CategoryTheory.Adjunction.restrictFullyFaithful` are identities, but their
source and target are two different *spellings* of one object, so `rw` and `simp` — which
type-check their motives at reducible transparency — cannot cancel them; `Eq.trans` and `congrArg`
elaborate at default transparency and can. -/
theorem forget_map_commRingImageAdjunction_unit_app (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose K (forget CommRingCat.{ww'})).map ((commRingImageAdjunction f).unit.app O) =
      f.adj.unit.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  have h1 : (pushforwardRingFunctor f).map
        ((forgetCommRingSheafCompPullbackIso J f.inverseImage).hom.app O) ≫
      (forgetCommRingSheafCompPullbackIso K f.pushforward).hom.app
        ((inverseImageCommRingFunctor f).obj O) =
      𝟙 ((pushforwardRingFunctor f).obj
        ((Stacks.forgetCommRingSheaf K ⋙ pullbackRingSheafFunctor J f.inverseImage).obj O)) :=
    (Category.comp_id _).trans (CategoryTheory.Functor.map_id (pushforwardRingFunctor f)
      ((Stacks.forgetCommRingSheaf K ⋙ pullbackRingSheafFunctor J f.inverseImage).obj O))
  have hUnit : (Stacks.forgetCommRingSheaf K).map ((commRingImageAdjunction f).unit.app O) =
      ringUnit f (SheafOfModules.Tensor.ringSheaf O) :=
    (Adjunction.map_restrictFullyFaithful_unit_app (ringImageAdjunction f)
        (fullyFaithfulForgetCommRingSheaf K) (fullyFaithfulForgetCommRingSheaf J)
        (forgetCommRingSheafCompPullbackIso J f.inverseImage)
        (forgetCommRingSheafCompPullbackIso K f.pushforward) O).trans
      ((congrArg (fun m ↦ ringUnit f (SheafOfModules.Tensor.ringSheaf O) ≫ m) h1).trans
        (Category.comp_id _))
  (congrArg (sheafCompose K (forget RingCat.{ww'})).map hUnit).trans
    (Stacks.Sheaves.RingedToposModules.ringSheafMap_ringUnit f (SheafOfModules.Tensor.ringSheaf O))

/-- Forgetting the ring operations carries the hom-set bijection of the adjunction of Stacks 00YV
on sheaves of commutative rings to the hom-set bijection of `f⁻¹ ⊣ f_*` on sheaves of sets. -/
theorem forget_map_commRingImageAdjunction_homEquiv (O : Sheaf K CommRingCat.{ww'})
    (R : Sheaf J CommRingCat.{ww}) (x : (inverseImageCommRingFunctor f).obj O ⟶ R) :
    (sheafCompose K (forget CommRingCat.{ww'})).map
        ((commRingImageAdjunction f).homEquiv O R x) =
      f.adj.homEquiv ((sheafCompose K (forget CommRingCat.{ww'})).obj O)
        ((sheafCompose J (forget CommRingCat.{ww})).obj R)
        ((sheafCompose J (forget CommRingCat.{ww})).map x) :=
  (congrArg (sheafCompose K (forget CommRingCat.{ww'})).map
      (Adjunction.homEquiv_apply (commRingImageAdjunction f) O R x)).trans
    (((sheafCompose K (forget CommRingCat.{ww'})).map_comp _ _).trans
      ((congrArg₂ (· ≫ ·) (forget_map_commRingImageAdjunction_unit_app f O)
          (underlyingRingSheaf_map_pullbackCommRingSheafMap K (Φ := f.pushforward) x)).trans
        (Adjunction.homEquiv_apply f.adj _ _ _).symm))

end Forget

section RingedToposSpelling

variable {C : Type uu} [Category.{vv} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (Y : AlgebraicGeometry.RingedTopos.{vv', uu', ww'})
  [Y.J.HasSheafCompose (forget RingCat.{ww'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [Y.J.HasSheafCompose (forget CommRingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf Y.J (Type ww')))

/-- `forget_map_commRingImageAdjunction_unit_app` with the forgetful functor spelled as
`AlgebraicGeometry.RingedTopos.forgetRing` of a ringed topos.

This is the same statement, but a statement about a *morphism of ringed topoi* presents its
forgetful functor through `RingedTopos.forgetRing` and its ambient sheaf categories through the
ringed topos's own carrier and topology. Those are definitionally the spellings used by
`forget_map_commRingImageAdjunction_unit_app`, but `rw` and `simp` unify at reducible transparency
and so cannot cross the gap; rewriting the functor alone, meanwhile, leaves the surrounding sheaf
categories pointing at the old carrier and the goal is then not type-correct at implicit
transparency. Stating the variant at the ringed-topos spelling makes the consumer and the lemma
share one spelling by construction, which is what makes it usable. -/
theorem forgetRing_map_commRingImageAdjunction_unit_app :
    Y.forgetRing.map ((commRingImageAdjunction f).unit.app Y.O) =
      f.adj.unit.app (Y.forgetRing.obj Y.O) :=
  forget_map_commRingImageAdjunction_unit_app f Y.O

end RingedToposSpelling

end Stacks.Sheaves.ToposPushforward

end
