module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEpiFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The commutative-ring image functors of a morphism of topoi

A morphism of topoi `f : Sh(C) → Sh(D)` carries sheaves of commutative rings along both of its
image functors, and the geometric adjunction `f⁻¹ ⊣ f_*` lifts to them. This is the
commutative-ring case of Stacks 00YV.

The two functors transport a sheaf of commutative rings along a finite-product-preserving functor
of sheaves of sets: `f_*` preserves finite products because it is a right adjoint, `f⁻¹` because it
is left exact.

Each image functor leaves the underlying sheaf of sets alone — it only carries the ring operations
over — so the underlying sheaf of sets of `f.pushforwardRing.obj O` *is* `f_*` of the underlying
sheaf of sets of `O` (`MorphismOfTopoi.pushforwardRing_forget`, by `rfl`). That is what makes the
comparisons with the geometric adjunction statable, and it makes the composition comparison
`MorphismOfTopoi.pushforwardRingCompIso` the identity on underlying sheaves of sets.

## Main definitions

* `MorphismOfTopoi.inverseImageRing` and `MorphismOfTopoi.pushforwardRing`: the inverse image and
  the direct image of sheaves of commutative rings along a morphism of topoi.
* `MorphismOfTopoi.ringAdjunction`: the adjunction `f⁻¹ ⊣ f_*` between them, the commutative-ring
  case of Stacks 00YV.
* `MorphismOfTopoi.pushforwardRingCompIso`: the direct image of a composite is the composite of the
  direct images.

## Main results

* `MorphismOfTopoi.pushforwardRing_forget` and `MorphismOfTopoi.inverseImageRing_forget`: the
  underlying sheaf of sets of a ring-level image is the geometric image of the underlying sheaf of
  sets, on the nose.
* `MorphismOfTopoi.ringAdjunction_homEquiv_forget` and
  `MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget`: the ring-level adjunction bijection is the
  geometric one on underlying sheaves of sets, in both directions.
* `MorphismOfTopoi.pushforwardRingCompIso_hom_forget` and
  `MorphismOfTopoi.pushforwardRingCompIso_inv_forget`: the composition comparison is the identity
  on underlying sheaves of sets.

## Implementation notes

`Stacks.instHasSheafComposeForgetRingCat` and `Stacks.instHasSheafComposeForget₂CommRingCatRingCat`
discharge, for every site and at every universe of sections, the two `HasSheafCompose` hypotheses
that the ring-level files assume. Neither needs a size condition relating the universe of the
sections to the universes of the site: the first because `forget RingCat` is corepresentable by the
free ring on one generator, so the sheaf condition for the underlying presheaf of types is one
instance of the sheaf condition itself; the second because `forget₂ CommRingCat RingCat` creates
limits of every size. The three site universes and the two universes of sections are therefore
independent here, as they are in `MorphismOfTopoi`.

The universes of `inverseImageCommRingFunctor` and its siblings are given explicitly at every call.
Those declarations take four `HasSheafCompose` instance arguments whose universes of sections are
not determined until the morphism of topoi is elaborated; left to search, the instances are
discharged with those universes still unknown, the morphism is never elaborated, and every universe
defaults to `0`.

The two composition comparisons are built by hand rather than as `Iso.refl`. Transporting the ring
operations along `f_* ⋙ g_*` in one step and along `f_*` then `g_*` in two gives the same
operations (`Stacks.Sheaves.ToposPushforward.ringAddObj_comp` and its siblings) but not the same
*term*: the two use different `PreservesFiniteProducts` instances, so the ring structures are equal
and not definitionally equal. `compApp` is therefore the identity on sections, with those four
lemmas as its `RingHom` axioms.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' w'' v v' v'' u u' u''

namespace MorphismOfTopoi

section Images

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The inverse image of sheaves of commutative rings along a morphism of topoi: the geometric
inverse image `f⁻¹` of the underlying sheaf of sets, with all the ring operations carried along. -/
noncomputable def inverseImageRing : Sheaf K CommRingCat.{w'} ⥤ Sheaf J CommRingCat.{w} :=
  inverseImageCommRingFunctor.{w, w', v, u, v', u'} f

/-- The direct image of sheaves of commutative rings along a morphism of topoi: the geometric
direct image `f_*` of the underlying sheaf of sets, with all the ring operations carried along. -/
noncomputable def pushforwardRing : Sheaf J CommRingCat.{w} ⥤ Sheaf K CommRingCat.{w'} :=
  pushforwardCommRingFunctor.{w, w', v, u, v', u'} f

/-- The underlying sheaf of sets of the ring-level inverse image is the geometric inverse image of
the underlying sheaf of sets, on the nose. -/
lemma inverseImageRing_forget (O : Sheaf K CommRingCat.{w'}) :
    (sheafCompose J (forget CommRingCat.{w})).obj (f.inverseImageRing.obj O) =
      f.inverseImage.obj ((sheafCompose K (forget CommRingCat.{w'})).obj O) :=
  rfl

/-- The underlying sheaf of sets of the ring-level direct image is the geometric direct image of
the underlying sheaf of sets, on the nose. -/
lemma pushforwardRing_forget (O : Sheaf J CommRingCat.{w}) :
    (sheafCompose K (forget CommRingCat.{w'})).obj (f.pushforwardRing.obj O) =
      f.pushforward.obj ((sheafCompose J (forget CommRingCat.{w})).obj O) :=
  rfl

/-- The ring-level inverse image acts on a morphism as the geometric inverse image acts on its
underlying morphism of sheaves of sets. -/
lemma inverseImageRing_map_forget {O O' : Sheaf K CommRingCat.{w'}} (a : O ⟶ O') :
    (sheafCompose J (forget CommRingCat.{w})).map (f.inverseImageRing.map a) =
      f.inverseImage.map ((sheafCompose K (forget CommRingCat.{w'})).map a) := by
  exact underlyingRingSheaf_map_pullbackCommRingSheafMap.{w, w', v, u, v', u'} J f.inverseImage a

/-- The ring-level direct image acts on a morphism as the geometric direct image acts on its
underlying morphism of sheaves of sets. -/
lemma pushforwardRing_map_forget {O O' : Sheaf J CommRingCat.{w}} (a : O ⟶ O') :
    (sheafCompose K (forget CommRingCat.{w'})).map (f.pushforwardRing.map a) =
      f.pushforward.map ((sheafCompose J (forget CommRingCat.{w})).map a) := by
  exact underlyingRingSheaf_map_pullbackCommRingSheafMap.{w', w, v', u', v, u} K f.pushforward a

/-- The inverse image of sheaves of commutative rings along a morphism of topoi is left adjoint to
the direct image. -/
noncomputable def ringAdjunction : f.inverseImageRing ⊣ f.pushforwardRing :=
  commRingImageAdjunction.{w, w', v, u, v', u'} f

/-- The ring-level adjunction bijection is the geometric one on underlying sheaves of sets. -/
lemma ringAdjunction_homEquiv_forget (O : Sheaf K CommRingCat.{w'})
    (O' : Sheaf J CommRingCat.{w}) (a : f.inverseImageRing.obj O ⟶ O') :
    (sheafCompose K (forget CommRingCat.{w'})).map (f.ringAdjunction.homEquiv O O' a) =
      f.adj.homEquiv _ _ ((sheafCompose J (forget CommRingCat.{w})).map a) := by
  have h := Adjunction.restrictFullyFaithful_homEquiv_apply
    (ringImageAdjunction.{w, w', v, u, v', u'} f)
    (fullyFaithfulForgetCommRingSheaf.{w', v', u'} K)
    (fullyFaithfulForgetCommRingSheaf.{w, v, u} J)
    (forgetCommRingSheafCompPullbackIso.{w, w', v, u, v', u'} J f.inverseImage)
    (forgetCommRingSheafCompPullbackIso.{w', w, v', u', v, u} K f.pushforward) a
  have h' := congrArg (Stacks.forgetCommRingSheaf.{v', u', w'} K).map h
  rw [(fullyFaithfulForgetCommRingSheaf.{w', v', u'} K).map_preimage] at h'
  have e1 : (pushforwardRingFunctor f).map
      ((forgetCommRingSheafCompPullbackIso.{w, w', v, u, v', u'} J f.inverseImage).hom.app O)
      = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  have e2 : (forgetCommRingSheafCompPullbackIso.{w', w, v', u', v, u} K f.pushforward).hom.app O'
      = 𝟙 _ := rfl
  have p : (pushforwardRingFunctor f).map
        ((forgetCommRingSheafCompPullbackIso.{w, w', v, u, v', u'} J f.inverseImage).hom.app O) ≫
      (pushforwardRingFunctor f).map ((Stacks.forgetCommRingSheaf.{v, u, w} J).map a) ≫
        (forgetCommRingSheafCompPullbackIso.{w', w, v', u', v, u} K f.pushforward).hom.app O' =
      (pushforwardRingFunctor f).map ((Stacks.forgetCommRingSheaf.{v, u, w} J).map a) := by
    rw [e1, e2]
    exact (Category.id_comp _).trans (Category.comp_id _)
  have h3 : (Stacks.forgetCommRingSheaf.{v', u', w'} K).map
        (f.ringAdjunction.homEquiv O O' a) =
      ringUnit f ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) O) ≫
        pullbackRingSheafMap.{w', w, v', u', v, u} K f.pushforward
          ((Stacks.forgetCommRingSheaf.{v, u, w} J).map a) :=
    h'.trans (congrArg (fun z ↦ ringUnit f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) O) ≫ z) p)
  have h4 := congrArg (sheafCompose K (forget RingCat.{w'})).map h3
  refine h4.trans (((sheafCompose K (forget RingCat.{w'})).map_comp _ _).trans ?_)
  refine Eq.trans ?_
    (f.adj.homEquiv_unit _ _ ((sheafCompose J (forget CommRingCat.{w})).map a)).symm
  exact congrArg₂ CategoryStruct.comp
    (Stacks.Sheaves.RingedToposModules.ringSheafMap_ringUnit f
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) O))
    (ringSheafMap_pullbackRingSheafMap.{w', w, v', u', v, u} K f.pushforward
      ((Stacks.forgetCommRingSheaf.{v, u, w} J).map a))

/-- The inverse of the ring-level adjunction bijection is the inverse of the geometric one on
underlying sheaves of sets. -/
lemma ringAdjunction_homEquiv_symm_forget (O : Sheaf K CommRingCat.{w'})
    (O' : Sheaf J CommRingCat.{w}) (a : O ⟶ f.pushforwardRing.obj O') :
    (sheafCompose J (forget CommRingCat.{w})).map ((f.ringAdjunction.homEquiv O O').symm a) =
      (f.adj.homEquiv _ _).symm ((sheafCompose K (forget CommRingCat.{w'})).map a) :=
  (Equiv.eq_symm_apply _).mpr
    ((ringAdjunction_homEquiv_forget f O O' _).symm.trans
      (congrArg (sheafCompose K (forget CommRingCat.{w'})).map
        ((f.ringAdjunction.homEquiv O O').apply_symm_apply a)))

end Images

section Comp

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))

/-- Over a fixed object of the target site, the two descriptions of the direct image of a composite
have the same sections, and the identity map between them is a ring homomorphism: transporting the
ring operations along `f_* ⋙ g_*` in one step gives the same operations as transporting them along
`f_*` and then `g_*`. -/
noncomputable def compApp (O : Sheaf J CommRingCat.{w}) (X : Eᵒᵖ) :
    ((g.comp f).pushforwardRing.obj O).obj.obj X ⟶
      ((f.pushforwardRing ⋙ g.pushforwardRing).obj O).obj.obj X :=
  CommRingCat.ofHom (R := ToType (((g.comp f).pushforwardRing.obj O).obj.obj X))
    (S := ToType (((f.pushforwardRing ⋙ g.pushforwardRing).obj O).obj.obj X))
    { toFun := _root_.id
      map_add' := fun x y ↦ (ringAddObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X) x y).symm
      map_mul' := fun x y ↦ (ringMulObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X) x y).symm
      map_zero' := (ringZeroObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X)).symm
      map_one' := (ringOneObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X)).symm }

/-- The inverse of `MorphismOfTopoi.compApp`: the same identity map of sections, read as a ring
homomorphism the other way. -/
noncomputable def compAppInv (O : Sheaf J CommRingCat.{w}) (X : Eᵒᵖ) :
    ((f.pushforwardRing ⋙ g.pushforwardRing).obj O).obj.obj X ⟶
      ((g.comp f).pushforwardRing.obj O).obj.obj X :=
  CommRingCat.ofHom (R := ToType (((f.pushforwardRing ⋙ g.pushforwardRing).obj O).obj.obj X))
    (S := ToType (((g.comp f).pushforwardRing.obj O).obj.obj X))
    { toFun := _root_.id
      map_add' := fun x y ↦ ringAddObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X) x y
      map_mul' := fun x y ↦ ringMulObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X) x y
      map_zero' := ringZeroObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X)
      map_one' := ringOneObj_comp.{w'', w', w, v', u', v, u} K f.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O)
        (g.pushforward ⋙ Sheaf.sectionsFunctor L X) }

/-- The direct image of a composite of morphisms of topoi agrees with the composite of the direct
images on a single sheaf of commutative rings, by the identity on sections. -/
noncomputable def compIsoApp (O : Sheaf J CommRingCat.{w}) :
    (g.comp f).pushforwardRing.obj O ≅ (f.pushforwardRing ⋙ g.pushforwardRing).obj O where
  hom := { hom := { app := fun X ↦ compApp f g O X
                    naturality := fun _ _ _ ↦ CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl) } }
  inv := { hom := { app := fun X ↦ compAppInv f g O X
                    naturality := fun _ _ _ ↦ CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl) } }
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext X x
    rfl
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext X x
    rfl

/-- `MorphismOfTopoi.compIsoApp` is the identity on underlying sheaves of sets. -/
lemma compIsoApp_hom_forget (O : Sheaf J CommRingCat.{w}) :
    (sheafCompose L (forget CommRingCat.{w''})).map (compIsoApp f g O).hom =
      𝟙 ((sheafCompose L (forget CommRingCat.{w''})).obj
        ((g.comp f).pushforwardRing.obj O)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The inverse of `MorphismOfTopoi.compIsoApp` is the identity on underlying sheaves of sets. -/
lemma compIsoApp_inv_forget (O : Sheaf J CommRingCat.{w}) :
    (sheafCompose L (forget CommRingCat.{w''})).map (compIsoApp f g O).inv =
      𝟙 ((sheafCompose L (forget CommRingCat.{w''})).obj
        ((g.comp f).pushforwardRing.obj O)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The direct image of a composite of morphisms of topoi is the composite of the direct images, on
sheaves of commutative rings. -/
noncomputable def pushforwardRingCompIso :
    (g.comp f).pushforwardRing ≅ f.pushforwardRing ⋙ g.pushforwardRing :=
  NatIso.ofComponents (fun P ↦ compIsoApp f g P) (fun {P Q} a ↦
    (sheafCompose L (forget CommRingCat.{w''})).map_injective (by
      refine (((sheafCompose L (forget CommRingCat.{w''})).map_comp _ _).trans ?_).trans
        ((sheafCompose L (forget CommRingCat.{w''})).map_comp _ _).symm
      rw [compIsoApp_hom_forget f g P, compIsoApp_hom_forget f g Q,
        (g.comp f).pushforwardRing_map_forget a]
      refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
      exact ((g.pushforwardRing_map_forget (f.pushforwardRing.map a)).trans
        (congrArg g.pushforward.map (f.pushforwardRing_map_forget a))).symm))

/-- The composition comparison is the identity on underlying sheaves of sets. -/
lemma pushforwardRingCompIso_hom_forget (O : Sheaf J CommRingCat.{w}) :
    (sheafCompose L (forget CommRingCat.{w''})).map
        ((f.pushforwardRingCompIso g).hom.app O) =
      𝟙 ((sheafCompose L (forget CommRingCat.{w''})).obj
        ((g.comp f).pushforwardRing.obj O)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The inverse composition comparison is the identity on underlying sheaves of sets. -/
lemma pushforwardRingCompIso_inv_forget (O : Sheaf J CommRingCat.{w}) :
    (sheafCompose L (forget CommRingCat.{w''})).map
        ((f.pushforwardRingCompIso g).inv.app O) =
      𝟙 ((sheafCompose L (forget CommRingCat.{w''})).obj
        ((g.comp f).pushforwardRing.obj O)) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Comp

end MorphismOfTopoi

end
