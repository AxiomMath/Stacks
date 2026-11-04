module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Transport of the inverse image of sheaves of modules along a natural isomorphism

The inverse image of sheaves of modules of Stacks 03D2,
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor J Φ O`, depends on the
finite-product-preserving functor `Φ` between categories of sheaves of sets.  This file shows
that it depends on `Φ` only through its isomorphism class: a natural transformation `Φ ⟶ Φ'`
induces a morphism of inverse images, over the induced morphism of the inverse images of the
sheaf of rings, and a natural isomorphism induces an isomorphism.

The consequence this is for is Stacks 03LU.  The direct image of sheaves of modules along a
morphism of ringed topoi,
`AlgebraicGeometry.RingedToposHom.pushforwardModules`, is `pullbackModuleFunctor` applied to the
direct image of sheaves of sets, followed by restriction of scalars along the structure map.  So
two morphisms of ringed topoi whose direct images of sheaves of sets are *isomorphic*, by an
isomorphism carrying one structure map to the other, have isomorphic direct images of sheaves of
modules.  For the small étale ringed topoi of algebraic spaces that is exactly the situation of
Stacks 03G8: the composite of the morphisms of ringed topoi attached to `f` and `g` and the
morphism attached to `f ≫ g` are not equal, only compared by the cartesian comparison of the
direct images.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackModuleMapOfNatTrans`: the morphism of inverse images of a
  sheaf of modules induced by a natural transformation of the two functors of sheaves of sets.
* `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso`: the isomorphism of the
  inverse-image functors induced by a natural isomorphism.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfPushforwardIso`: the comparison of the
  direct images of sheaves of modules of two morphisms of ringed topoi with isomorphic direct
  images of sheaves of sets and matching structure maps.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleAddHom_comp_natTrans_app` and
  `moduleSMulHom_comp_natTrans_app`: the induced morphism of underlying sheaves of sets is
  additive and compatible with the scalar actions, the scalars being carried along the induced
  morphism of the inverse images of the sheaf of rings.

## Implementation notes

The morphism of the inverse images of the sheaf of rings is taken as a *parameter* `β`, together
with the hypothesis that its underlying morphism of sheaves of sets is the given natural
transformation.  `Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans` is such a `β`, but
it lives downstream of this file, and a second construction of it here would be duplication; the
hypothesis is what the argument uses and nothing more.

As in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposModulesCompIso.lean`, the two
operation maps are compared through the transported operations
`CategoryTheory.Sheaf.moduleAddObj` and `CategoryTheory.Sheaf.moduleSMulObj`, whose behaviour
under a natural transformation of the transporting functor is `moduleAddObj_naturality` and
`moduleSMulObj_naturality`.  The natural transformation of sections functors that those lemmas
want is `CategoryTheory.Functor.whiskerRight` of the given one.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

/-- Every local section of a binary product of sheaves of sets is a pair of local sections. -/
private lemma exists_prodObjMk_sections {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
    (W : Cᵒᵖ) {A B : Sheaf J (Type ww)} (p : (Sheaf.sectionsFunctor J W).obj (A ⨯ B)) :
    ∃ (x : (Sheaf.sectionsFunctor J W).obj A) (y : (Sheaf.sectionsFunctor J W).obj B),
      p = Functor.prodObjMk (P := Sheaf.sectionsFunctor J W) x y :=
  ⟨_, _, (Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J W) p).symm⟩

/-- The image of a product of two morphisms of sheaves of sets on a pair of local sections. -/
private lemma sections_map_prodMap_prodObjMk {C : Type uu} [Category.{vv} C]
    (J : GrothendieckTopology C) (W : Cᵒᵖ) {A A' B B' : Sheaf J (Type ww)}
    (f : A ⟶ A') (g : B ⟶ B') (x : (Sheaf.sectionsFunctor J W).obj A)
    (y : (Sheaf.sectionsFunctor J W).obj B) :
    (Sheaf.sectionsFunctor J W).map (Limits.prod.map f g) (Functor.prodObjMk x y) =
      Functor.prodObjMk ((Sheaf.sectionsFunctor J W).map f x)
        ((Sheaf.sectionsFunctor J W).map g y) := by
  rw [Functor.map_prodMap_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  (O : Sheaf K RingCat.{ww'}) (e : Φ ⟶ Φ')

section Sections

variable (G : SheafOfModules.{ww'} O) (W : Cᵒᵖ)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- A natural transformation of the transporting functors carries the transported addition of an
inverse image of a sheaf of modules to the transported addition of the other inverse image. -/
lemma moduleAddObj_natTrans_app
    (x y : (Sheaf.sectionsFunctor J W).obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    (Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G))
        (Sheaf.moduleAddObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G)
          (Sheaf.sectionsFunctor J W) x y) =
      Sheaf.moduleAddObj (pullbackRingSheaf J Φ' O) (pullbackModuleObj J Φ' O G)
        (Sheaf.sectionsFunctor J W)
        ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)) x)
        ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)) y) :=
  ((congrArg ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)))
        (moduleAddObj_pullbackModuleObj J Φ O G (Sheaf.sectionsFunctor J W) x y)).trans
      (Sheaf.moduleAddObj_naturality O G
        (Functor.whiskerRight e (Sheaf.sectionsFunctor J W)) x y)).trans
    (moduleAddObj_pullbackModuleObj J Φ' O G (Sheaf.sectionsFunctor J W) _ _).symm

/-- A natural transformation of the transporting functors carries the transported scalar action
of an inverse image of a sheaf of modules to the transported scalar action of the other inverse
image, with the scalar carried along the same transformation. -/
lemma moduleSMulObj_natTrans_app
    (r : (Sheaf.sectionsFunctor J W).obj (Φ.obj (Sheaf.ringSheaf O)))
    (x : (Sheaf.sectionsFunctor J W).obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    (Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G))
        (Sheaf.moduleSMulObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G)
          (Sheaf.sectionsFunctor J W) r x) =
      Sheaf.moduleSMulObj (pullbackRingSheaf J Φ' O) (pullbackModuleObj J Φ' O G)
        (Sheaf.sectionsFunctor J W)
        ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.ringSheaf O)) r)
        ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)) x) :=
  ((congrArg ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)))
        (moduleSMulObj_pullbackModuleObj J Φ O G (Sheaf.sectionsFunctor J W) r x)).trans
      (Sheaf.moduleSMulObj_naturality O G
        (Functor.whiskerRight e (Sheaf.sectionsFunctor J W)) r x)).trans
    (moduleSMulObj_pullbackModuleObj J Φ' O G (Sheaf.sectionsFunctor J W) _ _).symm

end Sections

section Hom

variable (β : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ' O)
  (hβ : (sheafCompose J (forget RingCat.{ww})).map β = e.app (Sheaf.ringSheaf O))
  (G : SheafOfModules.{ww'} O)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The induced morphism of underlying sheaves of sets commutes with the addition maps. -/
lemma moduleAddHom_comp_natTrans_app :
    Sheaf.moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) ≫
        e.app (Sheaf.moduleSheaf O G) =
      Limits.prod.map (e.app (Sheaf.moduleSheaf O G)) (e.app (Sheaf.moduleSheaf O G)) ≫
        Sheaf.moduleAddHom (pullbackRingSheaf J Φ O)
          ((SheafOfModules.restrictScalars β).obj (pullbackModuleObj J Φ' O G)) := by
  refine Sheaf.hom_ext_sections fun W p ↦ ?_
  obtain ⟨x, y, rfl⟩ := exists_prodObjMk_sections J W p
  have key := sections_map_prodMap_prodObjMk J W
    (e.app (Sheaf.moduleSheaf O G)) (e.app (Sheaf.moduleSheaf O G)) x y
  refine ((Sheaf.sectionsFunctor J W).map_comp_apply _ _ _).trans
    ((moduleAddObj_natTrans_app J O e G W x y).trans (Eq.trans ?_
      ((Sheaf.sectionsFunctor J W).map_comp_apply _ _ _).symm))
  exact congrArg (fun z ↦ (Sheaf.sectionsFunctor J W).map
      (Sheaf.moduleAddHom (pullbackRingSheaf J Φ' O) (pullbackModuleObj J Φ' O G)) z) key.symm

/-- The induced morphism of underlying sheaves of sets commutes with the scalar-action maps, the
scalars on the target being carried along `β`. -/
lemma moduleSMulHom_comp_natTrans_app
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = e.app (Sheaf.ringSheaf O)) :
    Sheaf.moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) ≫
        e.app (Sheaf.moduleSheaf O G) =
      Limits.prod.map (𝟙 (Sheaf.ringSheaf (pullbackRingSheaf J Φ O)))
          (e.app (Sheaf.moduleSheaf O G)) ≫
        Sheaf.moduleSMulHom (pullbackRingSheaf J Φ O)
          ((SheafOfModules.restrictScalars β).obj (pullbackModuleObj J Φ' O G)) := by
  refine Sheaf.hom_ext_sections fun W p ↦ ?_
  obtain ⟨r, x, rfl⟩ := exists_prodObjMk_sections J W p
  have key := sections_map_prodMap_prodObjMk J W
    (𝟙 (Sheaf.ringSheaf (pullbackRingSheaf J Φ O))) (e.app (Sheaf.moduleSheaf O G)) r x
  rw [Functor.map_id_apply] at key
  refine ((Sheaf.sectionsFunctor J W).map_comp_apply _ _ _).trans
    ((moduleSMulObj_natTrans_app J O e G W r x).trans (Eq.trans ?_
      ((Sheaf.sectionsFunctor J W).map_comp_apply _ _ _).symm))
  refine Eq.trans ?_ (congrArg (fun z ↦ (Sheaf.sectionsFunctor J W).map
      (Sheaf.moduleSMulHom (pullbackRingSheaf J Φ O)
        ((SheafOfModules.restrictScalars β).obj (pullbackModuleObj J Φ' O G))) z) key.symm)
  refine Eq.trans ?_ (moduleSMulObj_restrictScalars β (pullbackModuleObj J Φ' O G)
    (Sheaf.sectionsFunctor J W) r
    ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)) x)).symm
  exact congrArg (fun z ↦ Sheaf.moduleSMulObj (pullbackRingSheaf J Φ' O)
      (pullbackModuleObj J Φ' O G) (Sheaf.sectionsFunctor J W) z
      ((Sheaf.sectionsFunctor J W).map (e.app (Sheaf.moduleSheaf O G)) x))
    (congrArg (fun m ↦ (Sheaf.sectionsFunctor J W).map m r) hβ).symm

include hβ

/-- The morphism of inverse images of a sheaf of modules induced by a natural transformation of
the two transporting functors of sheaves of sets. -/
noncomputable def pullbackModuleMapOfNatTrans :
    pullbackModuleObj J Φ O G ⟶
      (SheafOfModules.restrictScalars β).obj (pullbackModuleObj J Φ' O G) :=
  homEquivSubtype.symm ⟨e.app (Sheaf.moduleSheaf O G),
    moduleAddHom_comp_natTrans_app J O e β G,
    moduleSMulHom_comp_natTrans_app J O e β G hβ⟩

/-- The underlying morphism of sheaves of sets of `pullbackModuleMapOfNatTrans` is the component
of the natural transformation at the underlying sheaf of sets of the module. -/
@[simp]
lemma moduleSheafFunctor_map_pullbackModuleMapOfNatTrans :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ O)).map
        (pullbackModuleMapOfNatTrans J O e β hβ G) =
      e.app (Sheaf.moduleSheaf O G) := rfl

end Hom

section Iso

variable {Φ Φ'' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ'']

/-- The isomorphism of inverse images of a sheaf of modules induced by a natural isomorphism of
the two transporting functors. -/
noncomputable def pullbackModuleObjIsoOfNatIso (ε : Φ ≅ Φ'')
    (β : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ'' O)
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = ε.hom.app (Sheaf.ringSheaf O))
    (G : SheafOfModules.{ww'} O) :
    pullbackModuleObj J Φ O G ≅
      (SheafOfModules.restrictScalars β).obj (pullbackModuleObj J Φ'' O G) := by
  haveI : IsIso ((Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ O)).map
      (pullbackModuleMapOfNatTrans J O ε.hom β hβ G)) := by
    rw [moduleSheafFunctor_map_pullbackModuleMapOfNatTrans]
    exact inferInstanceAs (IsIso (ε.hom.app (Sheaf.moduleSheaf O G)))
  haveI := isIso_of_reflects_iso (pullbackModuleMapOfNatTrans J O ε.hom β hβ G)
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ O))
  exact asIso (pullbackModuleMapOfNatTrans J O ε.hom β hβ G)

/-- **The inverse image of sheaves of modules depends on the transporting functor only up to
isomorphism.**  A natural isomorphism of the two finite-product-preserving functors of sheaves of
sets induces an isomorphism of the inverse-image functors on sheaves of modules, the scalars
being read through the induced morphism of the inverse images of the sheaf of rings. -/
noncomputable def pullbackModuleFunctorIsoOfNatIso (ε : Φ ≅ Φ'')
    (β : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ'' O)
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = ε.hom.app (Sheaf.ringSheaf O)) :
    pullbackModuleFunctor J Φ O ≅
      pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars β :=
  NatIso.ofComponents (fun G ↦ pullbackModuleObjIsoOfNatIso J O ε β hβ G)
    (fun {_G _G'} φ ↦ hom_ext_moduleSheafFunctor (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      exact ε.hom.naturality ((Sheaf.moduleSheafFunctor O).map φ)))

end Iso

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v'' u'' w''

variable {X : RingedTopos.{v, u, w}} {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- **The direct image of sheaves of modules depends on a morphism of ringed topoi only up to a
comparison of its direct image of sheaves of sets.**  Given two morphisms of ringed topoi with
the same source and target, an isomorphism `θ` of their direct images of sheaves of sets, a
morphism `β` of the direct images of the structure sheaf of rings whose underlying morphism of
sheaves of sets is `θ`, and the identity saying that `β` carries one structure map to the other,
the two direct images of sheaves of modules are isomorphic. -/
noncomputable def pushforwardModulesIsoOfPushforwardIso (k k' : RingedToposHom X Z)
    (θ : k.toToposHom.pushforward ≅ k'.toToposHom.pushforward)
    (β : pullbackRingSheaf Z.J k.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⟶
      pullbackRingSheaf Z.J k'.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (hβ : (sheafCompose Z.J (forget RingCat.{w''})).map β =
      θ.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
    (hstruct : k.structureRingMap ≫ β = k'.structureRingMap) :
    k.pushforwardModules ≅ k'.pushforwardModules :=
  have h1 : (pullbackModuleFunctor Z.J k'.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
            SheafOfModules.restrictScalars β) ⋙
        SheafOfModules.restrictScalars k.structureRingMap =
      pullbackModuleFunctor Z.J k'.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        SheafOfModules.restrictScalars (k.structureRingMap ≫ β) := rfl
  have h2 : pullbackModuleFunctor Z.J k'.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        SheafOfModules.restrictScalars (k.structureRingMap ≫ β) =
      k'.pushforwardModules :=
    congrArg (fun α ↦ pullbackModuleFunctor Z.J k'.toToposHom.pushforward
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        SheafOfModules.restrictScalars α) hstruct
  Functor.isoWhiskerRight
      (pullbackModuleFunctorIsoOfNatIso Z.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) θ β hβ)
      (SheafOfModules.restrictScalars k.structureRingMap) ≪≫ eqToIso (h1.trans h2)

end AlgebraicGeometry.RingedToposHom

end
