module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# Pullback and pushforward of modules along a composite of morphisms of algebraic spaces

Stacks 03LU asserts that the pair `(f^*, f_*)` attached to a morphism `f : X ⟶ Y` of algebraic
spaces is pseudofunctorial: for `f : X ⟶ Y` and `g : Y ⟶ Z` there are canonical comparisons

`f_* ∘ g_* ≅ (f ≫ g)_*` and `g^* ∘ f^* ≅ (f ≫ g)^*`,

adjoint to one another.  This file supplies both, at the module universe of the structure
rings.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso` transports the direct image
  of sheaves of modules along a 2-isomorphism of morphisms of ringed topoi.
* `AlgebraicGeometry.Space.pushforwardModulesCompTransport` identifies the direct image of
  modules of a composite of the morphisms of ringed topoi of Stacks 03G8 with that of the
  morphism of ringed topoi of the composite.
* `AlgebraicGeometry.Space.modulePushforwardCompIso` is the comparison `f_* ∘ g_* ≅ (f ≫ g)_*`.
* `AlgebraicGeometry.Space.moduleCompAdjunction` is the composite of the two adjunctions, with
  its right adjoint read as `(f ≫ g)_*`.
* `AlgebraicGeometry.Space.modulePullbackCompIso` is the comparison `g^* ∘ f^* ≅ (f ≫ g)^*`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharpRing`: the composition law of
  Stacks 03G8 for the structure map, at the level of sheaves of rings.
* `AlgebraicGeometry.Space.modulePushforward_comp_eq`: the composite of the two direct images
  of modules of Stacks 03D6, part (1) is the composite of the direct images of the morphisms of
  ringed topoi of Stacks 03G8.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_pushforwardModulesCompTransport_hom_app`:
  the transport of Stacks 03G8 is the geometric comparison
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on
  underlying sheaves of sets.  This is the one factor of the comparison with content.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app`,
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_eqToHom_modulePushforward_comp_eq_app` and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_eqToHom_pushforwardModules_eq_app`: each of
  the other three factors of `AlgebraicGeometry.Space.modulePushforwardCompIso` is the
  identity on underlying sheaves of sets.
* `AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` and
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_counit`: the compatibility of the
  comparison of inverse images with the units and with the counits, which characterize it.

## Implementation notes

The morphism of ringed topoi of Stacks 03G8 does **not** take a composite to the composite on
the nose: the underlying morphisms of small étale topoi are compared by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, and the structure maps by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`, neither of which is an
equality.  So the ringed-topos comparison
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`, which is stated for the honest
composite `g ∘ f` of morphisms of ringed topoi, has to be transported along that
2-isomorphism before it says anything about `f ≫ g`.  That transport is
`AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso`: two morphisms of ringed topoi
with isomorphic direct images and matching structure maps have isomorphic direct images of
modules.  Its components are the given isomorphism of sheaves of sets, and the two things to
check are that it is additive — which is naturality of a transformation between
finite-product-preserving functors — and that it is linear, which is exactly the compatibility
of the transformation with the two structure maps.

The comparison of inverse images is then the mate of the comparison of direct images:
`g^* ∘ f^*` and `(f ≫ g)^*` are both left adjoint to `f_* ∘ g_*`, the first because adjunctions
compose and the second by `AlgebraicGeometry.Space.modulePullbackAdjunction` transported along
`modulePushforwardCompIso`, so they agree by uniqueness of left adjoints.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (ofSheafHom hom_ext_moduleSheafFunctor
  moduleSheafFunctor_map_ofSheafHom)

universe u

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  (F H : RingedToposHom X Y)

/-- The structure map of `H` is the structure map of `F` followed by the 2-isomorphism, on
underlying sheaves of sets. -/
theorem sheafCompose_map_fSharpRing_comp_hom
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing) :
    (sheafCompose Y.J (forget RingCat.{w₂})).map F.fSharpRing ≫
        e.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) =
      (sheafCompose Y.J (forget RingCat.{w₂})).map H.fSharpRing :=
  (congrArg (fun n ↦ (sheafCompose Y.J (forget RingCat.{w₂})).map F.fSharpRing ≫ n)
      (ringSheafMap_pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom).symm).trans
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg (fun m ↦ (sheafCompose Y.J (forget RingCat.{w₂})).map m) he))

/-- The structure map of `F` is the structure map of `H` followed by the inverse of the
2-isomorphism, on underlying sheaves of sets. -/
theorem sheafCompose_map_fSharpRing_comp_inv
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing) :
    (sheafCompose Y.J (forget RingCat.{w₂})).map H.fSharpRing ≫
        e.inv.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) =
      (sheafCompose Y.J (forget RingCat.{w₂})).map F.fSharpRing :=
  (congrArg (fun m ↦ m ≫ e.inv.app
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
      (sheafCompose_map_fSharpRing_comp_hom F H e he).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun n ↦ (sheafCompose Y.J (forget RingCat.{w₂})).map F.fSharpRing ≫ n)
        (e.hom_inv_id_app
          (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))).trans
        (Category.comp_id _)))

/-- The structure map of `H`, on sections, is the structure map of `F` followed by the
2-isomorphism. -/
theorem sectionsFunctor_map_hom_fSharpRing
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing)
    (V : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (Sheaf.sectionsFunctor Y.J V).map
        (e.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
        ((Sheaf.sectionsFunctor Y.J V).map
          ((sheafCompose Y.J (forget RingCat.{w₂})).map F.fSharpRing) r) =
      (Sheaf.sectionsFunctor Y.J V).map
        ((sheafCompose Y.J (forget RingCat.{w₂})).map H.fSharpRing) r :=
  ((Sheaf.sectionsFunctor Y.J V).map_comp_apply _ _ r).symm.trans
    (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J V).map m r)
      (sheafCompose_map_fSharpRing_comp_hom F H e he))

/-- The structure map of `F`, on sections, is the structure map of `H` followed by the inverse
of the 2-isomorphism. -/
theorem sectionsFunctor_map_inv_fSharpRing
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing)
    (V : Y.Cᵒᵖ)
    (r : (Sheaf.sectionsFunctor Y.J V).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (Sheaf.sectionsFunctor Y.J V).map
        (e.inv.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
        ((Sheaf.sectionsFunctor Y.J V).map
          ((sheafCompose Y.J (forget RingCat.{w₂})).map H.fSharpRing) r) =
      (Sheaf.sectionsFunctor Y.J V).map
        ((sheafCompose Y.J (forget RingCat.{w₂})).map F.fSharpRing) r :=
  ((Sheaf.sectionsFunctor Y.J V).map_comp_apply _ _ r).symm.trans
    (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J V).map m r)
      (sheafCompose_map_fSharpRing_comp_inv F H e he))

/-- The structure map of `F` is adjunct to the structure map of `H` through the inverse of the
2-isomorphism. -/
theorem fSharpRing_comp_pullbackRingSheafMapOfNatTrans_inv
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing) :
    H.fSharpRing ≫
        pullbackRingSheafMapOfNatTrans Y.J
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.symm.hom =
      F.fSharpRing := by
  refine (sheafCompose Y.J (forget RingCat.{w₂})).map_injective ?_
  refine (CategoryTheory.Functor.map_comp _ _ _).trans ?_
  refine Eq.trans (congrArg
    (fun n ↦ (sheafCompose Y.J (forget RingCat.{w₂})).map H.fSharpRing ≫ n)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans Y.J
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.symm.hom)) ?_
  exact sheafCompose_map_fSharpRing_comp_inv F H e he

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]

/-- The direct image of a single sheaf of modules, transported along a 2-isomorphism of
morphisms of ringed topoi: the isomorphism of the underlying sheaves of sets, carrying the
addition because it is a transformation of finite-product-preserving functors and the scalar
action because it matches the two structure maps. -/
noncomputable def pushforwardModulesMapOfNatIso
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing)
    (M : SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    F.pushforwardModules.obj M ⟶ H.pushforwardModules.obj M :=
  ofSheafHom
    (e.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M))
    (fun V x y ↦ by
      rw [F.pushforwardModules_add M V x y, H.pushforwardModules_add M V _ _]
      exact Sheaf.moduleAddObj_naturality
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
        (Functor.whiskerRight e.hom (Sheaf.sectionsFunctor Y.J V)) x y)
    (fun V r x ↦ by
      rw [F.pushforwardModules_smul M V r x, H.pushforwardModules_smul M V r _]
      refine Eq.trans (Sheaf.moduleSMulObj_naturality
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
        (Functor.whiskerRight e.hom (Sheaf.sectionsFunctor Y.J V)) _ x) ?_
      exact congrArg
        (fun t ↦ Sheaf.moduleSMulObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
          (H.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y.J V) t
          ((Sheaf.sectionsFunctor Y.J V).map
            (e.hom.app (Sheaf.moduleSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M)) x))
        (sectionsFunctor_map_hom_fSharpRing F H e he V r))

/-- The transported morphism of sheaves of modules is the given isomorphism on underlying
sheaves of sets. -/
@[simp]
theorem moduleSheafFunctor_map_pushforwardModulesMapOfNatIso
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing)
    (M : SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
        (pushforwardModulesMapOfNatIso F H e he M) =
      e.hom.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M) :=
  rfl

/-- The direct image of a single sheaf of modules, transported along a 2-isomorphism of
morphisms of ringed topoi. -/
noncomputable def pushforwardModulesIsoAppOfNatIso
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing)
    (M : SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    F.pushforwardModules.obj M ≅ H.pushforwardModules.obj M where
  hom := pushforwardModulesMapOfNatIso F H e he M
  inv := pushforwardModulesMapOfNatIso H F e.symm
    (fSharpRing_comp_pullbackRingSheafMapOfNatTrans_inv F H e he) M
  hom_inv_id := hom_ext_moduleSheafFunctor (by
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleSheafFunctor_map_pushforwardModulesMapOfNatIso, Iso.symm_hom]
    exact e.hom_inv_id_app _)
  inv_hom_id := hom_ext_moduleSheafFunctor (by
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleSheafFunctor_map_pushforwardModulesMapOfNatIso, Iso.symm_hom]
    exact e.inv_hom_id_app _)

/-- **The direct image of sheaves of modules is transported along a 2-isomorphism of morphisms
of ringed topoi.**  If the two direct images of sheaves of sets are isomorphic by a
transformation carrying the structure map of the one to the structure map of the other, then
the two direct images of sheaves of modules are isomorphic, by that transformation on
underlying sheaves of sets. -/
noncomputable def pushforwardModulesIsoOfNatIso
    (e : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (he : F.fSharpRing ≫
      pullbackRingSheafMapOfNatTrans Y.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) e.hom = H.fSharpRing) :
    F.pushforwardModules ≅ H.pushforwardModules :=
  NatIso.ofComponents (pushforwardModulesIsoAppOfNatIso F H e he) fun φ ↦
    hom_ext_moduleSheafFunctor (by
      simp only [CategoryTheory.Functor.map_comp,
        moduleSheafFunctor_map_pushforwardModules_map,
        pushforwardModulesIsoAppOfNatIso,
        moduleSheafFunctor_map_pushforwardModulesMapOfNatIso]
      exact e.hom.naturality _)

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 03G8**, the composition law for the structure map, at the level of sheaves of
rings: the structure map of the composite of the two morphisms of ringed topoi, followed by the
comparison of the direct images, is the structure map of the morphism of ringed topoi of the
composite.

This is `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp` with commutativity
forgotten; the comparison of the direct images of sheaves of commutative rings becomes the
comparison of the direct images of sheaves of rings induced by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`. -/
theorem smallEtaleRingedToposHom_comp_fSharpRing (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
          (smallEtaleRingedToposHom B S hS f)).fSharpRing ≫
        pullbackRingSheafMapOfNatTrans
          (Φ := ((smallEtaleRingedToposHom B S hS g).comp
            (smallEtaleRingedToposHom B S hS f)).toToposHom.pushforward)
          (Φ' := (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom.pushforward)
          _ _ (smallToposMorphismTypeU_comp B S hS f g).hom =
      (smallEtaleRingedToposHom B S hS (f ≫ g)).fSharpRing := by
  refine (sheafCompose (smallEtaleRingedTopos B S hS Z).J
    (forget RingCat.{u})).map_injective ?_
  have h2 : (smallEtaleRingedTopos B S hS Z).forgetRing.map
      ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
        (smallEtaleRingedTopos B S hS X).O) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) _ (smallToposMorphismTypeU_comp B S hS f g)
  have h := congrArg (fun m ↦ (smallEtaleRingedTopos B S hS Z).forgetRing.map m)
    (smallEtaleRingedToposHom_comp_fSharp B S hS f g)
  rw [CategoryTheory.Functor.map_comp, h2] at h
  refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _) ?_
  refine Eq.trans (congrArg
    (fun n ↦ (sheafCompose (smallEtaleRingedTopos B S hS Z).J (forget RingCat.{u})).map
      (((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).fSharpRing) ≫ n)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans _ _
      (smallToposMorphismTypeU_comp B S hS f g).hom)) ?_
  exact h

/-- The direct image of modules along a composite of morphisms of algebraic spaces, read
through the morphisms of small étale ringed topoi of Stacks 03G8. -/
theorem modulePushforward_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward B S hS f ⋙ modulePushforward B S hS g =
      (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS g).pushforwardModules :=
  congrArg₂ (fun (A : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
      (A' : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS Z.1 Z.2) ↦ A ⋙ A')
    (pushforwardModules_eq_modulePushforward B S hS f).symm
    (pushforwardModules_eq_modulePushforward B S hS g).symm

/-- The direct image of modules of the composite of the two morphisms of small étale ringed
topoi, identified with the direct image of modules of the morphism of ringed topoi attached to
the composite morphism of algebraic spaces.

The two morphisms of ringed topoi are 2-isomorphic and not equal — their geometric halves are
compared by `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` and their structure maps by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharpRing` — so this is the transport
of `AlgebraicGeometry.RingedToposHom.pushforwardModulesIsoOfNatIso` along that
2-isomorphism. -/
noncomputable def pushforwardModulesCompTransport (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModules :=
  RingedToposHom.pushforwardModulesIsoOfNatIso.{u, u + 1, u, u, u + 1, u} _ _
    (smallToposMorphismTypeU_comp B S hS f g)
    (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g)

/-- The canonical comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules along a
composite of morphisms of algebraic spaces.

Both sides have the direct image of sheaves of sets of the composite as their underlying
sheaf, and the comparison is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, the
comparison of Stacks 03G2, part (3), on it. -/
@[stacks 03LU "pushforward composition",
  stacks 03LU "the composition comparison for direct images"]
noncomputable def modulePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      modulePushforward B S hS (f ≫ g) :=
  eqToIso (modulePushforward_comp_eq B S hS f g) ≪≫
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫
    pushforwardModulesCompTransport B S hS f g ≪≫
    eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))

/-- An equality of functors into `𝒪_Z`-modules is, on underlying sheaves of sets, the comparison
of the two underlying sheaves, read through any sheaf `T` that both of them are. -/
theorem moduleSheafFunctor_map_eqToHom_app_eq_eqToHom_comp {D : Type*} [Category D]
    {G₁ G₂ : D ⥤ Modules.{u, u} B S hS Z.1 Z.2} (h : G₁ = G₂) (M : D)
    (T : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (h₁ : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj (G₁.obj M) = T)
    (h₂ : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj (G₂.obj M) = T) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map ((eqToHom h).app M) =
      eqToHom h₁ ≫ eqToHom h₂.symm := by
  subst h
  subst h₁
  exact (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map_id _

/-- Both sides of `AlgebraicGeometry.Space.modulePushforward_comp_eq` have the iterated direct
image of sheaves of sets as their underlying sheaf, so it is the identity there. -/
theorem moduleSheafFunctor_map_eqToHom_modulePushforward_comp_eq_app (f : X ⟶ Y)
    (g : Y ⟶ Z) (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((eqToHom (modulePushforward_comp_eq B S hS f g)).app F) =
      𝟙 ((smallToposMorphismTypeU B S hS g).pushforward.obj
        ((smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) :=
  (moduleSheafFunctor_map_eqToHom_app_eq_eqToHom_comp B S hS
      (modulePushforward_comp_eq B S hS f g) F
      ((smallToposMorphismTypeU B S hS g).pushforward.obj
        ((smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) rfl rfl).trans rfl

/-- The identification of `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` is the
identity on underlying sheaves of sets: the two direct images differ only in which of the two
adjunct forms of the structure map restricts the scalars. -/
theorem moduleSheafFunctor_map_eqToHom_pushforwardModules_eq_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((eqToHom (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))).app F) =
      𝟙 ((smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        (eqToHom_app (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)) F)).trans
      (eqToHom_map (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z))
        (Functor.congr_obj (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)) F))).trans
    (eqToHom_refl ((smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) _)

/-- The comparison `(g ∘ f)_* ≅ f_* ⋙ g_*` of direct images of modules for the honest composite of
the morphisms of ringed topoi is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).inv.app F) =
      𝟙 ((smallToposMorphismTypeU B S hS g).pushforward.obj
        ((smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))) := rfl

/-- The transport of `AlgebraicGeometry.Space.pushforwardModulesCompTransport` is the geometric
comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on
underlying sheaves of sets.  This is the only factor of the comparison with content. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompTransport_hom_app (f : X ⟶ Y)
    (g : Y ⟶ Z) (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((pushforwardModulesCompTransport B S hS f g).hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) := rfl

/-- The composite of the adjunctions `g^* ⊣ g_*` and `f^* ⊣ f_*`, with its right adjoint read
as `(f ≫ g)_*` using `AlgebraicGeometry.Space.modulePushforwardCompIso`. -/
noncomputable def moduleCompAdjunction (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback B S hS g ⋙ modulePullback B S hS f ⊣ modulePushforward B S hS (f ≫ g) :=
  ((modulePullbackAdjunction B S hS g).comp
    (modulePullbackAdjunction B S hS f)).ofNatIsoRight (modulePushforwardCompIso B S hS f g)

/-- The canonical comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of inverse images of `𝒪`-modules along a
composite of morphisms of algebraic spaces.

Both functors are left adjoint to `(f ≫ g)_*`: the left-hand side by
`AlgebraicGeometry.Space.moduleCompAdjunction`, which composes the two adjunctions and reads
the resulting right adjoint through `modulePushforwardCompIso`, and the right-hand side by
`AlgebraicGeometry.Space.modulePullbackAdjunction`.  The comparison is the uniqueness of a
left adjoint, so it is the mate of the comparison of direct images. -/
@[stacks 03LU "pullback composition",
  stacks 03LU "the composition comparison for pullbacks"]
noncomputable def modulePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback B S hS g ⋙ modulePullback B S hS f ≅ modulePullback B S hS (f ≫ g) :=
  Adjunction.leftAdjointUniq (moduleCompAdjunction B S hS f g)
    (modulePullbackAdjunction B S hS (f ≫ g))

section Equations

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Compatibility of the comparison of inverse images with the units.**  The unit of the
composite adjunction, followed by the direct image of the comparison, is the unit of
`(f ≫ g)^* ⊣ (f ≫ g)_*`. -/
theorem unit_comp_whiskerRight_modulePullbackCompIso_hom :
    (moduleCompAdjunction B S hS f g).unit ≫
        Functor.whiskerRight (modulePullbackCompIso B S hS f g).hom
          (modulePushforward B S hS (f ≫ g)) =
      (modulePullbackAdjunction B S hS (f ≫ g)).unit :=
  Adjunction.unit_leftAdjointUniq_hom (moduleCompAdjunction B S hS f g)
    (modulePullbackAdjunction B S hS (f ≫ g))

/-- **Compatibility of the comparison of inverse images with the counits.** -/
theorem modulePullbackCompIso_hom_comp_counit :
    Functor.whiskerLeft (modulePushforward B S hS (f ≫ g))
          (modulePullbackCompIso B S hS f g).hom ≫
        (modulePullbackAdjunction B S hS (f ≫ g)).counit =
      (moduleCompAdjunction B S hS f g).counit :=
  Adjunction.leftAdjointUniq_hom_counit (moduleCompAdjunction B S hS f g)
    (modulePullbackAdjunction B S hS (f ≫ g))

end Equations

end AlgebraicGeometry.Space

end
