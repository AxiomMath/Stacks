module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Basic
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TransitionCocycle

/-!
# The ringed morphisms of simplicial components induced by simplex maps

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Every component carries the ringed topos `(Sh(C_n), O_n)` of Stacks 0D72, whose
structure sheaf is the restriction of `O` along the component inclusion. A simplex map
`φ : m ⟶ n` induces a morphism of topoi `f_φ : Sh(C_n) ⟶ Sh(C_m)`, and the inverse-image
transition of Stacks 09WF carries the ring operations along, giving a map `f_φ⁻¹ O_m ⟶ O_n` of
structure sheaves and hence a morphism of *ringed* topoi.

This module builds that morphism of ringed topoi together with the ring-valued lifts of the
canonical unit and composition comparisons of inverse images of sheaves of sets.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionInverseImageCommRing`: the inverse image of
  sheaves of commutative rings along `f_φ`.
* `CategoryTheory.SimplicialSiteSituation.componentStructureSheafIso`: the structure sheaf of
  the component ringed topos, as the transport of the ring operations of `O` along restriction
  of sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionCommRing`: the map `f_φ⁻¹ O_m ⟶ O_n`
  of structure sheaves induced by a simplex map.
* `CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom`: the induced morphism of
  ringed topoi `(Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)`.
* `CategoryTheory.SimplicialSiteSituation.canonicalCommRingIdentityComparison` and
  `.canonicalCommRingCompositionComparison`: the ring-valued lifts of
  `CategoryTheory.SimplicialSiteSituation.canonicalIdentityComparison` and
  `.canonicalCompositionComparison`, identifying the inverse image of sheaves of commutative
  rings along `f_𝟙` with the identity and along `f_{ψ ≫ φ}` with the iterated inverse image.

## Main results

* `CategoryTheory.SimplicialSiteSituation.fiberTransitionCommRing_forget`,
  `.canonicalCommRingIdentityComparison_forget` and
  `.canonicalCommRingCompositionComparison_forget`: on underlying sheaves of sets, the three
  constructions are `CategoryTheory.SimplicialSiteSituation.fiberTransition` and the
  corresponding comparisons of inverse images of sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.fiberTransitionCommRing_id` and
  `.fiberTransitionCommRing_comp`: the unit and cocycle laws for the structure-sheaf
  transitions, stated through the two ring-valued comparisons.
* `CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom_toToposHom` and
  `.transitionRingedToposHom_fSharpInverseImage`: the underlying morphism of topoi and the
  structure map of the induced morphism of ringed topoi.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

attribute [local implicit_reducible]
  CategoryTheory.SimplicialSiteSituation.componentRingedTopos
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- Restriction of sheaves of sets to a simplicial component preserves finite products. -/
instance preservesFiniteProducts_restrict (n : SimplexCategory) :
    PreservesFiniteProducts (S.restrict.{u, u} n) :=
  inferInstanceAs (PreservesFiniteProducts
    ((S.inclusion n).sheafPushforwardContinuous (Type u) (S.componentTopology n) S.totalTopology))

/-- The inverse image of the morphism of topoi induced by a simplex map preserves finite
products. -/
instance preservesFiniteProducts_transitionMorphism_inverseImage {m n : SimplexCategory}
    (φ : m ⟶ n) : PreservesFiniteProducts (S.transitionMorphism φ).inverseImage :=
  have := (S.transitionMorphism φ).preservesFiniteLimits
  inferInstance

/-- The inverse image of sheaves of commutative rings along the morphism of topoi `f_φ` induced
by a simplex map `φ : m ⟶ n`. -/
noncomputable abbrev transitionInverseImageCommRing {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (S.componentTopology m) CommRingCat.{u} ⥤
      Sheaf (S.componentTopology n) CommRingCat.{u} :=
  inverseImageCommRingFunctor (J := S.componentTopology n) (K := S.componentTopology m)
    (S.transitionMorphism φ)

section Transition

variable (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The structure sheaf of the component ringed topos of Stacks 0D72 in degree `n`, which is a
restriction of sheaves of commutative rings, is the transport of the ring operations of `O`
along restriction of sheaves of sets to that component. The comparison is the identity on
sections. -/
noncomputable def componentStructureSheafIso (n : SimplexCategory) :
    pullbackCommRingSheaf (K := S.totalTopology) (S.componentTopology n)
        (S.restrict.{u, u} n) O ≅
      (S.componentRingedTopos O n).O :=
  restrictionCommRingIso (S.componentTopology n) S.totalTopology (S.inclusion n) O

/-- On underlying sheaves of sets, the forward map of `componentStructureSheafIso` is the identity.
-/
@[simp] theorem componentStructureSheafIso_hom_forget (n : SimplexCategory) :
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        (S.componentStructureSheafIso O n).hom =
      𝟙 ((S.restrict.{u, u} n).obj
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)) :=
  rfl

/-- On underlying sheaves of sets, the inverse of `componentStructureSheafIso` is the identity. -/
@[simp] theorem componentStructureSheafIso_inv_forget (n : SimplexCategory) :
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        (S.componentStructureSheafIso O n).inv =
      𝟙 ((S.restrict.{u, u} n).obj
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)) :=
  rfl

/-- The map `f_φ⁻¹ O_m ⟶ O_n` of structure sheaves of the component ringed topoi induced by a
simplex map `φ : m ⟶ n`: the inverse-image transition
`CategoryTheory.SimplicialSiteSituation.fiberTransition` of sheaves of sets, carrying the ring
operations of `O` along. -/
noncomputable def fiberTransitionCommRing {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionInverseImageCommRing φ).obj (S.componentRingedTopos O m).O ⟶
      (S.componentRingedTopos O n).O :=
  (S.transitionInverseImageCommRing φ).map (S.componentStructureSheafIso O m).inv ≫
    (pullbackCommRingSheafComp (S.componentTopology m) (S.componentTopology n)
        (S.restrict.{u, u} m) (S.transitionMorphism φ).inverseImage O).hom ≫
    pullbackCommRingSheafMapOfNatTrans (S.componentTopology n) (S.fiberTransition φ) O ≫
    (S.componentStructureSheafIso O n).hom

/-- On underlying sheaves of sets, the structure-sheaf transition is the inverse-image transition
`CategoryTheory.SimplicialSiteSituation.fiberTransition`. -/
theorem fiberTransitionCommRing_forget {m n : SimplexCategory} (φ : m ⟶ n) :
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        (S.fiberTransitionCommRing O φ) =
      (S.fiberTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) := by
  have hrestrict : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      ((S.transitionInverseImageCommRing φ).map (S.componentStructureSheafIso O m).inv) =
      𝟙 ((S.transitionMorphism φ).inverseImage.obj ((S.restrict.{u, u} m).obj
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))) :=
    (underlyingRingSheaf_map_pullbackCommRingSheafMap (S.componentTopology n)
        (Φ := (S.transitionMorphism φ).inverseImage)
        (S.componentStructureSheafIso O m).inv).trans
      ((S.transitionMorphism φ).inverseImage.map_id _)
  have hcomp : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      (pullbackCommRingSheafComp (S.componentTopology m) (S.componentTopology n)
        (S.restrict.{u, u} m) (S.transitionMorphism φ).inverseImage O).hom =
      𝟙 ((S.transitionMorphism φ).inverseImage.obj ((S.restrict.{u, u} m).obj
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))) :=
    forget_map_pullbackCommRingSheafComp_hom (S.componentTopology m) (S.componentTopology n)
      (S.restrict.{u, u} m) (S.transitionMorphism φ).inverseImage O
  have htransition : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      (pullbackCommRingSheafMapOfNatTrans (S.componentTopology n) (S.fiberTransition φ) O) =
      (S.fiberTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) :=
    pullbackCommRingSheafMapOfNatTrans_forget (S.componentTopology n) (S.fiberTransition φ) O
  rw [fiberTransitionCommRing, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  simp only [hrestrict, hcomp, htransition, componentStructureSheafIso_hom_forget]
  change 𝟙 _ ≫ 𝟙 _ ≫ (S.fiberTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) ≫ 𝟙 _ =
      (S.fiberTransition φ).app ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)
  rw [Category.id_comp, Category.id_comp, Category.comp_id]

/-- The morphism of ringed topoi `f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)` induced by a simplex
map `φ : m ⟶ n`: the morphism of topoi of Stacks 09WE, with the structure-sheaf transition as
its structure map in inverse-image form. -/
noncomputable def transitionRingedToposHom {m n : SimplexCategory} (φ : m ⟶ n) :
    RingedToposHom (S.componentRingedTopos O n) (S.componentRingedTopos O m) where
  toToposHom := S.transitionMorphism φ
  fSharp := (commRingImageAdjunction (S.transitionMorphism φ)).homEquiv
    (S.componentRingedTopos O m).O (S.componentRingedTopos O n).O
    (S.fiberTransitionCommRing O φ)

/-- The underlying morphism of topoi of the induced ringed morphism is the morphism of topoi of
Stacks 09WE. -/
@[simp] theorem transitionRingedToposHom_toToposHom {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionRingedToposHom O φ).toToposHom = S.transitionMorphism φ :=
  rfl

/-- The structure map of the induced ringed morphism, in inverse-image form, is the
structure-sheaf transition. -/
@[simp] theorem transitionRingedToposHom_fSharpInverseImage {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.transitionRingedToposHom O φ).fSharpInverseImage = S.fiberTransitionCommRing O φ :=
  ((commRingImageAdjunction (S.transitionMorphism φ)).homEquiv
    (S.componentRingedTopos O m).O (S.componentRingedTopos O n).O).symm_apply_apply _

end Transition

section Comparisons

/-- The ring-valued inverse-image unit comparison: the inverse image of sheaves of commutative
rings along `f_𝟙` is the identity. It is the ring-valued lift of
`CategoryTheory.SimplicialSiteSituation.canonicalIdentityComparison`. -/
noncomputable def canonicalCommRingIdentityComparison (n : SimplexCategory) :
    S.transitionInverseImageCommRing (𝟙 n) ≅
      𝟭 (Sheaf (S.componentTopology n) CommRingCat.{u}) :=
  pullbackCommRingSheafFunctorIsoOfNatIso (S.componentTopology n)
      (Φ := (S.transitionMorphism (𝟙 n)).inverseImage)
      (Φ' := 𝟭 (Sheaf (S.componentTopology n) (Type u)))
      (S.canonicalIdentityComparison n) ≪≫
    pullbackCommRingSheafFunctorId (S.componentTopology n)

/-- The ring-valued unit comparison has the prescribed comparison of inverse images of sheaves
of sets underneath. -/
theorem canonicalCommRingIdentityComparison_forget (n : SimplexCategory)
    (R : Sheaf (S.componentTopology n) CommRingCat.{u}) :
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        ((S.canonicalCommRingIdentityComparison n).hom.app R) =
      (S.canonicalIdentityComparison n).hom.app
        ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).obj R) := by
  have hlift : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      ((pullbackCommRingSheafIsoOfNatIso (S.componentTopology n)
        (Φ := (S.transitionMorphism (𝟙 n)).inverseImage)
        (Φ' := 𝟭 (Sheaf (S.componentTopology n) (Type u)))
        (S.canonicalIdentityComparison n) R).hom) =
      (S.canonicalIdentityComparison n).hom.app
        ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).obj R) :=
    pullbackCommRingSheafIsoOfNatIso_hom_forget (S.componentTopology n)
      (S.canonicalIdentityComparison n) R
  rw [canonicalCommRingIdentityComparison, Iso.trans_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp]
  simp only [hlift, forget_map_pullbackCommRingSheafFunctorId_hom_app,
    pullbackCommRingSheafFunctorIsoOfNatIso_hom_app]
  exact Category.comp_id _

/-- The ring-valued inverse-image compositor: the inverse image of sheaves of commutative rings
along `f_{ψ ≫ φ}` is the iterated inverse image along `f_ψ` and `f_φ`. It is the ring-valued
lift of `CategoryTheory.SimplicialSiteSituation.canonicalCompositionComparison`. -/
noncomputable def canonicalCommRingCompositionComparison {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.transitionInverseImageCommRing (ψ ≫ φ) ≅
      S.transitionInverseImageCommRing ψ ⋙ S.transitionInverseImageCommRing φ :=
  pullbackCommRingSheafFunctorIsoOfNatIso (S.componentTopology n)
      (Φ := (S.transitionMorphism (ψ ≫ φ)).inverseImage)
      (Φ' := (S.transitionMorphism ψ).inverseImage ⋙ (S.transitionMorphism φ).inverseImage)
      (S.canonicalCompositionComparison ψ φ) ≪≫
    (pullbackCommRingSheafFunctorComp (S.componentTopology m) (S.componentTopology n)
      (S.transitionMorphism ψ).inverseImage (S.transitionMorphism φ).inverseImage).symm

/-- The ring-valued compositor has the prescribed comparison of inverse images of sheaves of
sets underneath. -/
theorem canonicalCommRingCompositionComparison_forget {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (R : Sheaf (S.componentTopology l) CommRingCat.{u}) :
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        ((S.canonicalCommRingCompositionComparison ψ φ).hom.app R) =
      (S.canonicalCompositionComparison ψ φ).hom.app
        ((sheafCompose (S.componentTopology l) (forget CommRingCat.{u})).obj R) := by
  have hlift : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      ((pullbackCommRingSheafIsoOfNatIso (S.componentTopology n)
        (Φ := (S.transitionMorphism (ψ ≫ φ)).inverseImage)
        (Φ' := (S.transitionMorphism ψ).inverseImage ⋙ (S.transitionMorphism φ).inverseImage)
        (S.canonicalCompositionComparison ψ φ) R).hom) =
      (S.canonicalCompositionComparison ψ φ).hom.app
        ((sheafCompose (S.componentTopology l) (forget CommRingCat.{u})).obj R) :=
    pullbackCommRingSheafIsoOfNatIso_hom_forget (S.componentTopology n)
      (S.canonicalCompositionComparison ψ φ) R
  have hcomp : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
      ((pullbackCommRingSheafFunctorComp (S.componentTopology m) (S.componentTopology n)
        (S.transitionMorphism ψ).inverseImage
        (S.transitionMorphism φ).inverseImage).inv.app R) = 𝟙 _ :=
    forget_map_inverseImageCommRingComp_inv (S.transitionMorphism ψ)
      (S.transitionMorphism φ) R
  rw [canonicalCommRingCompositionComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp]
  simp only [hlift, hcomp, pullbackCommRingSheafFunctorIsoOfNatIso_hom_app]
  exact Category.comp_id _

variable (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The structure-sheaf transition of an identity simplex map is the ring-valued unit
comparison. -/
theorem fiberTransitionCommRing_id (n : SimplexCategory) :
    S.fiberTransitionCommRing O (𝟙 n) =
      (S.canonicalCommRingIdentityComparison n).hom.app (S.componentRingedTopos O n).O := by
  refine (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map_injective ?_
  simp only [S.fiberTransitionCommRing_forget, S.canonicalCommRingIdentityComparison_forget]
  exact S.fiberTransition_id n ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)

/-- The structure-sheaf transition of a composite simplex map is the composite of the two
transitions, compared by the ring-valued compositor. -/
theorem fiberTransitionCommRing_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.fiberTransitionCommRing O (ψ ≫ φ) =
      (S.canonicalCommRingCompositionComparison ψ φ).hom.app
          (S.componentRingedTopos O l).O ≫
        (S.transitionInverseImageCommRing φ).map (S.fiberTransitionCommRing O ψ) ≫
        S.fiberTransitionCommRing O φ := by
  refine (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [S.fiberTransitionCommRing_forget, S.canonicalCommRingCompositionComparison_forget,
    pullbackCommRingSheafFunctor_map, underlyingRingSheaf_map_pullbackCommRingSheafMap]
  exact S.fiberTransition_comp ψ φ
    ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)

end Comparisons

end CategoryTheory.SimplicialSiteSituation

end
