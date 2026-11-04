module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleRingedAugmentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism

/-!
# The square of a morphism of augmented simplicial algebraic spaces

Let `h : X → Y` be a morphism of simplicial algebraic spaces with augmentations `a : X → X₋₁`,
`b : Y → Y₋₁` and a morphism `h₋₁ : X₋₁ → Y₋₁` with `b₀ ∘ h₀ = h₋₁ ∘ a₀`, that is, a morphism of
augmented simplicial algebraic spaces. Section 0DE7 observes that the square of morphisms of
ringed topoi
```
(Sh(X_étale), 𝒪_X) --h_étale--> (Sh(Y_étale), 𝒪_Y)
        |a                               |b
(Sh(X₋₁), 𝒪_{X₋₁}) ----h₋₁----> (Sh(Y₋₁), 𝒪_{Y₋₁})
```
commutes. On a sheaf `F` on `X_étale` both `b_* h_{étale,*} F` and `h₋₁,* a_* F` are limits over
the simplex category whose terms over `W` étale over `Y₋₁` are the sections of `F` over
`(W ×_{Y₋₁} X₋₁) ×_{X₋₁} X_n`; the identification of the two cosimplicial sheaves, compatible with
their transitions, gives the isomorphism of direct images. The structure maps agree because both
pull global functions back along `(W ×_{Y₋₁} X₋₁) ×_{X₋₁} X_n ⟶ W`, which is checked in degree
zero, where the projection of the limit is injective.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleRingedHom`: the morphism of ringed spaces-étale topoi of a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.etaleSquarePushforwardIso`: `b_* ∘ h_{étale,*} ≅ h₋₁,* ∘ a_*`.
* `AlgebraicGeometry.Space.etaleSquareTwoIso`: the square, as a 2-isomorphism of morphisms of
  ringed topoi.

## Main results

* `AlgebraicGeometry.Space.etaleSquareTermIso_naturality`: the termwise identification is
  compatible with the cosimplicial structures.
* `AlgebraicGeometry.Space.etaleSquare_commutes`: the square is compatible with the structure maps.

## Implementation notes

The source writes an equality of morphisms of ringed topoi. As for Lemmas 0D96 and 0D99, it is
expressed by an isomorphism of direct-image functors, here compatible with the structure maps,
that is a 2-isomorphism of morphisms of ringed topoi (Stacks 04IC).

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The morphism of ringed spaces-étale topoi of a morphism of algebraic spaces -/

section BaseChange

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Base change along a morphism `f : X ⟶ Y` of algebraic spaces is continuous for the
spaces-étale topologies. -/
instance spacesBaseChange_isContinuous :
    (spacesBaseChange B S hS f).functor.IsContinuous (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X) :=
  (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous

/-- The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of base change along `f` on the spaces-étale sites:
over `V` étale over `Y`, pullback of global functions along the projection `V ×_Y X ⟶ V`. -/
def spacesBaseChangeStructureSharp :
    SpacesEtale.structureSheaf B S hS Y ⟶
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u + 1}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj
        (SpacesEtale.structureSheaf B S hS X) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op (spacesBaseChange B S hS f).projection)
      (globalFunctionsPresheaf B S hS))

/-- The morphism of ringed topoi `(Sh(X_{spaces, étale}), 𝒪_X) ⟶ (Sh(Y_{spaces, étale}), 𝒪_Y)` of a
morphism of algebraic spaces `f : X ⟶ Y`: the morphism of topoi of base change along `f`
(Stacks 03G2) and the pullback of global functions. -/
def spacesEtaleRingedHom :
    RingedToposHom (spacesEtaleRingedTopos B S hS X) (spacesEtaleRingedTopos B S hS Y) where
  toToposHom := (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi
  fSharp := spacesBaseChangeStructureSharp f ≫
    (restrictionCommRingIso (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
      (spacesBaseChange B S hS f).functor (SpacesEtale.structureSheaf B S hS X)).inv

end BaseChange

/-! ### Base change along `h` of the objects coming from `Y₋₁` -/

variable {A A' : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

open EtaleComponent SimplicialSiteSituation.Augmentation

namespace EtaleComponent

/-- Base change along `h_n` of the base change `V ×_{Y₋₁} Y_n` of a morphism `f` of objects étale
over `Y₋₁` is the base change `(V ×_{Y₋₁} X₋₁) ×_{X₋₁} X_n` of `f`. -/
theorem mapFunctor_map_baseObj (h : A ⟶ A') (n : SimplexCategory)
    {V W : SpacesEtale B S hS A'.right} (f : V ⟶ W) :
    (mapFunctor h n).map (InducedCategory.homMk
        ((spacesBaseChange B S hS (A'.hom.app (op n))).functor.map f) :
          baseObj n V ⟶ baseObj n W) =
      (InducedCategory.homMk ((spacesBaseChange B S hS (A.hom.app (op n))).functor.map
          ((spacesBaseChange B S hS h.right).functor.map f)) :
        baseObj n ((spacesBaseChange B S hS h.right).functor.obj V) ⟶
          baseObj n ((spacesBaseChange B S hS h.right).functor.obj W)) := by
  refine InducedCategory.hom_ext ((transportAlong_eq_iff
    (isPullback_mapComparison h (Sum.inl V : Index A' n)).toCommSq _ _ _).2 ?_)
  apply ((spacesBaseChange B S hS (A'.hom.app (op n))).isPullback W).hom_ext
  · have e₁ := (spacesBaseChange B S hS (A.hom.app (op n))).projection.naturality
      ((spacesBaseChange B S hS h.right).functor.map f)
    have e₂ := (spacesBaseChange B S hS h.right).projection.naturality f
    have e₃ := (spacesBaseChange B S hS (A'.hom.app (op n))).projection.naturality f
    refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (doubleBaseChangeComparison_projection _ _ _ _ (hom_app_comp_right h n) W)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e₂)))))).trans ?_
    exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₃).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (doubleBaseChangeComparison_projection _ _ _ _ (hom_app_comp_right h n) V)).trans
          (Category.assoc _ _ _))))).symm
  · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (mapComparison_hom h (Sum.inl W : Index A' n))).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w _))))).trans ?_
    exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w _)).trans
      (mapComparison_hom h (Sum.inl V : Index A' n)))).symm

end EtaleComponent

/-- The functor of total sites of `h` on the image of `Y₋₁` in degree `n`: base change along
`h₋₁` followed by the image of `X₋₁` in degree `n`. -/
theorem totalFunctor_map_totalComponentSiteFunctor_map (h : A ⟶ A') (n : SimplexCategory)
    {V W : SpacesEtale B S hS A'.right} (f : V ⟶ W) :
    (etaleSimplicialSiteMorphism h).totalFunctor.map
        (((etaleAugmentation A').totalComponentSiteFunctor n).map f) =
      ((etaleAugmentation A).totalComponentSiteFunctor n).map
        ((spacesBaseChange B S hS h.right).functor.map f) := by
  refine ((etaleSimplicialSiteMorphism h).ι_map_totalFunctor (op n)
    (((etaleAugmentation A').componentSiteFunctor n).map f)).trans ?_
  refine congrArg (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor
    (op n)).map ?_
  show (mapFunctor h n).map ((transition (SimplexCategory.const (SimplexCategory.mk 0) n 0)).map
      (augmentationFunctor.map f)) =
      (transition (SimplexCategory.const (SimplexCategory.mk 0) n 0)).map
        (augmentationFunctor.map ((spacesBaseChange B S hS h.right).functor.map f))
  rw [transition_map_augmentationFunctor, transition_map_augmentationFunctor]
  exact mapFunctor_map_baseObj h n f

/-- The functor of total sites of `h` sends the cartesian arrow over `φ` at the image of `W` to the
cartesian arrow over `φ` at the image of `W ×_{Y₋₁} X₋₁`. -/
theorem totalFunctor_map_ιNatTrans_baseObj (h : A ⟶ A') {m n : SimplexCategory} (φ : m ⟶ n)
    (W : SpacesEtale B S hS A'.right) :
    (etaleSimplicialSiteMorphism h).totalFunctor.map
        ((Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A').totalPseudofunctor
          φ.op).app (Sum.inl W : Index A' m)) =
      (Pseudofunctor.CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor
          φ.op).app (Sum.inl ((spacesBaseChange B S hS h.right).functor.obj W) : Index A m) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  show (mapFunctor h n).map (𝟙 _) ≫ eqToHom _ = 𝟙 _ ≫ eqToHom _
  exact congrArg (· ≫ _) ((mapFunctor h n).map_id _)

/-! ### The square of topoi -/

omit [B.Contains S] in
/-- The restriction maps of the direct image along a continuous functor, on a section. -/
theorem sheafPushforwardContinuous_obj_map_apply {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
    (F : Sheaf K (Type (u + 1))) {X Y : C} (k : X ⟶ Y) (s : F.obj.obj (op (G.obj Y))) :
    ((G.sheafPushforwardContinuous (Type (u + 1)) J K).obj F).obj.map k.op s =
      F.obj.map (G.map k).op s :=
  rfl

/-- The degree-`n` term of the cosimplicial sheaf of Stacks 0D70 for `b` applied to `h_{étale,*}F`
is the direct image along `h₋₁` of the degree-`n` term for `a` applied to `F`: both have the
sections of `F` over `(W ×_{Y₋₁} X₋₁) ×_{X₋₁} X_n`. -/
def etaleSquareTermIso (h : A ⟶ A') (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    (n : SimplexCategory) :
    (componentPushforward (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
        (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') n).obj
        ((etaleMorphismOfTopoi h).pushforward.obj F) ≅
      (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.obj
        ((componentPushforward (etaleSituation A)
          (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
          (etaleAugmentation A) n).obj F) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} g =>
    (Category.comp_id _).trans ((congrArg (fun k => F.obj.map (Quiver.Hom.op k))
      (totalFunctor_map_totalComponentSiteFunctor_map h n g.unop)).trans
        (Category.id_comp _).symm)))

/-- The identification `etaleSquareTermIso` is the identity on sections. -/
theorem etaleSquareTermIso_hom_app_apply (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) (n : SimplexCategory)
    (W : (SpacesEtale B S hS A'.right)ᵒᵖ) (s) :
    (etaleSquareTermIso h F n).hom.hom.app W s = s :=
  rfl

/-- The direct image along base change of a map of sheaves, on a section. -/
theorem spacesBaseChange_pushforward_map_hom_app_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {F F' : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))} (α : F ⟶ F')
    (W : (SpacesEtale B S hS Y)ᵒᵖ)
    (s : F.obj.obj (op ((spacesBaseChange B S hS f).functor.obj W.unop))) :
    ((spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi.pushforward.map α).hom.app W s =
      α.hom.app (op ((spacesBaseChange B S hS f).functor.obj W.unop)) s :=
  rfl

/-- The restriction maps of `h_{étale,*}F`, on a section. -/
theorem etaleMorphismOfTopoi_pushforward_obj_map_apply (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    {x y : (Pseudofunctor.CoGrothendieck (etaleSimplicialSite A').totalPseudofunctor)ᵒᵖ}
    (k : x ⟶ y) (s : ((etaleMorphismOfTopoi h).pushforward.obj F).obj.obj x) :
    ((etaleMorphismOfTopoi h).pushforward.obj F).obj.map k s =
      F.obj.map ((etaleSimplicialSiteMorphism h).totalFunctor.map k.unop).op s :=
  rfl

/-- The direct image along `h₋₁` of a map between terms of the cosimplicial sheaf of `a`, on a
section. -/
theorem spacesBaseChange_pushforward_map_component_apply (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) {m n : SimplexCategory}
    (α : (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) m).obj F ⟶
      (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).obj F)
    (W : SpacesEtale B S hS A'.right)
    (s : ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.obj
      ((componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) m).obj F)).obj.obj (op W)) :
    ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
        α).hom.app (op W) s = α.hom.app (op ((spacesBaseChange B S hS h.right).functor.obj W)) s :=
  rfl

/-- Two maps of sheaves of sets agree as soon as they agree on all sections. -/
private theorem sheaf_hom_ext_of_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q : Sheaf J (Type (u + 1))} (f g : P ⟶ Q)
    (H : ∀ (W : C) (x : P.obj.obj (op W)), f.hom.app (op W) x = g.hom.app (op W) x) : f = g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  induction W with | op W => ?_
  exact ConcreteCategory.hom_ext _ _ (H W)

/-- Equal maps of sheaves of sets act equally on sections. -/
private theorem sheaf_hom_app_apply_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q : Sheaf J (Type (u + 1))} {f g : P ⟶ Q} (H : f = g) (U : Cᵒᵖ) (x : P.obj.obj U) :
    f.hom.app U x = g.hom.app U x :=
  H ▸ rfl

/-- A criterion for the compatibility of `etaleSquareTermIso` with maps of the two cosimplicial
sheaves which act on sections by restriction along arrows corresponding to each other under the
functor of total sites. -/
theorem etaleSquareTermIso_comp_eq (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) {m n : SimplexCategory}
    (α' : (componentPushforward (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
        (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') m).obj
        ((etaleMorphismOfTopoi h).pushforward.obj F) ⟶
      (componentPushforward (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
        (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') n).obj
        ((etaleMorphismOfTopoi h).pushforward.obj F))
    (α : (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) m).obj F ⟶
      (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).obj F)
    (k' : ∀ W : SpacesEtale B S hS A'.right,
      (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A').totalPseudofunctor (op n)).obj
          (Sum.inl W : Index A' n) ⟶
        (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A').totalPseudofunctor (op m)).obj
          (Sum.inl W : Index A' m))
    (k : ∀ W : SpacesEtale B S hS A.right,
      (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).obj
          (Sum.inl W : Index A n) ⟶
        (Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op m)).obj
          (Sum.inl W : Index A m))
    (hα' : ∀ W, α'.hom.app (op W) = ((etaleMorphismOfTopoi h).pushforward.obj F).obj.map (k' W).op)
    (hα : ∀ W, α.hom.app (op W) = F.obj.map (k W).op)
    (hk : ∀ W, (etaleSimplicialSiteMorphism h).totalFunctor.map (k' W) =
      k ((spacesBaseChange B S hS h.right).functor.obj W)) :
    α' ≫ (etaleSquareTermIso h F n).hom =
      (etaleSquareTermIso h F m).hom ≫
        (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map α := by
  refine sheaf_hom_ext_of_apply _ _ fun W s => ?_
  refine (sheaf_comp_hom_app_apply _ _ _ s).trans ?_
  refine (etaleSquareTermIso_hom_app_apply h F n _ _).trans ?_
  refine Eq.trans ?_ (sheaf_comp_hom_app_apply _ _ _ s).symm
  refine Eq.trans ?_ (spacesBaseChange_pushforward_map_component_apply h F α W _).symm
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (hα _) _).symm
  refine Eq.trans ?_ (congrArg _ (etaleSquareTermIso_hom_app_apply h F m (op W) s).symm)
  refine (ConcreteCategory.congr_hom (hα' W) s).trans ?_
  refine (etaleMorphismOfTopoi_pushforward_obj_map_apply h F _ s).trans ?_
  exact congrArg (fun k => (F.obj.map (Quiver.Hom.op k)) s) (hk W)

/-- The identifications `etaleSquareTermIso` are compatible with the cosimplicial structures. -/
theorem etaleSquareTermIso_naturality (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (componentPushforwardTransition (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
        (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') φ).app
          ((etaleMorphismOfTopoi h).pushforward.obj F) ≫ (etaleSquareTermIso h F n).hom =
      (etaleSquareTermIso h F m).hom ≫
        (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
          ((componentPushforwardTransition (etaleSituation A)
            (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
            (etaleAugmentation A) φ).app F) :=
  etaleSquareTermIso_comp_eq h F _ _ _ _
    (fun W => transition_app_eq ((etaleMorphismOfTopoi h).pushforward.obj F) φ W)
    (fun W => transition_app_eq F φ W) (fun W => totalFunctor_map_ιNatTrans_baseObj h φ W)

/-- The identifications `etaleSquareTermIso` are natural in the sheaf. -/
theorem etaleSquareTermIso_natural (h : A ⟶ A')
    {F F' : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))} (β : F ⟶ F')
    (n : SimplexCategory) :
    (componentPushforward (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
        (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') n).map
          ((etaleMorphismOfTopoi h).pushforward.map β) ≫ (etaleSquareTermIso h F' n).hom =
      (etaleSquareTermIso h F n).hom ≫
        (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
          ((componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
            (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).map β) :=
  rfl

/-- The cosimplicial sheaf of Stacks 0D70 for `b` applied to `h_{étale,*}F` is the direct image
along `h₋₁` of the cosimplicial sheaf for `a` applied to `F`, naturally in `F`. -/
def etaleSquareDiagramIso (h : A ⟶ A') :
    (etaleMorphismOfTopoi h).pushforward ⋙
        (cosimplicialPushforward (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
          (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A')).flip ≅
      (cosimplicialPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).flip ⋙
        (Functor.whiskeringRight SimplexCategory _ _).obj
          (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun n => etaleSquareTermIso h F n)
      (fun φ => etaleSquareTermIso_naturality h F φ))
    (fun β => NatTrans.ext (funext fun n => etaleSquareTermIso_natural h β n))

/-- The direct image along `h₋₁` preserves limits indexed by the simplex category. -/
instance (h : A ⟶ A') : PreservesLimitsOfShape SimplexCategory
    (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward :=
  (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.adj
    |>.rightAdjoint_preservesLimits |>.preservesLimitsOfShape

omit [B.Contains S] in
/-- For an isomorphism `δ : Φ ⋙ P ≅ Q ⋙ G_*` of functors into diagrams and a functor `G` preserving
their limits, the induced isomorphism `Φ ⋙ P ⋙ lim ≅ Q ⋙ lim ⋙ G`, followed by `G` of a limit
projection, is the limit projection followed by `δ`. -/
theorem whiskered_lim_iso_hom_app_comp_map_π {J : Type*} [Category J] {C D E E' : Type*}
    [Category C] [Category D] [Category E] [Category E'] [HasLimitsOfShape J E]
    [HasLimitsOfShape J E'] (Φ : C ⥤ D) (P : D ⥤ J ⥤ E') (Q : C ⥤ J ⥤ E) (G : E ⥤ E')
    [hG : PreservesLimitsOfShape J G] (δ : Φ ⋙ P ≅ Q ⋙ (Functor.whiskeringRight J E E').obj G)
    (F : C) (n : J) :
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight δ lim ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q (preservesLimitNatIso G).symm ≪≫
          (Functor.associator _ _ _).symm).hom.app F ≫ G.map (limit.π (Q.obj F) n) =
      limit.π (P.obj (Φ.obj F)) n ≫ (δ.hom.app F).app n := by
  simp [preservesLimitNatIso]

/-- **Section 0DE7, the square of topoi.** For a morphism `h : X ⟶ Y` of augmented simplicial
algebraic spaces, with augmentations `a : X → X₋₁`, `b : Y → Y₋₁` and `h₋₁ : X₋₁ → Y₋₁`, the
square
```
Sh(X_étale) --h_étale--> Sh(Y_étale)
     |a                       |b
Sh(X₋₁, étale) --h₋₁--> Sh(Y₋₁, étale)
```
commutes: `b_* ∘ h_{étale,*} ≅ h₋₁,* ∘ a_*`. On a sheaf `F`, both sides are the limit over the
simplex category of the sections of `F` over the `(W ×_{Y₋₁} X₋₁) ×_{X₋₁} X_n`. -/
def etaleSquarePushforwardIso (h : A ⟶ A') :
    (etaleMorphismOfTopoi h).pushforward ⋙ (etaleAugmentationMorphism A').pushforward ≅
      (etaleAugmentationMorphism A).pushforward ⋙
        (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (etaleSquareDiagramIso h) lim ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (preservesLimitNatIso
        (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The square isomorphism followed by the projection of `h₋₁,* a_* F` to degree `n` is the
projection of `b_* h_{étale,*} F` to degree `n`, read through `etaleSquareTermIso`. -/
theorem etaleSquarePushforwardIso_hom_app_comp_projection (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) (n : SimplexCategory) :
    (etaleSquarePushforwardIso h).hom.app F ≫
        (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
          (pushforwardProjection (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
            (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) F n) =
      pushforwardProjection (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
          (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A')
          ((etaleMorphismOfTopoi h).pushforward.obj F) n ≫ (etaleSquareTermIso h F n).hom :=
  whiskered_lim_iso_hom_app_comp_map_π (etaleMorphismOfTopoi h).pushforward _ _ _
    (hG := (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.adj
      |>.rightAdjoint_preservesLimits |>.preservesLimitsOfShape) (etaleSquareDiagramIso h) F n

/-! ### The square of ringed topoi -/

/-- The morphism of ringed topoi `h₋₁ : (Sh(X₋₁, étale), 𝒪_{X₋₁}) ⟶ (Sh(Y₋₁, étale), 𝒪_{Y₋₁})`
between the bottom corners of the square. -/
abbrev etaleBaseRingedHom (h : A ⟶ A') :
    RingedToposHom (etaleRingedAugmentation A).augmentationRingedTopos
      (etaleRingedAugmentation A').augmentationRingedTopos :=
  spacesEtaleRingedHom h.right

/-- The projection of `a_*F` to degree zero is injective on sections. -/
theorem etalePushforwardProjection_zero_injective
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    (U : (SpacesEtale B S hS A.right)ᵒᵖ) :
    Function.Injective ((pushforwardProjection (etaleSituation A)
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) F (SimplexCategory.mk 0)).hom.app U) := by
  have hm : Mono (pushforwardProjection (etaleSituation A)
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) F (SimplexCategory.mk 0)) :=
    Fork.IsLimit.mono (totalPushforwardForkIsLimit (etaleSituation A)
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) F)
  exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance U)

/-- The direct image along `h₋₁` of the projection of `a_*F` to a degree, on a section. -/
theorem spacesBaseChange_pushforward_map_projection_apply (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) (n : SimplexCategory)
    (α : (pushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).obj F ⟶
      (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).obj F)
    (W : SpacesEtale B S hS A'.right)
    (s : ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.obj
      ((pushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).obj F)).obj.obj (op W)) :
    ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
        α).hom.app (op W) s = α.hom.app (op ((spacesBaseChange B S hS h.right).functor.obj W)) s :=
  rfl

/-- Two maps into `h₋₁,* a_* F` agree as soon as their projections to degree zero agree on
sections. -/
theorem etaleSquare_hom_ext (h : A ⟶ A')
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    {P : Sheaf (SpacesEtale.topology B S hS A'.right) (Type (u + 1))}
    (f g : P ⟶ (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.obj
      ((pushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).obj F))
    (hfg : ∀ W x,
      ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
        (pushforwardProjection (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) F
          (SimplexCategory.mk 0))).hom.app (op W) (f.hom.app (op W) x) =
      ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
        (pushforwardProjection (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) F
          (SimplexCategory.mk 0))).hom.app (op W) (g.hom.app (op W) x)) :
    f = g := by
  refine sheaf_hom_ext_of_apply _ _ fun W x => etalePushforwardProjection_zero_injective F _
    (((spacesBaseChange_pushforward_map_projection_apply h F _ _ W _).symm.trans (hfg W x)).trans
      (spacesBaseChange_pushforward_map_projection_apply h F _ _ W _))

/-- The composite `b ∘ h_étale` around the top and the right of the square, as a morphism of
ringed topoi. -/
abbrev etaleSquareTopRight (h : A ⟶ A') :
    RingedToposHom ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
      (etaleRingedAugmentation A').augmentationRingedTopos :=
  RingedToposHom.comp (X := (etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
    (Y := (etaleSituation A').totalRingedTopos (etaleStructureSheaf A'))
    (Z := (etaleRingedAugmentation A').augmentationRingedTopos)
    (etaleAugmentationRingedHom A') (etaleMorphismRingedHom h)

/-- The composite `h₋₁ ∘ a` around the left and the bottom of the square, as a morphism of
ringed topoi. -/
abbrev etaleSquareLeftBottom (h : A ⟶ A') :
    RingedToposHom ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
      (etaleRingedAugmentation A').augmentationRingedTopos :=
  RingedToposHom.comp (X := (etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
    (Y := (etaleRingedAugmentation A).augmentationRingedTopos)
    (Z := (etaleRingedAugmentation A').augmentationRingedTopos)
    (etaleBaseRingedHom h) (etaleAugmentationRingedHom A)

/-- The terms of the cosimplicial sheaf of Stacks 0D70 act on maps of sheaves by restriction. -/
theorem componentPushforward_map_hom_app_apply
    (A₀ : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) (n : SimplexCategory)
    {F F' : Sheaf (etaleSimplicialSite A₀).totalTopology (Type (u + 1))}
    (α : F ⟶ F') (W : SpacesEtale B S hS A₀.right)
    (s : ((componentPushforward (etaleSituation A₀) (Cat.of (SpacesEtale B S hS A₀.right))
      (SpacesEtale.topology B S hS A₀.right) (etaleAugmentation A₀) n).obj F).obj.obj (op W)) :
    ((componentPushforward (etaleSituation A₀) (Cat.of (SpacesEtale B S hS A₀.right))
        (SpacesEtale.topology B S hS A₀.right) (etaleAugmentation A₀) n).map α).hom.app (op W) s =
      α.hom.app (op ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A₀).totalPseudofunctor
        (op n)).obj (Sum.inl W : Index A₀ n))) s :=
  rfl

/-- The direct image along `h₋₁` of a map into a term of the cosimplicial sheaf of `a`, on a
section. -/
theorem spacesBaseChange_pushforward_map_into_component_apply (h : A ⟶ A')
    {P : Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))}
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))) (n : SimplexCategory)
    (α : P ⟶ (componentPushforward (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) n).obj F)
    (W : SpacesEtale B S hS A'.right)
    (s : ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.obj
      P).obj.obj (op W)) :
    ((spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
        α).hom.app (op W) s = α.hom.app (op ((spacesBaseChange B S hS h.right).functor.obj W)) s :=
  rfl

/-- The structure map of `h_étale`, on sections. -/
theorem forget_etaleMorphismRingedHom_fSharp_apply (h : A ⟶ A')
    (y : (Pseudofunctor.CoGrothendieck (etaleSimplicialSite A').totalPseudofunctor)ᵒᵖ)
    (z : ((sheafCompose (etaleSimplicialSite A').totalTopology (forget CommRingCat.{u + 1})).obj
      (etaleStructureSheaf A')).obj.obj y) :
    ((sheafCompose (etaleSituation A').totalTopology (forget CommRingCat.{u + 1})).map
        (etaleMorphismRingedHom h).fSharp).hom.app y z =
      (forget CommRingCat.{u + 1}).map
        ((globalFunctionsPresheaf B S hS).map (mapComparison h y.unop.fiber).op) z :=
  rfl

/-- The structure map of `h₋₁`, on sections. -/
theorem forget_spacesEtaleRingedHom_fSharp_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (W : (SpacesEtale B S hS Y)ᵒᵖ)
    (z : ((sheafCompose (SpacesEtale.topology B S hS Y) (forget CommRingCat.{u + 1})).obj
      (SpacesEtale.structureSheaf B S hS Y)).obj.obj W) :
    ((sheafCompose (SpacesEtale.topology B S hS Y) (forget CommRingCat.{u + 1})).map
        (spacesEtaleRingedHom f).fSharp).hom.app W z =
      (forget CommRingCat.{u + 1}).map
        ((globalFunctionsPresheaf B S hS).map
          ((spacesBaseChange B S hS f).projection.app W.unop).op) z :=
  rfl

/-- The criterion behind the compatibility of the square with the structure maps: a map
`O_{Y₋₁} ⟶ b_* O_Y ⟶ b_* h_* O_X` and a map `O_{Y₋₁} ⟶ h₋₁,* O_{X₋₁} ⟶ h₋₁,* a_* O_X` agree through
the square isomorphism as soon as their degree-zero components agree on sections. -/
theorem etaleSquare_comp_eq (h : A ⟶ A')
    {P : Sheaf (SpacesEtale.topology B S hS A'.right) (Type (u + 1))}
    {Q : Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))}
    {Fy : Sheaf (etaleSimplicialSite A').totalTopology (Type (u + 1))}
    {Fx : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1))}
    (bs : P ⟶ (etaleAugmentationMorphism A').pushforward.obj Fy)
    (α : Fy ⟶ (etaleMorphismOfTopoi h).pushforward.obj Fx)
    (c : P ⟶ (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.obj Q)
    (as : Q ⟶ (etaleAugmentationMorphism A).pushforward.obj Fx)
    (m' : P ⟶ (componentPushforward (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
      (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') (SimplexCategory.mk 0)).obj Fy)
    (m : Q ⟶ (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) (SimplexCategory.mk 0)).obj Fx)
    (hb : bs ≫ pushforwardProjection (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
      (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') Fy (SimplexCategory.mk 0) = m')
    (ha : as ≫ pushforwardProjection (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) Fx (SimplexCategory.mk 0) = m)
    (hfinal : ∀ (W : SpacesEtale B S hS A'.right) x,
      α.hom.app (op ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A').totalPseudofunctor
          (op (SimplexCategory.mk 0))).obj (Sum.inl W : Index A' (SimplexCategory.mk 0))))
          (m'.hom.app (op W) x) =
        m.hom.app (op ((spacesBaseChange B S hS h.right).functor.obj W)) (c.hom.app (op W) x)) :
    (bs ≫ (etaleAugmentationMorphism A').pushforward.map α) ≫
        (etaleSquarePushforwardIso h).hom.app Fx =
      c ≫ (spacesBaseChange_isMorphismOfSites B S hS h.right).morphismOfTopoi.pushforward.map
        as := by
  refine etaleSquare_hom_ext h Fx _ _ fun W x => ?_
  refine (congrArg _ (sheaf_comp_hom_app_apply _ _ _ x)).trans ?_
  refine (sheaf_comp_hom_app_apply _ _ _ _).symm.trans ?_
  refine (sheaf_hom_app_apply_congr
    (etaleSquarePushforwardIso_hom_app_comp_projection h Fx (SimplexCategory.mk 0))
      (op W) _).trans ?_
  refine (sheaf_comp_hom_app_apply _ _ _ _).trans ?_
  refine (etaleSquareTermIso_hom_app_apply h Fx (SimplexCategory.mk 0) (op W) _).trans ?_
  refine (congrArg _ (sheaf_comp_hom_app_apply _ _ _ x)).trans ?_
  refine (sheaf_comp_hom_app_apply _ _ _ _).symm.trans ?_
  refine (sheaf_hom_app_apply_congr
    (pushforward_map_comp_projection (etaleSituation A') (Cat.of (SpacesEtale B S hS A'.right))
      (SpacesEtale.topology B S hS A'.right) (etaleAugmentation A') α
      (SimplexCategory.mk 0)) (op W) _).trans ?_
  refine (sheaf_comp_hom_app_apply _ _ _ _).trans ?_
  refine (componentPushforward_map_hom_app_apply A' (SimplexCategory.mk 0) α W _).trans ?_
  refine (congrArg _ (sheaf_comp_hom_app_apply _ _ _ x).symm).trans ?_
  refine (congrArg _ (sheaf_hom_app_apply_congr hb (op W) x)).trans ?_
  refine (hfinal W x).trans ?_
  refine Eq.trans ?_ (congrArg _ (sheaf_comp_hom_app_apply _ _ _ x)).symm
  refine Eq.trans ?_ (spacesBaseChange_pushforward_map_projection_apply h Fx _ _ W _).symm
  refine Eq.trans ?_
    (congrArg _ (spacesBaseChange_pushforward_map_hom_app_apply h.right as _ _)).symm
  refine Eq.trans ?_ (sheaf_comp_hom_app_apply as
    (pushforwardProjection (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) Fx (SimplexCategory.mk 0))
    (op ((spacesBaseChange B S hS h.right).functor.obj W)) (c.hom.app (op W) x))
  exact (sheaf_hom_app_apply_congr ha
    (op ((spacesBaseChange B S hS h.right).functor.obj W)) _).symm

/-- In degree zero, the structure maps around the square agree on sections: both pull global
functions back along `(W ×_{Y₋₁} X₋₁) ×_{X₋₁} X₀ ⟶ W`. -/
theorem etaleSquare_structure_apply (h : A ⟶ A') (W : SpacesEtale B S hS A'.right)
    (x : ((sheafCompose (SpacesEtale.topology B S hS A'.right) (forget CommRingCat.{u + 1})).obj
      (SpacesEtale.structureSheaf B S hS A'.right)).obj.obj (op W)) :
    ((sheafCompose (etaleSituation A').totalTopology (forget CommRingCat.{u + 1})).map
        (etaleMorphismRingedHom h).fSharp).hom.app
        (op ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A').totalPseudofunctor
          (op (SimplexCategory.mk 0))).obj (Sum.inl W : Index A' (SimplexCategory.mk 0))))
        ((etaleComponentStructureMap A' (SimplexCategory.mk 0)).hom.app (op W) x) =
      (etaleComponentStructureMap A (SimplexCategory.mk 0)).hom.app
        (op ((spacesBaseChange B S hS h.right).functor.obj W))
        (((sheafCompose (SpacesEtale.topology B S hS A'.right) (forget CommRingCat.{u + 1})).map
          (spacesEtaleRingedHom h.right).fSharp).hom.app (op W) x) := by
  refine (forget_etaleMorphismRingedHom_fSharp_apply h _ _).trans ?_
  refine (congrArg _ (ConcreteCategory.congr_hom (etaleComponentStructureMap_app A'
    (SimplexCategory.mk 0) (op W)) x)).trans ?_
  refine (forget_map_map_apply_of_comp_eq (globalFunctionsPresheaf B S hS) _ _ _ rfl x).trans ?_
  refine Eq.trans ?_ (congrArg _ (forget_spacesEtaleRingedHom_fSharp_apply h.right (op W) x)).symm
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (etaleComponentStructureMap_app A
    (SimplexCategory.mk 0) (op _)) _).symm
  refine Eq.trans ?_
    (forget_map_map_apply_of_comp_eq (globalFunctionsPresheaf B S hS) _ _ _ rfl x).symm
  exact congrArg (fun k => (forget CommRingCat.{u + 1}).map
    ((globalFunctionsPresheaf B S hS).map (Quiver.Hom.op k)) x)
    (doubleBaseChangeComparison_projection _ _ _ _ (hom_app_comp_right h (SimplexCategory.mk 0)) W)

/-- The structure map of the augmentation, followed by the projection to degree zero. -/
theorem etaleAugmentationRingedHom_fSharp_comp_projection
    (A₀ : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) :
    (etaleRingedAugmentation A₀).augmentationRingedTopos.forgetRing.map
        (etaleAugmentationRingedHom A₀).fSharp ≫
      pushforwardProjection (etaleSituation A₀) (Cat.of (SpacesEtale B S hS A₀.right))
        (SpacesEtale.topology B S hS A₀.right) (etaleAugmentation A₀)
        (((etaleSituation A₀).totalRingedTopos (etaleStructureSheaf A₀)).forgetRing.obj
          (etaleStructureSheaf A₀)) (SimplexCategory.mk 0) =
      etaleComponentStructureMap A₀ (SimplexCategory.mk 0) :=
  (congrArg (· ≫ _) (forget_map_etaleAugmentationSharp A₀)).trans
    (etaleAugmentationSharpSet_comp_projection A₀ (SimplexCategory.mk 0))

/-- The square is compatible with the structure maps. -/
theorem etaleSquare_commutes (h : A ⟶ A') :
    RingedToposHom.forgetFSharp (etaleSquareTopRight h) ≫
        (etaleSquarePushforwardIso h).hom.app
          (((etaleSituation A).totalRingedTopos (etaleStructureSheaf A)).forgetRing.obj
            (etaleStructureSheaf A)) =
      RingedToposHom.forgetFSharp (etaleSquareLeftBottom h) :=
  (congrArg (· ≫ _) (RingedToposHom.comp_fSharp_forget (etaleAugmentationRingedHom A')
    (etaleMorphismRingedHom h))).trans
    ((etaleSquare_comp_eq h _ _ _ _ _ _ (etaleAugmentationRingedHom_fSharp_comp_projection A')
      (etaleAugmentationRingedHom_fSharp_comp_projection A) (etaleSquare_structure_apply h)).trans
      (RingedToposHom.comp_fSharp_forget (etaleBaseRingedHom h)
        (etaleAugmentationRingedHom A)).symm)

/-- **Section 0DE7, the commutative square of ringed topoi.** For a morphism `h : X ⟶ Y` of
augmented simplicial algebraic spaces — morphisms `h_n` commuting with the simplicial structure,
and `h₋₁ : X₋₁ ⟶ Y₋₁` with `b₀ ∘ h₀ = h₋₁ ∘ a₀` — the square of morphisms of ringed topoi
```
(Sh(X_étale), 𝒪_X) --h_étale--> (Sh(Y_étale), 𝒪_Y)
        |a                               |b
(Sh(X₋₁), 𝒪_{X₋₁}) ----h₋₁----> (Sh(Y₋₁), 𝒪_{Y₋₁})
```
commutes: the two composites are 2-isomorphic as morphisms of ringed topoi (Stacks 04IC), through
the identification of their direct images of `etaleSquarePushforwardIso`. -/
def etaleSquareTwoIso (h : A ⟶ A') :
    RingedToposHom.TwoIso (A := (etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
      (B := (etaleRingedAugmentation A').augmentationRingedTopos)
      (etaleSquareTopRight h) (etaleSquareLeftBottom h) where
  e := etaleSquarePushforwardIso h
  commutes := etaleSquare_commutes h

end AlgebraicGeometry.Space

end
