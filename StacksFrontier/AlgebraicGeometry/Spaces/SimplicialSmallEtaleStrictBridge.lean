module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleRingedToposHomComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback

/-!
# The strict components of a simplicial algebraic space against its degrees

Let `X` be a simplicial algebraic space and `(C_n, 𝒪_n)` the component ringed topoi of the
simplicial-site situation of its strict components (case (A) of Stacks 09WE). Each is equivalent
to `(Sh((X_n)_{spaces,étale}), 𝒪_{X_n})` through `strictComponentRingedToposHom`. This file
identifies the transition morphisms `f_φ : (C_n, 𝒪_n) ⟶ (C_m, 𝒪_m)` of the situation with the
morphisms of ringed topoi of `X(φ) : X_n ⟶ X_m` (Stacks 0DE7) under those equivalences.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentTransitionTwoIso`: the
  2-isomorphism `f_φ ∘ realize_n ≅ realize_m ∘ X(φ)_{étale}` of morphisms of ringed topoi.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentPullbackModulesTransitionIso`:
  the same square on pullbacks of sheaves of modules.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentDerivedTransitionIso`: the
  same square on derived pullbacks, `Lf_φ^* ⋙ L realize_n^* ≅ L realize_m^* ⋙ L X(φ)^*`.
* `derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge`:
  the derived pullback `Lf_φ^*` of the situation is the derived pullback along the ringed
  morphism `f_φ` (Stacks 06YY).

## Main results

* `SimplicialSiteSituation.forgetFSharp_transitionRingedToposHom_simplicialSmallEtaleStrictBridge`:
  the structure map of `f_φ`, on underlying sheaves of sets, is the direct-image transition of
  Stacks 09WF at the structure sheaf.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

-- no global `HasDerivedCategory` instance at this universe
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

/-- The structure map of the ringed transition `f_φ`, on underlying sheaves of sets and in its
direct-image form, is the direct-image transition of Stacks 09WF at the structure sheaf. -/
theorem forgetFSharp_transitionRingedToposHom_simplicialSmallEtaleStrictBridge
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    forgetFSharp (S.transitionRingedToposHom O φ) =
      (S.restrictTransition φ).app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) := by
  refine ((congrArg ((S.transitionMorphism φ).adj.homEquiv _ _)
    (fSharpInverseImage_forget_homEquiv (S.transitionRingedToposHom O φ))).trans
      (Equiv.apply_symm_apply _ _)).symm.trans ?_
  rw [transitionRingedToposHom_fSharpInverseImage]
  exact (congrArg (fun t ↦ (S.transitionMorphism φ).adj.homEquiv
      ((S.restrict m).obj ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))
      ((S.restrict n).obj ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)) t)
    (S.fiberTransitionCommRing_forget O φ)).trans (S.fiberTransition_adj φ _)

/-- The derived pullback `Lf_φ^*` of the situation along a simplex map is the derived pullback
along the morphism of ringed topoi `f_φ`: both are the total left derived functor of degreewise
pullback followed by localization. -/
def derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    S.derivedTransitionPullback O φ ≅
      derivedPullback (X := S.componentRingedTopos O n) (Y := S.componentRingedTopos O m)
        (S.transitionRingedToposHom O φ) :=
  Iso.refl _

end CategoryTheory.SimplicialSiteSituation

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The transition functor `u_φ` of the strict components, with source and target spelled as
the components of the simplicial-site situation. -/
abbrev componentStrictTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (strictSituation X).component m ⥤ (strictSituation X).component n :=
  strictTransition X φ

/-- `u_φ` realizes to base change along `X(φ)`, in the spelling of the components. -/
def componentStrictTransitionRealizeIso {m n : SimplexCategory} (φ : m ⟶ n) :
    componentStrictTransition X φ ⋙ componentRealize X n ≅
      componentRealize X m ⋙ (spacesBaseChange B S hS (X.map φ.op)).functor :=
  strictTransitionRealizeIso X φ

/-- `u_φ` is continuous for the component topologies of the situation. -/
instance componentStrictTransition_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentStrictTransition X φ).IsContinuous ((strictSituation X).componentTopology m)
      ((strictSituation X).componentTopology n) := by
  change (strictTransition X φ).IsContinuous (strictTopology X m).toPrecoverage.toGrothendieck
    (strictTopology X n).toPrecoverage.toGrothendieck
  rw [strictTopology_toPrecoverage_toGrothendieck, strictTopology_toPrecoverage_toGrothendieck]
  exact strictTransition_isContinuous X φ

/-- `u_φ` followed by the realization of degree `n` is continuous. -/
instance componentStrictTransition_comp_componentRealize_isContinuous {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (componentStrictTransition X φ ⋙ componentRealize X n).IsContinuous
      ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op n))) :=
  Functor.isContinuous_comp _ _ _ ((strictSituation X).componentTopology n) _

/-- The realization of degree `m` followed by base change along `X(φ)` is continuous. -/
instance componentRealize_comp_spacesBaseChange_isContinuous {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (componentRealize X m ⋙ (spacesBaseChange B S hS (X.map φ.op)).functor).IsContinuous
      ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op n))) :=
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS (X.obj (op m))) _

/-- **The strict components realize the transitions of `X`** (Stacks 0DE7): the square of
morphisms of ringed topoi
```
  (Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) --X(φ)--> (Sh((X_m)_{spaces,étale}), 𝒪_{X_m})
              |                                              |
              v                                              v
        (Sh(C_n), 𝒪_n) -----------------f_φ-----------> (Sh(C_m), 𝒪_m)
```
commutes up to the 2-isomorphism given on direct images by restriction along
`u_φ ⋙ realize_n ≅ realize_m ⋙ (- ×_{X_m} X_n)`. -/
def strictComponentTransitionTwoIso {m n : SimplexCategory} (φ : m ⟶ n) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (B := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (strictComponentRingedToposHom X n))
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (strictComponentRingedToposHom X m) (spacesEtaleRingedToposHom (X.map φ.op))) where
  e := Functor.sheafPushforwardContinuousComp (componentStrictTransition X φ) (componentRealize X n)
        (Type (u + 1)) ((strictSituation X).componentTopology m)
        ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n))) ≪≫
      Functor.sheafPushforwardContinuousIso (componentStrictTransitionRealizeIso X φ) (Type (u + 1))
        ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op n))) ≪≫
      (Functor.sheafPushforwardContinuousComp (componentRealize X m)
        (spacesBaseChange B S hS (X.map φ.op)).functor (Type (u + 1))
        ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op m)))
        (SpacesEtale.topology B S hS (X.obj (op n)))).symm
  commutes := by
    refine Eq.trans ?_ (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1} (strictComponentRingedToposHom X m)
        (spacesEtaleRingedToposHom (X.map φ.op))).symm
    refine Eq.trans (congrArg (· ≫ _) (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1} ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (strictComponentRingedToposHom X n))) ?_
    rw [(strictSituation X).forgetFSharp_transitionRingedToposHom_simplicialSmallEtaleStrictBridge]
    ext V : 3
    have key : (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          (StrictObj.transitionProj φ V.unop).op ≫
        (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          (StrictObj.transitionRealizeInv φ V.unop).op =
        (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          (pullback.fst (pullback.snd V.unop.obj.1.hom (X.map V.unop.simplex.op))
            (X.map φ.op)).op := by
      have h : StrictObj.transitionRealizeInv φ V.unop ≫ StrictObj.transitionProj φ V.unop =
          pullback.fst _ _ := (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (StrictObj.transitionRealizeInv_hom φ _)).trans (Category.id_comp _))
      rw [← Functor.map_comp, ← op_comp, h]
    exact key


/-- **The square of `strictComponentTransitionTwoIso` on pullbacks of modules**:
`realize_n^* ∘ f_φ^* ≅ X(φ)^* ∘ realize_m^*`. -/
def strictComponentPullbackModulesTransitionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (strictComponentRingedToposHom X n)).toModulesHom.pullbackModules ≅
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (strictComponentRingedToposHom X m)
        (spacesEtaleRingedToposHom (X.map φ.op))).toModulesHom.pullbackModules :=
  (strictComponentTransitionTwoIso X φ).pullbackModulesIso

/-- The derived pullback along the realization of a strict component exists, as for every
morphism of ringed topoi (Stacks 06YY). -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictComponentRingedToposHom
    (n : SimplexCategory) :
    (pullbackOnHomotopy (strictComponentRingedToposHom X n)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictComponentRingedToposHom X n)

/-- **The square of `strictComponentTransitionTwoIso` on derived pullbacks**:
`Lf_φ^* ⋙ L realize_n^* ≅ L realize_m^* ⋙ L X(φ)^*`, through the compositions of derived
pullbacks of Stacks 0D6D. -/
def strictComponentDerivedTransitionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (strictSituation X).derivedTransitionPullback (strictStructureSheaf X) φ ⋙
        derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n) ≅
      derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
          (strictComponentRingedToposHom X m) ⋙
        derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op)) :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (strictComponentRingedToposHom X n))
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (strictComponentRingedToposHom X m) (spacesEtaleRingedToposHom (X.map φ.op)))
  Functor.isoWhiskerRight
    ((strictSituation X).derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge
      (strictStructureSheaf X) φ) _ ≪≫
    derivedPullbackCompIso (strictComponentRingedToposHom X n)
      ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ) ≪≫
    derivedPullbackIsoOfPullbackModulesIso
      (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (strictComponentRingedToposHom X n))
      (ψ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (strictComponentRingedToposHom X m) (spacesEtaleRingedToposHom (X.map φ.op)))
      (strictComponentPullbackModulesTransitionIso X φ) ≪≫
    (derivedPullbackCompIso (spacesEtaleRingedToposHom (X.map φ.op))
      (strictComponentRingedToposHom X m)).symm

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
