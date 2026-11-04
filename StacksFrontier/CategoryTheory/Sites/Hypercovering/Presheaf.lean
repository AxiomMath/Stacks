module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Pretopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal.Existence
public import StacksFrontier.CategoryTheory.Limits.Finite.Connected
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductEqualizers

/-!
# Hypercoverings of a presheaf

Let `C` be a category with equalizers and fibre products, equipped with a pretopology `J`. The
category of semi-representable objects of `C` is `CategoryTheory.Limits.FormalCoproduct C`, and the
functor `F` sending a semi-representable object to the presheaf it represents is
`FormalCoproduct.uliftYoneda`. A *hypercovering of a presheaf of sets* `G` is a simplicial object
`K` of semi-representable objects together with an augmentation of the simplicial presheaf `F(K)`
towards the constant simplicial presheaf `G`, such that the degree-zero augmentation map, the
degree-one matching map into the fibre product of the two degree-zero maps, and every higher
matching map into `F` of the preceding coskeleton are all surjective after sheafification.

## Main definitions

* `associatedPresheafFunctor`: the functor `F`, sending a semi-representable object to the
  presheaf it represents, with its values lifted to the universe `max q w v`.
* `associatedSimplicialPresheaf`: `F` applied degreewise to a simplicial semi-representable
  object.
* `liftedPresheaf`: a presheaf with values in `Type q` lifted to the universe `max q w v`.
* `oneMatchingMap`: the canonical map from degree one to the fibre product of the two
  degree-zero augmentation maps.
* `positiveCoskeleton`: the `n`-coskeleton functor on simplicial semi-representable objects,
  for `1 ≤ n`.
* `higherMatchingMap`: the canonical map in degree `n + 1` from `F(K)` to `F(coskₙ skₙ K)`.
* `HypercoveringOf`: a hypercovering of a presheaf of sets.
* `HypercoveringOfTerminal`: a hypercovering, that is, a hypercovering of the final presheaf.
* `associatedPresheafFunctorYonedaIso`: the isomorphism of `associatedPresheafFunctor` with the
  lifted `FormalCoproduct.yoneda` when the index and hom universes agree.

## Main results

* `hasPositiveCoskeleta`: if `C` has equalizers and fibre products, the pointwise right Kan
  extensions defining the coskeleta of simplicial semi-representable objects in positive degree
  exist.
* `oneMatchingMap_fst` and `oneMatchingMap_snd`: the two fibre-product projections of the
  degree-one matching map are the two face maps.
* `higherMatchingMap_eq`: the higher matching map is the image under `F` of the unit of the
  coskeleton adjunction.
* `higherMatchingMap_naturality`: higher matching maps are natural in the simplicial
  semi-representable object.
* `higherMatchingMap_comp_yonedaIso_hom`: `associatedPresheafFunctorYonedaIso` commutes with the
  higher matching maps.

## References

* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public section

universe q w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

/-- The semi-representable presheaf functor, lifted to the common value universe. -/
noncomputable abbrev associatedPresheafFunctor :
    FormalCoproduct.{w} C ⥤ Cᵒᵖ ⥤ Type (max q w v) :=
  FormalCoproduct.uliftYoneda.{w} (C := C) ⋙
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{q}

/-- When the index and hom universes agree, the universe-lifted semi-representable presheaf functor
is isomorphic to the lifted `FormalCoproduct.yoneda`. -/
@[implicit_reducible]
noncomputable def associatedPresheafFunctorYonedaIso :
    associatedPresheafFunctor.{q, v} (C := C) ≅
      FormalCoproduct.yoneda (C := C) ⋙
        (Functor.whiskeringRight _ _ _).obj uliftFunctor.{q} :=
  Functor.isoWhiskerRight
    ((FormalCoproduct.eval C _).mapIso (uliftYonedaIsoYoneda.{v, 0} (C := C))) _

/-- Apply the semi-representable presheaf functor degreewise to a simplicial object. -/
noncomputable abbrev associatedSimplicialPresheaf
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    SimplicialObject (Cᵒᵖ ⥤ Type (max q w v)) :=
  K ⋙ associatedPresheafFunctor.{q}

/-- Lift a presheaf into the common universe of the augmentation. -/
noncomputable abbrev liftedPresheaf (G : Cᵒᵖ ⥤ Type q) :
    Cᵒᵖ ⥤ Type (max q w v) :=
  G ⋙ uliftFunctor.{max w v}

/-- The canonical map from degree one to the pullback of the two degree-zero augmentation
maps. -/
@[implicit_reducible]
noncomputable def oneMatchingMap
    (X : SimplicialObject (Cᵒᵖ ⥤ Type q)) (G : Cᵒᵖ ⥤ Type q)
    (augmentation : X ⟶ (SimplicialObject.const _).obj G) :
    X.obj (op (SimplexCategory.mk 1)) ⟶
      pullback (augmentation.app (op (SimplexCategory.mk 0)))
        (augmentation.app (op (SimplexCategory.mk 0))) :=
  pullback.lift (X.δ 0) (X.δ 1) (by
    rw [SimplicialObject.δ_naturality, SimplicialObject.δ_naturality]
    rfl)

/-- The first fibre-product projection of the degree-one matching map is the face map `δ 0`. -/
@[reassoc (attr := simp)]
lemma oneMatchingMap_fst
    (X : SimplicialObject (Cᵒᵖ ⥤ Type q)) (G : Cᵒᵖ ⥤ Type q)
    (augmentation : X ⟶ (SimplicialObject.const _).obj G) :
    oneMatchingMap X G augmentation ≫ pullback.fst _ _ = X.δ 0 :=
  pullback.lift_fst _ _ _

/-- The second fibre-product projection of the degree-one matching map is the face map `δ 1`. -/
@[reassoc (attr := simp)]
lemma oneMatchingMap_snd
    (X : SimplicialObject (Cᵒᵖ ⥤ Type q)) (G : Cᵒᵖ ⥤ Type q)
    (augmentation : X ⟶ (SimplicialObject.const _).obj G) :
    oneMatchingMap X G augmentation ≫ pullback.snd _ _ = X.δ 1 :=
  pullback.lift_snd _ _ _

/-- Equalizers and pullbacks give the pointwise right Kan extensions defining positive
coskeleta of semi-representable objects. -/
lemma hasPositiveCoskeleta [HasEqualizers C] [HasPullbacks C]
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ F : SimplicialObject.Truncated (FormalCoproduct.{w} C) n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F := by
  have hlim : ∀ (I : Type) [SmallCategory I] [FinCategory I] [IsConnected I],
      HasLimitsOfShape I (FormalCoproduct.{w} C) :=
    (hasLimitsOfShape_isConnected_iff_hasEqualizers_and_hasPullbacks
      (FormalCoproduct.{w} C)).2 ⟨inferInstance, inferInstance⟩
  exact
    (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
      (C := FormalCoproduct.{w} C)).2 hlim n hn

/-- The `n`-coskeleton functor on simplicial semi-representable objects, for `1 ≤ n`. -/
noncomputable abbrev positiveCoskeleton [HasEqualizers C] [HasPullbacks C]
    (n : ℕ) (hn : 1 ≤ n) :
    SimplicialObject (FormalCoproduct.{w} C) ⥤ SimplicialObject (FormalCoproduct.{w} C) :=
  letI := hasPositiveCoskeleta (C := C) n hn
  SimplicialObject.cosk n

/-- The canonical map from degree `n + 1` to `F(coskₙ skₙ K)` in that degree. -/
@[implicit_reducible]
noncomputable def higherMatchingMap [HasEqualizers C] [HasPullbacks C]
    (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) (hn : 1 ≤ n) :
    (associatedSimplicialPresheaf.{q} K).obj (op (SimplexCategory.mk (n + 1))) ⟶
      (associatedSimplicialPresheaf.{q} ((positiveCoskeleton n hn).obj K)).obj
        (op (SimplexCategory.mk (n + 1))) := by
  letI := hasPositiveCoskeleta (C := C) n hn
  exact (associatedPresheafFunctor.{q}).map
    (((SimplicialObject.coskAdj n).unit.app K).app (op (SimplexCategory.mk (n + 1))))

/-- The higher matching map is the image of the canonical coskeleton unit. -/
lemma higherMatchingMap_eq [HasEqualizers C] [HasPullbacks C]
    (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) (hn : 1 ≤ n) :
    letI := hasPositiveCoskeleta (C := C) n hn
    higherMatchingMap.{q} K n hn = (associatedPresheafFunctor.{q}).map
      (((SimplicialObject.coskAdj n).unit.app K).app (op (SimplexCategory.mk (n + 1)))) :=
  rfl

/-- Higher matching maps are natural in the simplicial semi-representable object. -/
@[reassoc]
lemma higherMatchingMap_naturality [HasEqualizers C] [HasPullbacks C]
    {K L : SimplicialObject (FormalCoproduct.{w} C)} (f : K ⟶ L)
    (n : ℕ) (hn : 1 ≤ n) :
    (associatedPresheafFunctor.{q}).map (f.app (op (SimplexCategory.mk (n + 1)))) ≫
        higherMatchingMap.{q} L n hn =
      higherMatchingMap.{q} K n hn ≫ (associatedPresheafFunctor.{q}).map
        (((positiveCoskeleton n hn).map f).app (op (SimplexCategory.mk (n + 1)))) := by
  let := hasPositiveCoskeleta.{w} (C := C) n hn
  simpa only [higherMatchingMap, Functor.map_comp, NatTrans.comp_app, Functor.id_map] using
    congrArg (fun η ↦ (associatedPresheafFunctor.{q}).map
      (η.app (op (SimplexCategory.mk (n + 1))))) ((SimplicialObject.coskAdj n).unit.naturality f)

/-- The isomorphism `associatedPresheafFunctorYonedaIso` commutes with the higher matching maps. -/
lemma higherMatchingMap_comp_yonedaIso_hom [HasEqualizers C] [HasPullbacks C]
    (K : SimplicialObject (FormalCoproduct.{v} C)) (n : ℕ) (hn : 1 ≤ n) :
    letI := hasPositiveCoskeleta (C := C) n hn
    higherMatchingMap.{q} K n hn ≫
        (associatedPresheafFunctorYonedaIso.{q}).hom.app
          (((positiveCoskeleton n hn).obj K).obj (op (SimplexCategory.mk (n + 1)))) =
      (associatedPresheafFunctorYonedaIso.{q}).hom.app
          (K.obj (op (SimplexCategory.mk (n + 1)))) ≫
        ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{q}).map
          (FormalCoproduct.yoneda.map
            (((SimplicialObject.coskAdj n).unit.app K).app
              (op (SimplexCategory.mk (n + 1))))) := by
  let := hasPositiveCoskeleta.{v} (C := C) n hn
  exact (associatedPresheafFunctorYonedaIso.{q}).hom.naturality _

variable [HasEqualizers C] [HasPullbacks C]

/-- A hypercovering of a presheaf of sets. -/
@[ext, stacks 09VU "hypercovering of a presheaf", sga "4 V 7.3.1.2", sga "4 V 7.3.1.3" "a)"]
structure HypercoveringOf (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) where
  /-- The underlying simplicial semi-representable object. -/
  toSimplicialObject : SimplicialObject (FormalCoproduct.{w} C)
  /-- The augmentation of its associated simplicial presheaf. -/
  augmentation : associatedSimplicialPresheaf.{q} toSimplicialObject ⟶
    (SimplicialObject.const _).obj (liftedPresheaf.{q, w} G)
  /-- Condition (1): the degree-zero map becomes surjective after sheafification. -/
  locallySurjective_zero : Presheaf.IsLocallySurjective J.toGrothendieck
    (augmentation.app (op (SimplexCategory.mk 0)))
  /-- Condition (2): the degree-one matching map becomes surjective after sheafification. -/
  locallySurjective_one : Presheaf.IsLocallySurjective J.toGrothendieck
    (oneMatchingMap (associatedSimplicialPresheaf.{q} toSimplicialObject)
      (liftedPresheaf.{q, w} G) augmentation)
  /-- Condition (3): every higher matching map becomes surjective after sheafification. -/
  locallySurjective_succ : ∀ (n : ℕ) (hn : 1 ≤ n),
    Presheaf.IsLocallySurjective J.toGrothendieck
      (higherMatchingMap.{q} toSimplicialObject n hn)

/-- A hypercovering can be used as its underlying simplicial semi-representable object. -/
instance instCoeOutHypercoveringOf (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) :
    CoeOut (HypercoveringOf.{q, w} J G) (SimplicialObject (FormalCoproduct.{w} C)) :=
  ⟨HypercoveringOf.toSimplicialObject⟩

/-- A hypercovering is a hypercovering of the final presheaf. -/
@[stacks 09VU "hypercovering of the final presheaf", sga "4 V 7.3.1.2", sga "4 V 7.3.1.3" "a)"]
abbrev HypercoveringOfTerminal (J : Pretopology C) :=
  HypercoveringOf.{v, w} J (⊤_ (Cᵒᵖ ⥤ Type v))

end Stacks.CategoryTheory.Hypercovering

end
