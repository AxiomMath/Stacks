module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.HigherDirectImageLocalAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.EtaleOverRestrictionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.InverseImageSquareTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CitedInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem

/-!
# The étale-local action of `R^q g_* ∘ g⁻¹` on morphisms

Let `g : X ⟶ U` be a morphism of schemes and `A`, `K` abelian sheaves on `U_étale`. A section
over an étale `V ⟶ U` of the internal hom `𝓗om(A, K)` is a morphism `α : A|_V ⟶ K|_V` between
the restrictions to the slice over `V`. This file makes `R^q g_*(g⁻¹ -)` act on such local
morphisms, compatibly with restriction, by the étale-local route:

* `α` is moved to inverse images along `V ⟶ U` (`Stacks.EtaleCohomology.pullbackSliceHom`),
  transported across the cartesian square of `V ⟶ U` and `g`
  (`Stacks.EtaleCohomology.inverseImageSquareTransport`), and acted on by `R^q` of the base change
  of `g` through the étale base change isomorphisms
  (`Stacks.EtaleCohomology.higherDirectImageLocalMap`, Stacks 0EZR via
  `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale`);
  this is `Stacks.EtaleCohomology.higherDirectImageInverseImageLocalMap`;
* read back on the slice it is a morphism
  `(R^q g_* g⁻¹ A)|_V ⟶ (R^q g_* g⁻¹ K)|_V`
  (`Stacks.EtaleCohomology.higherDirectImageInverseImageSliceHom`), which commutes with
  restriction along every `V' ⟶ V`
  (`Stacks.EtaleCohomology.higherDirectImageInverseImageSliceHom_overMapPullback`): the pasting
  law of the base change maps, the pentagon of the composition isomorphisms of inverse images and
  the coherence of restriction with inverse image.

On sections over `V` this gives `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap`,
natural in the target `K`, compatible with precomposition, sending the identity to the identity,
additive, and compatible with restriction. Evaluated at a fixed class `s`, it is the map
`𝓗om(A, K) ⟶ R^q g_*(g⁻¹ K)`, `α ↦ α_* s`, of the tower form of purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.higherDirectImageInverseImageLocalMap`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSliceHom`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap`.

## Main results

* `Stacks.EtaleCohomology.higherDirectImageInverseImageLocalMap_restrict`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSliceHom_overMapPullback`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap_restrict`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap_comp_map`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap_map_comp`.
* `Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap_id`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology

variable {X U : Scheme.{u}} (g : X ⟶ U) (q : ℕ)

/-- The structure morphism of a base change of an étale `U`-scheme is the second projection. -/
theorem smallEtaleBaseChange_obj_hom' (V : U.Etale) :
    ((smallEtaleBaseChange g).obj V).hom = pullback.snd V.hom g := rfl

/-- The base change of an étale `U`-scheme is the fibre product. -/
theorem smallEtaleBaseChange_obj_left' (V : U.Etale) :
    ((smallEtaleBaseChange g).obj V).left = pullback V.hom g := rfl

/-- The base change map of `R^q g_*` along an étale `V ⟶ U` is invertible. -/
theorem higherBaseChangeIsIso_smallEtaleBaseChange (V : U.Etale) :
    HigherBaseChangeIsIso g V.hom (pullback.fst V.hom g) ((smallEtaleBaseChange g).obj V).hom
      pullback.condition q :=
  fun F => SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
    SmoothBaseChange.etaleLocalHigherBaseChange V.hom (pullback.fst V.hom g)
    (pullback.snd V.hom g) g
    (IsPullback.of_hasPullback V.hom g) F q

/-- **The action of `R^q g_* ∘ g⁻¹` on a morphism between inverse images along an étale
`V ⟶ U`**: transport it across the cartesian square of `V ⟶ U` and `g`, and apply `R^q` of the
base change of `g`, through the base change isomorphisms. -/
def higherDirectImageInverseImageLocalMap (V : U.Etale)
    {A K : Sheaf (smallEtaleTopology U) Ab.{u + 1}}
    (β : (smallEtalePullbackAb V.hom).obj A ⟶ (smallEtalePullbackAb V.hom).obj K) :
    (smallEtalePullbackAb V.hom).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj A)) ⟶
      (smallEtalePullbackAb V.hom).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj K)) :=
  higherDirectImageLocalMap (higherBaseChangeIsIso_smallEtaleBaseChange g q V)
    (inverseImageSquareTransport V.hom g (pullback.fst V.hom g) ((smallEtaleBaseChange g).obj V).hom
      (pullback.fst V.hom g ≫ V.hom) rfl pullback.condition β)

/-- **The action is compatible with restriction along a morphism `V' ⟶ V` of étale
`U`-schemes.** -/
theorem higherDirectImageInverseImageLocalMap_restrict {V V' : U.Etale} (f : V' ⟶ V)
    {A K : Sheaf (smallEtaleTopology U) Ab.{u + 1}}
    (β : (smallEtalePullbackAb V.hom).obj A ⟶ (smallEtalePullbackAb V.hom).obj K) :
    higherDirectImageInverseImageLocalMap g q V'
        (smallEtalePullbackAbConj f.left V.hom V'.hom (MorphismProperty.Over.w f).symm
          ((smallEtalePullbackAb f.left).map β)) =
      smallEtalePullbackAbConj f.left V.hom V'.hom (MorphismProperty.Over.w f).symm
        ((smallEtalePullbackAb f.left).map (higherDirectImageInverseImageLocalMap g q V β)) := by
  have hQe : pullback.fst V'.hom g ≫ f.left =
      ((smallEtaleBaseChange g).map f).left ≫ pullback.fst V.hom g :=
    (smallEtaleBaseChange_map_left_fst g f).symm
  have he : ((smallEtaleBaseChange g).obj V').hom =
      ((smallEtaleBaseChange g).map f).left ≫ ((smallEtaleBaseChange g).obj V).hom :=
    (MorphismProperty.Over.w ((smallEtaleBaseChange g).map f)).symm
  exact (congrArg (higherDirectImageLocalMap (higherBaseChangeIsIso_smallEtaleBaseChange g q V'))
    (inverseImageSquareTransport_paste V.hom g (pullback.fst V.hom g)
      ((smallEtaleBaseChange g).obj V).hom (pullback.fst V.hom g ≫ V.hom) rfl pullback.condition
      f.left (pullback.fst V'.hom g) ((smallEtaleBaseChange g).map f).left
      (pullback.fst V'.hom g ≫ f.left) rfl hQe V'.hom (MorphismProperty.Over.w f).symm
      ((smallEtaleBaseChange g).obj V').hom he (pullback.fst V'.hom g ≫ V'.hom) rfl
      pullback.condition β)).trans
    (higherDirectImageLocalMap_paste' (higherBaseChangeIsIso_smallEtaleBaseChange g q V) f.left
      (pullback.fst V'.hom g) ((smallEtaleBaseChange g).map f).left hQe V'.hom
      (MorphismProperty.Over.w f).symm ((smallEtaleBaseChange g).obj V').hom he pullback.condition
      (higherBaseChangeIsIso_smallEtaleBaseChange g q V') _)

section LocalProperties

variable (V : U.Etale) {A K L : Sheaf (smallEtaleTopology U) Ab.{u + 1}}

/-- The local action of `R^q g_* ∘ g⁻¹` sends a composite to the composite of the actions. -/
theorem higherDirectImageInverseImageLocalMap_comp
    (β : (smallEtalePullbackAb V.hom).obj A ⟶ (smallEtalePullbackAb V.hom).obj K)
    (β' : (smallEtalePullbackAb V.hom).obj K ⟶ (smallEtalePullbackAb V.hom).obj L) :
    higherDirectImageInverseImageLocalMap g q V (β ≫ β') =
      higherDirectImageInverseImageLocalMap g q V β ≫
        higherDirectImageInverseImageLocalMap g q V β' :=
  (congrArg (higherDirectImageLocalMap (higherBaseChangeIsIso_smallEtaleBaseChange g q V))
    (inverseImageSquareTransport_comp _ _ _ _ _ _ _ β β')).trans
    (higherDirectImageLocalMap_comp _ _ _)

/-- The local action of `R^q g_* ∘ g⁻¹` is additive. -/
theorem higherDirectImageInverseImageLocalMap_add
    (β β' : (smallEtalePullbackAb V.hom).obj A ⟶ (smallEtalePullbackAb V.hom).obj K) :
    higherDirectImageInverseImageLocalMap g q V (β + β') =
      higherDirectImageInverseImageLocalMap g q V β +
        higherDirectImageInverseImageLocalMap g q V β' :=
  (congrArg (higherDirectImageLocalMap (higherBaseChangeIsIso_smallEtaleBaseChange g q V))
    (inverseImageSquareTransport_add _ _ _ _ _ _ _ β β')).trans
    (higherDirectImageLocalMap_add _ _ _)

/-- On the inverse image along `V ⟶ U` of a morphism `u' : A ⟶ K`, the local action is the inverse
image of `R^q g_*(g⁻¹ u')`. -/
theorem higherDirectImageInverseImageLocalMap_map (u' : A ⟶ K) :
    higherDirectImageInverseImageLocalMap g q V ((smallEtalePullbackAb V.hom).map u') =
      (smallEtalePullbackAb V.hom).map
        (((smallEtalePushforwardAb g).rightDerived q).map ((smallEtalePullbackAb g).map u')) :=
  (congrArg (higherDirectImageLocalMap (higherBaseChangeIsIso_smallEtaleBaseChange g q V))
    (inverseImageSquareTransport_map _ _ _ _ _ _ _ u')).trans
    (higherDirectImageLocalMap_map _ _)

/-- The local action of `R^q g_* ∘ g⁻¹` sends the identity to the identity. -/
theorem higherDirectImageInverseImageLocalMap_id (A : Sheaf (smallEtaleTopology U) Ab.{u + 1}) :
    higherDirectImageInverseImageLocalMap g q V (𝟙 ((smallEtalePullbackAb V.hom).obj A)) = 𝟙 _ :=
  (congrArg (higherDirectImageLocalMap (higherBaseChangeIsIso_smallEtaleBaseChange g q V))
    (inverseImageSquareTransport_id _ _ _ _ _ _ _ A)).trans
    (higherDirectImageLocalMap_id _ _)

end LocalProperties

section Slice

variable {A K L : Sheaf (smallEtaleTopology U) Ab.{u + 1}}

/-- Reading a morphism between restrictions to the slice over `W` on `W_étale` is injective. -/
theorem sliceToRestriction_injective {T : Scheme.{u}} (W : T.Etale)
    {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}} :
    Function.Injective (sliceToRestriction W (A := A) (K := K)) :=
  (etaleOverSheafEquivalence W Ab.{u + 1}).functor.map_injective

/-- The action of `R^q g_* ∘ g⁻¹` on a morphism between restrictions to the slice over `V`,
read on `V_étale`. -/
def higherDirectImageInverseImageSliceMap (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    (etaleOverRestriction V Ab.{u + 1}).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj A)) ⟶
      (etaleOverRestriction V Ab.{u + 1}).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj K)) :=
  (smallEtalePullbackAbIsoEtaleOverRestriction V).inv.app _ ≫
    higherDirectImageInverseImageLocalMap g q V (pullbackSliceHom V α) ≫
      (smallEtalePullbackAbIsoEtaleOverRestriction V).hom.app _

/-- **The action of `R^q g_* ∘ g⁻¹` on a morphism between restrictions to the slice over `V`**:
a morphism `A|_V ⟶ K|_V` gives `(R^q g_* g⁻¹ A)|_V ⟶ (R^q g_* g⁻¹ K)|_V`. -/
def higherDirectImageInverseImageSliceHom (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj A)) ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj
        (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj K)) :=
  (etaleOverSheafEquivalence V Ab.{u + 1}).fullyFaithfulFunctor.preimage
    (higherDirectImageInverseImageSliceMap g q V α)

/-- Read on `V_étale`, `higherDirectImageInverseImageSliceHom` is
`higherDirectImageInverseImageSliceMap`. -/
theorem sliceToRestriction_higherDirectImageInverseImageSliceHom (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    sliceToRestriction V (higherDirectImageInverseImageSliceHom g q V α) =
      higherDirectImageInverseImageSliceMap g q V α :=
  (etaleOverSheafEquivalence V Ab.{u + 1}).fullyFaithfulFunctor.map_preimage _

/-- **The action commutes with restriction along `V' ⟶ V`**: it is a morphism of sheaves
`𝓗om(A, K) ⟶ 𝓗om(R^q g_* g⁻¹ A, R^q g_* g⁻¹ K)` on sections. -/
theorem higherDirectImageInverseImageSliceHom_overMapPullback {V V' : U.Etale} (f : V' ⟶ V)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    (((smallEtaleTopology U).overMapPullback Ab.{u + 1} f).map
        (higherDirectImageInverseImageSliceHom g q V α) :
        ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj
            (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj A)) ⟶
          ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj
            (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj K))) =
      higherDirectImageInverseImageSliceHom g q V'
        (((smallEtaleTopology U).overMapPullback Ab.{u + 1} f).map α :
          ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj A ⟶
            ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj K) := by
  apply sliceToRestriction_injective V'
  have key : higherDirectImageInverseImageLocalMap g q V'
      (pullbackSliceHom V' (((smallEtaleTopology U).overMapPullback Ab.{u + 1} f).map α :
        ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj A ⟶
          ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj K)) =
      smallEtalePullbackAbConj f.left V.hom V'.hom (MorphismProperty.Over.w f).symm
        ((smallEtalePullbackAb f.left).map
          (higherDirectImageInverseImageLocalMap g q V (pullbackSliceHom V α))) :=
    (congrArg (higherDirectImageInverseImageLocalMap g q V')
      (pullbackSliceHom_overMapPullback f α)).trans
      (higherDirectImageInverseImageLocalMap_restrict g q f (pullbackSliceHom V α))
  refine (sliceToRestriction_overMapPullback f _).trans ?_
  refine (congrArg (fun x => (etaleOverRestrictionCompIso f).inv.app _ ≫
    (etaleOverRestriction (Scheme.Etale.mk f.left) Ab.{u + 1}).map x ≫
      (etaleOverRestrictionCompIso f).hom.app _)
    (sliceToRestriction_higherDirectImageInverseImageSliceHom g q V α)).trans ?_
  refine (etaleOverRestrictionCompIso_conj f _).trans ?_
  refine Eq.trans ?_ (sliceToRestriction_higherDirectImageInverseImageSliceHom g q V' _).symm
  exact congrArg (fun x => (smallEtalePullbackAbIsoEtaleOverRestriction V').inv.app _ ≫ x ≫
    (smallEtalePullbackAbIsoEtaleOverRestriction V').hom.app _) key.symm

/-- `higherDirectImageInverseImageSliceMap` is natural in the target: postcomposing with the
restriction of `u' : K ⟶ L` postcomposes with the restriction of `R^q g_*(g⁻¹ u')`. -/
theorem higherDirectImageInverseImageSliceMap_comp_map (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) (u' : K ⟶ L) :
    higherDirectImageInverseImageSliceMap g q V
        (α ≫ ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map u') =
      higherDirectImageInverseImageSliceMap g q V α ≫ (etaleOverRestriction V Ab.{u + 1}).map
        (((smallEtalePushforwardAb g).rightDerived q).map ((smallEtalePullbackAb g).map u')) := by
  rw [higherDirectImageInverseImageSliceMap, higherDirectImageInverseImageSliceMap,
    pullbackSliceHom_comp, pullbackSliceHom_map, higherDirectImageInverseImageLocalMap_comp,
    higherDirectImageInverseImageLocalMap_map]
  simp only [Category.assoc]
  rw [← (smallEtalePullbackAbIsoEtaleOverRestriction V).hom.naturality]

/-- `higherDirectImageInverseImageSliceMap` is natural in the source: precomposing with the
restriction of `p' : L ⟶ A` precomposes with the restriction of `R^q g_*(g⁻¹ p')`. -/
theorem higherDirectImageInverseImageSliceMap_map_comp (V : U.Etale) (p' : L ⟶ A)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    higherDirectImageInverseImageSliceMap g q V
        (((smallEtaleTopology U).overPullback Ab.{u + 1} V).map p' ≫ α) =
      (etaleOverRestriction V Ab.{u + 1}).map
          (((smallEtalePushforwardAb g).rightDerived q).map ((smallEtalePullbackAb g).map p')) ≫
        higherDirectImageInverseImageSliceMap g q V α := by
  rw [higherDirectImageInverseImageSliceMap, higherDirectImageInverseImageSliceMap,
    pullbackSliceHom_comp, pullbackSliceHom_map, higherDirectImageInverseImageLocalMap_comp,
    higherDirectImageInverseImageLocalMap_map]
  simp only [Category.assoc]
  rw [← (smallEtalePullbackAbIsoEtaleOverRestriction V).inv.naturality_assoc]

/-- `higherDirectImageInverseImageSliceMap` sends the identity to the identity. -/
@[simp]
theorem higherDirectImageInverseImageSliceMap_id (V : U.Etale) :
    higherDirectImageInverseImageSliceMap g q V
        (𝟙 (((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A)) = 𝟙 _ := by
  rw [higherDirectImageInverseImageSliceMap, pullbackSliceHom_id,
    higherDirectImageInverseImageLocalMap_id, Category.id_comp, Iso.inv_hom_id_app]

/-- `higherDirectImageInverseImageSliceMap` is additive. -/
theorem higherDirectImageInverseImageSliceMap_add (V : U.Etale)
    (α β : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    higherDirectImageInverseImageSliceMap g q V (α + β) =
      higherDirectImageInverseImageSliceMap g q V α +
        higherDirectImageInverseImageSliceMap g q V β := by
  rw [higherDirectImageInverseImageSliceMap, higherDirectImageInverseImageSliceMap,
    higherDirectImageInverseImageSliceMap, pullbackSliceHom_add,
    higherDirectImageInverseImageLocalMap_add, Preadditive.add_comp, Preadditive.comp_add]

end Slice

section Sections

variable {A K L : Sheaf (smallEtaleTopology U) Ab.{u + 1}}

/-- `higherDirectImageInverseImageSliceHom` is natural in the target: postcomposing with the
restriction of `u' : K ⟶ L` postcomposes with the restriction of `R^q g_*(g⁻¹ u')`. -/
theorem higherDirectImageInverseImageSliceHom_comp_map (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) (u' : K ⟶ L) :
    higherDirectImageInverseImageSliceHom g q V
        (α ≫ ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map u') =
      higherDirectImageInverseImageSliceHom g q V α ≫
        ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map
          (((smallEtalePushforwardAb g).rightDerived q).map ((smallEtalePullbackAb g).map u')) := by
  apply sliceToRestriction_injective V
  rw [sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_comp,
    sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_map,
    higherDirectImageInverseImageSliceMap_comp_map]

/-- `higherDirectImageInverseImageSliceHom` is natural in the source: precomposing with the
restriction of `p' : L ⟶ A` precomposes with the restriction of `R^q g_*(g⁻¹ p')`. -/
theorem higherDirectImageInverseImageSliceHom_map_comp (V : U.Etale) (p' : L ⟶ A)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    higherDirectImageInverseImageSliceHom g q V
        (((smallEtaleTopology U).overPullback Ab.{u + 1} V).map p' ≫ α) =
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map
          (((smallEtalePushforwardAb g).rightDerived q).map ((smallEtalePullbackAb g).map p')) ≫
        higherDirectImageInverseImageSliceHom g q V α := by
  apply sliceToRestriction_injective V
  rw [sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_comp,
    sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_map,
    higherDirectImageInverseImageSliceMap_map_comp]

/-- `higherDirectImageInverseImageSliceHom` sends the identity to the identity. -/
@[simp]
theorem higherDirectImageInverseImageSliceHom_id (V : U.Etale) :
    higherDirectImageInverseImageSliceHom g q V
        (𝟙 (((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A)) = 𝟙 _ := by
  apply sliceToRestriction_injective V
  rw [sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_id,
    higherDirectImageInverseImageSliceMap_id]

/-- `higherDirectImageInverseImageSliceHom` is additive. -/
theorem higherDirectImageInverseImageSliceHom_add (V : U.Etale)
    (α β : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    higherDirectImageInverseImageSliceHom g q V (α + β) =
      higherDirectImageInverseImageSliceHom g q V α +
        higherDirectImageInverseImageSliceHom g q V β := by
  apply sliceToRestriction_injective V
  rw [sliceToRestriction_higherDirectImageInverseImageSliceHom, sliceToRestriction_add,
    sliceToRestriction_higherDirectImageInverseImageSliceHom,
    sliceToRestriction_higherDirectImageInverseImageSliceHom,
    higherDirectImageInverseImageSliceMap_add]

/-- **The action of `R^q g_* ∘ g⁻¹` on sections over `V`**: a morphism `α : A|_V ⟶ K|_V` acts
on the sections of `R^q g_* g⁻¹ A` over `V`. -/
def higherDirectImageInverseImageSectionMap (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj A)).obj.obj
        (op V) ⟶
      (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj K)).obj.obj
        (op V) :=
  (higherDirectImageInverseImageSliceHom g q V α).hom.app (op (Over.mk (𝟙 V)))

/-- **The action on sections commutes with restriction.** -/
theorem higherDirectImageInverseImageSectionMap_restrict {V V' : U.Etale} (f : V' ⟶ V)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    (((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj A)).obj.map
        f.op ≫
      higherDirectImageInverseImageSectionMap g q V'
        (((smallEtaleTopology U).overMapPullback Ab.{u + 1} f).map α :
          ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj A ⟶
            ((smallEtaleTopology U).overPullback Ab.{u + 1} V').obj K) =
      higherDirectImageInverseImageSectionMap g q V α ≫
        (((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj K)).obj.map f.op := by
  have h := higherDirectImageInverseImageSliceHom_overMapPullback g q f α
  let ν : (Over.map f).obj (Over.mk (𝟙 V')) ⟶ Over.mk (𝟙 V) := Over.homMk f (by simp)
  unfold higherDirectImageInverseImageSectionMap
  rw [← h]
  exact (higherDirectImageInverseImageSliceHom g q V α).hom.naturality ν.op

/-- The action on sections over `V` is natural in the target: postcomposing with the restriction
of `u' : K ⟶ L` postcomposes with the map of `R^q g_*(g⁻¹ u')` on sections over `V`. -/
theorem higherDirectImageInverseImageSectionMap_comp_map (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) (u' : K ⟶ L) :
    higherDirectImageInverseImageSectionMap g q V
        (α ≫ ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map u') =
      higherDirectImageInverseImageSectionMap g q V α ≫
        (((smallEtalePushforwardAb g).rightDerived q).map
          ((smallEtalePullbackAb g).map u')).hom.app (op V) := by
  rw [higherDirectImageInverseImageSectionMap, higherDirectImageInverseImageSliceHom_comp_map]
  rfl

/-- The action on sections over `V` is natural in the source: precomposing with the restriction
of `p' : L ⟶ A` precomposes with the map of `R^q g_*(g⁻¹ p')` on sections over `V`. -/
theorem higherDirectImageInverseImageSectionMap_map_comp (V : U.Etale) (p' : L ⟶ A)
    (α : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    higherDirectImageInverseImageSectionMap g q V
        (((smallEtaleTopology U).overPullback Ab.{u + 1} V).map p' ≫ α) =
      (((smallEtalePushforwardAb g).rightDerived q).map
          ((smallEtalePullbackAb g).map p')).hom.app (op V) ≫
        higherDirectImageInverseImageSectionMap g q V α := by
  rw [higherDirectImageInverseImageSectionMap, higherDirectImageInverseImageSliceHom_map_comp]
  rfl

/-- The identity of `A|_V` acts as the identity on sections over `V`. -/
@[simp]
theorem higherDirectImageInverseImageSectionMap_id (V : U.Etale) :
    higherDirectImageInverseImageSectionMap g q V
        (𝟙 (((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A)) = 𝟙 _ := by
  rw [higherDirectImageInverseImageSectionMap, higherDirectImageInverseImageSliceHom_id]
  rfl

/-- The action on sections over `V` is additive in the morphism `α`. -/
theorem higherDirectImageInverseImageSectionMap_add (V : U.Etale)
    (α β : ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj A ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj K) :
    higherDirectImageInverseImageSectionMap g q V (α + β) =
      higherDirectImageInverseImageSectionMap g q V α +
        higherDirectImageInverseImageSectionMap g q V β := by
  rw [higherDirectImageInverseImageSectionMap, higherDirectImageInverseImageSliceHom_add]
  rfl

end Sections

end Stacks.EtaleCohomology

end
