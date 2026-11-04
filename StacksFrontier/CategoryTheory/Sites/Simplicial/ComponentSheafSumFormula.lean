module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackSumFormula
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentCommaDecomposition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# The sum formula for lower shriek on sheaves of sets (Stacks 09WG)

On a simplicial site, lower shriek from simplicial degree `n`, restricted back to degree `m`, is
the coproduct over the simplex maps `φ : [n] ⟶ [m]` of the inverse images along the transitions.
This file proves that for sheaves of sets, where
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentSumFormula.lean` proves it for sheaves of
abelian groups.

The two proofs are the same argument. The criteria it rests on —
`CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfRan` and
`…OfLan` — and the comma-category computations
`CategoryTheory.SimplicialSite.isLimitFanRanComponent` and
`CategoryTheory.CocontinuousSimplicialSite.isColimitCofanLanComponent` that feed them are stated
at an arbitrary coefficient category, so each of the two cases of the situation is the abelian
instantiation read at `Type u`.

What is not shared is the passage from the composite of a sheaf pullback with a pushforward to
the inverse image of the morphism of topoi, because the abelian file states the formula for the
former and Stacks 09WG asserts it for the latter. Three comparisons bridge them, and they are
recorded separately because each is about a different pair of constructions.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionInverseImageType`: inverse image of sheaves
  of sets along a simplicial transition, in the shape the two criteria produce it.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_restrictIsoCoproduct`:
  **Stacks 09WG**, the sum formula for sheaves of sets.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekRestrictionIsoCoproductType`: the
  same formula as an isomorphism of functors, hence natural in the sheaf. The tag sits on the
  objectwise form, which is what the source asserts; this is its strengthening.
* `CategoryTheory.SimplicialSiteSituation.transitionInverseImageTypeIso` and
  `…componentInverseImageIsoPushforward`: the two comparisons between the inverse images of the
  morphisms of topoi and the functors the criteria produce.

## Implementation notes

The main result is named `componentLowerShriek_restrictIsoCoproduct`, distinct from the companion
lemma's `componentLowerShriekRestrictionIsoCoproduct`, so that the two formulas are
not two spellings of one name differing only in their coefficient category.

The inverse image of `CategoryTheory.SimplicialSiteSituation.componentMorphism`, and the inverse
image of `…transitionMorphism` in case (B), are `CategoryTheory.gInv`, which is *definitionally*
`CategoryTheory.Functor.sheafPullbackCocontinuous`; so those two comparisons need no transport
beyond Stacks 00XR. In case (A) the transition inverse image is instead the *abstract* left
adjoint `CategoryTheory.Functor.sheafPullback`, not the Kan-extension construction
`…sheafPullbackConstruction.sheafPullback` that the criteria produce, and there the comparison is
genuinely needed: it is Mathlib's `…sheafPullbackConstruction.sheafPullbackIso`, uniqueness of
left adjoints. `rfl` between the two fails.

The pointwise evaluation of the coproduct is Mathlib's `CategoryTheory.Limits.sigmaObjIso`,
reused rather than restated.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor Opposite

universe u


namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) {n m : SimplexCategory}

/-- Inverse image of sheaves of sets along the simplicial transition attached to a simplex map
`φ : [n] ⟶ [m]`, in the shape the two sum-formula criteria produce it.

In case (A) the transition is a morphism of sites represented by a continuous functor
`u φ : C_n ⥤ C_m`, and this is the Kan-extension construction of the sheaf pullback along it. In
case (B) the transition is a cocontinuous functor `u φ : C_m ⥤ C_n` and this is restriction of
presheaves along it followed by sheafification. -/
noncomputable def transitionInverseImageType (φ : n ⟶ m) :
    Sheaf (S.componentTopology n) (Type u) ⥤ Sheaf (S.componentTopology m) (Type u) :=
  match S with
  | ⟨Sum.inl C⟩ =>
      have : ((C.underlying.map φ).toFunctor).IsContinuous
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
        (C.isMorphismOfSites φ).isContinuous
      sheafPullbackConstruction.sheafPullback ((C.underlying.map φ).toFunctor) (Type u)
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
  | ⟨Sum.inr C⟩ =>
      ((C.underlying.map φ.op).toFunctor).sheafPullbackCocontinuous (Type u)
        (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n)))

/-- Inverse image along the component inclusion is restriction: **Stacks 00XR (1)** at the
component inclusion, the inverse image of `componentMorphism` being `CategoryTheory.gInv` and
hence definitionally a sheaf pullback along a cocontinuous functor. -/
noncomputable def componentInverseImageIsoPushforward (m : SimplexCategory) :
    (componentMorphism S m).inverseImage ≅
      (componentFunctor S m).sheafPushforwardContinuous (Type u)
        (S.componentTopology m) S.totalTopology :=
  (componentFunctor S m).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u)
    (S.componentTopology m) S.totalTopology

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- The transition inverse image in case (A) is the Kan-extension construction of the sheaf
pullback. The inverse image of the morphism of topoi is the *abstract* left adjoint of
restriction, so this is uniqueness of left adjoints and not an identity. -/
noncomputable def transitionInverseImageTypeIso (C : SimplicialSite.{u}) {n m : SimplexCategory}
    (φ : n ⟶ m) :
    ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).inverseImage ≅
      transitionInverseImageType (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ :=
  have : ((C.underlying.map φ).toFunctor).IsContinuous
      (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
    (C.isMorphismOfSites φ).isContinuous
  Functor.sheafPullbackConstruction.sheafPullbackIso ((C.underlying.map φ).toFunctor) (Type u)
    (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG** for sheaves of sets in case (A), at the level of functors.

The right adjoint of the left-hand side is the right Kan extension along the degree-`m`
inclusion restricted to degree `n`, which
`CategoryTheory.SimplicialSite.isLimitFanRanComponent` exhibits as the product of the
evaluations at the objects `u φ (U)`; the ran criterion turns that product formula into this
coproduct formula. -/
noncomputable def componentLowerShriekRestrictionIsoCoproductType (C : SimplicialSite.{u})
    (n m : SimplexCategory) :
    sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n) (Type u)
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology ⋙
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
          m).sheafPushforwardContinuous (Type u)
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology ≅
      ∐ fun φ : n ⟶ m =>
        transitionInverseImageType (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  have hcont : ∀ φ : n ⟶ m, ((C.underlying.map φ).toFunctor).IsContinuous
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) :=
    fun φ => (C.isMorphismOfSites φ).isContinuous
  have hranRaw : ∀ G : (C.underlying.obj m)ᵒᵖ ⥤ Type u,
      (CoGrothendieck.ι C.totalPseudofunctor (op m)).op.HasRightKanExtension G :=
    fun G =>
      (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ G).hasRightKanExtension
  have hran : ∀ G : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).component m)ᵒᵖ ⥤ Type u,
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m).op.HasRightKanExtension G :=
    fun G =>
      (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ G).hasRightKanExtension
  exact Functor.sheafPullbackCompPushforwardIsoCoproductOfRan (ht := hcont) (Type u) _ _ _
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
    (fun φ : n ⟶ m => (C.underlying.map φ).toFunctor)
    (fun φ => SimplicialSiteSituation.continuousInclusionTransition C φ)
    (fun P U => isLimitFanRanComponent C U P)

end CategoryTheory.SimplicialSite

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG** for sheaves of sets in case (B), at the level of functors.

Here the right Kan extension side does not decompose, and the proof uses instead that the left
Kan extension along the degree-`n` inclusion, evaluated in degree `m`, is the coproduct of the
evaluations at the objects `u φ (V)` —
`CategoryTheory.CocontinuousSimplicialSite.isColimitCofanLanComponent` — and that sheafification
preserves that coproduct and commutes with restriction to the component. -/
noncomputable def componentLowerShriekRestrictionIsoCoproductType
    (C : CocontinuousSimplicialSite.{u}) (n m : SimplexCategory) :
    sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) (Type u)
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology ⋙
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
          m).sheafPushforwardContinuous (Type u)
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology ≅
      ∐ fun φ : n ⟶ m =>
        transitionInverseImageType (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ := by
  have hlanRaw : ∀ G : (C.underlying.obj (op n))ᵒᵖ ⥤ Type u,
      (Grothendieck.ι C.underlying (op n)).op.HasLeftKanExtension G :=
    fun G => (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension
  have hlan : ∀ G : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ ⥤ Type u,
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).op.HasLeftKanExtension G :=
    fun G => (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension
  exact Functor.sheafPullbackCompPushforwardIsoCoproductOfLan (Type u) _ _ _
    (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m)
    (fun φ : n ⟶ m => (C.underlying.map φ.op).toFunctor)
    (fun φ => Grothendieck.ιNatTrans (F := C.underlying) φ.op)
    (fun P V => isColimitCofanLanComponent C V P)

end CategoryTheory.CocontinuousSimplicialSite

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) {n m : SimplexCategory}

/-- The transition inverse image agrees with the functor the sum-formula criteria produce. In
case (B) the two are definitionally equal; in case (A) the comparison is uniqueness of left
adjoints. -/
noncomputable def transitionInverseImageTypeIso (φ : n ⟶ m) :
    (S.transitionMorphism φ).inverseImage ≅ transitionInverseImageType S φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.transitionInverseImageTypeIso C φ
  | inr C => exact Iso.refl _

/-- **Stacks 09WG** for sheaves of sets, at the level of functors: the strengthening of
`componentLowerShriek_restrictIsoCoproduct` by naturality in the sheaf. -/
noncomputable def componentLowerShriekRestrictionIsoCoproductType (n m : SimplexCategory) :
    sheafPullbackConstruction.sheafPullback (componentFunctor S n) (Type u)
        (S.componentTopology n) S.totalTopology ⋙
      (componentFunctor S m).sheafPushforwardContinuous (Type u)
        (S.componentTopology m) S.totalTopology ≅
      ∐ fun φ : n ⟶ m => transitionInverseImageType S φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.componentLowerShriekRestrictionIsoCoproductType C n m
  | inr C => exact CocontinuousSimplicialSite.componentLowerShriekRestrictionIsoCoproductType C n m

/-- **Stacks 09WG, the sheaf coproduct formula.** On a simplicial site, the degree-`m`
restriction of lower shriek from degree `n` of a sheaf of sets is the coproduct, over the
simplex maps `φ : [n] ⟶ [m]`, of the inverse images of that sheaf along the transitions. -/
@[stacks 09WG "sheaf_coproduct_formula"]
noncomputable def componentLowerShriek_restrictIsoCoproduct (n m : SimplexCategory)
    (G : Sheaf (S.componentTopology n) (Type u)) :
    (componentMorphism S m).inverseImage.obj ((componentLowerShriek.{u, u} S n).obj G) ≅
      ∐ fun φ : n ⟶ m => (S.transitionMorphism φ).inverseImage.obj G :=
  ((componentInverseImageIsoPushforward S m).app
      ((componentLowerShriek.{u, u} S n).obj G)).trans
    (((componentLowerShriekRestrictionIsoCoproductType S n m).app G).trans
      ((sigmaObjIso (fun φ : n ⟶ m => transitionInverseImageType S φ) G).trans
        (Sigma.mapIso fun φ : n ⟶ m => ((transitionInverseImageTypeIso S φ).app G).symm)))

end CategoryTheory.SimplicialSiteSituation

end
