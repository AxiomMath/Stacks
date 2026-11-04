module

public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Pushforward along a continuous functor with a fully faithful left adjoint

Let `u : C ⥤ D` be a continuous functor of sites, so that restriction along `u` carries sheaves
on `D` to sheaves on `C` and is the direct image `u^s : Sh(D) ⥤ Sh(C)` of a morphism of topoi.
Suppose `u` admits a left adjoint `v : D ⥤ C`.  Restriction `v^p` along `v` is then a left
adjoint of restriction `u^p` along `u` on presheaves, and the composite `v^p ∘ u^p` is
restriction along `v ⋙ u`.  If `v` is fully faithful the unit `𝟭 ⟶ v ⋙ u` is an isomorphism,
so that composite is the identity and `u^p` is fully faithful; full faithfulness descends to the
full subcategories of sheaves, giving `u^s` fully faithful and the counit of any adjunction with
right adjoint `u^s` an isomorphism.

## Main results

* `CategoryTheory.Functor.restrictionCompIsoIdOfAdjoint` — restriction along `u` followed by
  restriction along `v` is the identity on presheaves.
* `CategoryTheory.Functor.fullyFaithfulRestrictionOfAdjoint` — restriction along `u` is fully
  faithful on presheaves.
* `CategoryTheory.Functor.fullyFaithfulSheafPushforwardContinuousOfAdjoint` — the direct image
  `u^s` is fully faithful.
* `CategoryTheory.Functor.isIso_counit_of_fullyFaithful_leftAdjoint` — the counit
  `u_s u^s F ⟶ F` of any adjunction with right adjoint `u^s` is an isomorphism.

## Implementation notes

Continuity of `v` is not assumed anywhere: full faithfulness is settled on presheaves, where no
topology is involved, and is then transported to sheaves along the identification of `u^s` with
restriction along `u` and the full faithfulness of the inclusion of sheaves into presheaves.
The counit statement is phrased for an arbitrary left adjoint of `u^s`, so that it applies to a
geometric morphism whose inverse image was produced by some other construction.

## References

* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
* [Stacks Project, Tag 07RB](https://stacks.math.columbia.edu/tag/07RB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ w w' u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (A : Type w) [Category.{w'} A] (u : C ⥤ D) {v : D ⥤ C} (adj : v ⊣ u)

/-- Restriction along a functor `u : C ⥤ D` followed by restriction along a fully faithful left
adjoint `v` of `u` is the identity on presheaves: the composite is restriction along `v ⋙ u`,
and the unit `𝟭 D ⟶ v ⋙ u` is an isomorphism because `v` is fully faithful. -/
public noncomputable def restrictionCompIsoIdOfAdjoint [v.Full] [v.Faithful] :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⋙ (whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op ≅
      𝟭 (Dᵒᵖ ⥤ A) := by
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  exact NatIso.ofComponents
    (fun Q => isoWhiskerRight (NatIso.op (asIso adj.unit)) Q ≪≫ Q.leftUnitor)
    (by intros; ext; simp)

/-- **Restriction along a functor with a fully faithful left adjoint is fully faithful.**
Restriction along `v` is a left adjoint of restriction along `u`, obtained by whiskering the
adjunction `v ⊣ u` into presheaf categories, and `restrictionCompIsoIdOfAdjoint` identifies the
composite with the identity. -/
public noncomputable def fullyFaithfulRestrictionOfAdjoint [v.Full] [v.Faithful] :
    ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op).FullyFaithful :=
  (Adjunction.whiskerLeft A adj.op).fullyFaithfulROfCompIsoId
    (restrictionCompIsoIdOfAdjoint A u adj)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **The direct image along a continuous functor with a fully faithful left adjoint is fully
faithful.** The direct image `u^s : Sh(D) ⥤ Sh(C)` is restriction along `u` read on underlying
presheaves, where it is fully faithful by `fullyFaithfulRestrictionOfAdjoint`; the inclusion of
sheaves into presheaves is fully faithful, so full faithfulness descends to `u^s`. -/
public noncomputable def fullyFaithfulSheafPushforwardContinuousOfAdjoint
    [u.IsContinuous J K] [v.Full] [v.Faithful] :
    (u.sheafPushforwardContinuous A J K).FullyFaithful := by
  have hpre := fullyFaithfulRestrictionOfAdjoint A u adj
  haveI := hpre.full
  haveI := hpre.faithful
  haveI : (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A).Full :=
    Full.of_iso (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  haveI : (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A).Faithful :=
    Faithful.of_iso (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  haveI := Full.of_comp_faithful (u.sheafPushforwardContinuous A J K) (sheafToPresheaf J A)
  haveI := Faithful.of_comp (u.sheafPushforwardContinuous A J K) (sheafToPresheaf J A)
  exact FullyFaithful.ofFullyFaithful _

include adj in
/-- **The counit `u_s u^s F ⟶ F` is an isomorphism.** For a continuous `u : C ⥤ D` with a fully
faithful left adjoint, the direct image `u^s` is fully faithful, so the counit of any adjunction
having `u^s` as its right adjoint is an isomorphism. -/
public theorem isIso_counit_of_fullyFaithful_leftAdjoint
    [u.IsContinuous J K] [v.Full] [v.Faithful]
    {L : Sheaf J A ⥤ Sheaf K A} (adjSh : L ⊣ u.sheafPushforwardContinuous A J K) :
    IsIso adjSh.counit := by
  have hff := fullyFaithfulSheafPushforwardContinuousOfAdjoint A u adj J K
  have := hff.full
  have := hff.faithful
  exact adjSh.counit_isIso_of_R_fully_faithful

end CategoryTheory.Functor

end
