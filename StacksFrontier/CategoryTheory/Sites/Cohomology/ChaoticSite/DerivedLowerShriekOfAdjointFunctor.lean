module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek undoes inverse image along a functor with a fully faithful right adjoint

Let `u : C ⥤ D` be a functor between categories carrying the chaotic topology and let
`g : Sh(C) ⟶ Sh(D)` be the induced morphism of topoi, so that `g⁻¹` is restriction along `u`. If
`u` has a fully faithful right adjoint `s`, then `Lg_! ∘ g⁻¹` is the identity of `D(Ab(D))`.

This is Tag 08Q7 for a general functor rather than for the projection to the point: there `C ⥤ *`
has a right adjoint exactly when `C` has a final object, which is the hypothesis the source
states. The mechanism is the same. Restriction along `u` has restriction along `s` for a right
adjoint, that right adjoint is exact because on the chaotic topology sheaves are presheaves and
restriction of presheaves is precomposition, and restriction along `u` is fully faithful because
`s` is. So `g⁻¹` is a fully faithful functor with an exact right adjoint, and the counit of
`Lg_! ⊣ g⁻¹` on derived categories is an isomorphism.

## Main results

* `Stacks.ChaoticSite.fullyFaithfulSheafPushforwardContinuous`: restriction of sheaves along a
  continuous functor with a fully faithful right adjoint is fully faithful.
* `Stacks.ChaoticSite.preservesFiniteLimits_sheafPushforwardContinuous_bot` and
  `Stacks.ChaoticSite.preservesFiniteColimits_sheafPushforwardContinuous_bot`: for the chaotic
  topology, restriction of sheaves along any functor is exact.
* `Stacks.ChaoticSite.abelianDerivedLowerShriekInverseImageIso`: **Tag 08Q7 for a functor with a
  fully faithful right adjoint.** For any left derived functor `L` of lower shriek, presented by
  a comparison `α`, and any derived functor `G` of inverse image, presented by `e`, there is a
  natural isomorphism `G ⋙ L ≅ 𝟭`.

## Implementation notes

The topologies are taken to be arbitrary together with proofs that they are the chaotic one,
rather than literally `⊥`, because the sites of the applications carry topologies that are
*equal* to `⊥` but not syntactically so, and the category of sheaves depends on the topology.

The conclusion is stated for an arbitrary model `L` of the total left derived functor of lower
shriek and an arbitrary model `G` of the derived inverse image, as in
`Stacks.ChaoticSite.abelianDerivedInverseImageCompLowerShriekIso`, so nothing is assumed about
the existence of either derived functor.

## References

* [Stacks Project, Tag 08Q7](https://stacks.math.columbia.edu/tag/08Q7)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ChaoticSite

universe t uA v₁ u₁ v₂ u₂

/-- For the chaotic topology sheaves are presheaves, so the inclusion of sheaves into presheaves
is an equivalence. -/
@[sga "4 IV 6.8.6" "more general"]
instance isEquivalence_sheafToPresheaf_bot {C : Type u₁} [Category.{v₁} C]
    (A : Type uA) [Category.{t} A] :
    (sheafToPresheaf (⊥ : GrothendieckTopology C) A).IsEquivalence :=
  (sheafBotEquivalence A).isEquivalence_functor

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {uf : C ⥤ D} {sf : D ⥤ C} (A : Type uA) [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- Lower shriek of a continuous functor is additive, being a left adjoint of an additive
functor between preadditive categories. -/
instance additive_sheafPullback [Preadditive A] (F : C ⥤ D) [F.IsContinuous J K]
    [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    (F.sheafPullback A J K).Additive :=
  (F.sheafAdjunctionContinuous A J K).left_adjoint_additive

/-! ### Restriction along a functor with a fully faithful right adjoint -/

section FullyFaithful

variable [uf.IsContinuous J K] [sf.IsContinuous K J]

/-- The unit of the adjunction between restriction of presheaves along `u` and restriction along
a right adjoint `s` of `u` is an isomorphism when `s` is fully faithful. -/
instance isIso_whiskerLeft_op_unit (adj : uf ⊣ sf) [sf.Full] [sf.Faithful] :
    IsIso (Adjunction.whiskerLeft A adj.op).unit :=
  have : ∀ X : Dᵒᵖ ⥤ A, IsIso ((Adjunction.whiskerLeft A adj.op).unit.app X) := fun _ => by
    dsimp [Adjunction.whiskerLeft]
    infer_instance
  NatIso.isIso_of_isIso_app _

/-- The unit of the adjunction between restriction of sheaves along `u` and restriction along a
right adjoint `s` of `u` is an isomorphism when `s` is fully faithful: it is the unit of the
corresponding adjunction of presheaves. -/
instance isIso_sheafPushforwardContinuous_unit (adj : uf ⊣ sf) [sf.Full] [sf.Faithful] :
    IsIso (Adjunction.sheafPushforwardContinuous (E := A) adj J K).unit :=
  have : ∀ P : Sheaf K A,
      IsIso ((Adjunction.sheafPushforwardContinuous (E := A) adj J K).unit.app P) := fun P => by
    have : IsIso ((sheafToPresheaf K A).map
        ((Adjunction.sheafPushforwardContinuous (E := A) adj J K).unit.app P)) :=
      inferInstanceAs (IsIso ((Adjunction.whiskerLeft A adj.op).unit.app P.obj))
    exact isIso_of_reflects_iso _ (sheafToPresheaf K A)
  NatIso.isIso_of_isIso_app _

/-- **Restriction of sheaves along a functor with a fully faithful right adjoint is fully
faithful.** -/
def fullyFaithfulSheafPushforwardContinuous (adj : uf ⊣ sf) [sf.Full] [sf.Faithful] :
    (uf.sheafPushforwardContinuous A J K).FullyFaithful :=
  (Adjunction.sheafPushforwardContinuous (E := A) adj J K).fullyFaithfulLOfIsIsoUnit

end FullyFaithful

/-! ### Restriction of sheaves on a chaotic site is exact -/

section Exact

variable [Abelian A]

/-- **Restriction of sheaves for the chaotic topology preserves finite limits**, because sheaves
are presheaves there and restriction of presheaves is precomposition. -/
theorem preservesFiniteLimits_sheafPushforwardContinuous_bot (F : C ⥤ D)
    [F.IsContinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D)] :
    PreservesFiniteLimits (F.sheafPushforwardContinuous A
      (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D)) := by
  have : PreservesFiniteLimits (sheafToPresheaf (⊥ : GrothendieckTopology D) A ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (F.sheafPushforwardContinuous A ⊥ ⊥ ⋙
      sheafToPresheaf (⊥ : GrothendieckTopology C) A) :=
    preservesFiniteLimits_of_natIso
      (F.sheafPushforwardContinuousCompSheafToPresheafIso A ⊥ ⊥).symm
  exact ⟨fun _ _ _ => preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (⊥ : GrothendieckTopology C) A)⟩

/-- **Restriction of sheaves for the chaotic topology preserves finite colimits.** -/
theorem preservesFiniteColimits_sheafPushforwardContinuous_bot (F : C ⥤ D)
    [F.IsContinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D)] :
    PreservesFiniteColimits (F.sheafPushforwardContinuous A
      (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D)) := by
  have : PreservesFiniteColimits (sheafToPresheaf (⊥ : GrothendieckTopology D) A ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteColimits (F.sheafPushforwardContinuous A ⊥ ⊥ ⋙
      sheafToPresheaf (⊥ : GrothendieckTopology C) A) :=
    preservesFiniteColimits_of_natIso
      (F.sheafPushforwardContinuousCompSheafToPresheafIso A ⊥ ⊥).symm
  exact ⟨fun _ _ _ => preservesColimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (⊥ : GrothendieckTopology C) A)⟩

end Exact

end

/-! ### Tag 08Q7 for a functor with a fully faithful right adjoint -/

section Statement

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {uf : C ⥤ D} {sf : D ⥤ C} (A : Type uA) [Category.{t} A] [Abelian A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **Tag 08Q7 for a functor with a fully faithful right adjoint.** Let `u : C ⥤ D` be a functor
between categories carrying the chaotic topology and let `g` be the induced morphism of topoi, so
that `g⁻¹` is restriction along `u`. If `u` has a fully faithful right adjoint, then inverse image
followed by derived lower shriek is the identity of `D(Ab(D))`: for any left derived functor `L`
of lower shriek, presented by a comparison `α`, and any derived functor `G` of inverse image,
presented by `e`, there is a natural isomorphism `G ⋙ L ≅ 𝟭`. -/
@[stacks 08Q7 "for a functor of chaotic sites with a fully faithful right adjoint, of which the \
  projection to the point of a category with a final object is the case in the source"]
def abelianDerivedLowerShriekInverseImageIso (adj : uf ⊣ sf) [sf.Full] [sf.Faithful]
    (hJ : J = ⊥) (hK : K = ⊥)
    [HasSheafify J A] [HasSheafify K A]
    [uf.IsContinuous J K] [sf.IsContinuous K J]
    [(uf.sheafPushforwardContinuous A J K).IsRightAdjoint]
    (L : DerivedCategory (Sheaf J A) ⥤ DerivedCategory (Sheaf K A))
    (α : DerivedCategory.Qh ⋙ L ⟶
      (uf.sheafPullback A J K).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))]
    (G : DerivedCategory (Sheaf K A) ⥤ DerivedCategory (Sheaf J A))
    (e : DerivedCategory.Qh ⋙ G ≅
      (uf.sheafPushforwardContinuous A J K).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) :
    G ⋙ L ≅ 𝟭 _ := by
  subst hJ hK
  have hff := fullyFaithfulSheafPushforwardContinuous A ⊥ ⊥ adj
  have _ : (uf.sheafPushforwardContinuous A ⊥ ⊥).Full := hff.full
  have _ : (uf.sheafPushforwardContinuous A ⊥ ⊥).Faithful := hff.faithful
  have _ := preservesFiniteLimits_sheafPushforwardContinuous_bot A sf
  have _ := preservesFiniteColimits_sheafPushforwardContinuous_bot A sf
  exact derivedCompositeOfExactRightAdjoint (uf.sheafAdjunctionContinuous A ⊥ ⊥)
    (Adjunction.sheafPushforwardContinuous (E := A) adj ⊥ ⊥) L α G e

end Statement

end Stacks.ChaoticSite

end
