module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Presheaf.AlgebraicStructure.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LeftAdjoint
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek along a continuous functor that has a left adjoint

Let `G : C ⥤ D` be a continuous functor of sites which admits a left adjoint `W`. The
lower-shriek functor on abelian sheaves along `G` is then computable from `W`: restricting a
presheaf along `W` is a left Kan extension along `G`, so lower shriek commutes with passage to
underlying sheaves of sets, and it is exact. When `W` is in addition cocontinuous, the two
functors of the pair identify with the inverse- and direct-image functors attached to `W`, so
the geometric morphism of topoi defined by `G` is the one defined by `W` with the roles of the
two functors exchanged.

## Main results

* `Stacks.Sites.LowerShriek.lowerShriek_comp_forget_iso`: lower shriek commutes with passage to
  the underlying sheaf of sets.
* `Stacks.Sites.LowerShriek.lowerShriek_exact`: lower shriek on abelian sheaves is exact.
* `Stacks.Sites.LowerShriek.lowerShriek_iso_sheafPullbackCocontinuous`: lower shriek along `G`
  is the inverse image attached to the cocontinuous left adjoint `W`.
* `Stacks.Sites.LowerShriek.sheafPushforwardContinuous_iso_sheafPushforwardCocontinuous`: the
  inverse image along `G` is the direct image attached to `W`.

## Implementation notes

Lower shriek is Mathlib's constructed left adjoint
`Functor.sheafPullbackConstruction.sheafPullback`, the sheafification of the left Kan extension
along `G.op`. The identification with restriction along `W.op`, for a left adjoint `W` of `G`, is
uniqueness of left adjoints, applied to the adjunction obtained from `W ⊣ G` by whiskering. The
source also assumes that `G` is cocontinuous, in order to package the two functors as a morphism
of topoi; none of the four conclusions uses that hypothesis, so only continuity is kept — and the
two conclusions that compare `g_!` with a functor built the same way do not use even that.

Abelian groups and sets are taken in the universe `max u₂ v₂` of the target site `(D, K)`. There
Mathlib's plus construction supplies, as instances, everything the conclusions need about
sheafification for `K`: `HasWeakSheafify K AddCommGrpCat` and `HasWeakSheafify K (Type _)` (the
latter is Mathlib's `HasSheafify J (Type (max u v))`), the left exactness `HasSheafify`, and
`K.PreservesSheafification (forget AddCommGrpCat)`, the compatibility of the forgetful functor
with sheafification; `HasSheafCompose` on either site is the unconditional instance for a
corepresentable forgetful functor. So none of those is a hypothesis here. Fixing the universe
costs no generality: outside it the sheafifications that the conclusions *name* need not exist,
which is precisely why they previously had to be assumed.

The Kan extensions along `G.op` and `W.op` out of which Mathlib builds `g_!` and `h_*` are not
assumed either, and for a reason that has nothing to do with size: a functor that is a left
adjoint has left Kan extensions along it, and one that is a right adjoint has pointwise right Kan
extensions along it, because the comma categories indexing the (co)limits then have initial
objects. Those are `CategoryTheory.Functor.hasLeftKanExtension_of_isLeftAdjoint` and
`CategoryTheory.Functor.hasPointwiseRightKanExtensionAt_of_isRightAdjoint` below, and `W ⊣ G`
supplies both hypotheses by `Adjunction.op`. So the source's `u` having a left adjoint is the only
thing part (1) needs, and it is stated as `G.IsRightAdjoint`, which unfolds to exactly that. In
part (2) the left adjoint has to be named, so the adjunction `W ⊣ G` is an explicit argument;
`G.IsRightAdjoint` and `W.IsLeftAdjoint` are then redundant — each follows from that argument —
and are present only because the statement's own instance arguments are elaborated before the
explicit one is in scope.

## References

* [Stacks Project, Tag 08P3](https://stacks.math.columbia.edu/tag/08P3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₃ v₄ v₅ u₃ u₄ u₅

/-- A functor that is a left adjoint has left Kan extensions along it, with values in any
category and with no size hypothesis: restriction along a left adjoint `L` is itself a right
adjoint, so each category of left extensions along `L`, being a structured arrow category over
that restriction functor, has an initial object. -/
instance hasLeftKanExtension_of_isLeftAdjoint {X : Type u₃} [Category.{v₃} X] {Y : Type u₄}
    [Category.{v₄} Y] {A : Type u₅} [Category.{v₅} A] (L : X ⥤ Y) [L.IsLeftAdjoint] (F : X ⥤ A) :
    L.HasLeftKanExtension F :=
  have h : ((whiskeringLeft X Y A).obj L).IsRightAdjoint :=
    ⟨_, ⟨Adjunction.whiskerLeft A (Adjunction.ofIsLeftAdjoint L)⟩⟩
  isRightAdjoint_iff_hasInitial_structuredArrow.mp h F

/-- A functor that is a right adjoint has pointwise right Kan extensions along it, with values in
any category and with no size hypothesis: the category indexing the limit which computes the
extension at an object has an initial object. -/
instance hasPointwiseRightKanExtensionAt_of_isRightAdjoint {X : Type u₃} [Category.{v₃} X]
    {Y : Type u₄} [Category.{v₄} Y] {A : Type u₅} [Category.{v₅} A] (L : X ⥤ Y) [L.IsRightAdjoint]
    (F : X ⥤ A) (Z : Y) : L.HasPointwiseRightKanExtensionAt F Z :=
  have : Limits.HasInitial (StructuredArrow Z L) :=
    isRightAdjoint_iff_hasInitial_structuredArrow.mp ‹L.IsRightAdjoint› Z
  Limits.hasLimit_of_domain_hasInitial

end CategoryTheory.Functor

namespace Stacks.Sites.LowerShriek

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {G : C ⥤ D} {W : D ⥤ C} [G.IsContinuous J K]


/-- **Stacks 08P3 (1), compatibility with underlying sheaves.** When `G` has a left adjoint,
lower shriek on abelian sheaves agrees naturally, on underlying sheaves of sets, with lower
shriek on sheaves of sets. -/
@[stacks 08P3 "part (1), compatibility with underlying sheaves of sets"]
noncomputable def lowerShriek_comp_forget_iso [G.IsRightAdjoint] :
    Functor.sheafPullbackConstruction.sheafPullback G AddCommGrpCat.{max u₂ v₂} J K ⋙
          sheafCompose K (forget AddCommGrpCat.{max u₂ v₂}) ≅
        sheafCompose J (forget AddCommGrpCat.{max u₂ v₂}) ⋙
        Functor.sheafPullbackConstruction.sheafPullback G (Type (max u₂ v₂)) J K := by
  have : K.PreservesSheafification (forget AddCommGrpCat.{max u₂ v₂}) :=
    have : ∀ X : D, PreservesColimitsOfShape (K.Cover X)ᵒᵖ
        (forget AddCommGrpCat.{max u₂ v₂}) := fun X =>
      Stacks.ConstantSheaf.preservesColimitsOfShape_forget_addCommGrp_of_univLE K X
    GrothendieckTopology.instPreservesSheafification K (forget AddCommGrpCat.{max u₂ v₂})
  let adj := Adjunction.ofIsRightAdjoint G
  let restrictionAb :=
    (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{max u₂ v₂}).obj (Functor.leftAdjoint G).op
  let restrictionType :=
    (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ (Type (max u₂ v₂))).obj (Functor.leftAdjoint G).op
  let forgetC := (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{max u₂ v₂} (Type (max u₂ v₂))).obj
    (forget AddCommGrpCat.{max u₂ v₂})
  let forgetD := (Functor.whiskeringRight Dᵒᵖ AddCommGrpCat.{max u₂ v₂} (Type (max u₂ v₂))).obj
    (forget AddCommGrpCat.{max u₂ v₂})
  let eAb : restrictionAb ≅ G.op.lan :=
    Adjunction.leftAdjointUniq (Adjunction.whiskerLeft AddCommGrpCat.{max u₂ v₂} adj.op)
      (G.op.lanAdjunction AddCommGrpCat.{max u₂ v₂})
  let eType : restrictionType ≅ G.op.lan :=
    Adjunction.leftAdjointUniq (Adjunction.whiskerLeft (Type (max u₂ v₂)) adj.op)
      (G.op.lanAdjunction (Type (max u₂ v₂)))
  let eForget : restrictionAb ⋙ forgetD ≅ forgetC ⋙ restrictionType := by
    refine NatIso.ofComponents (fun F => Iso.refl _) ?_
    intro F₁ F₂ f
    ext X
    rfl
  let e := Functor.isoWhiskerRight eAb.symm forgetD ≪≫ eForget ≪≫
    Functor.isoWhiskerLeft forgetC eType
  exact (Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u₂ v₂})
    (Functor.isoWhiskerRight e.symm (presheafToSheaf K (Type (max u₂ v₂))) ≪≫
      Functor.isoWhiskerLeft G.op.lan
        (sheafComposeNatIso K (forget AddCommGrpCat.{max u₂ v₂})
          (sheafificationAdjunction K AddCommGrpCat.{max u₂ v₂})
          (sheafificationAdjunction K (Type (max u₂ v₂)))))).symm

/-- **Stacks 08P3 (2), the lower shriek.** If the left adjoint `W` is cocontinuous, lower
shriek along `G` is naturally isomorphic to the inverse-image functor associated to `W`. -/
@[stacks 08P3 "part (2), lower shriek equals inverse image"]
noncomputable def lowerShriek_iso_sheafPullbackCocontinuous [G.IsRightAdjoint]
    [W.IsCocontinuous K J] (adj : W ⊣ G) :
    Functor.sheafPullbackConstruction.sheafPullback G AddCommGrpCat.{max u₂ v₂} J K ≅
      W.sheafPullbackCocontinuous AddCommGrpCat.{max u₂ v₂} K J := by
  let e : (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{max u₂ v₂}).obj W.op ≅ G.op.lan :=
    Adjunction.leftAdjointUniq (Adjunction.whiskerLeft AddCommGrpCat.{max u₂ v₂} adj.op)
      (G.op.lanAdjunction AddCommGrpCat.{max u₂ v₂})
  exact (Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{max u₂ v₂})
    (Functor.isoWhiskerRight e (presheafToSheaf K AddCommGrpCat.{max u₂ v₂}))).symm

/-- **Stacks 08P3 (2), the inverse image.** If the left adjoint `W` is cocontinuous, inverse
image along `G` is naturally isomorphic to the direct-image functor associated to `W`. -/
@[stacks 08P3 "part (2), inverse image equals direct image"]
noncomputable def sheafPushforwardContinuous_iso_sheafPushforwardCocontinuous [W.IsLeftAdjoint]
    [W.IsCocontinuous K J] (adj : W ⊣ G) :
    G.sheafPushforwardContinuous AddCommGrpCat.{max u₂ v₂} J K ≅
      W.sheafPushforwardCocontinuous AddCommGrpCat.{max u₂ v₂} K J :=
  (adj.sheafPushforwardCocontinuousIso (A := AddCommGrpCat.{max u₂ v₂}) (J := K) (K := J)).symm

open CategoryTheory.Adjunction in
/-- **Stacks 08P3 (1), exactness.** The lower-shriek functor on abelian sheaves associated to
`G` is exact. -/
@[stacks 08P3 "part (1), exactness"]
theorem lowerShriek_exact [G.IsRightAdjoint] :
    exactFunctor (Sheaf J AddCommGrpCat.{max u₂ v₂}) (Sheaf K AddCommGrpCat.{max u₂ v₂})
      (Functor.sheafPullbackConstruction.sheafPullback G AddCommGrpCat.{max u₂ v₂} J K) := by
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · let h :=
      nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous
        AddCommGrpCat.{max u₂ v₂} J K (Adjunction.ofIsRightAdjoint G)
    let : HasFiniteLimits AddCommGrpCat.{max u₂ v₂} := inferInstance
    let : PreservesFiniteLimits (presheafToSheaf K AddCommGrpCat.{max u₂ v₂}) := inferInstance
    have : PreservesFiniteLimits
        (sheafToPresheaf J AddCommGrpCat.{max u₂ v₂} ⋙
          (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ AddCommGrpCat.{max u₂ v₂}).obj
            (Functor.leftAdjoint G).op ⋙
          presheafToSheaf K AddCommGrpCat.{max u₂ v₂}) := h.2.1
    let e := Adjunction.leftAdjointUniq h.1.some
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
        AddCommGrpCat.{max u₂ v₂} J K)
    exact preservesFiniteLimits_of_natIso e
  · let : PreservesColimitsOfSize.{0, 0}
        (Functor.sheafPullbackConstruction.sheafPullback G AddCommGrpCat.{max u₂ v₂} J K) :=
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
        AddCommGrpCat.{max u₂ v₂} J K).leftAdjoint_preservesColimits
    exact inferInstance

end Stacks.Sites.LowerShriek

end
