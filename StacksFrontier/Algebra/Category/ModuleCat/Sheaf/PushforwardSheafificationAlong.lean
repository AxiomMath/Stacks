module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification

/-!
# Restriction along a cocontinuous functor commutes with sheafification along a ring map

Let `G : C ⥤ D` be continuous and cocontinuous for topologies `J` on `C` and `K` on `D`, let
`R` be a sheaf of rings on `(D, K)` and let `α : R₀ ⟶ R` be a locally bijective morphism from a
presheaf of rings. Mathlib's `PresheafOfModules.sheafification α` carries a presheaf of
`R₀`-modules `P` to a sheaf of `R`-modules `P^#`. Restriction of sections along `G` carries `P`
to a presheaf of modules over `G^*R₀` and `P^#` to a sheaf of modules over `G^*R`, and the
restricted ring map `G^*α : G^*R₀ ⟶ G^*R` is again locally bijective. This file identifies the
two ways of going around:

`(G^*P)^# ≅ G^*(P^#)`,

naturally in `P`, the left-hand sheafification being the one along `G^*α`.

For `α = 𝟙` this is
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso`. The general ring
map is what the conormal sequence of a presentation needs, since its terms are sheafified along
the locally bijective map from the image presheaf `A/I` to the target sheaf of rings.

## Main definitions

* `Stacks.SheafOfModules.PushforwardSheafification.whiskerRingMap`: the restricted ring map
  `G^*α`.
* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardUnitAlong`: the restriction of
  the sheafification unit `P ⟶ P^#`.
* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHomAlong`: the comparison
  morphism `(G^*P)^# ⟶ G^*(P^#)` it classifies.
* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIsoAlong`: the natural
  isomorphism `G^* ⋙ (-)^# ≅ (-)^# ⋙ G^*`.

## Main results

* `Stacks.SheafOfModules.PushforwardSheafification.isIso_pushforwardSheafifyHomAlong`: the
  comparison morphism is an isomorphism. The restricted unit is locally bijective because `G` is
  cocontinuous, so it exhibits its target as the sheafification of its source.
* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHomAlong_naturality`: the
  comparison morphism is natural in the presheaf.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO), the morphism of topoi
  attached to a continuous and cocontinuous functor.
* [Stacks Project, Tag 00WW](https://stacks.math.columbia.edu/tag/00WW), sheafification.
-/

@[expose] public section

open CategoryTheory

universe w t v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} (G : C ⥤ D)
  [G.IsContinuous J K] [G.IsCocontinuous J K] {R₀ : Dᵒᵖ ⥤ RingCat.{t}} {R : Sheaf K RingCat.{t}}
  (α : R₀ ⟶ R.obj)

/-- The ring map `G^*α : G^*R₀ ⟶ G^*R` obtained by restricting `α : R₀ ⟶ R` along `G`. -/
abbrev whiskerRingMap : G.op ⋙ R₀ ⟶ (pushforwardRingSheaf J G R).obj :=
  Functor.whiskerLeft G.op α

/-- Restricting a locally injective ring map along a cocontinuous functor keeps it locally
injective. -/
instance [Presheaf.IsLocallyInjective K α] :
    Presheaf.IsLocallyInjective J (whiskerRingMap J G α) :=
  Presheaf.isLocallyInjective_whisker J K G α

/-- Restricting a locally surjective ring map along a cocontinuous functor keeps it locally
surjective. -/
instance [Presheaf.IsLocallySurjective K α] :
    Presheaf.IsLocallySurjective J (whiskerRingMap J G α) :=
  Presheaf.isLocallySurjective_whisker J K G α

variable [Presheaf.IsLocallyInjective K α] [Presheaf.IsLocallySurjective K α]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sheafification unit `P ⟶ P^#` along `α`, restricted along `G`: a morphism from the
restriction of `P` to the restriction of scalars along `G^*α` of the restriction of `P^#`. -/
noncomputable def pushforwardUnitAlong (P : PresheafOfModules.{w} R₀) :
    (PresheafOfModules.pushforward₀.{w} G R₀).obj P ⟶
      (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
          PresheafOfModules.restrictScalars (whiskerRingMap J G α)).obj
        ((sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} α).obj P)) where
  app V := ((PresheafOfModules.sheafificationAdjunction.{w} α).unit.app P).app (G.op.obj V)
  naturality f :=
    ((PresheafOfModules.sheafificationAdjunction.{w} α).unit.app P).naturality (G.op.map f)

omit [G.IsCocontinuous J K] in
/-- The restricted unit is the restriction of the sheafification unit. -/
theorem pushforwardUnitAlong_eq (P : PresheafOfModules.{w} R₀) :
    (PresheafOfModules.toPresheaf (G.op ⋙ R₀)).map (pushforwardUnitAlong J G α P) =
      Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P.presheaf) :=
  rfl

omit [G.IsCocontinuous J K] in
/-- The restricted unit is natural in the presheaf of modules. -/
theorem pushforwardUnitAlong_naturality {P Q : PresheafOfModules.{w} R₀} (f : P ⟶ Q) :
    (PresheafOfModules.pushforward₀.{w} G R₀).map f ≫ pushforwardUnitAlong J G α Q =
      pushforwardUnitAlong J G α P ≫
        (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
            PresheafOfModules.restrictScalars (whiskerRingMap J G α)).map
          ((sheafPushforwardFunctor.{w} J G R).map
            ((PresheafOfModules.sheafification.{w} α).map f)) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  exact congrArg (fun t => t.app (G.op.obj V))
    ((PresheafOfModules.sheafificationAdjunction.{w} α).unit.naturality f)

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The comparison morphism `(G^*P)^# ⟶ G^*(P^#)` classified by the restricted unit, the
left-hand sheafification being the one along `G^*α`. -/
noncomputable def pushforwardSheafifyHomAlong (P : PresheafOfModules.{w} R₀) :
    (PresheafOfModules.sheafification.{w} (whiskerRingMap J G α)).obj
        ((PresheafOfModules.pushforward₀.{w} G R₀).obj P) ⟶
      (sheafPushforwardFunctor.{w} J G R).obj ((PresheafOfModules.sheafification.{w} α).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (whiskerRingMap J G α)).symm
    (pushforwardUnitAlong J G α P)

/-- **The comparison morphism `(G^*P)^# ⟶ G^*(P^#)` is an isomorphism** for `G` cocontinuous:
the restricted unit is locally bijective, by cocontinuity, so its target is the sheafification
of its source. -/
instance isIso_pushforwardSheafifyHomAlong (P : PresheafOfModules.{w} R₀) :
    IsIso (pushforwardSheafifyHomAlong J G α P) :=
  SliceSheafification.isIso_sheafificationHomEquiv_symm.{w}
    (R₀ := G.op ⋙ R₀) (Rs := pushforwardRingSheaf J G R)
    (P := (PresheafOfModules.pushforward₀.{w} G R₀).obj P)
    (T := (sheafPushforwardFunctor.{w} J G R).obj
      ((PresheafOfModules.sheafification.{w} α).obj P))
    (whiskerRingMap J G α) (pushforwardUnitAlong J G α P)
    (Presheaf.isLocallyInjective_whisker J K G (CategoryTheory.toSheafify K P.presheaf))
    (Presheaf.isLocallySurjective_whisker J K G (CategoryTheory.toSheafify K P.presheaf))

/-- **The comparison morphism `(G^*P)^# ⟶ G^*(P^#)` is natural in the presheaf.** -/
theorem pushforwardSheafifyHomAlong_naturality {P Q : PresheafOfModules.{w} R₀} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification.{w} (whiskerRingMap J G α)).map
        ((PresheafOfModules.pushforward₀.{w} G R₀).map f) ≫
          pushforwardSheafifyHomAlong J G α Q =
      pushforwardSheafifyHomAlong J G α P ≫ (sheafPushforwardFunctor.{w} J G R).map
        ((PresheafOfModules.sheafification.{w} α).map f) := by
  have h (P : PresheafOfModules.{w} R₀) : pushforwardSheafifyHomAlong J G α P =
      ((PresheafOfModules.sheafificationAdjunction.{w} (whiskerRingMap J G α)).homEquiv _ _).symm
        (pushforwardUnitAlong J G α P) := by
    rw [sheafificationAdjunction_homEquiv_eq]; rfl
  rw [h P, h Q]
  exact ((PresheafOfModules.sheafificationAdjunction.{w}
        (whiskerRingMap J G α)).homEquiv_naturality_left_symm
      ((PresheafOfModules.pushforward₀.{w} G R₀).map f)
        (pushforwardUnitAlong J G α Q)).symm.trans
    ((congrArg ((PresheafOfModules.sheafificationAdjunction.{w}
          (whiskerRingMap J G α)).homEquiv _ _).symm
        (pushforwardUnitAlong_naturality J G α f)).trans
      ((PresheafOfModules.sheafificationAdjunction.{w}
          (whiskerRingMap J G α)).homEquiv_naturality_right_symm
        (pushforwardUnitAlong J G α P)
        ((sheafPushforwardFunctor.{w} J G R).map
          ((PresheafOfModules.sheafification.{w} α).map f))))

/-- **Sheafification along a locally bijective ring map commutes with restriction along a
continuous and cocontinuous functor of sites**, as an isomorphism of functors:
`G^* ⋙ (-)^# ≅ (-)^# ⋙ G^*`, the left-hand sheafification being the one along `G^*α`. -/
noncomputable def pushforwardSheafifyNatIsoAlong :
    PresheafOfModules.pushforward₀.{w} G R₀ ⋙
        PresheafOfModules.sheafification.{w} (whiskerRingMap J G α) ≅
      PresheafOfModules.sheafification.{w} α ⋙ sheafPushforwardFunctor.{w} J G R :=
  NatIso.ofComponents (fun P ↦ asIso (pushforwardSheafifyHomAlong J G α P))
    (fun f ↦ pushforwardSheafifyHomAlong_naturality J G α f)

end Stacks.SheafOfModules.PushforwardSheafification

end
