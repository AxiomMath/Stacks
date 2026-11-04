module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact

/-!
# Direct image of sheaves of `Λ`-modules is the lift of direct image of abelian sheaves

Let `F : C ⥤ D` be a continuous functor of sites and `Λ` a ring. Restriction of sheaves along
`F`, with coefficients in `Λ`-modules, has the same underlying abelian sheaf as restriction of
the underlying abelian sheaf, and the same action of `Λ` on it; so it is the lift
`Stacks.ModuleCatLift.moduleLift` of restriction of abelian sheaves. Consequently any left
adjoint of it is the lift of any left adjoint of restriction of abelian sheaves.

## Main definitions

* `Stacks.ModuleCatLift.sheafPushforwardContinuousIsoModuleLift` — the identification of the
  direct image of sheaves of `Λ`-modules with the lift of the direct image of abelian sheaves.
* `Stacks.ModuleCatLift.leftAdjointIsoModuleLift` — a left adjoint of the former is the lift of
  a left adjoint of the latter.

## Implementation notes

The identification is the identity on underlying abelian sheaves: both are precomposition with
`F.op` followed by the forgetful functor, and the actions of a scalar agree on the nose. It is
built from `Stacks.ModuleCatLift.sheafHomOfScalarComm` applied to identities, whose
compatibility condition then holds by `rfl`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁ u₂ v₂

namespace Stacks.ModuleCatLift

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- **Direct image of sheaves of `Λ`-modules is the lift of direct image of abelian sheaves.**
The two have the same underlying abelian sheaf and the same action of `Λ` on it. -/
public def sheafPushforwardContinuousIsoModuleLift :
    F.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K ≅
      moduleLift Λ K J (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K) :=
  NatIso.ofComponents
    (fun _ =>
      { hom := sheafHomOfScalarComm Λ J (𝟙 _) fun _ => rfl
        inv := sheafHomOfScalarComm Λ J (𝟙 _) fun _ => rfl
        hom_inv_id :=
          (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective rfl
        inv_hom_id :=
          (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective rfl })
    fun _ => (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective rfl

variable {LΛ : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf K (ModuleCat.{w} Λ)}
  {L : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}} [L.Additive]

/-- **A left adjoint of direct image of sheaves of `Λ`-modules is the lift of a left adjoint of
direct image of abelian sheaves.** The lift of an adjunction is an adjunction, and the direct
images correspond by `Stacks.ModuleCatLift.sheafPushforwardContinuousIsoModuleLift`. -/
public def leftAdjointIsoModuleLift
    (adjΛ : LΛ ⊣ F.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K)
    (adj : L ⊣ F.sheafPushforwardContinuous AddCommGrpCat.{w} J K) :
    LΛ ≅ moduleLift Λ J K L :=
  adjΛ.leftAdjointUniq ((moduleLiftAdjunction Λ J K L _ adj).ofNatIsoRight
    (sheafPushforwardContinuousIsoModuleLift Λ F J K).symm)

end Stacks.ModuleCatLift

end
