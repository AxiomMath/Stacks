module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCore.Tactic.EgaSgaAttribute

/-! # The morphism of topoi attached to a cocontinuous functor

## Main results

* `gStar`, `gInv`: for a cocontinuous functor `u : C ⥤ D` between sites, the direct image
  `g_* = {}_su` and the pullback `g^{-1} = (u^p -)^#` between the categories of sheaves of
  sets.
* `main_adjunction00XO`, `main_left_exact`: `g^{-1}` is left adjoint to `g_*` and is left
  exact, so the pair is a morphism of topoi `Sh(C) ⟶ Sh(D)` (Stacks 00XO).

Tags covered: 00XO.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable (C : Type u) [SmallCategory C] (D : Type u) [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) [u.IsCocontinuous J K]

/-- The direct image functor `g_* = {}_su : Sh(C) ⥤ Sh(D)` of the morphism of topoi attached
to a cocontinuous functor `u`. -/
@[sga "4 IV 4.7"]
noncomputable def gStar : Sheaf J (Type u) ⥤ Sheaf K (Type u) :=
  u.sheafPushforwardCocontinuous (Type u) J K

/-- The pullback functor `g^{-1} = (u^p -)^# : Sh(D) ⥤ Sh(C)` of the morphism of topoi attached
to a cocontinuous functor `u`: restrict a sheaf to a presheaf on `C` along `u.op`, then
sheafify. -/
@[sga "4 III 2.3"]
noncomputable def gInv : Sheaf K (Type u) ⥤ Sheaf J (Type u) :=
  sheafToPresheaf K (Type u) ⋙
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj u.op ⋙
    presheafToSheaf J (Type u)

/-- **Stacks 00XO.** For a cocontinuous functor `u`, the functor `g^{-1}` is left adjoint
to `g_*`. -/
@[stacks 00XO,
  sga "4 III 2.3" "3), special case",
  sga "4 III 2.6" "partial",
  sga "4 III 2.7" "partial",
  sga "4 III 4.4" "3), special case",
  sga "4 III 5.3" "partial",
  sga "4 IV 4.7" "partial",
  sga "4 IV 4.9.1" "For cocontinuous u"]
theorem main_adjunction00XO :
    Nonempty (gInv C D J K u ⊣ gStar C D J K u) :=
  ⟨Adjunction.restrictFullyFaithful
    ((u.op.ranAdjunction (Type u)).comp (sheafificationAdjunction J (Type u)))
    (fullyFaithfulSheafToPresheaf K (Type u))
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans
      (u.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type u) J K).symm)⟩

omit [u.IsCocontinuous J K] in
/-- **Stacks 00XO.** The functor `g^{-1}` is left exact; together with the adjunction this makes
`(g_*, g^{-1})` a morphism of topoi `Sh(C) ⟶ Sh(D)`. -/
@[stacks 00XO, sga "4 III 2.3" "1)"]
theorem main_left_exact :
    PreservesFiniteLimits (gInv C D J K u) := by
  unfold gInv
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj u.op ⋙ presheafToSheaf J (Type u)) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _
