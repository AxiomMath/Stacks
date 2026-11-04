module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf pullback along a cocontinuous functor

Let `u : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)`.

Mathlib already has the *pushforward* `u.sheafPushforwardCocontinuous`, which for
cocontinuous `u` is Stacks' `{}_s u : Sh(C) ⥤ Sh(D)`, obtained from the right Kan
extension `u.op.ran`. Mathlib's `Mathlib/CategoryTheory/Sites/CoverLifting.lean` leaves
as an explicit `TODO` both the construction of the left adjoint of that pushforward,
Stacks' `g^{-1} : G ↦ (u^p G)^#`, and the comparison of that left adjoint with plain
restriction when `u` is also continuous. This file supplies both, together with the
exactness statement, and the formulas available when `u` has a right adjoint.

## Main declarations

* `CategoryTheory.Functor.sheafPullbackCocontinuous`: the functor `Sh(D) ⥤ Sh(C)`,
  `G ↦ (u^p G)^#`, i.e. restriction along `u.op` followed by sheafification.
* `CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous`,
  `preservesFiniteColimits_sheafPullbackCocontinuous`,
  `preservesFiniteLimits_sheafPullbackCocontinuous` (Stacks 00XL): it is left adjoint to
  `u.sheafPushforwardCocontinuous`, and it is exact.
* `CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` and
  `sheafPullbackCocontinuousObjObjIso` (Stacks 00XR (1)): if `u` is moreover continuous,
  the sheafification is unnecessary — the pullback is plain restriction, so
  `g^{-1}(G)(U) = G(u(U))`.
* `CategoryTheory.Functor.preservesLimits_sheafPushforwardContinuous`,
  `preservesColimits_sheafPushforwardContinuous` (Stacks 00XR (3)): `g^{-1}` commutes
  with arbitrary limits and colimits.
* `CategoryTheory.Functor.ranIsoRestrictionOfAdjunction`,
  `sheafPushforwardCocontinuousIsoRestriction` (Stacks 00XX (1)): if `u` has a right
  adjoint `v`, then `g_*F = v^p F`, i.e. `(g_*F)(V) = F(v(V))`.
* `CategoryTheory.Functor.restrictionIsoLanOfAdjunction`,
  `sheafPullbackCocontinuousIsoLan` (Stacks 00XX (2)): with the same `v`,
  `g^{-1}G = (v_p G)^#`.
* `CategoryTheory.Functor.sheafPullbackAdjunctionOfAdjunction` and
  `isRightAdjoint_sheafPullback_of_continuous_leftAdjoint`: if `u ⊣ v` with both `u` and `v`
  continuous, the lower shriek `(v_p\ )^#` along `v` is itself a right adjoint, its left
  adjoint being the lower shriek `(u_p\ )^#` along `u`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits Opposite

universe v₁ v₂ w w' u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
variable (A : Type w) [Category.{w'} A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The sheaf pullback along `u : C ⥤ D`, Stacks' `G ↦ (u^p G)^#`: restrict a `K`-sheaf on
`D` along `u.op` to a presheaf on `C`, then sheafify for `J`.

Mathlib's `Mathlib/CategoryTheory/Sites/CoverLifting.lean` names this functor
`sheafPullbackCocontinuous` in a `TODO` comment but does not construct it. -/
noncomputable def sheafPullbackCocontinuous [HasWeakSheafify J A] :
    Sheaf K A ⥤ Sheaf J A :=
  sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⋙ presheafToSheaf J A

section Cocontinuous

variable [u.IsCocontinuous J K] [HasWeakSheafify J A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]

/-- **Stacks 00XL**, the adjunction. For a cocontinuous functor `u : C ⥤ D` between
sites, the functor `Sh(D) ⥤ Sh(C)`, `G ↦ (u^p G)^#`, is left adjoint to the pushforward
`{}_s u = u.sheafPushforwardCocontinuous`.

This is Stacks' chain of bijections: restriction along `u.op` is left adjoint to the
right Kan extension `u.op.ran`, whose restriction to sheaves is
`u.sheafPushforwardCocontinuous`, and sheafification is left adjoint to the inclusion of
sheaves into presheaves. -/
@[stacks 00XL, sga "4 III 5.3" "more general", sga "4 IV 4.6.1" "partial", sga "4 IV 4.7" "partial"]
noncomputable def sheafAdjunctionPullbackCocontinuous :
    u.sheafPullbackCocontinuous A J K ⊣ u.sheafPushforwardCocontinuous A J K :=
  Adjunction.restrictFullyFaithful
    ((u.op.ranAdjunction A).comp (sheafificationAdjunction J A))
    (fullyFaithfulSheafToPresheaf K A)
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans
      (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm)

/-- For a cocontinuous `u`, the functor `G ↦ (u^p G)^#` is a left adjoint, namely the left
half of `Functor.sheafAdjunctionPullbackCocontinuous`. -/
instance isLeftAdjoint_sheafPullbackCocontinuous :
    (u.sheafPullbackCocontinuous A J K).IsLeftAdjoint :=
  (u.sheafAdjunctionPullbackCocontinuous A J K).isLeftAdjoint

/-- **Stacks 00XL**, right exactness. `G ↦ (u^p G)^#` is a left adjoint, hence preserves
all colimits; in particular it is right exact. -/
@[stacks 00XL, sga "4 III 2.3" "clause 1"]
instance preservesFiniteColimits_sheafPullbackCocontinuous :
    PreservesFiniteColimits (u.sheafPullbackCocontinuous A J K) :=
  inferInstance

/-- **Stacks 00XL**, left exactness. `G ↦ (u^p G)^#` is the composite of three left exact
functors: the inclusion `Sh(D) ⥤ PSh(D)` (which creates limits), restriction along `u.op`
(limits of presheaves are computed pointwise), and sheafification, which is left exact by
Stacks 00WJ — here the `HasSheafify J A` hypothesis, whose `isLeftExact` field is exactly
that statement. -/
@[stacks 00XL]
instance preservesFiniteLimits_sheafPullbackCocontinuous
    [HasFiniteLimits A] [HasSheafify J A] :
    PreservesFiniteLimits (u.sheafPullbackCocontinuous A J K) := by
  have h₁ : PreservesFiniteLimits ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have h₂ := comp_preservesFiniteLimits ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op)
    (presheafToSheaf J A)
  exact comp_preservesFiniteLimits (sheafToPresheaf K A) _

end Cocontinuous

section ContinuousCocontinuous

variable [u.IsCocontinuous J K] [u.IsContinuous J K] [HasWeakSheafify J A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]

/-- **Stacks 00XR (1).** If `u` is both cocontinuous and continuous then the
sheafification in `g^{-1} = (u^p\ )^#` is unnecessary: the sheaf pullback is naturally
isomorphic to plain restriction along `u.op`, so `g^{-1}(G)(U) = G(u(U))`.

Both functors are left adjoint to `u.sheafPushforwardCocontinuous` — the first by
`sheafAdjunctionPullbackCocontinuous` (Stacks 00XL), the second by Mathlib's
`sheafAdjunctionCocontinuous` — so they agree by uniqueness of left adjoints.

See `sheafPullbackCocontinuousObjObjIso` for the displayed formula itself. Mathlib's
`CoverLifting.lean` records this comparison as a `TODO`. -/
@[stacks 00XR "(1)", sga "4 III 2.7" "more general"]
noncomputable def sheafPullbackCocontinuousIsoSheafPushforwardContinuous :
    u.sheafPullbackCocontinuous A J K ≅ u.sheafPushforwardContinuous A J K :=
  Adjunction.leftAdjointUniq
    (u.sheafAdjunctionPullbackCocontinuous A J K)
    (u.sheafAdjunctionCocontinuous A J K)

/-- **Stacks 00XR (1)**, the displayed formula `g^{-1}(G)(U) = G(u(U))`.

Composing `sheafPullbackCocontinuousIsoSheafPushforwardContinuous` — which removes the
sheafification — with the fact that `u.sheafPushforwardContinuous` is restriction along
`u.op`, so that its sections over `U` are literally `G(u(U))`. -/
@[stacks 00XR "(1)"]
noncomputable def sheafPullbackCocontinuousObjObjIso (G : Sheaf K A) (U : C) :
    ((u.sheafPullbackCocontinuous A J K).obj G).obj.obj (Opposite.op U) ≅
      G.obj.obj (Opposite.op (u.obj U)) :=
  ((sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (Opposite.op U)).mapIso
    ((u.sheafPullbackCocontinuousIsoSheafPushforwardContinuous A J K).app G)).trans
      (eqToIso (u.sheafPushforwardContinuous_obj_obj_obj A J K G (Opposite.op U)))

/-- **Stacks 00XR (3)**, colimits. `g^{-1}` commutes with arbitrary colimits: by
Mathlib's `sheafAdjunctionCocontinuous` it is a left adjoint, its right adjoint being
`{}_s u = u.sheafPushforwardCocontinuous`. -/
@[stacks 00XR "(3)",
  sga "4 III 2.6" "u* commutes w/ colimits",
  sga "4 III 2.3" "continuous u; colimits", sga "4 IV 4.6.1" "f^* commutes with colim"]
instance preservesColimits_sheafPushforwardContinuous :
    PreservesColimits (u.sheafPushforwardContinuous A J K) :=
  (u.sheafAdjunctionCocontinuous A J K).leftAdjoint_preservesColimits

end ContinuousCocontinuous

section LeftAdjointOfPullback

variable [u.IsContinuous J K] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]

/-- **Stacks 00XR (2).** `g^{-1}` has a left adjoint `g_! = (u_p\ )^#`.

The left adjoint is Mathlib's `sheafPullbackConstruction.sheafPullback`, which is
literally `(u_p\ )^#`: the left Kan extension `u.op.lan = u_p` followed by
sheafification. -/
@[stacks 00XR "(2)",
  sga "4 III 1.3" "1)",
  sga "4 IV 4.9.1" "left adjoint f^s ⊣ f_s",
  sga "4 IV 4.7.4" "sufficiency: F_! exists",
  sga "4 IV 4.6.1" "left adjoint f_!",
  sga "4 IV 4.7" "f̃_! ⊣ f̃^*", sga "4 III 5.3" "more general"]
noncomputable def sheafAdjunctionLowerShriek :
    sheafPullbackConstruction.sheafPullback u A J K ⊣ u.sheafPushforwardContinuous A J K :=
  sheafPullbackConstruction.sheafAdjunctionContinuous u A J K

/-- **Stacks 00XR (3)**, limits. `g^{-1}` commutes with arbitrary limits: it is a right
adjoint, its left adjoint being `g_! = (u_p\ )^#`. -/
@[stacks 00XR "(3)",
  sga "4 III 2.6" "u* commutes w/ limits",
  sga "4 IV 4.6.1" "f^* commutes with lim",
  sga "4 IV 4.7" "f also continuous",
  sga "4 IV 3.1.2" "special case"]
instance preservesLimits_sheafPushforwardContinuous :
    PreservesLimits (u.sheafPushforwardContinuous A J K) :=
  (u.sheafAdjunctionLowerShriek A J K).rightAdjoint_preservesLimits

end LeftAdjointOfPullback

section RightAdjoint

variable {u} {v : D ⥤ C} (adj : u ⊣ v)

/-- Restriction along `u.op` is left adjoint to restriction along `v.op`, whiskering the
adjunction `u ⊣ v` into presheaf categories. -/
noncomputable def whiskeringLeftAdjunctionOfAdjunction :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⊣ (whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op :=
  Adjunction.whiskerLeft A adj.op

/-- If `v` is right adjoint to `u`, the right Kan extension `{}_p u = u.op.ran` *is*
restriction `v^p` along `v.op`: both are right adjoint to restriction along `u.op`. -/
noncomputable def ranIsoRestrictionOfAdjunction
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F] :
    u.op.ran ≅ (whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op :=
  Adjunction.rightAdjointUniq (u.op.ranAdjunction A)
    (whiskeringLeftAdjunctionOfAdjunction A adj)

/-- **Stacks 00XX (1).** Let `u : C ⥤ D` be cocontinuous with right adjoint `v : D ⥤ C`,
and let `g : Sh(C) → Sh(D)` be the associated morphism of topoi. Then for a sheaf `F` on
`C` the sheaf `g_*F` is the presheaf `v^p F`, in other words `(g_*F)(V) = F(v(V))`.

Underlying presheaves are compared because `g_* = {}_s u` lands in sheaves on `D` while
`v^p F = F ∘ v` is a priori only a presheaf; the isomorphism says the latter is the
former, hence a sheaf. -/
@[stacks 00XX "(1)"]
noncomputable def sheafPushforwardCocontinuousIsoRestriction
    [u.IsCocontinuous J K] [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ (whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op :=
  (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).trans
    (isoWhiskerLeft (sheafToPresheaf J A) (ranIsoRestrictionOfAdjunction A adj))

/-- If `v` is right adjoint to `u`, restriction `u^p` along `u.op` *is* the left Kan
extension `v_p = v.op.lan`: both are left adjoint to restriction along `v.op`. -/
@[sga "4 I 5.5" "more general", sga "4 I 5.5.2" "identification v* ≅ u_!"]
noncomputable def restrictionIsoLanOfAdjunction
    [∀ F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F] :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ≅ v.op.lan :=
  Adjunction.leftAdjointUniq (whiskeringLeftAdjunctionOfAdjunction A adj)
    (v.op.lanAdjunction A)

/-- **Stacks 00XX (2).** In the situation of `sheafPushforwardCocontinuousIsoRestriction`,
for a sheaf `G` on `D` we have `g^{-1}G = (v_p G)^#`: the sheaf pullback
`G ↦ (u^p G)^#` agrees with the sheafified left Kan extension along `v.op`. -/
@[stacks 00XX "(2)"]
noncomputable def sheafPullbackCocontinuousIsoLan
    [HasWeakSheafify J A] [∀ F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F] :
    u.sheafPullbackCocontinuous A J K ≅
      sheafToPresheaf K A ⋙ v.op.lan ⋙ presheafToSheaf J A :=
  isoWhiskerLeft (sheafToPresheaf K A)
    (isoWhiskerRight (restrictionIsoLanOfAdjunction A adj) (presheafToSheaf J A))

section ContinuousPair

variable [u.IsContinuous J K] [v.IsContinuous K J] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F] [∀ F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F]

/-- If `v : D ⥤ C` is continuous and has a continuous left adjoint `u : C ⥤ D`, then the
lower shriek `(v_p\ )^#` along `v` has itself a left adjoint, namely the lower shriek
`(u_p\ )^#` along `u`.

Indeed `(v_p\ )^#` is restriction along `u`, because both are left adjoint to restriction
along `v` on sheaves — this is the sheaf-level form of `restrictionIsoLanOfAdjunction` — and
restriction along `u` is the right half of `sheafAdjunctionLowerShriek` for `u`. -/
noncomputable def sheafPullbackAdjunctionOfAdjunction :
    sheafPullbackConstruction.sheafPullback u A J K ⊣
      sheafPullbackConstruction.sheafPullback v A K J :=
  (u.sheafAdjunctionLowerShriek A J K).ofNatIsoRight
    (Adjunction.leftAdjointUniq
      (sheafPullbackConstruction.sheafAdjunctionContinuous v A K J)
      (adj.sheafPushforwardContinuous J K)).symm

include adj in
/-- The inverse image `g^{-1} = (v_p\ )^#` of a continuous functor `v : D ⥤ C` which has a
continuous left adjoint is a right adjoint, so sheaves on `(D, K)` have a lower shriek along
`v`. -/
theorem isRightAdjoint_sheafPullback_of_continuous_leftAdjoint :
    (sheafPullbackConstruction.sheafPullback v A K J).IsRightAdjoint :=
  (sheafPullbackAdjunctionOfAdjunction A J K adj).isRightAdjoint

end ContinuousPair

end RightAdjoint

end CategoryTheory.Functor
