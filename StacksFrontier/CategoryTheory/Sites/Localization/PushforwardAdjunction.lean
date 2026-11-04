module

public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localization at an object of a site with binary products

Let `(C, J)` be a site with products of pairs of objects and let `U` be an object of `C`.  The
localization functor `j_U : C/U ⥤ C` is the forgetful functor `Over.forget U`.  Stacks 03CE says
that `j_U` then has a *continuous* right adjoint `v : X ↦ X × U / U`, that `v` defines a morphism
of sites `C/U → C` whose associated morphism of topoi is the one induced by `j_U`, and that
consequently `j_{U*}F(X) = F(X × U / U)`.

The first half of the file is the general mechanism, valid for any adjoint pair `u ⊣ v` between
sites.  The pushforward `{}_su` along a cocontinuous `u` is the pushforward `v^s` along a
continuous `v`; this needs no continuity of `u`, because the identification already holds between
the underlying presheaf-valued functors and descends by cancelling the fully faithful inclusion of
sheaves into presheaves.  When `u` too is continuous, precomposition along the two functors is
again an adjoint pair `u^s ⊣ v^s`, and uniqueness of adjoints identifies the pullback `v_s` with
`u^s`.  This is what turns the site-level adjunction `j_U ⊣ v` into the equality of morphisms of
topoi asserted by Stacks 03CE, and it is reused for Stacks 09W9.

## Main results

* `CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso`: for a cocontinuous `u` with a
  continuous right adjoint `v`, `{}_su ≅ v^s`.  This is the sheaf-level form of Stacks 00XX (1).
* `CategoryTheory.Adjunction.sheafPushforwardAdjunction`: for an adjoint pair `u ⊣ v` of
  continuous functors between sites, `u^s` is left adjoint to `v^s`.  This refines
  `CategoryTheory.Functor.whiskeringLeftAdjunctionOfAdjunction` from presheaves to sheaves.
* `CategoryTheory.Adjunction.sheafPullbackIso`: consequently `v_s ≅ u^s`.
* `StacksLocalizationProducts.bijective_left_comp_prodSnd`: the right adjoint of `j_U` is
  `X ↦ X × U / U` (Stacks 03CE(1)).
* `StacksLocalizationProducts.isMorphismOfSites_star`: `v` defines a morphism of sites
  (Stacks 03CE(2), first half).
* `StacksLocalizationProducts.sheafPushforwardOverForgetIso`,
  `StacksLocalizationProducts.sheafPullbackStarIso`: the morphism of topoi attached to `v` is the
  one attached to `j_U` (Stacks 03CE(2), second half).
* `StacksLocalizationProducts.sheafPushforwardObjEquiv`: `j_{U*}F(X) = F(X × U / U)`
  (Stacks 03CE(3)).

Tags covered: 03CE.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory Opposite Limits

universe v₁ v₂ u₁ u₂ v' u'

section AdjointPair

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (A : Type u') [Category.{v'} A]
variable {u : C ⥤ D} {v : D ⥤ C}

/-- For a cocontinuous `u` with a continuous right adjoint `v`, the pushforward `{}_su` attached
to cocontinuity of `u` is the pushforward `v^s` attached to continuity of `v`.

This is the sheaf-level form of Stacks 00XX (1).  Continuity of `u` is not needed: the
identification already holds between the underlying presheaf-valued functors, where it is
`Functor.sheafPushforwardCocontinuousIsoRestriction` against
`Functor.sheafPushforwardContinuousCompSheafToPresheafIso`, and the inclusion `sheafToPresheaf` of
sheaves into presheaves is fully faithful, so it may be cancelled. -/
@[sga "4 III 2.5" "v_* ≅ u_s"]
noncomputable def Adjunction.sheafPushforwardCocontinuousIso (adj : u ⊣ v)
    [u.IsCocontinuous J K] [v.IsContinuous K J]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ≅ v.sheafPushforwardContinuous A K J :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K A)
    ((Functor.sheafPushforwardCocontinuousIsoRestriction A J K adj).trans
      (v.sheafPushforwardContinuousCompSheafToPresheafIso A K J).symm)

/-- If `u ⊣ v` is an adjoint pair of continuous functors between the sites `(C, J)` and `(D, K)`,
then the induced pushforwards on sheaves form an adjoint pair `u^s ⊣ v^s`.

Both pushforwards are precomposition, with `u.op` and with `v.op` respectively, and
precomposition along the two members of an adjoint pair is again an adjoint pair
(`Functor.whiskeringLeftAdjunctionOfAdjunction`); restricting that adjunction from presheaves to
sheaves along the fully faithful inclusions is `Adjunction.restrictFullyFaithful`. -/
@[sga "4 III 1.3" "clause 1), special case"]
noncomputable def Adjunction.sheafPushforwardAdjunction (adj : u ⊣ v)
    [u.IsContinuous J K] [v.IsContinuous K J] :
    u.sheafPushforwardContinuous A J K ⊣ v.sheafPushforwardContinuous A K J :=
  (Functor.whiskeringLeftAdjunctionOfAdjunction A adj).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (v.sheafPushforwardContinuousCompSheafToPresheafIso A K J).symm

/-- For an adjoint pair `u ⊣ v` of continuous functors, the pullback `v_s` on sheaves is the
pushforward `u^s`: both are left adjoint to `v^s`.  In particular `v_s` needs no sheafification. -/
noncomputable def Adjunction.sheafPullbackIso (adj : u ⊣ v)
    [u.IsContinuous J K] [v.IsContinuous K J]
    [∀ F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F] [HasWeakSheafify J A] :
    v.sheafPullback A K J ≅ u.sheafPushforwardContinuous A J K :=
  (v.sheafAdjunctionContinuous A K J).leftAdjointUniq (adj.sheafPushforwardAdjunction A)

end AdjointPair

end CategoryTheory

namespace StacksLocalizationProducts

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [SmallCategory C] [HasBinaryProducts C] (J : GrothendieckTopology C) (U : C)

/-- **Stacks 03CE(1).** The right adjoint of the localization functor
`j_U = Over.forget U : C/U ⥤ C` is `v : X ↦ X × U / U`: for `Y/U` in `C/U` and `X` in `C` the
map sending a morphism `Y ⟶ X × U / U` over `U` to its underlying morphism followed by the
projection to `X` is a bijection `Mor_{C/U}(Y/U, X × U/U) ≃ Mor_C(Y, X)`.

This is the counit description `Over.forgetAdjStar_counit_app` of Mathlib's adjunction
`Over.forgetAdjStar U : Over.forget U ⊣ Over.star U`. -/
@[stacks 03CE, sga "3 I 1.6" "i_S ⊣ p_S hom bijection"]
theorem bijective_left_comp_prodSnd (Y : Over U) (X : C) :
    Function.Bijective fun g : Y ⟶ (Over.star U).obj X => g.left ≫ prod.snd := by
  have h : (fun g : Y ⟶ (Over.star U).obj X => g.left ≫ prod.snd) =
      ((Over.forgetAdjStar U).homEquiv Y X).symm := by
    funext g
    rw [Adjunction.homEquiv_counit, Over.forgetAdjStar_counit_app]
    rfl
  rw [h]
  exact Equiv.bijective _

/-- **Stacks 03CE(2), first half.** The functor `v = Over.star U : C ⥤ C/U` defines a morphism of
sites `C/U → C`: it is continuous, and the induced pullback on sheaves of sets is exact.

Exactness holds because `v` is a right adjoint, hence representably flat, so this is the criterion
`CategoryTheory.Functor.isMorphismOfSites_of_representablyFlat` (Stacks 00X5). -/
@[stacks 03CE]
theorem isMorphismOfSites_star : (Over.star U).IsMorphismOfSites J (J.over U) :=
  Functor.isMorphismOfSites_of_representablyFlat (Over.star U) J (J.over U)

/-- **Stacks 03CE(2), second half.** The pushforward `j_{U*}` of the morphism of topoi attached to
the continuous and cocontinuous functor `j_U` agrees with the pushforward `v^s` of the morphism of
sites given by `v = Over.star U`; that is, the two morphisms of topoi coincide. -/
@[stacks 03CE]
noncomputable def sheafPushforwardOverForgetIso :
    (Over.forget U).sheafPushforwardCocontinuous (Type u) (J.over U) J ≅
      (Over.star U).sheafPushforwardContinuous (Type u) J (J.over U) :=
  (Over.forgetAdjStar U).sheafPushforwardCocontinuousIso (Type u)

/-- **Stacks 03CE(2), second half.** Dually, the pullback `v_s = f⁻¹` of the morphism of sites
given by `v = Over.star U` is the restriction functor `j_U⁻¹` along `j_U = Over.forget U`. -/
@[stacks 03CE]
noncomputable def sheafPullbackStarIso :
    (Over.star U).sheafPullback (Type u) J (J.over U) ≅
      (Over.forget U).sheafPushforwardContinuous (Type u) (J.over U) J :=
  (Over.forgetAdjStar U).sheafPullbackIso (Type u)

/-- **Stacks 03CE(3).** For a sheaf `F` on `C/U` the sections of `j_{U*}F` over an object `X` of
`C` are the sections of `F` over `X × U / U`. -/
@[stacks 03CE]
noncomputable def sheafPushforwardObjEquiv (F : Sheaf (J.over U) (Type u)) (X : C) :
    (((Over.forget U).sheafPushforwardCocontinuous (Type u) (J.over U) J).obj F).obj.obj (op X) ≃
      F.obj.obj (op ((Over.star U).obj X)) :=
  (((sheafToPresheaf J (Type u)).mapIso ((sheafPushforwardOverForgetIso J U).app F)).app
    (op X)).toEquiv

end StacksLocalizationProducts
