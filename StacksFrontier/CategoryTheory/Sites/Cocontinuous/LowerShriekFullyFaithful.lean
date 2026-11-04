module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This problem concerns the standard theory of sites, sheaves, and morphisms of topoi
(Stacks Project, Chapters 7 "Sites and Sheaves" and 18 "Modules on Sites"). Throughout,
`C` and `D` are sites and `u : C ⥤ D` is a functor.

This is Lemma 18.16.4 of the Stacks Project (Tag 077I), in the section "Exactness of
lower shriek". It is the abelian-sheaf analogue of the sheaf-of-sets statement
Lemma 7.21.7 (Tag 00XT).

## Main Statement (Stacks Tag 077I)

Let `C` and `D` be sites and let `u : C ⥤ D` be a functor. Assume that
- (a) `u` is cocontinuous,
- (b) `u` is continuous, and
- (c) `u` is fully faithful.

Then, with the morphism of topoi `g` and the lower shriek `g_!` set up below, for every
abelian sheaf `F` on `C` the canonical adjunction maps
* the unit `η_F : F → g⁻¹ g_! F`, and
* the counit `ε_F : g⁻¹ g_* F → F`
are isomorphisms of abelian sheaves on `C`.

## Background and conventions

* (Continuous functor, Tag 00WV) `u` is continuous if for every covering `{V_i → V}` the
  family `{u(V_i) → u(V)}` is a covering and the relevant fibre products are preserved; in
  particular pushing forward along `u` preserves the sheaf condition. In Mathlib this is
  `CategoryTheory.Functor.IsContinuous`.
* (Cocontinuous functor, Tag 00XJ) `u` is cocontinuous (cover-lifting): for every object
  `U` of `C` and every covering `{V_j → u(U)}` of `D` there is a covering `{U_i → U}` of
  `C` whose image `{u(U_i) → u(U)}` refines `{V_j → u(U)}`. In Mathlib this is
  `CategoryTheory.Functor.IsCocontinuous`.
* (Fully faithful functor, Definition 3) `u` is fully faithful if
  `u : Mor_C(X, Y) → Mor_D(u X, u Y)` is a bijection for all `X, Y`. In Mathlib this is
  the pair of instances `[u.Full] [u.Faithful]`.

## The functors `g⁻¹`, `g_*`, `g_!` (Tags 00XO, 00XR, 04BF, 04BG)

We formalize the morphism of topoi `g : Sh(C) → Sh(D)` and the lower shriek using the
ambient Mathlib library, applied to the coefficient category `Ab` of abelian groups, so
that `Sheaf J Ab` is the category of abelian sheaves on `C` (Definition 4, 5):

* The pullback `g⁻¹ : Ab(D) → Ab(C)` is `u.sheafPushforwardContinuous Ab J K`
  (requires `u` continuous; Tag 00XR). On a sheaf `G` it is given by `(g⁻¹ G)(U) = G(u U)`.
* The pushforward `g_* : Ab(C) → Ab(D)` is `u.sheafPushforwardCocontinuous Ab J K`
  (requires `u` cocontinuous; Tag 00XO). One has the adjunction `g⁻¹ ⊣ g_*`, given by
  `u.sheafAdjunctionCocontinuous`.
* The lower shriek `g_! : Ab(C) → Ab(D)` is `u.sheafPullback Ab J K`, the left adjoint
  of `g⁻¹` (requires `u` continuous; Tags 04BF, 04BG). It is constructed in Mathlib via a
  left Kan extension followed by sheafification, which is canonically isomorphic to the
  colimit / plus-construction formula `g_! F = (g_{p!} F)^#`. One has the adjunction
  `g_! ⊣ g⁻¹`, given by `u.sheafAdjunctionContinuous`.

The canonical maps of Definition 6 are then:
* `η_F : F → g⁻¹ (g_! F)`, the unit component of `g_! ⊣ g⁻¹`, and
* `ε_F : g⁻¹ (g_* F) → F`, the counit component of `g⁻¹ ⊣ g_*`.

Note. We place the sites `C` and `D` in a common universe (`Type u₁` with morphisms in
`Type v₁`), the standard small-site setting, which ensures the left adjoint
`g_! = u.sheafPullback` exists. The coefficient category `Ab` is taken at the universe
`max u₁ v₁` so that sheafification of abelian-group valued (pre)sheaves is available.

## Proof outline of this Lean development

The two displayed statements are *isomorphy of adjunction (co)units*, and we use the
standard categorical equivalence

  * for an adjunction `L ⊣ R`, the counit `LR → 1` is an isomorphism  ⟺  `R` is fully
    faithful, and the unit `1 → RL` is an isomorphism  ⟺  `L` is fully faithful.

In Mathlib this is the instance pair
`CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful` /
`...instIsIsoAppUnitOfFullOfFaithful`. Applying it:

  * the counit `ε_F : g⁻¹ g_* F → F` of `adjStar : g⁻¹ ⊣ g_*` is an isomorphism for all
    `F`  ⟸  `g_*` is fully faithful  (`gStar_full`, `gStar_faithful`);
  * the unit `η_F : F → g⁻¹ g_! F` of `adjShriek : g_! ⊣ g⁻¹` is an isomorphism for all
    `F`  ⟸  `g_!` is fully faithful  (`gShriek_full`, `gShriek_faithful`).

So the entire content of Tag 077I is repackaged into the four named lemmas asserting that
`g_*` and `g_!` are fully faithful. This is not circular: the lemma statements speak only of
full faithfulness of the functors, not of the iso-ness of the (co)unit they imply; the
equivalence "R fully faithful ⟺ counit iso" is a general lemma of category theory that does
not depend on Tag 077I. (Conversely, full faithfulness of `g_*` / `g_!` is *equivalent* to
the (co)unit being iso, so these four lemmas carry exactly the analytic content of the
Stacks proof, simply phrased through the (co)unit.)
-/

open CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

-- Main Definition(s)

/-- The coefficient category of abelian groups in which we take sheaves; `Sheaf J AbCat`
is the category of abelian sheaves on the site `(C, J)`. -/
@[ega "III 7.1.1", sga "4 I 2.3.2"]
abbrev AbCat := Ab.{max u₁ v₁}

namespace Stacks.Sites.LowerShriek.FullyFaithful

variable [u.IsContinuous J K] [u.IsCocontinuous J K]

/-- The pullback functor `g⁻¹ : Ab(D) → Ab(C)`, `(g⁻¹ G)(U) = G(u U)` (Stacks Tag 00XR). -/
noncomputable abbrev gInv : Sheaf K (AbCat.{v₁, u₁}) ⥤ Sheaf J (AbCat.{v₁, u₁}) :=
  u.sheafPushforwardContinuous (AbCat.{v₁, u₁}) J K

/-- The pushforward functor `g_* : Ab(C) → Ab(D)` (Stacks Tag 00XO). -/
noncomputable abbrev gStar : Sheaf J (AbCat.{v₁, u₁}) ⥤ Sheaf K (AbCat.{v₁, u₁}) :=
  u.sheafPushforwardCocontinuous (AbCat.{v₁, u₁}) J K

/-- The lower shriek functor `g_! : Ab(C) → Ab(D)`, left adjoint to `g⁻¹`
(Stacks Tags 04BF, 04BG). -/
noncomputable abbrev gShriek : Sheaf J (AbCat.{v₁, u₁}) ⥤ Sheaf K (AbCat.{v₁, u₁}) :=
  u.sheafPullback (AbCat.{v₁, u₁}) J K

/-- The adjunction `g_! ⊣ g⁻¹`. Its unit is the canonical map `η_F : F → g⁻¹ (g_! F)`. -/
noncomputable abbrev adjShriek :
    gShriek u J K ⊣ gInv u J K :=
  u.sheafAdjunctionContinuous (AbCat.{v₁, u₁}) J K

/-- The adjunction `g⁻¹ ⊣ g_*`. Its counit is the canonical map `ε_F : g⁻¹ (g_* F) → F`. -/
noncomputable abbrev adjStar :
    gInv u J K ⊣ gStar u J K :=
  u.sheafAdjunctionCocontinuous (AbCat.{v₁, u₁}) J K

/-- If `u` is fully faithful, then the counit of `adjStar` (i.e. `g⁻¹ ⊣ g_*`) at a sheaf `F`
is an isomorphism of underlying presheaves. -/
@[sga "4 I 5.7" "special case"]
instance gStar_counit_hom_isIso [u.Full] [u.Faithful] (F : Sheaf J (AbCat.{v₁, u₁})) :
    IsIso ((adjStar u J K).counit.app F).hom := by
  rw [u.sheafAdjunctionCocontinuous_counit_app_hom]
  infer_instance

/-- If `u` is fully faithful, then the counit of `adjStar` at a sheaf `F` is an isomorphism. -/
instance gStar_counit_app_isIso [u.Full] [u.Faithful] (F : Sheaf J (AbCat.{v₁, u₁})) :
    IsIso ((adjStar u J K).counit.app F) :=
  (ObjectProperty.isIso_hom_iff _).mp (gStar_counit_hom_isIso u J K F)

/-- If `u` is fully faithful, then the counit of `adjStar` is a natural isomorphism. -/
instance gStar_counit_isIso [u.Full] [u.Faithful] : IsIso (adjStar u J K).counit :=
  NatIso.isIso_of_isIso_app _

/-- If `u` is fully faithful, then the pushforward `g_*` is fully faithful. -/
noncomputable def gStarFullyFaithful [u.Full] [u.Faithful] : (gStar u J K).FullyFaithful :=
  (adjStar u J K).fullyFaithfulROfIsIsoCounit

/-- If `u` is fully faithful, then the pushforward `g_*` is full. -/
lemma gStar_full [u.Full] [u.Faithful] : (gStar u J K).Full :=
  (gStarFullyFaithful u J K).full

/-- If `u` is fully faithful, then the pushforward `g_*` is faithful. -/
lemma gStar_faithful [u.Full] [u.Faithful] : (gStar u J K).Faithful :=
  (gStarFullyFaithful u J K).faithful

/-- In an adjoint triple `L ⊣ M ⊣ R`, if the counit of `M ⊣ R` is an isomorphism, then so is
the unit of `L ⊣ M`. -/
lemma adjointTriple_isIso_unit_of_isIso_counit
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L R : 𝒟 ⥤ 𝒞} {M : 𝒞 ⥤ 𝒟}
    (adjL : L ⊣ M) (adjR : M ⊣ R) [IsIso adjR.counit] : IsIso adjL.unit := by
  have h : conjugateEquiv (adjL.comp adjR) (Adjunction.id) adjL.unit = adjR.counit := by
    ext X; simp [conjugateEquiv_apply_app, Adjunction.comp]
  have : IsIso (conjugateEquiv (adjL.comp adjR) (Adjunction.id) adjL.unit) := h ▸ inferInstance
  exact conjugateEquiv_of_iso (adjL.comp adjR) (Adjunction.id) adjL.unit

/-- If `u` is fully faithful, then the unit of `adjShriek` (i.e. `g_! ⊣ g⁻¹`) is a natural
isomorphism. -/
instance gShriek_unit_isIso [u.Full] [u.Faithful] : IsIso (adjShriek u J K).unit :=
  adjointTriple_isIso_unit_of_isIso_counit (adjShriek u J K) (adjStar u J K)

/-- If `u` is fully faithful, then the lower shriek `g_!` is fully faithful. -/
noncomputable def gShriekFullyFaithful [u.Full] [u.Faithful] : (gShriek u J K).FullyFaithful :=
  (adjShriek u J K).fullyFaithfulLOfIsIsoUnit

/-- If `u` is fully faithful, then the lower shriek `g_!` is full. -/
lemma gShriek_full [u.Full] [u.Faithful] : (gShriek u J K).Full :=
  (gShriekFullyFaithful u J K).full

/-- If `u` is fully faithful, then the lower shriek `g_!` is faithful. -/
lemma gShriek_faithful [u.Full] [u.Faithful] : (gShriek u J K).Faithful :=
  (gShriekFullyFaithful u J K).faithful

end Stacks.Sites.LowerShriek.FullyFaithful

-- Main Statement(s)

open Stacks.Sites.LowerShriek.FullyFaithful in
/-- If `u : C ⥤ D` is continuous, cocontinuous and fully faithful, then for every abelian sheaf
`F` on `C` the counit `ε_F : g⁻¹ (g_* F) → F` of the adjunction `g⁻¹ ⊣ g_*` is an isomorphism. -/
@[stacks 077I "counit", sga "4 III 2.6" "u ff ⇒ u_* ff, abelian"]
theorem stacks077I_counit_isIso
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
    (F : Sheaf J (AbCat.{v₁, u₁})) :
    IsIso ((adjStar u J K).counit.app F) := by
  infer_instance

open Stacks.Sites.LowerShriek.FullyFaithful in
/-- If `u : C ⥤ D` is continuous, cocontinuous and fully faithful, then for every abelian sheaf
`F` on `C` the unit `η_F : F → g⁻¹ (g_! F)` of the adjunction `g_! ⊣ g⁻¹` is an isomorphism. -/
@[stacks 077I "unit", sga "4 III 2.6" "u ff ⇒ u_! ff, abelian", sga "4 VII 4.1" "Clause (i)"]
theorem stacks077I_unit_isIso
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
    (F : Sheaf J (AbCat.{v₁, u₁})) :
    IsIso ((adjShriek u J K).unit.app F) := by
  infer_instance
