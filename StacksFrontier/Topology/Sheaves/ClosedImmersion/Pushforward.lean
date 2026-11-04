module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed immersions and (pre)sheaves

Let `i : Z → X` be the inclusion of a closed subset `Z` of a topological space `X` and let
`F` be a sheaf on `Z`. Stacks 00AE describes the pushforward `i_* F`:

* at a point `x ∉ Z` the stalk `(i_* F)_x` is a singleton — more precisely a *terminal
  object* of the target category, which is `{*}` for sheaves of sets, `0` for abelian
  sheaves and a final object for sheaves of algebraic structures, exactly as the tag
  states;
* at a point `z ∈ Z` the canonical map `(i_* F)_{i z} → F_z` is an isomorphism;
* `i⁻¹ i_* = id` on the category of sheaves on `Z`.

## Main results

* `ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange` — the stalk of `i_* F`
  at a point off `Z` is terminal.
* `ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso` — the counit
  `i⁻¹ i_* ⟶ id` of `TopCat.Sheaf.pullbackPushforwardAdjunction` is an isomorphism.
* The remaining clause, that `(i_* F)_{i z} ≅ F_z` for `z ∈ Z`, is Mathlib's
  `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`, registered below.

Both statements proved here are for an arbitrary target category, so they cover sheaves of
sets, of abelian groups and of algebraic structures uniformly (the counit statement needs
the concreteness hypotheses under which `TopCat.Sheaf.pullback` is defined).

The full faithfulness of `i_*` is established for any *inducing* map, which is all the
argument uses: every open of `Z` is the preimage of an open of `X`, canonically so via
`Topology.IsInducing.functor`, which is right adjoint to `Opens.map i`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open TopCat
open scoped AlgebraicGeometry

universe v u

namespace ClosedImmersionSheaves

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor

variable {C : Type u} [Category.{v} C] {X Z : TopCat.{v}}

/-! ### Stalks of `i_* F` at points outside the image -/

section Stalks

variable [HasColimits.{v} C] (i : Z ⟶ X) {F : Z.Presheaf C} (hF : F.IsSheaf)

omit [HasColimits.{v} C] in
/-- If `V ⊆ X` is open with `i⁻¹(V) = ∅`, then the sections `(i_* F)(V) = F(∅)` of the
pushforward over `V` form a terminal object: a sheaf has terminal sections over `∅`. -/
noncomputable def isTerminalPushforwardObj (V : Opens X) (hV : (Opens.map i).obj V = ⊥) :
    IsTerminal ((i _* F).obj (op V)) :=
  TopCat.Sheaf.isTerminalOfEqEmpty (⟨F, hF⟩ : Z.Sheaf C) hV

/-- If `x` lies in an open `W` with `i⁻¹(W) = ∅`, then the germ map
`(i_* F)(W) ⟶ (i_* F)_x` is an isomorphism.

The inverse is the map out of the stalk colimit induced by the cocone whose leg at a
neighbourhood `V` of `x` is the unique morphism `(i_* F)(V) ⟶ (i_* F)(W)` into the terminal
object `(i_* F)(W)`; its naturality is automatic. That this inverse is a section of the germ
map is checked neighbourhood by neighbourhood after restricting to `V ⊓ W`, whose sections
are terminal too, so the two competing morphisms `(i_* F)(V) ⟶ (i_* F)(V ⊓ W)` coincide. -/
noncomputable def pushforwardStalkIsoOfEmptyPreimage
    (x : X) (W : Opens X) (hxW : x ∈ W) (hW : (Opens.map i).obj W = ⊥) :
    (i _* F).obj (op W) ≅ stalk (i _* F) x := by
  have hT : ∀ V : Opens X, V ≤ W → IsTerminal ((i _* F).obj (op V)) := by
    intro V hVW
    refine isTerminalPushforwardObj i hF V (le_antisymm ?_ bot_le)
    intro z hz
    have h2 : z ∈ (Opens.map i).obj W := hVW hz
    rw [hW] at h2
    exact h2
  have hTW : IsTerminal ((i _* F).obj (op W)) := hT W le_rfl
  let c : Cocone ((OpenNhds.inclusion x).op ⋙ (i _* F)) :=
    { pt := (i _* F).obj (op W)
      ι := { app := fun _ => hTW.from _
             naturality := fun _ _ _ => hTW.hom_ext _ _ } }
  refine ⟨germ (i _* F) W x hxW, colimit.desc _ c, hTW.hom_ext _ _, ?_⟩
  refine stalk_hom_ext _ fun V hxV => ?_
  have hxV' : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have hTV' : IsTerminal ((i _* F).obj (op (V ⊓ W))) := hT (V ⊓ W) inf_le_right
  have e1 : (i _* F).map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op ≫
      germ (i _* F) (V ⊓ W) x hxV' = germ (i _* F) V x hxV :=
    germ_res (i _* F) (homOfLE inf_le_left) x hxV'
  have e2 : (i _* F).map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op ≫
      germ (i _* F) (V ⊓ W) x hxV' = germ (i _* F) W x hxW :=
    germ_res (i _* F) (homOfLE inf_le_right) x hxV'
  have key : hTW.from ((i _* F).obj (op V)) ≫
      (i _* F).map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op
      = (i _* F).map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op := hTV'.hom_ext _ _
  have hdesc : germ (i _* F) V x hxV ≫ colimit.desc _ c
      = hTW.from ((i _* F).obj (op V)) := colimit.ι_desc c (op ⟨V, hxV⟩)
  rw [Category.comp_id, ← Category.assoc, hdesc, ← e2, ← Category.assoc, key, e1]

/-- **Stacks 00AE, the stalks of `i_* F` away from `Z`.** For `i : Z ⟶ X` a closed embedding,
`F` a sheaf on `Z` and `x ∈ X` not in the image of `i`, the stalk `(i_* F)_x` is a terminal
object of the target category: a singleton for sheaves of sets, `0` for abelian sheaves, a
final object for sheaves of algebraic structures.

The complement of the (closed) image is an open neighbourhood `W` of `x` with `i⁻¹(W) = ∅`,
so `pushforwardStalkIsoOfEmptyPreimage` identifies the stalk with the terminal object
`(i_* F)(W) = F(∅)`. -/
@[stacks 00AE, ega "0 4.2.5" "zero stalks outside X"]
noncomputable def isTerminalStalkPushforwardOfNotMemRange
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i)) :
    IsTerminal (stalk (i _* F) x) := by
  let W : Opens X := ⟨(Set.range (ConcreteCategory.hom i))ᶜ, hi.isClosed_range.isOpen_compl⟩
  have hW : (Opens.map i).obj W = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    exact absurd (Set.mem_range_self z) hz
  exact IsTerminal.ofIso (isTerminalPushforwardObj i hF W hW)
    (pushforwardStalkIsoOfEmptyPreimage i hF x W hx hW)

end Stalks

/-! ### `i_*` is fully faithful along an inducing map -/

section FullyFaithful

variable {i : Z ⟶ X}

/-- For an inducing map `i`, the presheaf pushforward `i_* = (Opens.map i).op ⋙ -` is fully
faithful.

`Topology.IsInducing.functor` picks out, for each open `V` of `Z`, the largest open of `X`
with preimage `V`, and is right adjoint to `Opens.map i`. The counit of that adjunction is an
isomorphism because `Opens.map i` undoes `IsInducing.functor` on the nose
(`Topology.IsInducing.map_functorObj`) and `Opens Z` is a poset, so `IsInducing.functor` is
fully faithful and the opposite adjunction `IsInducing.functor.op ⊣ (Opens.map i).op` has an
invertible unit. Whiskering that adjunction into presheaves keeps the unit invertible — its
components are images of isomorphisms under a functor — and its left adjoint is `i_*`. -/
noncomputable def presheafPushforwardFullyFaithful
    (hi : IsInducing (ConcreteCategory.hom i)) :
    (Presheaf.pushforward C i).FullyFaithful := by
  have hcounitApp : ∀ V : Opens Z, IsIso (hi.adjunction.counit.app V) := fun V =>
    ⟨⟨eqToHom (hi.map_functorObj V).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have hcounit : IsIso hi.adjunction.counit := NatIso.isIso_of_isIso_app _
  have ff : hi.functor.FullyFaithful := Adjunction.fullyFaithfulROfIsIsoCounit hi.adjunction
  have : hi.functor.Full := ff.full
  have : hi.functor.Faithful := ff.faithful
  have adjOp : hi.functor.op ⊣ (Opens.map i).op := hi.adjunction.op
  have hunitOp : IsIso adjOp.unit := inferInstance
  have hwunit : IsIso (Adjunction.whiskerLeft C adjOp).unit := by
    have h1 : ∀ P, IsIso ((Adjunction.whiskerLeft C adjOp).unit.app P) := by
      intro P
      have h2 : ∀ z, IsIso (((Adjunction.whiskerLeft C adjOp).unit.app P).app z) := by
        intro z
        rw [Adjunction.whiskerLeft_unit_app_app]
        exact Functor.map_isIso P (adjOp.unit.app z)
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  exact @Adjunction.fullyFaithfulLOfIsIsoUnit _ _ _ _ _ _ (Adjunction.whiskerLeft C adjOp) hwunit

/-- For an inducing map `i`, the sheaf pushforward `i_*` is fully faithful.

The underlying presheaf of `i_* F` is the presheaf pushforward of the underlying presheaf of
`F`, so `i_* ⋙ sheafToPresheaf` is the composite of the fully faithful functors
`sheafToPresheaf` and `Presheaf.pushforward`; a functor whose composite with a faithful
functor is fully faithful is itself fully faithful. -/
noncomputable def sheafPushforwardFullyFaithful
    (hi : IsInducing (ConcreteCategory.hom i)) :
    (Sheaf.pushforward C i).FullyFaithful := by
  have ffp := presheafPushforwardFullyFaithful (C := C) hi
  have hcomp : (Sheaf.pushforward C i ⋙ sheafToPresheaf _ _).FullyFaithful :=
    (CategoryTheory.fullyFaithfulSheafToPresheaf _ _).comp ffp
  have hF : (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat)) C).Faithful :=
    inferInstance
  exact @Functor.FullyFaithful.ofCompFaithful _ _ _ _ _ _ _ _ hF hcomp

end FullyFaithful

/-! ### `i⁻¹ i_* = id` -/

section Counit

variable (A : Type u) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {i : Z ⟶ X}

/-- **Stacks 00AE, `i⁻¹ i_* = id`.** For an inducing `i : Z ⟶ X` — in particular for the
inclusion of a closed subset — the counit `i⁻¹ i_* ⟶ 𝟭` of the adjunction
`i⁻¹ ⊣ i_*` between categories of sheaves is a natural isomorphism, because its right
adjoint `i_*` is fully faithful. -/
@[stacks 00AE]
theorem sheaf_pullback_pushforward_counit_isIso
    (hi : IsInducing (ConcreteCategory.hom i)) :
    IsIso (Sheaf.pullbackPushforwardAdjunction A i).counit := by
  have ff := sheafPushforwardFullyFaithful (C := A) hi
  have := ff.full
  have := ff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

end Counit

/- The remaining clause of Stacks 00AE, that for `z ∈ Z` the canonical comparison
`(i_* F)_{i z} ⟶ F_z` is an isomorphism, is Mathlib's, stated for any inducing map — and a
closed embedding is inducing. Combined with
`ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange` this gives the tag's
description of every stalk of `i_* F`. -/
add_to_stacks 00AE "The stalk of `i_* F` at a point `i z` of the closed subset `Z` is
  `F_z`, via the canonical comparison map `stalkPushforward`. Mathlib proves this for any
  inducing map, and a closed embedding is inducing."
  TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
add_to_ega "0 3.4.5" "more general"
  TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing

end ClosedImmersionSheaves

namespace Stacks

/-- The inclusion of a subset `Z` of `X` as a morphism `TopCat.of Z ⟶ X` in `TopCat`. In the
consumers below `Z` is the closed subset of Stacks 00AH, but nothing in the definition uses
closedness. -/
def subsetInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of a subset is an inducing map: `Z` carries the subspace topology. -/
lemma subsetInclusion_isInducing (X : TopCat.{u}) (Z : Set X) :
    Topology.IsInducing ((ConcreteCategory.hom (subsetInclusion X Z))) :=
  Topology.IsInducing.subtypeVal

/-- The inclusion of a closed subset is a closed embedding. -/
lemma subsetInclusion_isClosedEmbedding (X : TopCat.{u}) (Z : Set X) (hZ : IsClosed Z) :
    Topology.IsClosedEmbedding ((ConcreteCategory.hom (subsetInclusion X Z))) :=
  hZ.isClosedEmbedding_subtypeVal

end Stacks
