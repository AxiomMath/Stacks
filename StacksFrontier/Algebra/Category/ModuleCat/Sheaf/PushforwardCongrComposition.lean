module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# The composition law for the transport of a pushforward along an isomorphism of index functors

For a continuous functor `G : C ⥤ D` of sites and a morphism of sheaves of rings
`φ : T ⟶ (G.sheafPushforwardContinuous RingCat J K).obj S`, Mathlib's
`SheafOfModules.pushforwardCongr₂` transports the direct image
`SheafOfModules.pushforward φ` across an isomorphism `e : F ≅ G` of index functors, provided the
structure maps are compatible: `φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app S`
is the structure map `ψ` of the other index functor.  On sections the transport is a single
restriction map of the sheaf of modules, namely `M.val.map (e.hom.app U.unop).op`.

Mathlib records how that transport behaves on sections, how it interacts with the identity
(`SheafOfModules.pushforwardNatTrans_id`) and the composition law for the underlying natural
transformation (`SheafOfModules.pushforwardNatTrans_comp`), but **not** the composition law for
`pushforwardCongr₂` itself: that transporting along `e₁ : F ≅ G` and then along `e₂ : G ≅ H` is
transporting along the composite `e₁ ≪≫ e₂ : F ≅ H`.  That law is what this file supplies.

The law is not a formality to be absorbed into a `simp` call at a consumer: both sides are
isomorphisms of functors between categories of sheaves of modules, and the three structure maps
`χ`, `φ` and `ψ` of the three index functors are genuinely different morphisms of sheaves of
rings, so the two sides are not definitionally equal.  The content is one application of the
functoriality of a sheaf of modules in its restriction maps, read at every object.

## Main results

* `Stacks.SheafOfModules.sheafPushforwardContinuousNatTrans_app_comp`: the composition law one
  level down, for the action of a natural transformation of index functors on the pushforward of
  sheaves of rings.  It is contravariant.
* `Stacks.SheafOfModules.sheafPushforwardContinuousNatTrans_app_eq_of_comp`: the compatibility
  hypothesis that `pushforwardCongr₂` asks of the composite, derived from the two compatibility
  hypotheses of the factors.  A consumer never has to prove it by hand.
* `Stacks.SheafOfModules.pushforwardCongr₂_comp`: **the composition law**, at the level of
  isomorphisms of functors.
* `Stacks.SheafOfModules.pushforwardCongr₂_hom_comp` and
  `Stacks.SheafOfModules.pushforwardCongr₂_inv_comp`: the same for the forward and backward
  natural transformations.
* `Stacks.SheafOfModules.pushforwardCongr₂_comp_four` and
  `Stacks.SheafOfModules.pushforwardCongr₂_hom_comp_four`: the law iterated, at the arity at
  which a composition law for a comparison of index functors of sites arrives.  Such a
  comparison decomposes into four factors — two whiskerings of the comparison itself and the two
  composition comparisons of the two kinds of base change — so this is the form a consumer
  applies, and applying it costs no intermediate statement.

## Implementation notes

The composite isomorphism of index functors enters as a variable `e₃ : F ≅ H` together with the
equation `w : e₁ ≪≫ e₂ = e₃`, rather than being written out as `e₁ ≪≫ e₂`.  At `e₃ := e₁ ≪≫ e₂`
and `w := rfl` this is the literal law, so nothing is lost; and a consumer that holds its
composite isomorphism under some other name — which is the normal situation, since an index
functor of a site is usually a named base-change construction and its comparisons are named
isomorphisms — applies the law without first rewriting inside the argument of
`pushforwardCongr₂`.  The same idiom is used by
`CategoryTheory.Functor.relativelyRepresentable.pullbackComp` and its siblings.

For the same reason the compatibility hypothesis `he₃` of the composite is a variable too: the
value of `pushforwardCongr₂` does not depend on which proof of that equation is supplied (it is a
proof of an equality of morphisms, so proof irrelevance applies), and taking it as a hypothesis
means the law applies to whatever proof term the consumer already has in hand.
`Stacks.SheafOfModules.sheafPushforwardContinuousNatTrans_app_eq_of_comp` produces one.

The law is stated with the single transport on the left of the equation and the composite on the
right, matching the direction in which a consumer reads a chain of transports apart.
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Functor

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F G H : C ⥤ D}
  [F.IsContinuous J K] [G.IsContinuous J K] [H.IsContinuous J K]

section NatTrans

variable {A : Type u'} [Category.{v} A] (S : Sheaf K A)

/-- **The action of a natural transformation of index functors on the pushforward of sheaves is
contravariantly functorial**, read at one sheaf.

For `α : F ⟶ G` and `β : G ⟶ H` the pushforward along `H` is compared with the pushforward
along `F` either in one step along `α ≫ β`, or in two steps — first along `β`, then along `α`.
The two agree. -/
theorem sheafPushforwardContinuousNatTrans_app_comp (α : F ⟶ G) (β : G ⟶ H) :
    (Functor.sheafPushforwardContinuousNatTrans (α ≫ β) A J K).app S =
      (Functor.sheafPushforwardContinuousNatTrans β A J K).app S ≫
        (Functor.sheafPushforwardContinuousNatTrans α A J K).app S := by
  ext X : 3
  exact Functor.map_comp S.obj ((NatTrans.op β).app X) ((NatTrans.op α).app X)

end NatTrans

variable {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  {χ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).obj S}
  {φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S}
  {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S}

/-- **The compatibility hypothesis of a composite transport**, derived from those of the two
factors.

`SheafOfModules.pushforwardCongr₂` asks, for an isomorphism `e : F ≅ G` of index
functors, that the structure map of `G` carried along `e` be the structure map of `F`.  Given
that for `e₂ : G ≅ H` (carrying `χ` to `φ`) and for `e₁ : F ≅ G` (carrying `φ` to `ψ`), the
composite `e₃` carries `χ` to `ψ`. -/
theorem sheafPushforwardContinuousNatTrans_app_eq_of_comp (e₁ : F ≅ G) (e₂ : G ≅ H) (e₃ : F ≅ H)
    (w : e₁ ≪≫ e₂ = e₃)
    (he₂ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₂.hom RingCat.{u} J K).app S = φ)
    (he₁ : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e₁.hom RingCat.{u} J K).app S = ψ) :
    χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₃.hom RingCat.{u} J K).app S = ψ := by
  subst w
  rw [Iso.trans_hom, sheafPushforwardContinuousNatTrans_app_comp, ← Category.assoc, he₂, he₁]

/-- **The composition law for `SheafOfModules.pushforwardCongr₂`.**

Transporting the direct image of sheaves of modules along an isomorphism `e₂ : G ≅ H` of index
functors and then along `e₁ : F ≅ G` is transporting it along the composite isomorphism `e₃`.

The composite isomorphism and its compatibility hypothesis are variables, pinned by `w` and
`he₃`; see the implementation notes of this file. -/
theorem pushforwardCongr₂_comp (e₁ : F ≅ G) (e₂ : G ≅ H) (e₃ : F ≅ H) (w : e₁ ≪≫ e₂ = e₃)
    (he₂ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₂.hom RingCat.{u} J K).app S = φ)
    (he₁ : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e₁.hom RingCat.{u} J K).app S = ψ)
    (he₃ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₃.hom RingCat.{u} J K).app S = ψ) :
    _root_.SheafOfModules.pushforwardCongr₂.{v} χ e₃ he₃ =
      _root_.SheafOfModules.pushforwardCongr₂.{v} χ e₂ he₂ ≪≫
        _root_.SheafOfModules.pushforwardCongr₂.{v} φ e₁ he₁ := by
  subst w
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  ext U x
  have h : M.val.presheaf.map (e₂.hom.app U.unop).op ≫
      M.val.presheaf.map (e₁.hom.app U.unop).op =
        M.val.presheaf.map ((e₁ ≪≫ e₂).hom.app U.unop).op := by
    rw [← Functor.map_comp, ← op_comp, Iso.trans_hom, NatTrans.comp_app]
  exact congr($h x).symm

/-- **The composition law for `SheafOfModules.pushforwardCongr₂`**, for the
forward natural transformations. -/
theorem pushforwardCongr₂_hom_comp (e₁ : F ≅ G) (e₂ : G ≅ H) (e₃ : F ≅ H) (w : e₁ ≪≫ e₂ = e₃)
    (he₂ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₂.hom RingCat.{u} J K).app S = φ)
    (he₁ : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e₁.hom RingCat.{u} J K).app S = ψ)
    (he₃ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₃.hom RingCat.{u} J K).app S = ψ) :
    (_root_.SheafOfModules.pushforwardCongr₂.{v} χ e₃ he₃).hom =
      (_root_.SheafOfModules.pushforwardCongr₂.{v} χ e₂ he₂).hom ≫
        (_root_.SheafOfModules.pushforwardCongr₂.{v} φ e₁ he₁).hom :=
  congrArg Iso.hom (pushforwardCongr₂_comp.{v} e₁ e₂ e₃ w he₂ he₁ he₃)

/-- **The composition law for `SheafOfModules.pushforwardCongr₂`**, for the
backward natural transformations. -/
theorem pushforwardCongr₂_inv_comp (e₁ : F ≅ G) (e₂ : G ≅ H) (e₃ : F ≅ H) (w : e₁ ≪≫ e₂ = e₃)
    (he₂ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₂.hom RingCat.{u} J K).app S = φ)
    (he₁ : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e₁.hom RingCat.{u} J K).app S = ψ)
    (he₃ : χ ≫ (Functor.sheafPushforwardContinuousNatTrans e₃.hom RingCat.{u} J K).app S = ψ) :
    (_root_.SheafOfModules.pushforwardCongr₂.{v} χ e₃ he₃).inv =
      (_root_.SheafOfModules.pushforwardCongr₂.{v} φ e₁ he₁).inv ≫
        (_root_.SheafOfModules.pushforwardCongr₂.{v} χ e₂ he₂).inv :=
  congrArg Iso.inv (pushforwardCongr₂_comp.{v} e₁ e₂ e₃ w he₂ he₁ he₃)

section Four

variable {F₁ F₂ F₃ F₄ F₅ : C ⥤ D} [F₁.IsContinuous J K] [F₂.IsContinuous J K]
  [F₃.IsContinuous J K] [F₄.IsContinuous J K] [F₅.IsContinuous J K]
  {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  {χ₁ : T ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J K).obj S}
  {χ₂ : T ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J K).obj S}
  {χ₃ : T ⟶ (F₃.sheafPushforwardContinuous RingCat.{u} J K).obj S}
  {χ₄ : T ⟶ (F₄.sheafPushforwardContinuous RingCat.{u} J K).obj S}
  {χ₅ : T ⟶ (F₅.sheafPushforwardContinuous RingCat.{u} J K).obj S}

/-- **The composition law for `SheafOfModules.pushforwardCongr₂` at a four-factor composite.**

This is `Stacks.SheafOfModules.pushforwardCongr₂_comp` iterated, stated at the arity at which a
composition law for an index functor of sites actually arrives: a comparison of two routes round
a square of sites decomposes into four factors — two whiskerings of the comparison and the two
composition comparisons of the two kinds of base change — so the transport of a direct image of
modules along it decomposes into four transports.

Note that the four transports appear in the *reverse* order to the four isomorphisms of index
functors, because `SheafOfModules.pushforwardCongr₂` is contravariant in the index functor.

Every datum is a variable and every compatibility an equation, so that at an instantiation no
intermediate statement has to be written out: `w` is the index functors' own composition law
applied verbatim, and each `h` is the square-compatibility of one factor. -/
theorem pushforwardCongr₂_comp_four (e₁ : F₁ ≅ F₂) (e₂ : F₂ ≅ F₃) (e₃ : F₃ ≅ F₄) (e₄ : F₄ ≅ F₅)
    (e : F₁ ≅ F₅) (w : e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ = e)
    (h₄ : χ₅ ≫ (Functor.sheafPushforwardContinuousNatTrans e₄.hom RingCat.{u} J K).app S = χ₄)
    (h₃ : χ₄ ≫ (Functor.sheafPushforwardContinuousNatTrans e₃.hom RingCat.{u} J K).app S = χ₃)
    (h₂ : χ₃ ≫ (Functor.sheafPushforwardContinuousNatTrans e₂.hom RingCat.{u} J K).app S = χ₂)
    (h₁ : χ₂ ≫ (Functor.sheafPushforwardContinuousNatTrans e₁.hom RingCat.{u} J K).app S = χ₁)
    (h : χ₅ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app S = χ₁) :
    _root_.SheafOfModules.pushforwardCongr₂.{v} χ₅ e h =
      _root_.SheafOfModules.pushforwardCongr₂.{v} χ₅ e₄ h₄ ≪≫
        _root_.SheafOfModules.pushforwardCongr₂.{v} χ₄ e₃ h₃ ≪≫
          _root_.SheafOfModules.pushforwardCongr₂.{v} χ₃ e₂ h₂ ≪≫
            _root_.SheafOfModules.pushforwardCongr₂.{v} χ₂ e₁ h₁ := by
  subst w
  have h₅ := sheafPushforwardContinuousNatTrans_app_eq_of_comp e₃ e₄ _ rfl h₄ h₃
  have h₆ := sheafPushforwardContinuousNatTrans_app_eq_of_comp e₂ _ _ rfl h₅ h₂
  rw [pushforwardCongr₂_comp e₁ _ _ rfl h₆ h₁ h, pushforwardCongr₂_comp e₂ _ _ rfl h₅ h₂ h₆,
    pushforwardCongr₂_comp e₃ e₄ _ rfl h₄ h₃ h₅]
  simp only [Iso.trans_assoc]

/-- **The composition law for `SheafOfModules.pushforwardCongr₂` at a four-factor composite**, for
the forward natural transformations. -/
theorem pushforwardCongr₂_hom_comp_four (e₁ : F₁ ≅ F₂) (e₂ : F₂ ≅ F₃) (e₃ : F₃ ≅ F₄)
    (e₄ : F₄ ≅ F₅) (e : F₁ ≅ F₅) (w : e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ = e)
    (h₄ : χ₅ ≫ (Functor.sheafPushforwardContinuousNatTrans e₄.hom RingCat.{u} J K).app S = χ₄)
    (h₃ : χ₄ ≫ (Functor.sheafPushforwardContinuousNatTrans e₃.hom RingCat.{u} J K).app S = χ₃)
    (h₂ : χ₃ ≫ (Functor.sheafPushforwardContinuousNatTrans e₂.hom RingCat.{u} J K).app S = χ₂)
    (h₁ : χ₂ ≫ (Functor.sheafPushforwardContinuousNatTrans e₁.hom RingCat.{u} J K).app S = χ₁)
    (h : χ₅ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app S = χ₁) :
    (_root_.SheafOfModules.pushforwardCongr₂.{v} χ₅ e h).hom =
      (_root_.SheafOfModules.pushforwardCongr₂.{v} χ₅ e₄ h₄).hom ≫
        (_root_.SheafOfModules.pushforwardCongr₂.{v} χ₄ e₃ h₃).hom ≫
          (_root_.SheafOfModules.pushforwardCongr₂.{v} χ₃ e₂ h₂).hom ≫
            (_root_.SheafOfModules.pushforwardCongr₂.{v} χ₂ e₁ h₁).hom :=
  congrArg Iso.hom (pushforwardCongr₂_comp_four.{v} e₁ e₂ e₃ e₄ e w h₄ h₃ h₂ h₁ h)

end Four

end Stacks.SheafOfModules

end
