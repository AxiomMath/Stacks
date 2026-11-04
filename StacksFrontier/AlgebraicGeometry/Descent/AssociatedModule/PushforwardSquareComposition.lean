module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PushforwardComparisonWhiskering

/-!
# Composing the comparison of the two direct images round a square of ringed sites

Let a square of morphisms of ringed sites be given, with index functors `e` down the two sides
and `b`, `k` along the two edges, and let `Φ` be the comparison of the two composite direct
images of sheaves of modules.  For two composable squares, `Φ` of the composite square is
assembled from `Φ` of the two factors together with the composition comparisons of the direct
images along the three functors on each side.  This file proves that assembly, in the shape the
two-categorical skeleton `Stacks.CategoryTheory.squareIsoCompOfChart` asks for as its `hstep`
hypothesis.

Every datum is a variable: the six sites, their topologies, the nine index functors, the six
structure sheaves and the nine structure maps.  The comparison of the two routes enters only
through the four transports `β₁`, …, `β₄` into which the composition law for the transport of a
direct image decomposes it, each pinned by an equation; so a consumer supplies the composition
law it already holds together with four applications of the whiskering identities below, and
writes no statement of its own out.

## Main results

* `Stacks.SheafOfModules.pushforwardComp_symm_trans` and
  `Stacks.SheafOfModules.trans_pushforwardComp`: the two remaining ways of dropping a
  `CategoryTheory.SheafOfModules.pushforwardComp` from a composite of isomorphisms.
* `Stacks.SheafOfModules.pushforwardComp_assoc`: the composition comparison of a threefold
  composite of direct images is unambiguous.
* `Stacks.SheafOfModules.isoWhiskerRight_pushforwardComp_symm_trans_isoWhiskerLeft` and
  `Stacks.SheafOfModules.isoWhiskerLeft_pushforwardComp_symm_trans_isoWhiskerRight`: **the two
  interchange laws for a pair of composition comparisons of direct images whiskered on opposite
  sides.**  Each such pair is the identity: the two whiskerings read a threefold composite of
  direct images in the two bracketings, and both bracketings are the direct image along the
  composite structure map.
* `Stacks.SheafOfModules.pushforwardComp_trans_isoWhiskerRight_pushforwardCongr₂` and
  `Stacks.SheafOfModules.pushforwardComp_trans_isoWhiskerLeft_pushforwardCongr₂`: **the two
  whiskering identities for a transport of a direct image, conjugated by the composition
  comparisons on either side.**  This is the form in which they compose with one another.
* `Stacks.CategoryTheory.trans_four_assoc` and `Stacks.CategoryTheory.trans_telescope_four`: the
  bookkeeping of a fourfold composite — splitting its last factor off, and telescoping it
  against four matching identities — at plain variables of an arbitrary category.
* `Stacks.SheafOfModules.pushforwardSquareIso_step`: **the comparison of the two direct images
  round a composite square is the composite of the two factors' comparisons, whiskered, together
  with the composition comparisons on the two sides.**
* `Stacks.SheafOfModules.pushforwardSquareIso_step_of_data`: the same from the comparisons of the
  index functors and their eight structure-map compatibilities, which is what a consumer holds.

## Implementation notes

The two interchange laws, and the telescope, are stated in tail-carrying form — with a further
isomorphism composed on the right — so that they fire on a right-associated composite without
first being re-bracketed.  The same reason the dropping lemmas are stated that way.

No `CategoryTheory.SheafOfModules.pushforwardComp` is ever cancelled against
`CategoryTheory.Iso.refl`, although it is one, and the two whiskering identities are used only
in the **conjugated** form above.  This is the reason the file is arranged this way: the
unconjugated identity `β = CategoryTheory.Functor.isoWhiskerLeft _ B` equates two isomorphisms
whose types are the two spellings of one functor — the direct image along a
`CategoryTheory.SheafOfModules.comparisonComp`, and the composite of the two direct images — so
elaborating it decides that definitional equality, and four of them together exhaust the
heartbeat budget of one declaration even at the variables of this file.  Conjugated by the two
`CategoryTheory.SheafOfModules.pushforwardComp`, each side is written in a single spelling and
the statement is free.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

universe v u
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory Functor

namespace Stacks.CategoryTheory

open CategoryTheory

variable {𝒦 : Type u₁} [Category.{v₁} 𝒦]

/-- A matching identity between two composites of isomorphisms may be used under a common
tail. -/
theorem trans_trans_of_trans_eq {w x y z : 𝒦} {a : w ≅ x} {b : x ≅ y} {c : w ≅ z} {d : z ≅ y}
    (h : a ≪≫ b = c ≪≫ d) {y' : 𝒦} (e : y ≅ y') : a ≪≫ b ≪≫ e = c ≪≫ d ≪≫ e := by
  rw [← Iso.trans_assoc, h, Iso.trans_assoc]

/-- **Splitting the last factor off a fourfold composite of isomorphisms.**  Supplied as a
lemma at plain variables so that a consumer does not rewrite with associativity at a geometric
instantiation: there the two readings of such a composite mix two definitionally equal spellings
of one category of sheaves of modules, and `rw` leaves a term that is not type-correct at the
transparency it checks. -/
theorem trans_four_assoc {w x y z z' : 𝒦} (a : w ≅ x) (b : x ≅ y) (c : y ≅ z) (d : z ≅ z') :
    a ≪≫ b ≪≫ c ≪≫ d = (a ≪≫ b ≪≫ c) ≪≫ d := by
  rw [Iso.trans_assoc, Iso.trans_assoc]

/-- **A fourfold composite of isomorphisms, telescoped against four matching identities.**
The four identities move the head of the composite past each factor in turn, leaving a bridge
`pᵢ` behind; the fifth hypothesis says the last bridge cancels the tail.

Every datum is a variable of an arbitrary category, so an instantiation restates nothing. -/
theorem trans_telescope_four {x₀ x₁ x₂ x₃ x₄ x₅ y₁ y₂ y₃ y₄ : 𝒦}
    {a : x₀ ≅ x₁} {β₁ : x₁ ≅ x₂} {β₂ : x₂ ≅ x₃} {β₃ : x₃ ≅ x₄} {β₄ : x₄ ≅ x₅} {c : x₅ ≅ y₄}
    {u₁ : x₀ ≅ y₁} {u₂ : y₁ ≅ y₂} {u₃ : y₂ ≅ y₃} {u₄ : y₃ ≅ y₄}
    {p₁ : y₁ ≅ x₂} {p₂ : y₂ ≅ x₃} {p₃ : y₃ ≅ x₄} {p₄ : y₄ ≅ x₅}
    (h₁ : a ≪≫ β₁ = u₁ ≪≫ p₁) (h₂ : p₁ ≪≫ β₂ = u₂ ≪≫ p₂)
    (h₃ : p₂ ≪≫ β₃ = u₃ ≪≫ p₃) (h₄ : p₃ ≪≫ β₄ = u₄ ≪≫ p₄)
    (h₅ : p₄ ≪≫ c = Iso.refl y₄) :
    a ≪≫ (β₁ ≪≫ β₂ ≪≫ β₃ ≪≫ β₄) ≪≫ c = u₁ ≪≫ u₂ ≪≫ u₃ ≪≫ u₄ := by
  simp only [Iso.trans_assoc]
  rw [trans_trans_of_trans_eq h₁, trans_trans_of_trans_eq h₂, trans_trans_of_trans_eq h₃,
    trans_trans_of_trans_eq h₄, h₅, Iso.trans_refl]

end Stacks.CategoryTheory

namespace Stacks.SheafOfModules

/-- Two isomorphisms of functors between categories of sheaves of modules are equal when they
agree on sections. -/
private theorem iso_eq_of_forall_apply {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    {X Y : _root_.SheafOfModules.{v} S ⥤ _root_.SheafOfModules.{v} R} {e e' : X ≅ Y}
    (h : ∀ N U x, (e.hom.app N).val.app U x = (e'.hom.app N).val.app U x) : e = e' :=
  Iso.ext (NatTrans.ext (funext fun N => by ext U x; exact h N U x))

/-! ### Dropping a composition comparison -/

section Drop

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}
  {F : C ⥤ D} [F.IsContinuous J K] {G : D ⥤ E} [G.IsContinuous K L]
  [(F ⋙ G).IsContinuous J L]
  (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S)
  (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T)

omit [(F ⋙ G).IsContinuous J L] in
/-- **The inverse of a composition comparison of direct images may be dropped from the left of a
composite of isomorphisms.**  `SheafOfModules.pushforwardComp` is `CategoryTheory.Iso.refl`, so
the inverse is too. -/
theorem pushforwardComp_symm_trans
    {H : _root_.SheafOfModules.{v} T ⥤ _root_.SheafOfModules.{v} R}
    (e : _root_.SheafOfModules.pushforward.{v} ψ ⋙ _root_.SheafOfModules.pushforward.{v} φ ≅ H) :
    (_root_.SheafOfModules.pushforwardComp.{v} φ ψ).symm ≪≫ e = e :=
  Iso.refl_trans e

omit [(F ⋙ G).IsContinuous J L] in
/-- **A composition comparison of direct images may be dropped from the right of a composite of
isomorphisms.** -/
theorem trans_pushforwardComp
    {H : _root_.SheafOfModules.{v} T ⥤ _root_.SheafOfModules.{v} R}
    (e : H ≅ _root_.SheafOfModules.pushforward.{v} ψ ⋙ _root_.SheafOfModules.pushforward.{v} φ) :
    e ≪≫ _root_.SheafOfModules.pushforwardComp.{v} φ ψ = e :=
  Iso.trans_refl e

end Drop

/-! ### Three direct images -/

section Three

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {Z : Type u₄} [Category.{v₄} Z]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {M : GrothendieckTopology Z}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}
  {W : Sheaf M RingCat.{u}}
  {F : C ⥤ D} [F.IsContinuous J K] {G : D ⥤ E} [G.IsContinuous K L]
  {H : E ⥤ Z} [H.IsContinuous L M]
  [(F ⋙ G).IsContinuous J L] [(G ⋙ H).IsContinuous K M]
  [(F ⋙ G ⋙ H).IsContinuous J M] [((F ⋙ G) ⋙ H).IsContinuous J M]
  (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S)
  (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T)
  (θ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} L M).obj W)

/-- **The composition comparison of a threefold composite of direct images of sheaves of modules
is unambiguous.**  Reading the last two direct images as one and comparing with the first gives
the same identification as reading the first two as one and comparing with the last. -/
theorem pushforwardComp_assoc :
    _root_.SheafOfModules.pushforwardComp.{v} φ (_root_.SheafOfModules.comparisonComp ψ θ) =
      _root_.SheafOfModules.pushforwardComp.{v}
        (_root_.SheafOfModules.comparisonComp φ ψ) θ :=
  rfl

/-- **Rebracketing the head of a composite that begins with a composition comparison of three
direct images.**  One direction of
`Stacks.SheafOfModules.pushforwardComp_assoc` under a composite. -/
theorem pushforwardComp_assoc_trans
    {Y : _root_.SheafOfModules.{v} W ⥤ _root_.SheafOfModules.{v} R}
    {β : _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp
          (_root_.SheafOfModules.comparisonComp φ ψ) θ) ≅ Y}
    {X : _root_.SheafOfModules.pushforward.{v} θ ⋙
      _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp φ ψ) ≅ Y}
    (h : _root_.SheafOfModules.pushforwardComp.{v}
      (_root_.SheafOfModules.comparisonComp φ ψ) θ ≪≫ β = X) :
    _root_.SheafOfModules.pushforwardComp.{v} φ
        (_root_.SheafOfModules.comparisonComp ψ θ) ≪≫ β =
      X :=
  (congrArg (fun z => z ≪≫ β) (pushforwardComp_assoc.{v} φ ψ θ)).trans h

/-- **The other direction of the rebracketing.** -/
theorem pushforwardComp_assoc_trans'
    {Y : _root_.SheafOfModules.{v} W ⥤ _root_.SheafOfModules.{v} R}
    {β : _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp φ
          (_root_.SheafOfModules.comparisonComp ψ θ)) ≅ Y}
    {X : _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp ψ θ) ⋙
      _root_.SheafOfModules.pushforward.{v} φ ≅ Y}
    (h : _root_.SheafOfModules.pushforwardComp.{v} φ
      (_root_.SheafOfModules.comparisonComp ψ θ) ≪≫ β = X) :
    _root_.SheafOfModules.pushforwardComp.{v}
        (_root_.SheafOfModules.comparisonComp φ ψ) θ ≪≫ β =
      X :=
  (congrArg (fun z => z ≪≫ β) (pushforwardComp_assoc.{v} φ ψ θ).symm).trans h

omit [(G ⋙ H).IsContinuous K M] [(F ⋙ G ⋙ H).IsContinuous J M] in
/-- **Reading a threefold composite of direct images in the two bracketings is the identity.**
The inverse of the composition comparison of the last two direct images, whiskered on the right
with the first, followed by the composition comparison of the first two whiskered on the left
with the last, changes nothing: both bracketings are the direct image along the structure map of
the composite of the three morphisms of ringed sites. -/
theorem isoWhiskerRight_pushforwardComp_symm_trans_isoWhiskerLeft
    {P : _root_.SheafOfModules.{v} W ⥤ _root_.SheafOfModules.{v} R}
    (e : _root_.SheafOfModules.pushforward.{v} θ ⋙
      _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp φ ψ) ≅ P) :
    Functor.isoWhiskerRight (_root_.SheafOfModules.pushforwardComp.{v} ψ θ).symm
          (_root_.SheafOfModules.pushforward.{v} φ) ≪≫
        Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} θ)
          (_root_.SheafOfModules.pushforwardComp.{v} φ ψ) ≪≫ e =
      e := by
  exact iso_eq_of_forall_apply fun _ _ _ => rfl

omit [(F ⋙ G).IsContinuous J L] [(F ⋙ G ⋙ H).IsContinuous J M] in
/-- **The same interchange with the two whiskerings on the other sides.**  The inverse of the
composition comparison of the first two direct images, whiskered on the left with the last,
followed by the composition comparison of the last two whiskered on the right with the first,
changes nothing. -/
theorem isoWhiskerLeft_pushforwardComp_symm_trans_isoWhiskerRight
    {P : _root_.SheafOfModules.{v} W ⥤ _root_.SheafOfModules.{v} R}
    (e : _root_.SheafOfModules.pushforward.{v}
      (_root_.SheafOfModules.comparisonComp ψ θ) ⋙
        _root_.SheafOfModules.pushforward.{v} φ ≅ P) :
    Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} θ)
          (_root_.SheafOfModules.pushforwardComp.{v} φ ψ).symm ≪≫
        Functor.isoWhiskerRight (_root_.SheafOfModules.pushforwardComp.{v} ψ θ)
          (_root_.SheafOfModules.pushforward.{v} φ) ≪≫ e =
      e := by
  exact iso_eq_of_forall_apply fun _ _ _ => rfl

end Three

/-! ### The whiskering identities, conjugated -/

section Conjugate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}

/-- **Whiskering a transported direct image on the right, conjugated by the two composition
comparisons.**  This is `Stacks.SheafOfModules.isoWhiskerRight_pushforwardCongr₂` with the
composition comparison of the two direct images composed on either side, so that both sides are
written as composites of direct images at the ends and as a direct image along a
`CategoryTheory.SheafOfModules.comparisonComp` in the middle.  That is what lets such identities
be composed with one another; see the implementation notes. -/
theorem pushforwardComp_trans_isoWhiskerRight_pushforwardCongr₂ {G₀ : C ⥤ D} [G₀.IsContinuous J K]
    {F G : D ⥤ E} [F.IsContinuous K L] [G.IsContinuous K L]
    [(G₀ ⋙ F).IsContinuous J L] [(G₀ ⋙ G).IsContinuous J L] (e : F ≅ G)
    (θ : R ⟶ (G₀.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    {φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T}
    {ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K L).obj T}
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} K L).app T = ψ)
    (he' : _root_.SheafOfModules.comparisonComp θ φ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerLeft G₀ e.hom)
          RingCat.{u} J L).app T =
      _root_.SheafOfModules.comparisonComp θ ψ) :
    _root_.SheafOfModules.pushforwardComp.{v} θ φ ≪≫
        _root_.SheafOfModules.pushforwardCongr₂.{v}
          (_root_.SheafOfModules.comparisonComp θ φ) (Functor.isoWhiskerLeft G₀ e) he' =
      Functor.isoWhiskerRight (_root_.SheafOfModules.pushforwardCongr₂.{v} φ e he)
          (_root_.SheafOfModules.pushforward.{v} θ) ≪≫
        _root_.SheafOfModules.pushforwardComp.{v} θ ψ := by
  exact iso_eq_of_forall_apply fun _ _ _ => rfl

/-- **Whiskering a transported direct image on the left, conjugated by the two composition
comparisons.**  The companion of
`Stacks.SheafOfModules.pushforwardComp_trans_isoWhiskerRight_pushforwardCongr₂`. -/
theorem pushforwardComp_trans_isoWhiskerLeft_pushforwardCongr₂ {F G : C ⥤ D}
    [F.IsContinuous J K] [G.IsContinuous J K] {H₀ : D ⥤ E} [H₀.IsContinuous K L]
    [(F ⋙ H₀).IsContinuous J L] [(G ⋙ H₀).IsContinuous J L] (e : F ≅ G)
    {φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    (θ : S ⟶ (H₀.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app S = ψ)
    (he' : _root_.SheafOfModules.comparisonComp φ θ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerRight e.hom H₀)
          RingCat.{u} J L).app T =
      _root_.SheafOfModules.comparisonComp ψ θ) :
    _root_.SheafOfModules.pushforwardComp.{v} φ θ ≪≫
        _root_.SheafOfModules.pushforwardCongr₂.{v}
          (_root_.SheafOfModules.comparisonComp φ θ) (Functor.isoWhiskerRight e H₀) he' =
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} θ)
          (_root_.SheafOfModules.pushforwardCongr₂.{v} φ e he) ≪≫
        _root_.SheafOfModules.pushforwardComp.{v} ψ θ := by
  exact iso_eq_of_forall_apply fun _ _ _ => rfl

end Conjugate

/-! ### The comparison of the two direct images round a composite square -/

section Square

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C₁ : Type u₂} [Category.{v₂} C₁]
  {C₂ : Type u₃} [Category.{v₃} C₂]
  {D₀ : Type u₄} [Category.{v₄} D₀] {D₁ : Type u₅} [Category.{v₅} D₁]
  {D₂ : Type u₆} [Category.{v₆} D₂]
  {JC₀ : GrothendieckTopology C₀} {JC₁ : GrothendieckTopology C₁}
  {JC₂ : GrothendieckTopology C₂}
  {JD₀ : GrothendieckTopology D₀} {JD₁ : GrothendieckTopology D₁}
  {JD₂ : GrothendieckTopology D₂}
  {RC₀ : Sheaf JC₀ RingCat.{u}} {RC₁ : Sheaf JC₁ RingCat.{u}} {RC₂ : Sheaf JC₂ RingCat.{u}}
  {RD₀ : Sheaf JD₀ RingCat.{u}} {RD₁ : Sheaf JD₁ RingCat.{u}} {RD₂ : Sheaf JD₂ RingCat.{u}}
  {e₀ : D₀ ⥤ C₀} {e₁ : D₁ ⥤ C₁} {e₂ : D₂ ⥤ C₂}
  {b : C₂ ⥤ C₀} {b₁ : C₁ ⥤ C₀} {b₂ : C₂ ⥤ C₁}
  {k : D₂ ⥤ D₀} {k₁ : D₁ ⥤ D₀} {k₂ : D₂ ⥤ D₁}
  [ie₀ : e₀.IsContinuous JD₀ JC₀] [ie₁ : e₁.IsContinuous JD₁ JC₁]
  [ie₂ : e₂.IsContinuous JD₂ JC₂]
  [ib : b.IsContinuous JC₂ JC₀] [ib₁ : b₁.IsContinuous JC₁ JC₀] [ib₂ : b₂.IsContinuous JC₂ JC₁]
  [ik : k.IsContinuous JD₂ JD₀] [ik₁ : k₁.IsContinuous JD₁ JD₀] [ik₂ : k₂.IsContinuous JD₂ JD₁]
  [ieb : (e₂ ⋙ b).IsContinuous JD₂ JC₀] [ike : (k ⋙ e₀).IsContinuous JD₂ JC₀]
  [ibb : (b₂ ⋙ b₁).IsContinuous JC₂ JC₀] [iebb : (e₂ ⋙ b₂ ⋙ b₁).IsContinuous JD₂ JC₀]
  [ieb₂ : (e₂ ⋙ b₂).IsContinuous JD₂ JC₁] [iebb' : ((e₂ ⋙ b₂) ⋙ b₁).IsContinuous JD₂ JC₀]
  [ike₁ : (k₂ ⋙ e₁).IsContinuous JD₂ JC₁] [ikeb : ((k₂ ⋙ e₁) ⋙ b₁).IsContinuous JD₂ JC₀]
  [ieb₁ : (e₁ ⋙ b₁).IsContinuous JD₁ JC₀] [ikeb' : (k₂ ⋙ e₁ ⋙ b₁).IsContinuous JD₂ JC₀]
  [ike₀ : (k₁ ⋙ e₀).IsContinuous JD₁ JC₀] [ikke : (k₂ ⋙ k₁ ⋙ e₀).IsContinuous JD₂ JC₀]
  [ikk : (k₂ ⋙ k₁).IsContinuous JD₂ JD₀] [ikke' : ((k₂ ⋙ k₁) ⋙ e₀).IsContinuous JD₂ JC₀]
  {α₀ : RD₀ ⟶ (e₀.sheafPushforwardContinuous RingCat.{u} JD₀ JC₀).obj RC₀}
  {α₁ : RD₁ ⟶ (e₁.sheafPushforwardContinuous RingCat.{u} JD₁ JC₁).obj RC₁}
  {α₂ : RD₂ ⟶ (e₂.sheafPushforwardContinuous RingCat.{u} JD₂ JC₂).obj RC₂}
  {s : RC₂ ⟶ (b.sheafPushforwardContinuous RingCat.{u} JC₂ JC₀).obj RC₀}
  {s₁ : RC₁ ⟶ (b₁.sheafPushforwardContinuous RingCat.{u} JC₁ JC₀).obj RC₀}
  {s₂ : RC₂ ⟶ (b₂.sheafPushforwardContinuous RingCat.{u} JC₂ JC₁).obj RC₁}
  {t : RD₂ ⟶ (k.sheafPushforwardContinuous RingCat.{u} JD₂ JD₀).obj RD₀}
  {t₁ : RD₁ ⟶ (k₁.sheafPushforwardContinuous RingCat.{u} JD₁ JD₀).obj RD₀}
  {t₂ : RD₂ ⟶ (k₂.sheafPushforwardContinuous RingCat.{u} JD₂ JD₁).obj RD₁}

/-- **The comparison of the two direct images of sheaves of modules round a composite square of
ringed sites is the composite of the two factors' comparisons.**

The square for the composite is presented by `Φc`, those for the two factors by `Φh` and `Φg`,
each pinned to a `CategoryTheory.SheafOfModules.pushforwardComp`, a transport, and the inverse
of a `CategoryTheory.SheafOfModules.pushforwardComp`.  `Ψ` and `Θ` are the composition
comparisons of the direct images on the two sides, each pinned to a
`CategoryTheory.SheafOfModules.pushforwardComp` and a transport; `Bc` is the transport of the
composite square, decomposed by `hBc` into the four transports of the factors of the sites level
composition law, and `hβ₁`–`hβ₄` identify those four — conjugated by the composition comparisons
on either side — with the whiskerings of the two factors' transports and the two sides' ones.

This is the `hstep` hypothesis of `Stacks.CategoryTheory.squareIsoCompOfChart`: the composition
law for the comparisons *before* a further identification of the functors on one side.  The only
content is bookkeeping — every `CategoryTheory.SheafOfModules.pushforwardComp` is
`CategoryTheory.Iso.refl`, and the three residual pairs of them cancel in the two bracketings of
a threefold composite of direct images. -/
theorem pushforwardSquareIso_step
    {Ψ₀ : _root_.SheafOfModules.pushforward.{v} s ≅
      _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp s₂ s₁)}
    {Bg : _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp α₂ s₂) ≅
      _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp t₂ α₁)}
    {Bh : _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp α₁ s₁) ≅
      _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp t₁ α₀)}
    {Θ₀ : _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp t₂ t₁) ≅
      _root_.SheafOfModules.pushforward.{v} t}
    {Bc : _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp α₂ s) ≅
      _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp t α₀)}
    {β₁ : _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp α₂ s) ≅
      _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp α₂ (_root_.SheafOfModules.comparisonComp s₂ s₁))}
    {β₂ : _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp
          (_root_.SheafOfModules.comparisonComp α₂ s₂) s₁) ≅
      _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp
          (_root_.SheafOfModules.comparisonComp t₂ α₁) s₁)}
    {β₃ : _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp t₂
          (_root_.SheafOfModules.comparisonComp α₁ s₁)) ≅
      _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp t₂
          (_root_.SheafOfModules.comparisonComp t₁ α₀))}
    {β₄ : _root_.SheafOfModules.pushforward.{v}
        (_root_.SheafOfModules.comparisonComp
          (_root_.SheafOfModules.comparisonComp t₂ t₁) α₀) ≅
      _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp t α₀)}
    {Φc : _root_.SheafOfModules.pushforward.{v} s ⋙ _root_.SheafOfModules.pushforward.{v} α₂ ≅
      _root_.SheafOfModules.pushforward.{v} α₀ ⋙ _root_.SheafOfModules.pushforward.{v} t}
    {Φg : _root_.SheafOfModules.pushforward.{v} s₂ ⋙ _root_.SheafOfModules.pushforward.{v} α₂ ≅
      _root_.SheafOfModules.pushforward.{v} α₁ ⋙ _root_.SheafOfModules.pushforward.{v} t₂}
    {Φh : _root_.SheafOfModules.pushforward.{v} s₁ ⋙ _root_.SheafOfModules.pushforward.{v} α₁ ≅
      _root_.SheafOfModules.pushforward.{v} α₀ ⋙ _root_.SheafOfModules.pushforward.{v} t₁}
    {Ψ : _root_.SheafOfModules.pushforward.{v} s ≅
      _root_.SheafOfModules.pushforward.{v} s₁ ⋙ _root_.SheafOfModules.pushforward.{v} s₂}
    {Θ : _root_.SheafOfModules.pushforward.{v} t₁ ⋙ _root_.SheafOfModules.pushforward.{v} t₂ ≅
      _root_.SheafOfModules.pushforward.{v} t}
    (hΦc : Φc = _root_.SheafOfModules.pushforwardComp.{v} α₂ s ≪≫ Bc ≪≫
      (_root_.SheafOfModules.pushforwardComp.{v} t α₀).symm)
    (hΦg : Φg = _root_.SheafOfModules.pushforwardComp.{v} α₂ s₂ ≪≫ Bg ≪≫
      (_root_.SheafOfModules.pushforwardComp.{v} t₂ α₁).symm)
    (hΦh : Φh = _root_.SheafOfModules.pushforwardComp.{v} α₁ s₁ ≪≫ Bh ≪≫
      (_root_.SheafOfModules.pushforwardComp.{v} t₁ α₀).symm)
    (hΨ : Ψ = Ψ₀ ≪≫ (_root_.SheafOfModules.pushforwardComp.{v} s₂ s₁).symm)
    (hΘ : Θ = _root_.SheafOfModules.pushforwardComp.{v} t₂ t₁ ≪≫ Θ₀)
    (hBc : Bc = β₁ ≪≫ β₂ ≪≫ β₃ ≪≫ β₄)
    (hβ₁ : _root_.SheafOfModules.pushforwardComp.{v} α₂ s ≪≫ β₁ =
      Functor.isoWhiskerRight Ψ₀ (_root_.SheafOfModules.pushforward.{v} α₂) ≪≫
        _root_.SheafOfModules.pushforwardComp.{v} α₂
          (_root_.SheafOfModules.comparisonComp s₂ s₁))
    (hβ₂ : _root_.SheafOfModules.pushforwardComp.{v}
        (_root_.SheafOfModules.comparisonComp α₂ s₂) s₁ ≪≫ β₂ =
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} s₁) Bg ≪≫
        _root_.SheafOfModules.pushforwardComp.{v}
          (_root_.SheafOfModules.comparisonComp t₂ α₁) s₁)
    (hβ₃ : _root_.SheafOfModules.pushforwardComp.{v} t₂
        (_root_.SheafOfModules.comparisonComp α₁ s₁) ≪≫ β₃ =
      Functor.isoWhiskerRight Bh (_root_.SheafOfModules.pushforward.{v} t₂) ≪≫
        _root_.SheafOfModules.pushforwardComp.{v} t₂
          (_root_.SheafOfModules.comparisonComp t₁ α₀))
    (hβ₄ : _root_.SheafOfModules.pushforwardComp.{v}
        (_root_.SheafOfModules.comparisonComp t₂ t₁) α₀ ≪≫ β₄ =
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} α₀) Θ₀ ≪≫
        _root_.SheafOfModules.pushforwardComp.{v} t α₀) :
    Φc = Functor.isoWhiskerRight Ψ (_root_.SheafOfModules.pushforward.{v} α₂) ≪≫
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} s₁) Φg ≪≫
        Functor.isoWhiskerRight Φh (_root_.SheafOfModules.pushforward.{v} t₂) ≪≫
          Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} α₀) Θ := by
  subst hΦc hΦg hΦh hΨ hΘ hBc
  refine Eq.trans (Stacks.CategoryTheory.trans_telescope_four hβ₁
    (pushforwardComp_assoc_trans.{v} (h := hβ₂))
    (pushforwardComp_assoc_trans'.{v} (h := hβ₃))
    (pushforwardComp_assoc_trans.{v} (h := hβ₄)) (Iso.self_symm_id _)) ?_
  simp only [Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans, Iso.trans_assoc,
    isoWhiskerRight_pushforwardComp_symm_trans_isoWhiskerLeft,
    isoWhiskerLeft_pushforwardComp_symm_trans_isoWhiskerRight]
  exact iso_eq_of_forall_apply fun _ _ _ => rfl

/-- **The comparison of the two direct images round a composite square, from the comparisons of
the index functors and their structure-map compatibilities.**

This is `Stacks.SheafOfModules.pushforwardSquareIso_step` with the four transports written out:
`σ` is the composition comparison of the index functors on the first side, `Λ` that on the
second, `Ξg` and `Ξh` the comparisons of the two routes for the two factors, and `hσ`, `hΛ`,
`hΞg`, `hΞh`, `h₁`, `h₂`, `h₃`, `h₄` the eight structure-map compatibilities — the four of the
factors and the four the sites level composition law asks of the composite.  A consumer supplies
exactly the statements it already holds. -/
theorem pushforwardSquareIso_step_of_data
    (σ : b₂ ⋙ b₁ ≅ b) (Ξg : k₂ ⋙ e₁ ≅ e₂ ⋙ b₂) (Ξh : k₁ ⋙ e₀ ≅ e₁ ⋙ b₁)
    (Λ : k₂ ⋙ k₁ ≅ k)
    (hσ : s ≫ (Functor.sheafPushforwardContinuousNatTrans σ.hom RingCat.{u} JC₂ JC₀).app RC₀ =
      _root_.SheafOfModules.comparisonComp s₂ s₁)
    (hΞg : _root_.SheafOfModules.comparisonComp α₂ s₂ ≫
        (Functor.sheafPushforwardContinuousNatTrans Ξg.hom RingCat.{u} JD₂ JC₁).app RC₁ =
      _root_.SheafOfModules.comparisonComp t₂ α₁)
    (hΞh : _root_.SheafOfModules.comparisonComp α₁ s₁ ≫
        (Functor.sheafPushforwardContinuousNatTrans Ξh.hom RingCat.{u} JD₁ JC₀).app RC₀ =
      _root_.SheafOfModules.comparisonComp t₁ α₀)
    (hΛ : _root_.SheafOfModules.comparisonComp t₂ t₁ ≫
        (Functor.sheafPushforwardContinuousNatTrans Λ.inv RingCat.{u} JD₂ JD₀).app RD₀ = t)
    (h₁ : _root_.SheafOfModules.comparisonComp α₂ s ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerLeft e₂ σ.hom)
          RingCat.{u} JD₂ JC₀).app RC₀ =
      _root_.SheafOfModules.comparisonComp α₂ (_root_.SheafOfModules.comparisonComp s₂ s₁))
    (h₂ : _root_.SheafOfModules.comparisonComp
          (_root_.SheafOfModules.comparisonComp α₂ s₂) s₁ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerRight Ξg.hom b₁)
          RingCat.{u} JD₂ JC₀).app RC₀ =
      _root_.SheafOfModules.comparisonComp (_root_.SheafOfModules.comparisonComp t₂ α₁) s₁)
    (h₃ : _root_.SheafOfModules.comparisonComp t₂
          (_root_.SheafOfModules.comparisonComp α₁ s₁) ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerLeft k₂ Ξh.hom)
          RingCat.{u} JD₂ JC₀).app RC₀ =
      _root_.SheafOfModules.comparisonComp t₂ (_root_.SheafOfModules.comparisonComp t₁ α₀))
    (h₄ : _root_.SheafOfModules.comparisonComp
          (_root_.SheafOfModules.comparisonComp t₂ t₁) α₀ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerRight Λ.inv e₀)
          RingCat.{u} JD₂ JC₀).app RC₀ =
      _root_.SheafOfModules.comparisonComp t α₀)
    {Bc : _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp α₂ s) ≅
      _root_.SheafOfModules.pushforward.{v} (_root_.SheafOfModules.comparisonComp t α₀)}
    {Φc : _root_.SheafOfModules.pushforward.{v} s ⋙ _root_.SheafOfModules.pushforward.{v} α₂ ≅
      _root_.SheafOfModules.pushforward.{v} α₀ ⋙ _root_.SheafOfModules.pushforward.{v} t}
    {Φg : _root_.SheafOfModules.pushforward.{v} s₂ ⋙ _root_.SheafOfModules.pushforward.{v} α₂ ≅
      _root_.SheafOfModules.pushforward.{v} α₁ ⋙ _root_.SheafOfModules.pushforward.{v} t₂}
    {Φh : _root_.SheafOfModules.pushforward.{v} s₁ ⋙ _root_.SheafOfModules.pushforward.{v} α₁ ≅
      _root_.SheafOfModules.pushforward.{v} α₀ ⋙ _root_.SheafOfModules.pushforward.{v} t₁}
    {Ψ : _root_.SheafOfModules.pushforward.{v} s ≅
      _root_.SheafOfModules.pushforward.{v} s₁ ⋙ _root_.SheafOfModules.pushforward.{v} s₂}
    {Θ : _root_.SheafOfModules.pushforward.{v} t₁ ⋙ _root_.SheafOfModules.pushforward.{v} t₂ ≅
      _root_.SheafOfModules.pushforward.{v} t}
    (hΦc : Φc = _root_.SheafOfModules.pushforwardComp.{v} α₂ s ≪≫ Bc ≪≫
      (_root_.SheafOfModules.pushforwardComp.{v} t α₀).symm)
    (hΦg : Φg = _root_.SheafOfModules.pushforwardComp.{v} α₂ s₂ ≪≫
      _root_.SheafOfModules.pushforwardCongr₂.{v}
          (_root_.SheafOfModules.comparisonComp α₂ s₂) Ξg hΞg ≪≫
        (_root_.SheafOfModules.pushforwardComp.{v} t₂ α₁).symm)
    (hΦh : Φh = _root_.SheafOfModules.pushforwardComp.{v} α₁ s₁ ≪≫
      _root_.SheafOfModules.pushforwardCongr₂.{v}
          (_root_.SheafOfModules.comparisonComp α₁ s₁) Ξh hΞh ≪≫
        (_root_.SheafOfModules.pushforwardComp.{v} t₁ α₀).symm)
    (hΨ : Ψ = _root_.SheafOfModules.pushforwardCongr₂.{v} s σ hσ ≪≫
      (_root_.SheafOfModules.pushforwardComp.{v} s₂ s₁).symm)
    (hΘ : Θ = _root_.SheafOfModules.pushforwardComp.{v} t₂ t₁ ≪≫
      _root_.SheafOfModules.pushforwardCongr₂.{v}
        (_root_.SheafOfModules.comparisonComp t₂ t₁) Λ.symm hΛ)
    (hBc : Bc =
      _root_.SheafOfModules.pushforwardCongr₂.{v}
          (_root_.SheafOfModules.comparisonComp α₂ s) (Functor.isoWhiskerLeft e₂ σ) h₁ ≪≫
        _root_.SheafOfModules.pushforwardCongr₂.{v}
            (_root_.SheafOfModules.comparisonComp
              (_root_.SheafOfModules.comparisonComp α₂ s₂) s₁)
            (Functor.isoWhiskerRight Ξg b₁) h₂ ≪≫
          _root_.SheafOfModules.pushforwardCongr₂.{v}
              (_root_.SheafOfModules.comparisonComp t₂
                (_root_.SheafOfModules.comparisonComp α₁ s₁))
              (Functor.isoWhiskerLeft k₂ Ξh) h₃ ≪≫
            _root_.SheafOfModules.pushforwardCongr₂.{v}
              (_root_.SheafOfModules.comparisonComp
                (_root_.SheafOfModules.comparisonComp t₂ t₁) α₀)
              (Functor.isoWhiskerRight Λ e₀).symm h₄) :
    Φc = Functor.isoWhiskerRight Ψ (_root_.SheafOfModules.pushforward.{v} α₂) ≪≫
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} s₁) Φg ≪≫
        Functor.isoWhiskerRight Φh (_root_.SheafOfModules.pushforward.{v} t₂) ≪≫
          Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} α₀) Θ :=
  pushforwardSquareIso_step.{v} hΦc hΦg hΦh hΨ hΘ hBc
    (pushforwardComp_trans_isoWhiskerRight_pushforwardCongr₂.{v} σ α₂ hσ h₁)
    (pushforwardComp_trans_isoWhiskerLeft_pushforwardCongr₂.{v} Ξg s₁ hΞg h₂)
    (pushforwardComp_trans_isoWhiskerRight_pushforwardCongr₂.{v} Ξh t₂ hΞh h₃)
    (pushforwardComp_trans_isoWhiskerLeft_pushforwardCongr₂.{v} Λ.symm α₀ hΛ h₄)

end Square

end Stacks.SheafOfModules

end
