module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback

/-!
# Whiskering a transported direct image of sheaves of modules

`SheafOfModules.pushforwardCongr₂` transports the direct image of sheaves of modules along an
isomorphism `e : F ≅ G` of the index functors of two morphisms of ringed sites with the same
structure sheaves, provided the structure maps are compatible.  A composite of two morphisms of
ringed sites has `SheafOfModules.comparisonComp` for its structure map, and
`SheafOfModules.pushforwardComp` — which is `CategoryTheory.Iso.refl` — says that the direct
image along the composite *is* the composite of the two direct images.  So a transport of one
factor of such a composite is at the same time a whiskering of the transport of that factor and
a transport of the whole composite, along `e` whiskered with the other index functor.

This file supplies those two identities, together with the compatibility hypotheses the
transport of the composite asks for, derived from the compatibility of the one factor.  Every
datum is a variable: the sites, the two topologies, the structure sheaves, the index functors
and their structure maps.

## Main results

* `Stacks.SheafOfModules.comparisonComp_natTrans_whiskerRight` and
  `Stacks.SheafOfModules.comparisonComp_natTrans_whiskerLeft`: the square compatibility of a
  composite, derived from that of one factor whiskered with the other index functor.  These are
  the hypotheses that `SheafOfModules.pushforwardCongr₂` asks of the composite.
* `Stacks.SheafOfModules.isoWhiskerRight_pushforwardCongr₂` and
  `Stacks.SheafOfModules.isoWhiskerLeft_pushforwardCongr₂`: **whiskering a transport is
  transporting along a whiskered isomorphism.**
* `Stacks.SheafOfModules.comparisonComp_natTrans_inv`: the compatibility of a square read in the
  other direction, which is what a consumer holding the forward compatibility of a composition
  comparison needs in order to transport the other way.
* `Stacks.SheafOfModules.comparisonComp_assoc`: `SheafOfModules.comparisonComp` is associative,
  by `rfl`.  So the two ways of reading the structure map of a composite of three morphisms of
  ringed sites are interchangeable in a position where only definitional equality is available,
  which is what lets the two whiskering identities below be composed with one another.

## Implementation notes

The two identities between actions of natural transformations of index functors —
`Stacks.SheafOfModules.sheafPushforwardContinuousNatTrans_app_sheafPushforwardContinuous_obj`
and `Stacks.SheafOfModules.sheafPushforwardContinuousNatTrans_whiskerLeft_app` — hold by `rfl`:
both sides restrict along the same morphism of the site, and the two spellings of the source and
target sheaves differ only by unfolding
`CategoryTheory.Functor.sheafPushforwardContinuous`.  They are stated separately so that the
compatibility lemmas below are one rewrite plus naturality, with no component computation at an
instantiation.

For the same reason `SheafOfModules.comparisonComp` is used rather than its unfolding: its type
ascribes the composite structure map to the sheaf that pushforward along the composite index
functor expects, which is the spelling `SheafOfModules.pushforwardCongr₂` consumes.
-/

@[expose] public section

universe v v₁ v₂ v₃ u₁ u₂ u₃ ua va u

open CategoryTheory Functor

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}

/-! ### The action of a natural transformation of index functors on an iterated direct image -/

section NatTrans

variable {A : Type ua} [Category.{va} A]

/-- **Acting on an iterated direct image of sheaves is acting on the direct image along the
composite index functor.**  Both sides restrict a sheaf on the third site along the image under
the second index functor of the given natural transformation. -/
theorem sheafPushforwardContinuousNatTrans_app_sheafPushforwardContinuous_obj
    {F G : C ⥤ D} [F.IsContinuous J K] [G.IsContinuous J K]
    (H : D ⥤ E) [H.IsContinuous K L]
    [(F ⋙ H).IsContinuous J L] [(G ⋙ H).IsContinuous J L]
    (α : F ⟶ G) (S : Sheaf L A) :
    (Functor.sheafPushforwardContinuousNatTrans α A J K).app
        ((H.sheafPushforwardContinuous A K L).obj S) =
      (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerRight α H) A J L).app S :=
  rfl

/-- **Acting by a natural transformation whiskered on the left is the direct image of acting by
it.**  Both sides restrict a sheaf on the third site along the component of the given natural
transformation at the image under the first index functor. -/
theorem sheafPushforwardContinuousNatTrans_whiskerLeft_app
    (H : C ⥤ D) [H.IsContinuous J K]
    {F G : D ⥤ E} [F.IsContinuous K L] [G.IsContinuous K L]
    [(H ⋙ F).IsContinuous J L] [(H ⋙ G).IsContinuous J L]
    (α : F ⟶ G) (S : Sheaf L A) :
    (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerLeft H α) A J L).app S =
      (H.sheafPushforwardContinuous A J K).map
        ((Functor.sheafPushforwardContinuousNatTrans α A K L).app S) :=
  rfl

end NatTrans

/-! ### The square compatibility of a composite -/

variable {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}

/-- **The square compatibility of a composite whose second factor is transported.**  If the
structure map of `G` carried along `α : F ⟶ G` is the structure map of `F`, then the structure
map of the composite `G` then `H` carried along `α` whiskered with `H` is the structure map of
the composite `F` then `H`. -/
theorem comparisonComp_natTrans_whiskerRight {F G : C ⥤ D} [F.IsContinuous J K]
    [G.IsContinuous J K] {H : D ⥤ E} [H.IsContinuous K L]
    [(F ⋙ H).IsContinuous J L] [(G ⋙ H).IsContinuous J L] (α : F ⟶ G)
    {φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    (θ : S ⟶ (H.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    (hα : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat.{u} J K).app S = ψ) :
    _root_.SheafOfModules.comparisonComp φ θ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerRight α H)
          RingCat.{u} J L).app T =
      _root_.SheafOfModules.comparisonComp ψ θ := by
  change φ ≫ (G.sheafPushforwardContinuous RingCat.{u} J K).map θ ≫
      (Functor.sheafPushforwardContinuousNatTrans α RingCat.{u} J K).app
        ((H.sheafPushforwardContinuous RingCat.{u} K L).obj T) =
    ψ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map θ
  rw [(Functor.sheafPushforwardContinuousNatTrans α RingCat.{u} J K).naturality θ,
    ← Category.assoc, hα]

/-- **The square compatibility of a composite whose first factor is transported.**  If the
structure map of `G` carried along `α : F ⟶ G` is the structure map of `F`, then the structure
map of the composite `H` then `G` carried along `α` whiskered with `H` is the structure map of
the composite `H` then `F`. -/
theorem comparisonComp_natTrans_whiskerLeft {H : C ⥤ D} [H.IsContinuous J K]
    {F G : D ⥤ E} [F.IsContinuous K L] [G.IsContinuous K L]
    [(H ⋙ F).IsContinuous J L] [(H ⋙ G).IsContinuous J L] (α : F ⟶ G)
    (θ : R ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    {φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T}
    {ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K L).obj T}
    (hα : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat.{u} K L).app T = ψ) :
    _root_.SheafOfModules.comparisonComp θ φ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerLeft H α)
          RingCat.{u} J L).app T =
      _root_.SheafOfModules.comparisonComp θ ψ := by
  change θ ≫ (H.sheafPushforwardContinuous RingCat.{u} J K).map φ ≫
      (H.sheafPushforwardContinuous RingCat.{u} J K).map
        ((Functor.sheafPushforwardContinuousNatTrans α RingCat.{u} K L).app T) =
    θ ≫ (H.sheafPushforwardContinuous RingCat.{u} J K).map ψ
  rw [← (H.sheafPushforwardContinuous RingCat.{u} J K).map_comp, hα]

/-- **A square compatibility read in the other direction.**  If the structure map of `G` carried
along the forward direction of an isomorphism `e : F ≅ G` of index functors is the structure map
of `F`, then the structure map of `F` carried along the backward direction is the structure map
of `G`.

A composition comparison of index functors is naturally available in one direction only, and the
transport of a direct image reads it in whichever direction the consumer composes; this is the
passage between the two. -/
theorem comparisonComp_natTrans_inv {F G : C ⥤ D} [F.IsContinuous J K] [G.IsContinuous J K]
    (e : F ≅ G) {φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app S = ψ) :
    ψ ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u} J K).app S = φ := by
  have hid : (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app S ≫
      (Functor.sheafPushforwardContinuousNatTrans e.inv RingCat.{u} J K).app S =
      𝟙 ((G.sheafPushforwardContinuous RingCat.{u} J K).obj S) :=
    (Functor.sheafPushforwardContinuousIso e RingCat.{u} J K).inv_hom_id_app S
  rw [← he, Category.assoc, hid, Category.comp_id]

/-- **The structure map of a composite of three morphisms of ringed sites is unambiguous.** -/
theorem comparisonComp_assoc {C' : Type*} [Category C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{u}} {F : C' ⥤ C} [F.IsContinuous J' J] {G : C ⥤ D}
    [G.IsContinuous J K] {H : D ⥤ E} [H.IsContinuous K L] [(F ⋙ G).IsContinuous J' K]
    [(G ⋙ H).IsContinuous J L] [(F ⋙ G ⋙ H).IsContinuous J' L]
    [((F ⋙ G) ⋙ H).IsContinuous J' L]
    (φ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J' J).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    (θ : S ⟶ (H.sheafPushforwardContinuous RingCat.{u} K L).obj T) :
    _root_.SheafOfModules.comparisonComp (_root_.SheafOfModules.comparisonComp φ ψ) θ =
      _root_.SheafOfModules.comparisonComp φ (_root_.SheafOfModules.comparisonComp ψ θ) :=
  rfl

/-! ### The composition comparison of two direct images is an identity -/

section Comp

variable {C' : Type*} [Category C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{u}} {F : C' ⥤ C} [F.IsContinuous J' J] {G : C ⥤ D}
  [G.IsContinuous J K] [(F ⋙ G).IsContinuous J' K]
  (φ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J' J).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)

/-- **A composition comparison of direct images of sheaves of modules may be dropped from the
left of a composite of isomorphisms.**  `SheafOfModules.pushforwardComp` is
`CategoryTheory.Iso.refl`, so composing with it changes nothing. -/
theorem pushforwardComp_trans {H : _root_.SheafOfModules.{v} S ⥤ _root_.SheafOfModules.{v} R'}
    (e : _root_.SheafOfModules.pushforward.{v}
      (_root_.SheafOfModules.comparisonComp φ ψ) ≅ H) :
    _root_.SheafOfModules.pushforwardComp.{v} φ ψ ≪≫ e = e :=
  Iso.refl_trans e

/-- **A composition comparison of direct images of sheaves of modules may be dropped from the
right of a composite of isomorphisms.** -/
theorem trans_pushforwardComp_symm
    {H : _root_.SheafOfModules.{v} S ⥤ _root_.SheafOfModules.{v} R'}
    (e : H ≅ _root_.SheafOfModules.pushforward.{v}
      (_root_.SheafOfModules.comparisonComp φ ψ)) :
    e ≪≫ (_root_.SheafOfModules.pushforwardComp.{v} φ ψ).symm = e :=
  Iso.trans_refl e

end Comp

/-! ### Whiskering a transport -/

/-- **Whiskering a transported direct image on the right is transporting along the isomorphism
whiskered on the left.**  Both sides are the restriction, at a sheaf of modules on the third
site, along the component of the isomorphism of index functors at the image of the first one. -/
theorem isoWhiskerRight_pushforwardCongr₂ {H : C ⥤ D} [H.IsContinuous J K]
    {F G : D ⥤ E} [F.IsContinuous K L] [G.IsContinuous K L]
    [(H ⋙ F).IsContinuous J L] [(H ⋙ G).IsContinuous J L] (e : F ≅ G)
    (θ : R ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    {φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T}
    {ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K L).obj T}
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} K L).app T = ψ)
    (he' : _root_.SheafOfModules.comparisonComp θ φ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerLeft H e.hom)
          RingCat.{u} J L).app T =
      _root_.SheafOfModules.comparisonComp θ ψ) :
    _root_.SheafOfModules.pushforwardCongr₂.{v}
        (_root_.SheafOfModules.comparisonComp θ φ) (Functor.isoWhiskerLeft H e) he' =
      Functor.isoWhiskerRight (_root_.SheafOfModules.pushforwardCongr₂.{v} φ e he)
        (_root_.SheafOfModules.pushforward.{v} θ) := by
  ext M U x
  rfl

/-- **Whiskering a transported direct image on the left is transporting along the isomorphism
whiskered on the right.**  Both sides are the restriction, at a sheaf of modules on the third
site, along the image under the second index functor of the component of the isomorphism. -/
theorem isoWhiskerLeft_pushforwardCongr₂ {F G : C ⥤ D} [F.IsContinuous J K]
    [G.IsContinuous J K] {H : D ⥤ E} [H.IsContinuous K L]
    [(F ⋙ H).IsContinuous J L] [(G ⋙ H).IsContinuous J L] (e : F ≅ G)
    {φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj S}
    (θ : S ⟶ (H.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app S = ψ)
    (he' : _root_.SheafOfModules.comparisonComp φ θ ≫
        (Functor.sheafPushforwardContinuousNatTrans (Functor.whiskerRight e.hom H)
          RingCat.{u} J L).app T =
      _root_.SheafOfModules.comparisonComp ψ θ) :
    _root_.SheafOfModules.pushforwardCongr₂.{v}
        (_root_.SheafOfModules.comparisonComp φ θ) (Functor.isoWhiskerRight e H) he' =
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pushforward.{v} θ)
        (_root_.SheafOfModules.pushforwardCongr₂.{v} φ e he) := by
  ext M U x
  rfl

end Stacks.SheafOfModules

end
