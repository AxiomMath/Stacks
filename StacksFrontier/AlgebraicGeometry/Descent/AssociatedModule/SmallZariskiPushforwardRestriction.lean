module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom

/-!
# The direct image of a morphism of schemes against the small Zariski restriction

Let `f : T ⟶ S` be a morphism of schemes of a big Zariski site.  Restriction along the
inclusion of the opens of the space of `S` into the small Zariski site,
`AlgebraicGeometry.SmallZariski.restrictModule`, is the right adjoint of the associated-module
functor of Stacks 03DU (4) at `τ = Zariski`.  This file is the statement for the right
adjoints:

the restriction to the opens of `S` of `f_{small, *} 𝓖` is `f_*` of the restriction of `𝓖` to
the opens of `T`,

for an arbitrary `𝒪`-module `𝓖` on the small Zariski site of `T` and an arbitrary morphism `f`.

This is the small Zariski counterpart of
`AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardRestriction.lean`),
which is the same square at `τ = étale`; Stacks 071N states its comparison "for either the
étale or the Zariski topology", and before this file the Zariski side of the comparison had no
inputs at all.

## Main definitions

* `AlgebraicGeometry.SmallZariski.baseChangeOpensIso`: **the geometric half of the square**,
  that base-changing an open of `S` along `f` gives the preimage open.
* `AlgebraicGeometry.SmallZariski.structureMapRing`: the structure map of `f_small`, read on
  sheaves of not necessarily commutative rings.
* `AlgebraicGeometry.SmallZariski.restrictModulePushforwardSquareIso`: **the square of direct
  images**, as an isomorphism of functors.
* `AlgebraicGeometry.SmallZariski.restrictModulePushforwardObjIso`: the same at one module.

## Main results

* `AlgebraicGeometry.SmallZariski.smallZariskiToOpens_baseChange`: the open image of the base
  change of an object of the small Zariski site of `S` is the preimage of its open image.
* `AlgebraicGeometry.SmallZariski.structureMap_comp_baseChangeOpensIso`: **the ring half of the
  square**, that the two composite comparisons of structure sheaves agree.

## Implementation notes

As on the étale side, all four functors round the square are
`CategoryTheory.SheafOfModules.pushforward`s — restriction along a continuous functor of sites
— so the identification is `CategoryTheory.SheafOfModules.pushforwardComp` at each corner and
`CategoryTheory.SheafOfModules.pushforwardCongr₂` in the middle, over the two halves below.  No
mate argument and no adjointness is needed.

What has to be rebuilt rather than transported is the two halves, and the Zariski site forces a
different construction for each.  The inclusion of the opens of `S`,
`AlgebraicGeometry.SmallZariski.opensToSmallZariski`, is the *inverse of an equivalence* — the
open-image comparison `AlgebraicGeometry.smallZariskiSiteEquiv` of Stacks 020X — and not a
concrete functor sending an open to a chosen object, which is what the étale file has.  So the
geometric half is built by descending an isomorphism along that equivalence
(`CategoryTheory.Functor.fullyFaithfulCancelRight`): its components are checked after taking
open images, where the target category is a lattice of opens, so both the component equality and
its naturality are equalities of opens.  The component equality is
`AlgebraicGeometry.SmallZariski.smallZariskiToOpens_baseChange`, which comes from
`AlgebraicGeometry.smallZariskiBaseChangeIso` — the identification of small Zariski base change
with the fibre product, the only data `AlgebraicGeometry.smallZariskiBaseChange` carries, it
being defined by a choice — together with `AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd`.

For the ring half the étale file can quote
`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`, because at `τ = étale` the objects
of the small Zariski site in play are literally open subschemes.  Here they are only isomorphic
to open subschemes, so the comparison of structure sheaves is the canonical identification
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop` of the sections of `𝒪_S` over an open image with the
global functions of the object, and the statement to prove is
`AlgebraicGeometry.SmallZariski.appTop_square_of_comp`: for two open immersions `jX`, `jY` lying
over `g` through `n`, the two ways of pulling a section of `𝒪_{S}` over an open `V` back to a
global function on the source of `jX` agree.  Both are `AlgebraicGeometry.Scheme.Hom.appLE` of
the one composite, so the proof is `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` on each side
and then the commuting square.

No `@[stacks]` attribute is carried, exactly as on the étale side: the tag the square belongs
to, Stacks 070R (2), is about the morphism of ringed sites `f_small`, which
`AlgebraicGeometry.smallZariskiRingedSiteHom` already builds; this is a compatibility of the
functors formed from it.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SmallZariski

/-- **Pulling a section back to a global function, two ways round a square.**  Let `jX` and
`jY` be open immersions and let `n` carry `jX` to `jY` over `g`, that is `n ≫ jY = jX ≫ g`.  For
an open `V` of `S'` containing the image of `jY`, restricting a section of `𝒪_{S'}` over `V` to
the image of `jY`, reading it as a global function there and pulling it back along `n` is
pulling it back along `g` and then reading it as a global function on the source of `jX`.

Both composites are `AlgebraicGeometry.Scheme.Hom.appLE` of the common composite
`n ≫ jY = jX ≫ g` over `V`, by `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`. -/
public theorem appTop_square_of_comp {X Y S' T' : Scheme.{u}} (g : T' ⟶ S')
    (jX : X ⟶ T') (jY : Y ⟶ S') [IsOpenImmersion jX] [IsOpenImmersion jY]
    (n : X ⟶ Y) (w : n ≫ jY = jX ≫ g) (V : S'.Opens)
    (h₁ : jY.opensRange ≤ V) (h₂ : jX.opensRange ≤ g ⁻¹ᵁ V) :
    (S'.presheaf.map (homOfLE h₁).op ≫ (IsOpenImmersion.ΓIsoTop jY).inv) ≫ n.appTop =
      g.app V ≫ (T'.presheaf.map (homOfLE h₂).op ≫ (IsOpenImmersion.ΓIsoTop jX).inv) := by
  have key : ∀ {k l : X ⟶ S'} (_ : k = l) (e : (⊤ : X.Opens) ≤ k ⁻¹ᵁ V)
      (e' : (⊤ : X.Opens) ≤ l ⁻¹ᵁ V), k.appLE V ⊤ e = l.appLE V ⊤ e' := by
    intro k l hk e e'
    subst hk
    rfl
  have hn : n.appTop = n.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  rw [openImmersion_ΓIsoTop_inv, openImmersion_ΓIsoTop_inv, Scheme.Hom.map_appLE,
    Scheme.Hom.map_appLE, hn, Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_comp_appLE n jY V ⊤ ⊤ _ _).trans
    ((key w _ _).trans (Scheme.Hom.appLE_comp_appLE jX g V (g ⁻¹ᵁ V) ⊤ _ _).symm)

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- The morphism of schemes underlying a morphism of the big Zariski site. -/
public abbrev schemeHom : T.1 ⟶ S.1 := B.inclusion.map f

section Geometric

variable (W : SmallZariski B S.1 S.property)

/-- The structure morphism of an object of the small Zariski site of `S` is an open
immersion. -/
public instance isOpenImmersion_smallZariskiHom :
    IsOpenImmersion (B.inclusion.map W.obj.hom) := W.property

/-- The comparison of the base change of `W` along `f` with the fibre product `T ×_S W`, read on
schemes.  It is the only data `AlgebraicGeometry.smallZariskiBaseChange` carries, that functor
being defined by a choice. -/
public noncomputable abbrev baseChangeLeft :
    B.inclusion.obj ((smallZariskiBaseChange B f).obj W).obj.left ⟶
      pullback (B.inclusion.map W.obj.hom) (schemeHom B f) :=
  ((smallZariskiBaseChangeIso B f).hom.app W).left

/-- The comparison with the fibre product is an isomorphism of schemes, being a component of an
isomorphism of functors into a slice category. -/
public instance isIso_baseChangeLeft : IsIso (baseChangeLeft B f W) :=
  inferInstanceAs (IsIso ((Over.forget _).map ((smallZariskiBaseChangeIso B f).hom.app W)))

/-- The comparison with the fibre product is over `T`. -/
public theorem baseChangeLeft_snd :
    baseChangeLeft B f W ≫ pullback.snd (B.inclusion.map W.obj.hom) (schemeHom B f) =
      B.inclusion.map ((smallZariskiBaseChange B f).obj W).obj.hom :=
  Over.w ((smallZariskiBaseChangeIso B f).hom.app W)

/-- The open image of the base change of `W` is the preimage of the open image of `W`. -/
public theorem smallZariskiToOpens_baseChange :
    (smallZariskiToOpens B T.1 T.property).obj ((smallZariskiBaseChange B f).obj W) =
      (schemeHom B f) ⁻¹ᵁ (smallZariskiToOpens B S.1 S.property).obj W := by
  have h : (baseChangeLeft B f W ≫
        pullback.snd (B.inclusion.map W.obj.hom) (schemeHom B f)).opensRange =
      (schemeHom B f) ⁻¹ᵁ (B.inclusion.map W.obj.hom).opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]
  have h2 : (B.inclusion.map ((smallZariskiBaseChange B f).obj W).obj.hom).opensRange =
      (schemeHom B f) ⁻¹ᵁ (B.inclusion.map W.obj.hom).opensRange := by
    simpa only [baseChangeLeft_snd] using h
  exact h2

/-- The square relating the base-change projection to `W` with `f`. -/
public theorem baseChangeLeft_fst_comp :
    (baseChangeLeft B f W ≫ pullback.fst (B.inclusion.map W.obj.hom) (schemeHom B f)) ≫
        B.inclusion.map W.obj.hom =
      B.inclusion.map ((smallZariskiBaseChange B f).obj W).obj.hom ≫ schemeHom B f := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, baseChangeLeft_snd]

end Geometric

/-- The open image of the object of the small Zariski site attached to an open is that open. -/
public theorem smallZariskiToOpens_opensToSmallZariski (S' : Scheme.{u}) (hS' : B.Contains S')
    (V : S'.Opens) :
    (smallZariskiToOpens B S' hS').obj ((opensToSmallZariski B S' hS').obj V) = V :=
  le_antisymm (leOfHom ((smallZariskiSiteEquiv B S' hS').counitIso.app V).hom)
    (leOfHom ((smallZariskiSiteEquiv B S' hS').counitIso.app V).inv)

/-! ### Continuity of the two routes round the square -/

/-- Taking preimages along `f` is a continuous functor of the Zariski sites of the spaces. -/
public instance isContinuous_opensMap :
    (Opens.map (schemeHom B f).base).IsContinuous
      (Opens.grothendieckTopology ↥S.1) (Opens.grothendieckTopology ↥T.1) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
    (coverPreserving_opens_map _)

/-- Taking the preimage of an open of `S` and including it into the small Zariski site of `T`
is a continuous functor. -/
public instance isContinuous_opensMap_comp_opensToSmallZariski :
    (Opens.map (schemeHom B f).base ⋙ opensToSmallZariski B T.1 T.property).IsContinuous
      (Opens.grothendieckTopology ↥S.1) (topology B T.1 T.property) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _ (isContinuous_opensMap B f) inferInstance

/-- Including an open of `S` into the small Zariski site of `S` and base-changing along `f` is
a continuous functor. -/
public instance isContinuous_opensToSmallZariski_comp_baseChange :
    (opensToSmallZariski B S.1 S.property ⋙ smallZariskiBaseChange B f).IsContinuous
      (Opens.grothendieckTopology ↥S.1) (topology B T.1 T.property) :=
  Functor.isContinuous_comp _ _ _ (topology B S.1 S.property) _

/-! ### The geometric half of the square -/

/-- **Base change along `f` carries the opens of `S` to their preimages.**  Taking the preimage
of an open of `S` and including it into the small Zariski site of `T` is including the open into
the small Zariski site of `S` and base-changing along `f`.

The small Zariski site of a scheme is equivalent to the lattice of opens of its space by the
open-image comparison of Stacks 020X, and the inclusion of the opens is the inverse of that
equivalence, so it is enough to give the isomorphism after taking open images.  There it is
`AlgebraicGeometry.SmallZariski.smallZariskiToOpens_baseChange`, and the naturality is automatic,
the opens of a space being a lattice. -/
public noncomputable def baseChangeOpensIso :
    Opens.map (schemeHom B f).base ⋙ opensToSmallZariski B T.1 T.property ≅
      opensToSmallZariski B S.1 S.property ⋙ smallZariskiBaseChange B f :=
  Functor.fullyFaithfulCancelRight (smallZariskiToOpens B T.1 T.property)
    (NatIso.ofComponents
      (fun V => eqToIso (by
        change (smallZariskiToOpens B T.1 T.property).obj
            ((opensToSmallZariski B T.1 T.property).obj ((schemeHom B f) ⁻¹ᵁ V)) =
          (smallZariskiToOpens B T.1 T.property).obj ((smallZariskiBaseChange B f).obj
            ((opensToSmallZariski B S.1 S.property).obj V))
        rw [smallZariskiToOpens_opensToSmallZariski, smallZariskiToOpens_baseChange,
          smallZariskiToOpens_opensToSmallZariski]))
      (fun _ => Subsingleton.elim _ _))

/-! ### The structure map on sheaves of rings -/

/-- **The structure map of `f_small`, read on sheaves of not necessarily commutative rings.**
Over an object `W / S` of the small Zariski site it pulls a global function on `W` back along the
base-change projection `T ×_S W ⟶ W`.

This is the structure map `AlgebraicGeometry.smallZariskiStructureSharp` of the morphism of
ringed sites `AlgebraicGeometry.smallZariskiRingedSiteHom` of Stacks 070R (2) with the
commutativity of the sections forgotten; sheaves of modules are indexed by a sheaf of rings, so
this is the form over which pushforward of sheaves of modules along `f_small` is taken. -/
public noncomputable def structureMapRing :
    structureSheaf B S.1 S.property ⟶
      ((smallZariskiBaseChange B f).sheafPushforwardContinuous RingCat.{u}
          (topology B S.1 S.property) (topology B T.1 T.property)).obj
        (structureSheaf B T.1 T.property) :=
  ObjectProperty.homMk (Functor.whiskerRight (smallZariskiRingedSiteHom B f).fsharp.hom
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The structure map of `f_small` is pullback of functions along the base-change projection. -/
@[simp]
public theorem structureMapRing_hom_app (W : SmallZariski B S.1 S.property) :
    (structureMapRing B f).hom.app (op W) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map (op (baseChangeLeft B f W ≫
          pullback.fst (B.inclusion.map W.obj.hom) (schemeHom B f)))) :=
  rfl

/-! ### The ring half of the square -/

/-- **The section identity over an open of `S`.**  Restricting a section of `𝒪_S` over an open
`V` to the object of the small Zariski site attached to `V`, reading it as a global function
there and pulling it back along the base-change projection and the comparison of
`AlgebraicGeometry.SmallZariski.baseChangeOpensIso` is pulling it back along `f` and reading it
as a global function on the object attached to `f⁻¹(V)`. -/
public theorem appTop_baseChangeOpens (V : S.1.Opens) :
    (S.1.presheaf.map (homOfLE
            (smallZariskiToOpens_opensToSmallZariski B S.1 S.property V).le).op ≫
          (IsOpenImmersion.ΓIsoTop (smallZariskiOpenImmersion B S.1 S.property
            ((opensToSmallZariski B S.1 S.property).obj V))).inv) ≫
        (B.inclusion.map ((baseChangeOpensIso B f).hom.app V).hom.left ≫
          (baseChangeLeft B f ((opensToSmallZariski B S.1 S.property).obj V) ≫
            pullback.fst
              (B.inclusion.map ((opensToSmallZariski B S.1 S.property).obj V).obj.hom)
              (schemeHom B f))).appTop =
      (schemeHom B f).app V ≫
        (T.1.presheaf.map (homOfLE
              (smallZariskiToOpens_opensToSmallZariski B T.1 T.property
                ((schemeHom B f) ⁻¹ᵁ V)).le).op ≫
          (IsOpenImmersion.ΓIsoTop (smallZariskiOpenImmersion B T.1 T.property
            ((opensToSmallZariski B T.1 T.property).obj ((schemeHom B f) ⁻¹ᵁ V)))).inv) := by
  refine appTop_square_of_comp (schemeHom B f) _ _ _ ?_ V _ _
  have h₂ : B.inclusion.map ((baseChangeOpensIso B f).hom.app V).hom.left ≫
        B.inclusion.map ((smallZariskiBaseChange B f).obj
          ((opensToSmallZariski B S.1 S.property).obj V)).obj.hom =
      B.inclusion.map ((opensToSmallZariski B T.1 T.property).obj
        ((schemeHom B f) ⁻¹ᵁ V)).obj.hom := by
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w ((baseChangeOpensIso B f).hom.app V).hom)
  rw [Category.assoc, baseChangeLeft_fst_comp, ← Category.assoc, h₂]

/-- **The two composite comparisons of structure sheaves agree.**  This is the ring half of the
square of ringed sites: over an open `V` of `S` both composites are the map of global functions
of `AlgebraicGeometry.SmallZariski.appTop_baseChangeOpens`, with the commutativity of the
sections forgotten. -/
public theorem structureMap_comp_baseChangeOpensIso :
    SheafOfModules.comparisonComp (structureMap B S.1 S.property) (structureMapRing B f) ≫
        (Functor.sheafPushforwardContinuousNatTrans (baseChangeOpensIso B f).hom RingCat.{u}
          (Opens.grothendieckTopology ↥S.1) (topology B T.1 T.property)).app
          (structureSheaf B T.1 T.property) =
      SheafOfModules.comparisonComp (schemeHom B f).toRingCatSheafHom
        (structureMap B T.1 T.property) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  exact congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map (appTop_baseChangeOpens B f V.unop)

/-! ### The square of direct images -/

/-- Pushforward of sheaves of modules along `f_small` has a left adjoint: the small Zariski site
of `S` is essentially small in the universe of the sections of the structure sheaves. -/
public instance pushforward_structureMapRing_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (structureMapRing B f)).IsRightAdjoint :=
  SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall.{u} _

/-- Pushforward of sheaves of modules along `f` has a left adjoint; this is the pushforward of
`𝒪`-modules of a morphism of schemes, restated at the spelling the square consumes. -/
public instance pushforward_toRingCatSheafHom_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (schemeHom B f).toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward (schemeHom B f)).IsRightAdjoint

/-- **The direct image along `f_small` commutes with restriction to the opens of the space.**
For an `𝒪`-module `𝓖` on the small Zariski site of `T`, the restriction to the opens of `S` of
the direct image of `𝓖` along the morphism of ringed sites `f_small` of Stacks 070R (2) is the
direct image along `f` of the restriction of `𝓖` to the opens of `T`.

Both routes round the square are pushforwards of sheaves of modules, so this is
`CategoryTheory.SheafOfModules.pushforwardComp` at the two corners and
`CategoryTheory.SheafOfModules.pushforwardCongr₂` over
`AlgebraicGeometry.SmallZariski.baseChangeOpensIso` and
`AlgebraicGeometry.SmallZariski.structureMap_comp_baseChangeOpensIso` in the middle. -/
public noncomputable def restrictModulePushforwardSquareIso :
    SheafOfModules.pushforward.{u} (structureMapRing B f) ⋙ restrictModule B S.1 S.property ≅
      restrictModule B T.1 T.property ⋙ Scheme.Modules.pushforward (schemeHom B f) :=
  SheafOfModules.pushforwardComp.{u} (structureMap B S.1 S.property)
      (structureMapRing B f) ≪≫
    SheafOfModules.pushforwardCongr₂.{u}
      (SheafOfModules.comparisonComp (structureMap B S.1 S.property) (structureMapRing B f))
      (baseChangeOpensIso B f) (structureMap_comp_baseChangeOpensIso B f) ≪≫
    (SheafOfModules.pushforwardComp.{u} (schemeHom B f).toRingCatSheafHom
      (structureMap B T.1 T.property)).symm

/-- **The direct image along `f_small` commutes with restriction to the opens of the space**, at
one module. -/
public noncomputable def restrictModulePushforwardObjIso
    (𝓖 : SheafOfModules.{u} (structureSheaf B T.1 T.property)) :
    (restrictModule B S.1 S.property).obj
        ((SheafOfModules.pushforward.{u} (structureMapRing B f)).obj 𝓖) ≅
      (Scheme.Modules.pushforward (schemeHom B f)).obj
        ((restrictModule B T.1 T.property).obj 𝓖) :=
  (restrictModulePushforwardSquareIso B f).app 𝓖

end AlgebraicGeometry.SmallZariski

end
