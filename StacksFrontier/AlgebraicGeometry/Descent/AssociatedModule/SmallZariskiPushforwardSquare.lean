module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiSpaceFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall

/-!
# Stacks 03LC at `τ = Zariski` and Stacks 03FH (2) at the small Zariski site

Let `f : T ⟶ S` be a morphism of schemes of a big Zariski site and let
`f_small : (T_Zar, 𝒪) ⟶ (S_Zar, 𝒪)` be the morphism of ringed small Zariski sites of
Stacks 070R (2), `AlgebraicGeometry.smallZariskiRingedSiteHom`.  This file proves, for the
functor `𝓖 ↦ 𝓖^a` of Definition 03DU (4) at `τ = Zariski`,
`AlgebraicGeometry.SmallZariski.associatedModule`:

* **Stacks 03LC part (1) at `τ = Zariski`**, that `(f^*𝓖)^a ≅ f_small^*(𝓖^a)` — which is at the
  same time **Stacks 03FH part (2) for the small Zariski `f_small` of Remark 070R (2)**, the two
  clauses being the same statement at this `f_sites`; both are registered on the one
  declaration `AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`, as
  `AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso` registers both for the big
  sites; and
* **part (3) at `τ = Zariski`** in two of its three conjuncts: that
  `f_{small, *}(𝓕^a) ≅ (f_*𝓕)^a`, and that `f_{small, *}` carries modules quasi-coherent on
  `T_Zar` to modules quasi-coherent on `S_Zar` when `f` is quasi-compact and quasi-separated.

The third conjunct of part (3), that the ordinary `f_*` preserves quasi-coherence, is Stacks
01LC, `AlgebraicGeometry.pushforward_isQuasicoherent`, where part (3) is already registered.

The clauses are stated over the functor the source names, not over the identity reading of
`StacksDraft.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiEquivalence`: the coefficient
sheaf of Definition 03DU (2) on `S_Zar` is the sheaf `T/S ↦ Γ(T, 𝒪_T)`, isomorphic to `𝒪_S` and
not equal to it, so the identity reading states something else — as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSite` and
`...SmallZariskiRealFullyFaithful` record.  The same convention is what puts clause (2) of
Stacks 03DX at `τ = Zariski` on `AlgebraicGeometry.SmallZariski.associatedModuleEquivalence`.

## The proof

Part (1) is `SheafOfModules.pullbackSquareIso`, Stacks 03D8 for a square of morphisms of ringed
sites, so it needs exactly two inputs.

* The **geometric half**: the base change of the object of `S_Zar` chosen over an open `V` of `S`
  is the object of `T_Zar` chosen over `f⁻¹(V)`.  Both `AlgebraicGeometry.smallZariskiBaseChange`
  and `AlgebraicGeometry.SmallZariski.opensToSmallZariski` pick their values by `Classical.choice`,
  so nothing is known about those two objects individually; but the open image of each is
  `f⁻¹(V)` — by `AlgebraicGeometry.smallZariskiToOpens_baseChange_obj` and
  `AlgebraicGeometry.smallZariskiToOpens_opensToSmallZariski_obj`, equalities rather than
  isomorphisms because `S.Opens` is a poset — and `AlgebraicGeometry.smallZariskiToOpens` is fully
  faithful, which makes them isomorphic.  Naturality is free: the small Zariski site is thin.
* The **ring half**: both routes round the square pull a function on `V` back along one morphism
  of schemes.  The component of the structure-sheaf comparison of the small Zariski site at `V` is
  `AlgebraicGeometry.Scheme.Hom.appLE` of the open immersion of the chosen object
  (`AlgebraicGeometry.SmallZariski.lcStructureIso_hom_app`), `f_small^♯` is pullback along the
  base-change projection, and the two morphisms of schemes agree by
  `AlgebraicGeometry.SmallZariski.lcProjection_comp_openImmersion`, which is the fibre-product
  square of the base change together with the comparison of chosen objects being a morphism over
  `T`.

Part (3) is then formal, and that is special to `τ = Zariski`: `f_{small, *}(𝓕^a)` restricts along
the inclusion of the opens of `S` to `f_*𝓕`, by the mate square of part (1) and the unit
isomorphism, and the counit of the associated-module adjunction of `S_Zar` is an isomorphism at
*every* module, `AlgebraicGeometry.SmallZariski.restrictModule` being an equivalence
(`AlgebraicGeometry.isIso_counit_smallZariskiAssociatedModuleAdjunction`).  So
`f_{small, *}(𝓕^a)` is the associated module of `f_*𝓕`.  Quasi-coherence of the direct image then
follows from Stacks 01LC and Stacks 03DV (2), every quasi-coherent module on `T_Zar` being an
associated module.  At `τ = étale` the counit is an isomorphism only over quasi-coherence of the
module on the site, and that conjunct of part (3) is not available; see
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardSquare.lean`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.lcStructureMapRing`: `f_small^♯` over sheaves of rings, the
  form the pullback and pushforward of sheaves of modules are taken along.
* `AlgebraicGeometry.SmallZariski.lcBaseChangeOpensIso`: the geometric half of the square.
* `AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`: **Stacks 03LC part (1) at
  `τ = Zariski`, equivalently Stacks 03FH part (2) at the small Zariski `f_sites`.**
* `AlgebraicGeometry.SmallZariski.lcAssociatedModuleObjPullbackIso`: the same at one module,
  which is the form in which Stacks 03FH states its clause.
* `AlgebraicGeometry.SmallZariski.lcRestrictModuleBaseChangeIso`: the mate square of the two
  composite restrictions.
* `AlgebraicGeometry.SmallZariski.lcAssociatedModuleSmallPushforwardIso` and
  `...lcAssociatedModuleSmallPushforwardNatIso`: **Stacks 03LC part (3) at `τ = Zariski`, the
  commuting square**, at one module and as an isomorphism of functors.

## Main results

* `AlgebraicGeometry.SmallZariski.lcProjection_comp_openImmersion` and
  `...lcSections_square`: the geometric and the sections identity round the square.
* `AlgebraicGeometry.SmallZariski.lcStructureMap_comp_baseChangeOpensIso`: the ring half of the
  square, the second input of `SheafOfModules.pullbackSquareIso`.
* `AlgebraicGeometry.SmallZariski.lcIsQuasicoherentOnSite_smallPushforward`: **Stacks 03LC
  part (3) at `τ = Zariski`, preservation of quasi-coherence by `f_{small, *}`.**

## Implementation notes

Every name here is prefixed `lc`, the file being written beside two other developments of the
same square — the big sites of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigSites.lean` and the small étale
site of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleMorphismBaseChange.lean` —
whose plain names are taken.
The plain name `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso` is taken too, by the
identity reading in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiMorphismPullback.lean`.

The continuity instances are written with `Functor.IsContinuous.{u}`, pinning the universe of the
sheaves of sets to that of the sections of the structure sheaves:
`AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites` is stated one universe up, and
`AlgebraicGeometry.smallZariskiBaseChange_isMorphismOfSites_ringUniverse` is the instance the
square needs.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- The morphism of schemes underlying a morphism of the big Zariski site, at the spelling the
small Zariski sites of its source and target consume. -/
public abbrev lcSchemeHom : T.1 ⟶ S.1 := B.inclusion.map f

/-- Two objects of the small Zariski site with the same open image are isomorphic. -/
public noncomputable def lcIsoOfOpensEq (X : Scheme.{u}) (hX : B.Contains X)
    {U V : SmallZariski B X hX}
    (h : (smallZariskiToOpens B X hX).obj U = (smallZariskiToOpens B X hX).obj V) :
    U ≅ V :=
  (smallZariskiToOpens B X hX).preimageIso (eqToIso h)

/-- The base change of the object chosen over an open `V` of `S` is the object chosen over the
preimage of `V`. -/
public noncomputable def lcBaseChangeOpensObjIso (V : (S.1).Opens) :
    (opensToSmallZariski B T.1 T.property).obj (lcSchemeHom B f ⁻¹ᵁ V) ≅
      (smallZariskiBaseChange B f).obj ((opensToSmallZariski B S.1 S.property).obj V) :=
  lcIsoOfOpensEq B T.1 T.property
    (by
      rw [smallZariskiToOpens_baseChange_obj,
        smallZariskiToOpens_opensToSmallZariski_obj B S.1 S.property V,
        smallZariskiToOpens_opensToSmallZariski_obj B T.1 T.property])

/-- **Base change carries the opens of `S` to the opens of `T`.**  Taking the preimage of an open
of `S` and choosing the object of the small Zariski site of `T` over it is choosing the object of
the small Zariski site of `S` over the open and base-changing along `f`. -/
public noncomputable def lcBaseChangeOpensIso :
    Opens.map (lcSchemeHom B f).base ⋙ opensToSmallZariski B T.1 T.property ≅
      opensToSmallZariski B S.1 S.property ⋙ smallZariskiBaseChange B f :=
  NatIso.ofComponents (fun V ↦ lcBaseChangeOpensObjIso B f V)
    fun {_ _} _ ↦ Subsingleton.elim _ _

/-- Taking preimages along the morphism of schemes is a continuous functor of the sites of
opens. -/
public instance lcIsContinuous_opensMap :
    (Opens.map (lcSchemeHom B f).base).IsContinuous.{u}
      (Opens.grothendieckTopology ↥S.1) (Opens.grothendieckTopology ↥T.1) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
    (coverPreserving_opens_map _)

/-- Taking the preimage of an open of `S` and choosing the object of the small Zariski site of
`T` over it is a continuous functor. -/
public instance lcIsContinuous_opensMap_comp_opensToSmallZariski :
    (Opens.map (lcSchemeHom B f).base ⋙ opensToSmallZariski B T.1 T.property).IsContinuous.{u}
      (Opens.grothendieckTopology ↥S.1) (topology B T.1 T.property) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _ (lcIsContinuous_opensMap B f) inferInstance

/-- Choosing the object of the small Zariski site of `S` over an open and base-changing along
`f` is a continuous functor. -/
public instance lcIsContinuous_opensToSmallZariski_comp_baseChange :
    (opensToSmallZariski B S.1 S.property ⋙ smallZariskiBaseChange B f).IsContinuous.{u}
      (Opens.grothendieckTopology ↥S.1) (topology B T.1 T.property) :=
  Functor.isContinuous_comp _ _ _ (topology B S.1 S.property) _

/-- **`f_small^♯` on sheaves of not necessarily commutative rings.**  This is
`AlgebraicGeometry.smallZariskiStructureSharp`, the structure map of the morphism of ringed
small Zariski sites of Stacks 070R (2), with the commutativity of the sections forgotten:
sheaves of modules are indexed by a sheaf of rings, so this is the form over which the pullback
and pushforward of sheaves of modules along `f_small` are formed. -/
public noncomputable def lcStructureMapRing :
    structureSheaf B S.1 S.property ⟶
      ((smallZariskiBaseChange B f).sheafPushforwardContinuous RingCat.{u}
          (topology B S.1 S.property) (topology B T.1 T.property)).obj
        (structureSheaf B T.1 T.property) :=
  ObjectProperty.homMk (Functor.whiskerRight (smallZariskiStructureSharp B f).hom
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The object chosen over an open `V` has `V` as the preimage of `V` along its open
immersion. -/
public theorem lcTop_le_preimage (X : Scheme.{u}) (hX : B.Contains X) (V : X.Opens) :
    (⊤ : ((SmallZariski.toScheme B X hX).obj
        ((opensToSmallZariski B X hX).obj V)).Opens) ≤
      smallZariskiOpenImmersion B X hX ((opensToSmallZariski B X hX).obj V) ⁻¹ᵁ V := by
  have h : (smallZariskiOpenImmersion B X hX
      ((opensToSmallZariski B X hX).obj V)).opensRange = V :=
    smallZariskiToOpens_opensToSmallZariski_obj B X hX V
  intro x _
  have hx : (smallZariskiOpenImmersion B X hX ((opensToSmallZariski B X hX).obj V)).base x ∈
      (smallZariskiOpenImmersion B X hX ((opensToSmallZariski B X hX).obj V)).opensRange :=
    ⟨x, rfl⟩
  rw [h] at hx
  exact hx

/-- **The component of the structure-sheaf comparison of the small Zariski site at an open `V`
is the pullback of functions along the open immersion of the object chosen over `V`.** -/
public theorem lcStructureIso_hom_app (X : Scheme.{u}) (hX : B.Contains X) (V : X.Opens) :
    (smallZariskiCommStructureIso B X hX).hom.app (op V) =
      (smallZariskiOpenImmersion B X hX ((opensToSmallZariski B X hX).obj V)).appLE V ⊤
        (lcTop_le_preimage B X hX V) := by
  change X.presheaf.map _ ≫ (IsOpenImmersion.ΓIsoTop _).inv = _
  refine Eq.trans (congrArg (fun k => X.presheaf.map
      ((smallZariskiSiteEquiv B X hX).op.counitIso.inv.app (op V)) ≫ k)
    (openImmersion_ΓIsoTop_inv (smallZariskiOpenImmersion B X hX
      ((opensToSmallZariski B X hX).obj V)))) ?_
  exact Scheme.Hom.map_appLE _ _ _

/-- **The base-change projection of the object chosen over an open, followed by its open
immersion, is the open immersion of the object chosen over the preimage followed by `f`.**  This
is the geometric content of the square: the projection `X ×_S V ⟶ V` of the base change sits in
the fibre-product square, and the comparison of the chosen objects is a morphism over `T`. -/
public theorem lcProjection_comp_openImmersion (V : (S.1).Opens) :
    ((SmallZariski.toScheme B T.1 T.property).map ((lcBaseChangeOpensIso B f).hom.app V) ≫
        ((smallZariskiBaseChangeIso B f).hom.app
            ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
          pullback.fst ((smallSiteInSchemesOver B S).obj
            ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f)) ≫
      smallZariskiOpenImmersion B S.1 S.property
          ((opensToSmallZariski B S.1 S.property).obj V) =
    smallZariskiOpenImmersion B T.1 T.property
        ((opensToSmallZariski B T.1 T.property).obj (lcSchemeHom B f ⁻¹ᵁ V)) ≫
      lcSchemeHom B f := by
  have hc : (SmallZariski.toScheme B T.1 T.property).map
        ((lcBaseChangeOpensIso B f).hom.app V) ≫
        smallZariskiOpenImmersion B T.1 T.property
          ((smallZariskiBaseChange B f).obj
            ((opensToSmallZariski B S.1 S.property).obj V)) =
      smallZariskiOpenImmersion B T.1 T.property
        ((opensToSmallZariski B T.1 T.property).obj (lcSchemeHom B f ⁻¹ᵁ V)) :=
    smallZariskiOpenImmersion_comp B T.1 T.property ((lcBaseChangeOpensIso B f).hom.app V)
  have hw : ((smallZariskiBaseChangeIso B f).hom.app
          ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
        pullback.snd ((smallSiteInSchemesOver B S).obj
          ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f) =
      smallZariskiOpenImmersion B T.1 T.property
        ((smallZariskiBaseChange B f).obj
          ((opensToSmallZariski B S.1 S.property).obj V)) :=
    ((smallZariskiBaseChangeIso B f).hom.app
      ((opensToSmallZariski B S.1 S.property).obj V)).w
  have hcond : pullback.fst ((smallSiteInSchemesOver B S).obj
          ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f) ≫
        smallZariskiOpenImmersion B S.1 S.property
          ((opensToSmallZariski B S.1 S.property).obj V) =
      pullback.snd ((smallSiteInSchemesOver B S).obj
          ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f) ≫
        lcSchemeHom B f :=
    pullback.condition
  have hbc : ((smallZariskiBaseChangeIso B f).hom.app
          ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
        pullback.fst ((smallSiteInSchemesOver B S).obj
          ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f) ≫
          smallZariskiOpenImmersion B S.1 S.property
            ((opensToSmallZariski B S.1 S.property).obj V) =
      smallZariskiOpenImmersion B T.1 T.property
          ((smallZariskiBaseChange B f).obj
            ((opensToSmallZariski B S.1 S.property).obj V)) ≫ lcSchemeHom B f :=
    (congrArg (fun k => ((smallZariskiBaseChangeIso B f).hom.app
        ((opensToSmallZariski B S.1 S.property).obj V)).left ≫ k) hcond).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ lcSchemeHom B f) hw))
  refine (Category.assoc _ _ _).trans (Eq.trans (congrArg
    (fun k => (SmallZariski.toScheme B T.1 T.property).map
      ((lcBaseChangeOpensIso B f).hom.app V) ≫ k)
    ((Category.assoc _ _ _).trans hbc)) ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ lcSchemeHom B f) hc)

/-- The whole space is contained in the preimage of the whole space. -/
public theorem lcTop_le_preimage_top {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (⊤ : X.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := fun _ _ => trivial

/-- Over the whole space, `AlgebraicGeometry.Scheme.Hom.appLE` is
`AlgebraicGeometry.Scheme.Hom.appTop`. -/
public theorem lcAppLE_top {X Y : Scheme.{u}} (g : X ⟶ Y) :
    g.appLE ⊤ ⊤ (lcTop_le_preimage_top g) = g.appTop :=
  Scheme.Hom.appLE_preimage_self g ⊤

/-- `AlgebraicGeometry.Scheme.Hom.appLE` depends on the morphism only through its value. -/
public theorem lcAppLE_congr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g')
    (U : Y.Opens) (W : X.Opens) (e : W ≤ g ⁻¹ᵁ U) (e' : W ≤ g' ⁻¹ᵁ U) :
    g.appLE U W e = g'.appLE U W e' := by
  subst h
  rfl

/-- **The sections identity round the square**, in `CommRingCat`: pulling a function on an open
`V` of `S` back to the object chosen over `V` and then along the base-change projection is
pulling it back along `f` and then to the object chosen over the preimage of `V`.  Both are the
pullback of functions along one morphism of schemes, by
`AlgebraicGeometry.SmallZariski.lcProjection_comp_openImmersion`. -/
public theorem lcSections_square (V : (S.1).Opens) :
    (smallZariskiOpenImmersion B S.1 S.property
          ((opensToSmallZariski B S.1 S.property).obj V)).appLE V ⊤
        (lcTop_le_preimage B S.1 S.property V) ≫
      ((SmallZariski.toScheme B T.1 T.property).map ((lcBaseChangeOpensIso B f).hom.app V) ≫
        ((smallZariskiBaseChangeIso B f).hom.app
            ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
          pullback.fst ((smallSiteInSchemesOver B S).obj
            ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f)).appTop =
    (lcSchemeHom B f).app V ≫
      (smallZariskiOpenImmersion B T.1 T.property
          ((opensToSmallZariski B T.1 T.property).obj (lcSchemeHom B f ⁻¹ᵁ V))).appLE
        (lcSchemeHom B f ⁻¹ᵁ V) ⊤ (lcTop_le_preimage B T.1 T.property _) := by
  have h1 := Scheme.Hom.appLE_comp_appLE
    ((SmallZariski.toScheme B T.1 T.property).map ((lcBaseChangeOpensIso B f).hom.app V) ≫
      ((smallZariskiBaseChangeIso B f).hom.app
          ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
        pullback.fst ((smallSiteInSchemesOver B S).obj
          ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f))
    (smallZariskiOpenImmersion B S.1 S.property ((opensToSmallZariski B S.1 S.property).obj V))
    V ⊤ ⊤ (lcTop_le_preimage B S.1 S.property V) (lcTop_le_preimage_top _)
  have h2 := Scheme.Hom.appLE_comp_appLE
    (smallZariskiOpenImmersion B T.1 T.property
      ((opensToSmallZariski B T.1 T.property).obj (lcSchemeHom B f ⁻¹ᵁ V)))
    (lcSchemeHom B f) V (lcSchemeHom B f ⁻¹ᵁ V) ⊤ le_rfl
    (lcTop_le_preimage B T.1 T.property _)
  refine Eq.trans (congrArg (fun k => (smallZariskiOpenImmersion B S.1 S.property
      ((opensToSmallZariski B S.1 S.property).obj V)).appLE V ⊤
        (lcTop_le_preimage B S.1 S.property V) ≫ k) (lcAppLE_top _).symm) ?_
  refine h1.trans ?_
  refine (lcAppLE_congr (lcProjection_comp_openImmersion B f V) V ⊤ _
    (by rw [Scheme.Hom.comp_preimage]; exact lcTop_le_preimage B T.1 T.property _)).trans ?_
  refine h2.symm.trans ?_
  exact congrArg (fun k => k ≫ (smallZariskiOpenImmersion B T.1 T.property
      ((opensToSmallZariski B T.1 T.property).obj (lcSchemeHom B f ⁻¹ᵁ V))).appLE
      (lcSchemeHom B f ⁻¹ᵁ V) ⊤ (lcTop_le_preimage B T.1 T.property _))
    (Scheme.Hom.app_eq_appLE _).symm

/-- The restriction maps of the structure presheaf of the small Zariski site are the pullbacks
of functions along the underlying morphisms of schemes. -/
public theorem lcCommRings_map (X : Scheme.{u}) (hX : B.Contains X)
    {U W : SmallZariski B X hX} (g : U ⟶ W) :
    (smallZariskiCommRings B X hX).map g.op =
      Scheme.Γ.map ((SmallZariski.toScheme B X hX).map g).op := rfl

/-- **`f_small^♯` at the object chosen over an open `V`, followed by restriction along the
comparison of chosen objects, is the pullback of functions along one morphism of schemes.** -/
public theorem lcSharp_comp_restriction (V : (S.1).Opens) :
    (smallZariskiStructureSharp B f).hom.app
          (op ((opensToSmallZariski B S.1 S.property).obj V)) ≫
        (smallZariskiCommRings B T.1 T.property).map
          ((lcBaseChangeOpensIso B f).hom.app V).op =
      ((SmallZariski.toScheme B T.1 T.property).map ((lcBaseChangeOpensIso B f).hom.app V) ≫
        ((smallZariskiBaseChangeIso B f).hom.app
            ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
          pullback.fst ((smallSiteInSchemesOver B S).obj
            ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f)).appTop := by
  rw [smallZariskiStructureSharp_hom_app, lcCommRings_map, Scheme.Γ_map_op]
  exact (Scheme.Hom.comp_appTop
    ((SmallZariski.toScheme B T.1 T.property).map ((lcBaseChangeOpensIso B f).hom.app V))
    (((smallZariskiBaseChangeIso B f).hom.app
        ((opensToSmallZariski B S.1 S.property).obj V)).left ≫
      pullback.fst ((smallSiteInSchemesOver B S).obj
        ((opensToSmallZariski B S.1 S.property).obj V)).hom (B.inclusion.map f))).symm

/-- **The two composite comparisons of structure sheaves round the square agree**, in
`CommRingCat`.  Both are the pullback of functions along one morphism of schemes, by
`AlgebraicGeometry.SmallZariski.lcSections_square`. -/
public theorem lcStructureComm_square (V : (S.1).Opens) :
    (smallZariskiCommStructureIso B S.1 S.property).hom.app (op V) ≫
        (smallZariskiStructureSharp B f).hom.app
            (op ((opensToSmallZariski B S.1 S.property).obj V)) ≫
          (smallZariskiCommRings B T.1 T.property).map
            ((lcBaseChangeOpensIso B f).hom.app V).op =
      (lcSchemeHom B f).app V ≫
        (smallZariskiCommStructureIso B T.1 T.property).hom.app
          (op (lcSchemeHom B f ⁻¹ᵁ V)) := by
  rw [lcStructureIso_hom_app B S.1 S.property V,
    lcStructureIso_hom_app B T.1 T.property (lcSchemeHom B f ⁻¹ᵁ V)]
  refine Eq.trans (congrArg (fun k => (smallZariskiOpenImmersion B S.1 S.property
      ((opensToSmallZariski B S.1 S.property).obj V)).appLE V ⊤
        (lcTop_le_preimage B S.1 S.property V) ≫ k)
    (lcSharp_comp_restriction B f V)) (lcSections_square B f V)

/-- The two composite comparisons of structure sheaves round the square agree. -/
public theorem lcStructureMap_comp_baseChangeOpensIso :
    SheafOfModules.comparisonComp (structureMap B S.1 S.property) (lcStructureMapRing B f) ≫
        (Functor.sheafPushforwardContinuousNatTrans (lcBaseChangeOpensIso B f).hom RingCat.{u}
          (Opens.grothendieckTopology ↥S.1) (topology B T.1 T.property)).app
          (structureSheaf B T.1 T.property) =
      SheafOfModules.comparisonComp (lcSchemeHom B f).toRingCatSheafHom
        (structureMap B T.1 T.property) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V ↦ ?_)
  have h := congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    (lcStructureComm_square B f V.unop)
  simp only [Functor.map_comp] at h
  exact h

/-! ### The square of ringed sites -/

/-- Pushforward of sheaves of modules along `f_small` has a left adjoint: the small Zariski site
of `S` is essentially small in the universe of the sections of the structure sheaves. -/
public instance lcPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (lcStructureMapRing B f)).IsRightAdjoint :=
  SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall.{u} _

/-- Pushforward of sheaves of modules along the morphism of schemes, at the spelling the square
consumes. -/
public instance lcPushforwardScheme_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (lcSchemeHom B f).toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward (lcSchemeHom B f)).IsRightAdjoint

/-- **Stacks 03LC part (1) at `τ = Zariski`, for the small Zariski sites.**  The equivalence of
Stacks 03DX (2) at `τ = Zariski` is compatible with pullback: for `f : T ⟶ S` a morphism of
schemes of the big Zariski site, with `f_small : (T_Zar, 𝒪) ⟶ (S_Zar, 𝒪)` the morphism of ringed
sites of Stacks 070R (2) and `𝓖` an `𝒪_S`-module,

    `(f^*𝓖)^a ≅ f_small^*(𝓖^a)`,

naturally in `𝓖` and with no quasi-coherence hypothesis.

Here `𝓖 ↦ 𝓖^a` is `AlgebraicGeometry.SmallZariski.associatedModule`, the functor of
Definition 03DU (4) at `τ = Zariski` over the structure sheaf `T/S ↦ Γ(T, 𝒪_T)` of the small
Zariski site — not the identity reading introduced in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful`.  That
distinction is what gives this declaration its content.
`AlgebraicGeometry.SmallZariski.associatedModulePullbackIso` states the corresponding
commutation over the identity reading, and it does **not** state this clause: the identity
reading is pullback along the identity morphism of ringed sites, isomorphic to `𝟭`, so that
statement reads `f_small^* ⋙ 𝟭 ≅ 𝟭 ⋙ f_small^*` and is proved by whiskering the two unit
isomorphisms and applying the two unitors, never touching the coefficient sheaf
`T/S ↦ Γ(T, 𝒪_T)` that clause (2) is about.  It is accordingly untagged.

The proof is `SheafOfModules.pullbackSquareIso`, Stacks 03D8 for a square: the geometric half of
the square is `AlgebraicGeometry.SmallZariski.lcBaseChangeOpensIso`, that the base change of the
object chosen over an open `V` of `S` is the object chosen over `f⁻¹(V)`, and the ring half is
`AlgebraicGeometry.SmallZariski.lcStructureMap_comp_baseChangeOpensIso`.

**This is also Stacks 03FH part (2)** for the small Zariski `f_small` of Remark 070R (2).  That
clause asserts `(f^*𝓕)^a = f_sites^*𝓕^a` for every `f_sites` the enumeration of Remark 070R
lists, and the two clauses coincide at this `f_sites`: both are the statement that the
associated-module functor of Definition 03DU (4) at `τ = Zariski` commutes with pullback along
the morphism of ringed small Zariski sites of Stacks 070R (2).  The companions are
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso` — which carries the same two
clauses on one declaration — for the big site at each of the five topologies, and
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` for the small étale `f_small`.
Those are every `f_sites` of the enumeration; the mixed-topology entries
`(Sch/X)_τ ⟶ (Sch/Y)_{τ'}` with `τ ≠ τ'` of Topologies, Section 03FE are not claimed. -/
@[stacks 03LC "part (1) at τ = Zariski, for the small Zariski sites: (f^*𝓖)^a ≅ \
f_small^*(𝓖^a), for an arbitrary morphism of schemes of the site and arbitrary modules",
  stacks 03FH "part (2), for the morphism f_small : (T_Zar, 𝒪_T) → (S_Zar, 𝒪_S) of \
Stacks 070R (2), for the associated-module functor of Definition 03DU (4)"]
public noncomputable def lcAssociatedModulePullbackIso :
    Scheme.Modules.pullback (lcSchemeHom B f) ⋙ associatedModule B T.1 T.property ≅
      associatedModule B S.1 S.property ⋙
        SheafOfModules.pullback.{u} (lcStructureMapRing B f) :=
  SheafOfModules.pullbackSquareIso.{u} (lcSchemeHom B f).toRingCatSheafHom
    (structureMap B T.1 T.property) (structureMap B S.1 S.property) (lcStructureMapRing B f)
    (lcBaseChangeOpensIso B f) (lcStructureMap_comp_baseChangeOpensIso B f)

/-- **Stacks 03FH part (2) at one module**, and equally **Stacks 03LC part (1) at `τ = Zariski`
at one module**: `(f^*𝓕)^a ≅ f_small^*(𝓕^a)` for the morphism `f_small` of the small Zariski
sites of Stacks 070R (2) and the associated-module functor of Definition 03DU (4).  This is the
form in which Stacks 03FH states its clause, read off from
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`. -/
@[stacks 03FH "part (2) at one module, for the morphism f_small of the small Zariski sites and \
the associated-module functor of Definition 03DU (4)"]
public noncomputable def lcAssociatedModuleObjPullbackIso (𝓖 : (S.1).Modules) :
    (associatedModule B T.1 T.property).obj
        ((Scheme.Modules.pullback (lcSchemeHom B f)).obj 𝓖) ≅
      (SheafOfModules.pullback.{u} (lcStructureMapRing B f)).obj
        ((associatedModule B S.1 S.property).obj 𝓖) :=
  (lcAssociatedModulePullbackIso B f).app 𝓖

/-- **The comparison of the two composite right adjoints round the square**: restricting a sheaf
of modules on the small Zariski site of `T` along `f_small` and then to the opens of `S` is
restricting it to the opens of `T` and then pushing forward along `f`.  This is the
right-adjoint transpose of `AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`. -/
public noncomputable abbrev lcRestrictModuleBaseChangeIso :
    SheafOfModules.pushforward.{u} (lcStructureMapRing B f) ⋙
        restrictModule B S.1 S.property ≅
      restrictModule B T.1 T.property ⋙ Scheme.Modules.pushforward (lcSchemeHom B f) :=
  SheafOfModules.pushforwardComp.{u} (structureMap B S.1 S.property)
      (lcStructureMapRing B f) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (lcBaseChangeOpensIso B f)
      (lcStructureMap_comp_baseChangeOpensIso B f) ≪≫
    (SheafOfModules.pushforwardComp.{u} (lcSchemeHom B f).toRingCatSheafHom
      (structureMap B T.1 T.property)).symm

/-! ### Stacks 03LC (3) at `τ = Zariski` -/

/-- **The restriction of `f_{small, *}(𝓕^a)` to the opens of `S` is `f_*𝓕`**, for every
`𝒪_T`-module `𝓕` and with no hypothesis on `f`: the mate square
`AlgebraicGeometry.SmallZariski.lcRestrictModuleBaseChangeIso` identifies the restriction with
`f_*` of the restriction of `𝓕^a`, and the unit of the associated-module adjunction of the small
Zariski site is an isomorphism at every module, `restrictModule` being an equivalence. -/
public noncomputable def lcRestrictModuleSmallPushforwardAssociatedModuleIso
    (𝓕 : (T.1).Modules) :
    (restrictModule B S.1 S.property).obj
        ((SheafOfModules.pushforward.{u} (lcStructureMapRing B f)).obj
          ((associatedModule B T.1 T.property).obj 𝓕)) ≅
      (Scheme.Modules.pushforward (lcSchemeHom B f)).obj 𝓕 :=
  (lcRestrictModuleBaseChangeIso B f).app ((associatedModule B T.1 T.property).obj 𝓕) ≪≫
    (Scheme.Modules.pushforward (lcSchemeHom B f)).mapIso
      ((restrictAssociatedModuleIso B T.1 T.property).app 𝓕).symm

/-- **Stacks 03LC part (3) at `τ = Zariski`, the commuting square**, at one module and with no
hypothesis on `f`: for every `𝒪_T`-module `𝓕`,

    `(f_*𝓕)^a ≅ f_{small, *}(𝓕^a)`.

The isomorphism is the counit of the associated-module adjunction of the small Zariski site of
`S` at `f_{small, *}(𝓕^a)`, which is an isomorphism at every module by
`AlgebraicGeometry.isIso_counit_smallZariskiAssociatedModuleAdjunction`, precomposed with the
associated module of the identification
`AlgebraicGeometry.SmallZariski.lcRestrictModuleSmallPushforwardAssociatedModuleIso` of its
restriction with `f_*𝓕`.

The source states the square for `f` quasi-compact and quasi-separated, where it is a square of
the categories of *quasi-coherent* modules; the isomorphism of modules holds without those
hypotheses, and
`AlgebraicGeometry.SmallZariski.lcIsQuasicoherentOnSite_smallPushforward` supplies the
quasi-coherence of the two corners under them. -/
@[stacks 03LC "part (3) at τ = Zariski, the commuting square f_{small,*}(𝓕^a) ≅ (f_*𝓕)^a, at \
one module and with no hypothesis on f"]
public noncomputable def lcAssociatedModuleSmallPushforwardIso (𝓕 : (T.1).Modules) :
    (associatedModule B S.1 S.property).obj
        ((Scheme.Modules.pushforward (lcSchemeHom B f)).obj 𝓕) ≅
      (SheafOfModules.pushforward.{u} (lcStructureMapRing B f)).obj
        ((associatedModule B T.1 T.property).obj 𝓕) :=
  (associatedModule B S.1 S.property).mapIso
      (lcRestrictModuleSmallPushforwardAssociatedModuleIso B f 𝓕).symm ≪≫
    @asIso _ _ _ _ _ (isIso_counit_smallZariskiAssociatedModuleAdjunction B S.1 S.property _)

/-- **Stacks 03LC part (3) at `τ = Zariski`, the commuting square as an isomorphism of
functors.**  The square

```
  Mod(𝒪_T) ------ f_* ------> Mod(𝒪_S)
      |                          |
   𝓕 ↦ 𝓕^a                   𝓖 ↦ 𝓖^a
      v                          v
  Mod(T_Zar, 𝒪) - f_{small,*} -> Mod(S_Zar, 𝒪)
```

commutes up to the canonical natural isomorphism, with no hypothesis on `f` and on all modules.
Its components are `AlgebraicGeometry.SmallZariski.lcAssociatedModuleSmallPushforwardIso`; the
proof is the same three steps, read as isomorphisms of functors: the unit of the
associated-module adjunction of `T_Zar`, the mate square
`AlgebraicGeometry.SmallZariski.lcRestrictModuleBaseChangeIso`, and the counit of the
associated-module adjunction of `S_Zar`, which is an isomorphism of functors because
`AlgebraicGeometry.SmallZariski.restrictModule` is an equivalence. -/
@[stacks 03LC "part (3) at τ = Zariski, the commuting square of the part, as an isomorphism of \
functors Mod(𝒪_T) ⥤ Mod(S_Zar, 𝒪) and with no hypothesis on f"]
public noncomputable def lcAssociatedModuleSmallPushforwardNatIso :
    Scheme.Modules.pushforward (lcSchemeHom B f) ⋙ associatedModule B S.1 S.property ≅
      associatedModule B T.1 T.property ⋙
        SheafOfModules.pushforward.{u} (lcStructureMapRing B f) :=
  Functor.isoWhiskerRight (restrictAssociatedModuleIso B T.1 T.property)
      (Scheme.Modules.pushforward (lcSchemeHom B f) ⋙ associatedModule B S.1 S.property) ≪≫
    Functor.isoWhiskerLeft (associatedModule B T.1 T.property)
      (Functor.isoWhiskerRight (lcRestrictModuleBaseChangeIso B f).symm
          (associatedModule B S.1 S.property) ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.pushforward.{u} (lcStructureMapRing B f))
          (asIso (associatedModuleAdjunction B S.1 S.property).counit))

/-- **Stacks 03LC part (3) at `τ = Zariski`, the preservation of quasi-coherence by
`f_{small, *}`.**  For `f : T ⟶ S` quasi-compact and quasi-separated, the direct image along
`f_small : (T_Zar, 𝒪) ⟶ (S_Zar, 𝒪)` of a module quasi-coherent on the small Zariski site of `T`
is quasi-coherent on the small Zariski site of `S`.

Every such module is an associated module: its restriction to the opens of `T` is quasi-coherent
by `AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule` and the counit exhibits the
module as the associated module of that restriction.  Its direct image is then
`(f_*𝓕)^a` by `AlgebraicGeometry.SmallZariski.lcAssociatedModuleSmallPushforwardIso`, and
`f_*𝓕` is quasi-coherent by Stacks 01LC, so that associated module is quasi-coherent on the site
by Stacks 03DV (2). -/
@[stacks 03LC "part (3) at τ = Zariski, f_{small,*} carries quasi-coherent 𝒪-modules on the \
small Zariski site to quasi-coherent 𝒪-modules on the small Zariski site"]
public theorem lcIsQuasicoherentOnSite_smallPushforward
    [QuasiCompact (lcSchemeHom B f)] [QuasiSeparated (lcSchemeHom B f)]
    (𝒢 : SheafOfModules.{u} (structureSheaf B T.1 T.property))
    (h𝒢 : 𝒢.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (lcStructureMapRing B f)).obj 𝒢).IsQuasicoherentOnSite := by
  have h1 : SheafOfModules.IsQuasicoherent (R := (T.1).ringCatSheaf)
      ((restrictModule B T.1 T.property).obj 𝒢) :=
    isQuasicoherent_restrictModule B T.1 T.property 𝒢 h𝒢
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SheafOfModules.pushforward.{u} (lcStructureMapRing B f)).mapIso
      (@asIso _ _ _ _ _
        (isIso_counit_smallZariskiAssociatedModuleAdjunction B T.1 T.property 𝒢))) ?_
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (lcAssociatedModuleSmallPushforwardIso B f ((restrictModule B T.1 T.property).obj 𝒢))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S.1 S.property _
      (AlgebraicGeometry.pushforward_isQuasicoherent (lcSchemeHom B f) _))

end AlgebraicGeometry.SmallZariski

end
