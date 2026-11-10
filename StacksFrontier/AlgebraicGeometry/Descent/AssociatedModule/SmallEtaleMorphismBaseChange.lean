module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom

/-!
# Base change of the associated module along a morphism of schemes

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `r` be the underlying
morphism of schemes.  The associated-module functor `𝓕 ↦ 𝓕^a` of the small étale site commutes
with pullback:

`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`,

naturally in the `𝒪_Y`-module `𝓕`, where `ε_a` is the morphism of ringed sites
`(X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Stacks 070R (2).

The proof is the mate argument of `SheafOfModules.pullbackSquareIso` applied to the square

```
  Y_Zar ---- V ↦ r⁻¹(V) ----> X_Zar
    |                           |
    |                           |
    v                           v
  Y_étale -- base change ----> X_étale
```

of morphisms of ringed sites.  Both routes round the square are pullbacks of sheaves of modules,
so it suffices to identify the two composite continuous functors compatibly with the two
composite comparisons of structure sheaves.  The geometric half of that identification is that
base-changing an open `V ⊆ Y` along `r` gives the preimage open `r⁻¹(V)`, and its ring half is
that pulling a function on `V` back along the base-change projection is pulling it back along `r`
and restricting to `r⁻¹(V)`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`: the structure map of `ε_a`, read as a
  map of sheaves of not necessarily commutative rings.  Pullback of sheaves of modules along
  `ε_a` is formed over this map.
* `AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso`: **the base change of an open.**  For `V`
  an open of `Y`, the base change along `a` of the object of `Y_étale` given by `V` is the object
  of `X_étale` given by the preimage open `r⁻¹(V)`.
* `AlgebraicGeometry.SmallEtale.baseChangeOpensIso`: the same identification as an isomorphism of
  continuous functors `Y_Zar ⥤ X_étale`, which is the geometric half of the square.
* `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`: **`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`**, as an
  isomorphism of functors.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`: the same at one module.
* `AlgebraicGeometry.SmallEtale.baseChangeRestrictIso`: the comparison of the two composite
  restrictions round the square, which is the right adjoint of the base-change isomorphism and,
  unlike it, has a formula on sections.
* `AlgebraicGeometry.SmallEtale.zariskiRouteAdjunction` and `.etaleRouteAdjunction`: the two
  composite adjunctions round the square.

## Main results

* `AlgebraicGeometry.SmallEtale.topIso_inv_appTop_baseChangeOpens`: **the section identity.**
  Pulling a section of `𝒪_Y` over `V` back to a global function on the open subscheme `V` and
  then along the base-change projection is pulling it back along `r` and viewing the result as a
  global function on `r⁻¹(V)`.
* `AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso`: the compatibility of the
  two composite comparisons of structure sheaves, which is the ring half of the square.
* `AlgebraicGeometry.SmallEtale.mono_baseChangeOpens_hom` and
  `AlgebraicGeometry.SmallEtale.subsingleton_hom_baseChangeOpens`: the structure morphism of the
  base change of an open is a monomorphism, so morphisms into such a base change are unique.
* `AlgebraicGeometry.SmallEtale.unit_comp_associatedModuleObjBaseChangeIso`: **the adjunct square
  of `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`.**  The unit of the Zariski route followed by the base-change
  isomorphism is the unit of the étale route followed by
  `AlgebraicGeometry.SmallEtale.baseChangeRestrictIso`.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_hom_val_app_unit`: **base change
  for the sections of a module.**  The base-change isomorphism carries the canonical section of
  `(r^*𝓕)^a` over `r⁻¹(V)` attached to a section of `𝓕` over an open `V` of `Y` to the
  restriction to `r⁻¹(V)` of the canonical section of `ε_a^*(𝓕^a)` over the base change
  `X ×_Y V`.

## Implementation notes

The comparison of structure sheaves of `ε_a` is given in `CommRingCat` by
`AlgebraicGeometry.structureSharp`, since a ringed site carries a sheaf of commutative rings,
whereas sheaves of modules are indexed by a sheaf of rings.  The two differ by
`CategoryTheory.forget₂`, applied to the underlying presheaves on the nose, which is what
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` records.

Morphisms of the small étale site into the base change of an open are unique, the structure
morphism of such a base change being a monomorphism; so the naturality of the geometric half of
the square needs no computation.

The morphism of schemes underlying a morphism `a` of the big étale site is written
`AlgebraicGeometry.SmallEtale.schemeHom` rather than `B.inclusion.map a`, so that the small
Zariski sites of the source and the target are presented by the opens of `X.obj` and of `Y.obj`:
those are the presentations the structure sheaves of Stacks 03DU and the sheaf of rings of a
scheme are indexed by.

**Why the statement on sections is an adjunct square and not a formula.**  Both sides of
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` are pullbacks of sheaves of
modules, hence values of left adjoints, and the sections of such a pullback over an object are
computed by no formula — which is exactly why the isomorphism is produced by
`CategoryTheory.Adjunction.leftAdjointUniq` and had no description.  The description it does
admit is the compatibility with the units of the two composite adjunctions, which is
`SheafOfModules.unit_comp_pullbackSquareIso_hom_app` instantiated here, and that becomes a
statement about sections because the comparison of the two composite *right* adjoints is a
restriction map: `AlgebraicGeometry.SmallEtale.baseChangeRestrictIso_hom_app_val_app` reads it
over an open `V` of `Y` as restriction along
`AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso`, the identification of `r⁻¹(V)` with
`X ×_Y V`.  Neither statement assumes quasi-coherence.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The morphism of schemes underlying a morphism of the big étale site. -/
public abbrev schemeHom : X.obj ⟶ Y.obj := B.inclusion.map a

/-! ### The base change of an open of the target -/

section Opens

variable (V : Y.obj.Opens)

/-- The open immersion of an open `V` of `Y`, as a morphism of the big étale site. -/
public abbrev opensSchemeι :
    B.obj (V : Scheme.{u}) (BigEtaleOver.contains_opens B Y.property V) ⟶ Y :=
  ObjectProperty.homMk V.ι

/-- The preimage of an open `V` of `Y` along `a`, as an object of the big étale site. -/
public abbrev preimageSchemeObj : B.Scheme :=
  B.obj ((schemeHom B a ⁻¹ᵁ V : X.obj.Opens) : Scheme.{u})
    (BigEtaleOver.contains_opens B X.property (schemeHom B a ⁻¹ᵁ V))

/-- The fibre product of an open of `Y` with `X`, computed in schemes: it is the preimage
open, by the pullback square of the restriction of a morphism to an open of its target. -/
public def openPullbackSchemeIso :
    B.inclusion.obj (preimageSchemeObj B a V) ≅
      B.inclusion.obj (pullback (opensSchemeι B V) a) :=
  (isPullback_morphismRestrict (schemeHom B a) V).isoPullback ≪≫
    (PreservesPullback.iso B.inclusion (opensSchemeι B V) a).symm

/-- The fibre product of an open of `Y` with `X`, computed in the big étale site. -/
public def openPullbackIso :
    preimageSchemeObj B a V ≅ pullback (opensSchemeι B V) a :=
  B.inclusion.preimageIso (openPullbackSchemeIso B a V)

/-- The identification of the fibre product with the preimage open, read on underlying
schemes: it is the comparison of the pullback square of the restriction of `r` to `V` with the
fibre product of the big étale site. -/
public theorem inclusion_map_openPullbackIso_hom :
    B.inclusion.map (openPullbackIso B a V).hom =
      (isPullback_morphismRestrict (schemeHom B a) V).isoPullback.hom ≫
        (PreservesPullback.iso B.inclusion (opensSchemeι B V) a).inv :=
  B.inclusion.map_preimage _

/-- The identification of the fibre product with the preimage open is over `X`. -/
public theorem openPullbackIso_hom_snd :
    (openPullbackIso B a V).hom ≫ pullback.snd (opensSchemeι B V) a =
      ObjectProperty.homMk (schemeHom B a ⁻¹ᵁ V).ι := by
  apply B.inclusion.map_injective
  rw [Functor.map_comp, inclusion_map_openPullbackIso_hom, Category.assoc,
    PreservesPullback.iso_inv_snd]
  exact (isPullback_morphismRestrict (schemeHom B a) V).isoPullback_hom_snd

/-- The identification of the fibre product with the preimage open carries the projection to
`V` to the restriction of `r` to `V`. -/
public theorem openPullbackIso_hom_fst :
    B.inclusion.map (openPullbackIso B a V).hom ≫
        B.inclusion.map (pullback.fst (opensSchemeι B V) a) =
      schemeHom B a ∣_ V := by
  rw [inclusion_map_openPullbackIso_hom, Category.assoc, PreservesPullback.iso_inv_fst]
  exact (isPullback_morphismRestrict (schemeHom B a) V).isoPullback_hom_fst

/-- **The base change of an open of `Y` is the preimage open.**  For `V` an open of `Y`, the
base change along `a : X ⟶ Y` of the object of the small étale site of `Y` given by `V` is the
object of the small étale site of `X` given by `r⁻¹(V)`, where `r` is the morphism of schemes
underlying `a`.

Both are open subschemes of `X`: the base change because an open immersion stays one after base
change, and the identification is the pullback square of the restriction of `r` to `V`. -/
public def baseChangeOpensObjIso :
    opensObj B X.obj X.property (schemeHom B a ⁻¹ᵁ V) ≅
      (smallEtaleBaseChange B a).obj (opensObj B Y.obj Y.property V) :=
  ObjectProperty.isoMk _ (Over.isoMk (openPullbackIso B a V) (openPullbackIso_hom_snd B a V))

/-- On underlying schemes, the base change of an open composed with the projection to `V` is the
restriction of `r` to `V`. -/
public theorem inclusion_map_baseChangeOpensObjIso_hom_fst :
    B.inclusion.map (baseChangeOpensObjIso B a V).hom.hom.left ≫
        B.inclusion.map (pullback.fst (opensSchemeι B V) a) =
      schemeHom B a ∣_ V :=
  openPullbackIso_hom_fst B a V

/-- The open immersion of an open of `Y`, read in the big étale site, is a monomorphism. -/
public instance mono_opensSchemeι : Mono (opensSchemeι B V) :=
  B.inclusion.mono_of_mono_map (show Mono V.ι from inferInstance)

/-- The structure morphism of the base change of an open of `Y` is a monomorphism, being the
base change of an open immersion. -/
public instance mono_baseChangeOpens_hom :
    Mono ((smallEtaleBaseChange B a).obj
      ((opensToSmallEtale B Y.obj Y.property).obj V)).obj.hom :=
  inferInstanceAs (Mono (pullback.snd (opensSchemeι B V) a))

/-- **Morphisms into the base change of an open are unique**, the structure morphism of such a
base change being a monomorphism. -/
public instance subsingleton_hom_baseChangeOpens (Z : SmallEtale B X.obj X.property) :
    Subsingleton (Z ⟶ (smallEtaleBaseChange B a).obj
      ((opensToSmallEtale B Y.obj Y.property).obj V)) := by
  refine ⟨fun f g ↦ ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [← cancel_mono ((smallEtaleBaseChange B a).obj
    ((opensToSmallEtale B Y.obj Y.property).obj V)).obj.hom, Over.w, Over.w]

end Opens

/-! ### The geometric half of the square -/

/-- **Base change along `a` carries the small Zariski site of `Y` to the small Zariski site of
`X`.**  Taking the preimage of an open of `Y` and including it into the small étale site of `X`
is including the open into the small étale site of `Y` and base-changing along `a`.

This is `AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso` read as an isomorphism of
continuous functors; its naturality is automatic, morphisms into the base change of an open
being unique. -/
public def baseChangeOpensIso :
    Opens.map (schemeHom B a).base ⋙ opensToSmallEtale B X.obj X.property ≅
      opensToSmallEtale B Y.obj Y.property ⋙ smallEtaleBaseChange B a :=
  NatIso.ofComponents (fun V ↦ baseChangeOpensObjIso B a V)
    fun {_ W} _ ↦ (subsingleton_hom_baseChangeOpens B a W _).allEq _ _

/-- The components of the comparison of the two routes are the identifications of the base
change of an open with the preimage open. -/
@[simp]
public theorem baseChangeOpensIso_hom_app (V : Y.obj.Opens) :
    (baseChangeOpensIso B a).hom.app V = (baseChangeOpensObjIso B a V).hom :=
  rfl

/-- Taking preimages along `r` is a continuous functor of the small Zariski sites. -/
public instance isContinuous_opensMap :
    (Opens.map (schemeHom B a).base).IsContinuous
      (Opens.grothendieckTopology ↥Y.obj) (Opens.grothendieckTopology ↥X.obj) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
    (coverPreserving_opens_map _)

/-- Taking the preimage of an open of `Y` and including it into the small étale site of `X` is
a continuous functor. -/
public instance isContinuous_opensMap_comp_opensToSmallEtale :
    (Opens.map (schemeHom B a).base ⋙
        opensToSmallEtale B X.obj X.property).IsContinuous
      (Opens.grothendieckTopology ↥Y.obj) (topology B X.obj X.property) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _ (isContinuous_opensMap B a)
    (isContinuous_opensToSmallEtale B X.obj X.property)

/-- Including an open of `Y` into the small étale site of `Y` and base-changing along `a` is a
continuous functor. -/
public instance isContinuous_opensToSmallEtale_comp_baseChange :
    (opensToSmallEtale B Y.obj Y.property ⋙ smallEtaleBaseChange B a).IsContinuous
      (Opens.grothendieckTopology ↥Y.obj) (topology B X.obj X.property) :=
  Functor.isContinuous_comp _ _ _ (topology B Y.obj Y.property) _

/-! ### The structure map of `ε_a` on sheaves of rings -/

/-- **The structure map of `ε_a`, read on sheaves of not necessarily commutative rings.**  At an
étale `W / Y` it pulls a global function on `W` back along the base-change projection
`X ×_Y W ⟶ W`.

This is the structure map `AlgebraicGeometry.structureSharp` of the morphism of ringed sites
`AlgebraicGeometry.smallEtaleRingedSiteHom` with the commutativity of the sections forgotten;
sheaves of modules are indexed by a sheaf of rings, so this is the form over which the pullback
of sheaves of modules along `ε_a` is formed. -/
public def smallEtaleStructureMapRing :
    structureSheaf B Y.obj Y.property ⟶
      ((smallEtaleBaseChange B a).sheafPushforwardContinuous RingCat.{u}
          (topology B Y.obj Y.property) (topology B X.obj X.property)).obj
        (structureSheaf B X.obj X.property) :=
  ObjectProperty.homMk (Functor.whiskerRight (smallEtaleRingedSiteHom B a).fsharp.hom
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The structure map of `ε_a` is pullback of functions along the base-change projection. -/
@[simp]
public theorem smallEtaleStructureMapRing_hom_app (W : SmallEtale B Y.obj Y.property) :
    (smallEtaleStructureMapRing B a).hom.app (Opposite.op W) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map (Opposite.op (B.inclusion.map (pullback.fst W.obj.hom a)))) :=
  rfl

/-! ### The ring half of the square -/

/-- The restriction of `r` to an open `V` of `Y`, computed through the identification of the base
change of `V` with the preimage open, sits in the commutative square defining `r ∣_ V`. -/
public theorem baseChangeOpensObjIso_hom_fst_comp_ι (V : Y.obj.Opens) :
    (B.inclusion.map (baseChangeOpensObjIso B a V).hom.hom.left ≫
        B.inclusion.map (pullback.fst (opensSchemeι B V) a)) ≫ V.ι =
      (schemeHom B a ⁻¹ᵁ V).ι ≫ schemeHom B a := by
  rw [inclusion_map_baseChangeOpensObjIso_hom_fst, morphismRestrict_ι]

/-- **The section identity at the restriction of `r` to an open.**  Pulling a section of `𝒪_Y`
over `V` back to a global function on the open subscheme `V` and then along the base-change
projection `X ×_Y V ⟶ V`, read through the identification of the base change of `V` with the
preimage open, is pulling it back along `r` and viewing it as a global function on `r⁻¹(V)`. -/
public theorem topIso_inv_appTop_baseChangeOpens (V : Y.obj.Opens) :
    (V.topIso).inv ≫ (B.inclusion.map (baseChangeOpensObjIso B a V).hom.hom.left ≫
        B.inclusion.map (pullback.fst (opensSchemeι B V) a)).appTop =
      (schemeHom B a).app V ≫ ((schemeHom B a) ⁻¹ᵁ V).topIso.inv :=
  Scheme.Opens.topIso_inv_appTop_of_comp (schemeHom B a) V _
    (baseChangeOpensObjIso_hom_fst_comp_ι B a V)

/-- **The two composite comparisons of structure sheaves agree.**  This is the ring half of the
square of ringed sites: over an open `V` of `Y` both composites are the map of global functions
of `AlgebraicGeometry.SmallEtale.topIso_inv_appTop_baseChangeOpens`, with the commutativity of
the sections forgotten. -/
public theorem structureMap_comp_baseChangeOpensIso :
    SheafOfModules.comparisonComp (structureMap B Y.obj Y.property)
          (smallEtaleStructureMapRing B a) ≫
        (Functor.sheafPushforwardContinuousNatTrans (baseChangeOpensIso B a).hom RingCat.{u}
          (Opens.grothendieckTopology ↥Y.obj) (topology B X.obj X.property)).app
          (structureSheaf B X.obj X.property) =
      SheafOfModules.comparisonComp (schemeHom B a).toRingCatSheafHom
        (structureMap B X.obj X.property) := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V ↦ ?_)
  exact congrArg (forget₂ CommRingCat.{u} RingCat.{u}).map
    (topIso_inv_appTop_baseChangeOpens B a V.unop)

/-! ### Base change of the associated module -/

/-- Pushforward of sheaves of modules along `ε_a` has a left adjoint: the small étale site of `Y`
is essentially small in the universe of the sections of the structure sheaves. -/
public instance pushforward_smallEtaleStructureMapRing_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).IsRightAdjoint :=
  SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall.{u} _

/-- Pushforward of sheaves of modules along `r` has a left adjoint; this is the pushforward of
`𝒪`-modules of a morphism of schemes, restated at the spelling the square consumes. -/
public instance pushforward_toRingCatSheafHom_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward (schemeHom B a)).IsRightAdjoint

/-- **The associated module of a pullback is the pullback of the associated module.**  For
`a : X ⟶ Y` a morphism of schemes of the big étale site, with `r` the underlying morphism of
schemes and `ε_a` the morphism of ringed sites of Stacks 070R (2),

`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`,

naturally in the `𝒪_Y`-module `𝓕`, with no quasi-coherence hypothesis.  This **is Stacks 03LC
part (1) at `τ = étale`**, for the small étale sites of two schemes and a morphism between them:
the equivalence of Stacks 03DX (2) at `τ = étale` is compatible with pullback.  It is proved
here for arbitrary modules, not only quasi-coherent ones.

Each side is a composite of two pullbacks of sheaves of modules round the square of ringed sites
whose geometric half is `AlgebraicGeometry.SmallEtale.baseChangeOpensIso` and whose ring half is
`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso`, so the two agree because a
left adjoint is determined by its right adjoint.

**This also carries Stacks 03FH (2)** for the morphism `f_{small} : X_étale ⟶ Y_étale` of
Remark 070R (2): that clause asserts `(f^*𝓕)^a = f_{sites}^*𝓕^a` for every `f_{sites}` of
Remark 070R, and this is the small étale one.  The big fppf one is
`AlgebraicGeometry.BigFppfOver.associatedModuleBigPullbackIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigFppf.lean`); the big Zariski,
étale, smooth and syntomic ones are
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigSites.lean`), and the small
Zariski one is `AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiPushforwardSquare.lean`,
line 458).
(It was formerly cited as `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso`, which
states the commutation over the *identity reading* of `𝓕 ↦ 𝓕^a` and is a tautology about `𝟭`;
that declaration is untagged, and naming it here made this enumeration a false completeness
claim.)
Those are every `f_sites` the enumeration of Remark 070R lists; the mixed-topology entries
`(Sch/X)_τ ⟶ (Sch/Y)_{τ'}` with `τ ≠ τ'` of the Topologies, Section 03FE list that the remark's
opening sentence also covers are not claimed. -/
@[stacks 03LC "part (1) at τ = étale, for the small étale sites",
  stacks 03FH "part (2), for the morphism f_small : X_étale → Y_étale of Stacks 070R (2)"]
public def associatedModuleBaseChangeIso :
    Scheme.Modules.pullback (schemeHom B a) ⋙ associatedModule B X.obj X.property ≅
      associatedModule B Y.obj Y.property ⋙
        SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a) :=
  SheafOfModules.pullbackSquareIso.{u} (schemeHom B a).toRingCatSheafHom
    (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
    (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
    (structureMap_comp_baseChangeOpensIso B a)

/-- **`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` at one module**, read off from
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`. -/
public def associatedModuleObjBaseChangeIso (𝓕 : Y.obj.Modules) :
    (associatedModule B X.obj X.property).obj
        ((Scheme.Modules.pullback (schemeHom B a)).obj 𝓕) ≅
      (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B Y.obj Y.property).obj 𝓕) :=
  (associatedModuleBaseChangeIso B a).app 𝓕

/-! ### The base change on sections -/

/-- **The comparison of the two composite restrictions round the square.**  Restricting a module
on the small étale site of `X` along `ε_a` and then to the small Zariski site of `Y` is
restricting it to the small Zariski site of `X` and pushing forward along `r`.

Both routes are restriction along a continuous functor, so unlike the pullbacks this comparison
has a formula on sections: over an open `V` of `Y` it is restriction of a section over the base
change `X ×_Y V` to the preimage open `r⁻¹(V)`, by
`AlgebraicGeometry.SmallEtale.baseChangeRestrictIso_hom_app_val_app`.  That is what makes the
adjunct square below a statement about sections. -/
public def baseChangeRestrictIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        restrictModule B Y.obj Y.property ≅
      restrictModule B X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom B a) :=
  SheafOfModules.pushforwardSquareIso.{u} (schemeHom B a).toRingCatSheafHom
    (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
    (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
    (structureMap_comp_baseChangeOpensIso B a)

/-- **The comparison of the two composite restrictions is restriction to the preimage open.**
Over an open `V` of `Y` it carries a section of `𝓖` over the base change `X ×_Y V` to its
restriction along the identification
`AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso` of `r⁻¹(V)` with that base change. -/
public theorem baseChangeRestrictIso_hom_app_val_app
    (𝓖 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (V : (Y.obj.Opens)ᵒᵖ)
    (y : ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
      restrictModule B Y.obj Y.property).obj 𝓖).val.obj V) :
    ((baseChangeRestrictIso B a).hom.app 𝓖).val.app V y =
      𝓖.val.map (baseChangeOpensObjIso B a V.unop).hom.op y :=
  rfl

/-- The composite adjunction round the Zariski side of the square: Zariski pullback along `r`
followed by the associated-module functor of `X` is left adjoint to restriction to the small
Zariski site of `X` followed by pushforward along `r`. -/
public def zariskiRouteAdjunction :
    Scheme.Modules.pullback (schemeHom B a) ⋙ associatedModule B X.obj X.property ⊣
      restrictModule B X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom B a) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).comp
    (associatedModuleAdjunction B X.obj X.property)

/-- The composite adjunction round the étale side of the square: the associated-module functor of
`Y` followed by pullback along `ε_a` is left adjoint to restriction along `ε_a` followed by
restriction to the small Zariski site of `Y`. -/
public def etaleRouteAdjunction :
    associatedModule B Y.obj Y.property ⋙
        SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a) ⊣
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        restrictModule B Y.obj Y.property :=
  (associatedModuleAdjunction B Y.obj Y.property).comp
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a))

/-- **The adjunct square of `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`.**  The unit of the Zariski route, followed
by the base-change isomorphism, is the unit of the étale route, followed by the comparison
`AlgebraicGeometry.SmallEtale.baseChangeRestrictIso` of the two composite restrictions.

This is the description of the base-change isomorphism: both sides of it are pullbacks of
sheaves of modules, hence left adjoints, so no formula computes their sections, and the unit of
the adjunction is the only handle on them.  It holds for an arbitrary `𝒪_Y`-module, with no
quasi-coherence hypothesis, and it is the statement whose reading on sections is
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_hom_val_app_unit`. -/
public theorem unit_comp_associatedModuleObjBaseChangeIso (𝓕 : Y.obj.Modules) :
    (zariskiRouteAdjunction B a).unit.app 𝓕 ≫
        (restrictModule B X.obj X.property ⋙
            Scheme.Modules.pushforward (schemeHom B a)).map
          (associatedModuleObjBaseChangeIso B a 𝓕).hom =
      (etaleRouteAdjunction B a).unit.app 𝓕 ≫
        (baseChangeRestrictIso B a).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
            ((associatedModule B Y.obj Y.property).obj 𝓕)) :=
  SheafOfModules.unit_comp_pullbackSquareIso_hom_app.{u}
    (schemeHom B a).toRingCatSheafHom (structureMap B X.obj X.property)
    (structureMap B Y.obj Y.property) (smallEtaleStructureMapRing B a)
    (baseChangeOpensIso B a) (structureMap_comp_baseChangeOpensIso B a) 𝓕

/-- **Base change for the sections of a module.**  Let `V` be an open of `Y` and `s` a section
of `𝓕` over `V`.  Take the image of `s` under the unit of the Zariski route — the canonical
section of the associated module `(r^*𝓕)^a` over the preimage open `r⁻¹(V)` — and carry it along
the base-change isomorphism.  The result is the canonical section of `ε_a^*(𝓕^a)` over the base
change `X ×_Y V`, given by the unit of the étale route, restricted to `r⁻¹(V)`.

This is the content on sections of
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`, and it is the adjunct square
`AlgebraicGeometry.SmallEtale.unit_comp_associatedModuleObjBaseChangeIso` evaluated at `V` and
`s`: the two units have formulas over an object, and the comparison of the two composite
restrictions is a restriction map.  No quasi-coherence is assumed. -/
public theorem associatedModuleObjBaseChangeIso_hom_val_app_unit (𝓕 : Y.obj.Modules)
    (V : Y.obj.Opens) (s : 𝓕.val.obj (Opposite.op V)) :
    (associatedModuleObjBaseChangeIso B a 𝓕).hom.val.app
        (Opposite.op ((opensToSmallEtale B X.obj X.property).obj (schemeHom B a ⁻¹ᵁ V)))
        (((zariskiRouteAdjunction B a).unit.app 𝓕).val.app (Opposite.op V) s) =
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
            ((associatedModule B Y.obj Y.property).obj 𝓕)).val.map
          (baseChangeOpensObjIso B a V).hom.op
        (((etaleRouteAdjunction B a).unit.app 𝓕).val.app (Opposite.op V) s) :=
  congrArg
    (fun m : 𝓕 ⟶ (restrictModule B X.obj X.property ⋙
        Scheme.Modules.pushforward (schemeHom B a)).obj
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
        ((associatedModule B Y.obj Y.property).obj 𝓕)) ↦ m.val.app (Opposite.op V) s)
    (unit_comp_associatedModuleObjBaseChangeIso B a 𝓕)

end AlgebraicGeometry.SmallEtale

end
