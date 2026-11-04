module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigFppf

/-!
# The associated module commutes with pullback along `f_big`, in each of the five big sites

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigFppf` proves Stacks 03FH (2)
for the morphism of ringed sites `f_big : ((Sch/X)_fppf, 𝒪_X) ⟶ ((Sch/Y)_fppf, 𝒪_Y)` of
Remark 070R (1).  That remark's clause (1) adds "similarly for the big syntomic, smooth, étale
and Zariski sites", and this file supplies those four, so that 03FH (2) is proved for every
`f_big` the remark lists.

Nothing in the fppf argument is fppf-specific.  The five big sites over a scheme `S` are the one
category `AlgebraicGeometry.BigFppfOver B S hS` carrying the five localized topologies
`AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ`, and their structure sheaves have the
same underlying presheaf `T/S ↦ Γ(T, 𝒪_T)`
(`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj` is `rfl`); so the geometric half of
the square of ringed sites,

```
    Opens Y  --- f⁻¹ --->  Opens X
       |                      |
    opensToBig            opensToBig
       |                      |
       v                      v
   (Sch/Y)_τ  --- X ×_Y - -> (Sch/X)_τ
```

is literally `AlgebraicGeometry.BigFppfOver.opensBaseChangeIso`, which mentions no topology at
all, and the ring half is the same computation as in the fppf case.  What has to be supplied for
each `τ` is the *continuity* of the three functors involved: base change is continuous for the
two localizations of `AlgebraicGeometry.BigFppfSite.baseTopology B τ` because a localized
topology is a slice topology, and the inclusion of the small Zariski site is continuous into each
of the five by `AlgebraicGeometry.BigFppfOver.isContinuous_baseOpensToBig`, which is the
substance of `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseStructureComparison`: `f_big^♯`, in each of the five
  topologies — the same map of presheaves of rings as the fppf one, at the type pushforward
  along base change for the `τ`-localized topologies expects.
* `AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleBaseObjPullbackIso`: **Stacks 03FH (2)** for
  `f_big : ((Sch/X)_τ, 𝒪_X) ⟶ ((Sch/Y)_τ, 𝒪_Y)` at every one of the five `τ`, as functors and at
  one module.

## Main results

* `AlgebraicGeometry.BigFppfOver.isContinuous_baseChange_base`: base change along `f` is
  continuous for the two `τ`-localized topologies.
* `AlgebraicGeometry.BigFppfOver.comparisonComp_baseOpensBaseChangeIso`: the two routes round
  the square carry the same comparison of structure sheaves, the second proviso of
  `SheafOfModules.pullbackSquareIso`, in each of the five topologies.

## Implementation notes

`AlgebraicGeometry.BigFppfOver.baseStructureComparison` is *definitionally* the fppf
`AlgebraicGeometry.BigFppfOver.structureComparison`, for the reason
`AlgebraicGeometry.BigFppfOver.baseStructureMap` is definitionally the fppf
`AlgebraicGeometry.BigFppfOver.structureMap`: the sheaves of rings it compares have the same
underlying presheaves, and the topology enters only through the proof-irrelevant sheaf
conditions and the continuity instance.  No bridge between two structure sheaves is therefore
needed, or possible.

At `τ = fppf` the conclusion here is the one
`AlgebraicGeometry.BigFppfOver.associatedModuleBigPullbackIso` already states; that declaration
keeps its registration, this one is not a second construction of it but the same construction
read at a variable topology.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (f : X ⟶ Y) (τ : SiteKind)

/-! ### Continuity of base change for the five localized topologies -/

/-- Base change along `f` is continuous for the two `τ`-localized topologies, for each of the
five `τ`.  A localized big site is a slice of the chosen category of schemes with the localized
topology, and the chosen category is closed under fibre products by Stacks 021U, so this is the
general slice instance. -/
public instance isContinuous_baseChange_base :
    (baseChange B hX hY f).IsContinuous (baseOverTopology B Y hY τ)
      (baseOverTopology B X hX τ) :=
  inferInstanceAs ((Over.pullback (siteHom B hX hY f)).IsContinuous
    ((B.baseTopology τ).over (B.obj hY)) ((B.baseTopology τ).over (B.obj hX)))

/-- The small Zariski site of `Y` into the indicated big site of `X` through the preimage is
continuous: a composite of two continuous functors. -/
public instance isContinuous_opensMap_comp_baseOpensToBig :
    (Opens.map f.base ⋙ opensToBig B X hX).IsContinuous
      (Opens.grothendieckTopology ↥Y) (baseOverTopology B X hX τ) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥X) _

/-- The small Zariski site of `Y` into the indicated big site of `X` through base change is
continuous: a composite of two continuous functors. -/
public instance isContinuous_baseOpensToBig_comp_baseChange :
    (opensToBig B Y hY ⋙ baseChange B hX hY f).IsContinuous
      (Opens.grothendieckTopology ↥Y) (baseOverTopology B X hX τ) :=
  Functor.isContinuous_comp _ _ _ (baseOverTopology B Y hY τ) _

/-! ### `f_big^♯` in each of the five topologies -/

/-- **Stacks 070R, part (1): the structure-sheaf map `f_big^♯ : 𝒪_Y ⟶ f_{big, *}𝒪_X`**, in each
of the five topologies.  Its component at an object `T/Y` is the map on global functions induced
by the projection `X ×_Y T ⟶ T`, that is, the map `𝒪(T/Y) ⟶ 𝒪(X ×_Y T/X)` of the source.

This is `AlgebraicGeometry.BigFppfOver.structureComparison` read at the `τ`-localized
topologies: the same map of presheaves of rings, the topology entering only through the sheaf
conditions and the continuity instance. -/
@[stacks 070R "part (1): `f_big^♯` for the big fppf, syntomic, smooth, étale and Zariski sites, \
at the structure sheaves over which modules are taken"]
public noncomputable def baseStructureComparison :
    FibredSite.baseRingStructureSheaf B Y hY τ ⟶
      ((baseChange B hX hY f).sheafPushforwardContinuous RingCat.{u}
        (baseOverTopology B Y hY τ) (baseOverTopology B X hX τ)).obj
        (FibredSite.baseRingStructureSheaf B X hX τ) :=
  ⟨Functor.whiskerRight (NatTrans.op (baseChangeProjection B hX hY f))
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u})⟩

/-- The component of `f_big^♯` at an object `T/Y` is the map on global functions induced by the
projection `X ×_Y T ⟶ T`. -/
@[simp]
public theorem baseStructureComparison_hom_app (T : (BigFppfOver B Y hY)ᵒᵖ) :
    (baseStructureComparison B hX hY f τ).hom.app T
      = (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map (pullback.fst T.unop.hom (siteHom B hX hY f))).op := rfl

/-! ### The comparison of structure sheaves round the square -/

/-- **The two routes round the square of ringed sites carry the same comparison of structure
sheaves**, in each of the five topologies.  Both composites restrict a section of `𝒪_Y` over `V`
to the open `f⁻¹(V)` of `X`: going round the big sites one pulls back along the projection
`X ×_Y V ⟶ V` and then along the comparison `f⁻¹(V) ⟶ X ×_Y V`, whose composite is `f ∣_ V`;
going round the small sites one applies `f^♯` and then identifies global functions.  The two
agree by `AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`.

This is the second proviso of `SheafOfModules.pullbackSquareIso`. -/
public theorem comparisonComp_baseOpensBaseChangeIso :
    SheafOfModules.comparisonComp (baseStructureMap B Y hY τ)
          (baseStructureComparison B hX hY f τ) ≫
        (Functor.sheafPushforwardContinuousNatTrans (opensBaseChangeIso B hX hY f).hom
          RingCat.{u} (Opens.grothendieckTopology ↥Y) (baseOverTopology B X hX τ)).app
          (FibredSite.baseRingStructureSheaf B X hX τ) =
      SheafOfModules.comparisonComp f.toRingCatSheafHom (baseStructureMap B X hX τ) := by
  ext : 2
  funext V
  show (structureMap B Y hY).hom.app V ≫
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map
            (pullback.fst (opensObj B Y hY V.unop).hom (siteHom B hX hY f))).op ≫
        (structureSheaf B X hX).obj.map
          ((opensBaseChangeHom B hX hY f V.unop)).op =
    (f.toRingCatSheafHom).hom.app V ≫
      (structureMap B X hX).hom.app (op ((Opens.map f.base).obj V.unop))
  have hcomb : (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map
            (pullback.fst (opensObj B Y hY V.unop).hom (siteHom B hX hY f))).op ≫
        (structureSheaf B X hX).obj.map ((opensBaseChangeHom B hX hY f V.unop)).op
      = (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map (restrictHom B hX hY f V.unop)).op :=
    ((Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
      (congrArg
        (fun k : B.obj (contains_opens B hX (f ⁻¹ᵁ V.unop)) ⟶ B.obj (contains_opens B hY V.unop)
          => (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map (B.inclusion.map k).op)
        (opensBaseChangeHom_left_comp_fst B hX hY f V.unop))
  refine Eq.trans (congrArg (fun k => (structureMap B Y hY).hom.app V ≫ k) hcomb) ?_
  have key := Scheme.Opens.topIso_inv_appTop_of_comp f V.unop (f ∣_ V.unop)
    (morphismRestrict_ι f V.unop)
  show (forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso (X := Y) V.unop).inv ≫
      (forget₂ CommRingCat RingCat.{u}).map (f ∣_ V.unop).appTop =
    (forget₂ CommRingCat RingCat.{u}).map (f.app V.unop) ≫
      (forget₂ CommRingCat RingCat.{u}).map
        (Scheme.Opens.topIso (X := X) ((Opens.map f.base).obj V.unop)).inv
  rw [← Functor.map_comp, key, Functor.map_comp]

/-! ### Stacks 03FH (2) for `f_big`, in each of the five topologies -/

/-- **Stacks 03FH, part (2), for the morphism of big sites
`f_big : ((Sch/X)_τ, 𝒪_X) ⟶ ((Sch/Y)_τ, 𝒪_Y)` of Stacks 070R (1), at each of the five
topologies `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  The associated module of a
pullback is the pullback of the associated module, `(f^*𝓕)^a ≅ f_big^*(𝓕^a)`, naturally in the
`𝒪_Y`-module `𝓕`.

No hypothesis: the morphism of ringed sites is `AlgebraicGeometry.BigFppfOver.baseChange`
together with `AlgebraicGeometry.BigFppfOver.baseStructureComparison`, and the two provisos of
`SheafOfModules.pullbackSquareIso` are
`AlgebraicGeometry.BigFppfOver.opensBaseChangeIso`, which is topology-free, and
`AlgebraicGeometry.BigFppfOver.comparisonComp_baseOpensBaseChangeIso`.

Together with
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` (the small étale `f_small`) and
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso` (the small Zariski `f_small`,
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallZariskiPushforwardSquare.lean:458`)
this is every `f_sites` the enumeration of Remark 070R lists: clause (1) of that remark gives
the big site at each of these five topologies, and clause (2) the small site at the two
topologies that have one.  (The small Zariski entry was formerly cited as
`AlgebraicGeometry.SmallZariski.associatedModulePullbackIso`, which states the commutation over
the *identity reading* of `𝓕 ↦ 𝓕^a` and is a tautology about `𝟭`; it is untagged, and naming it
here made this enumeration a false completeness claim.) -/
@[stacks 03FH "part (2), for the morphism of big sites f_big : ((Sch/X)_τ, 𝒪_X) → \
((Sch/Y)_τ, 𝒪_Y) of Stacks 070R (1), at each of τ = Zariski, étale, smooth, syntomic, fppf",
  stacks 03LC "part (1) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, for the big \
sites: (f^*𝓖)^a ≅ f_big^*(𝓖^a), for an arbitrary morphism of schemes and arbitrary modules"]
public noncomputable def associatedModuleBasePullbackIso :
    Scheme.Modules.pullback f ⋙ baseAssociatedModule B X hX τ ≅
      baseAssociatedModule B Y hY τ ⋙
        SheafOfModules.pullback.{u} (baseStructureComparison B hX hY f τ) :=
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  SheafOfModules.pullbackSquareIso.{u} f.toRingCatSheafHom (baseStructureMap B X hX τ)
    (baseStructureMap B Y hY τ) (baseStructureComparison B hX hY f τ)
    (opensBaseChangeIso B hX hY f) (comparisonComp_baseOpensBaseChangeIso B hX hY f τ)

/-- **Stacks 03FH, part (2), at one module**: `(f^*𝓕)^a ≅ f_big^*(𝓕^a)` for the morphism of big
sites `f_big` at each of the five topologies, read off from
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`. -/
@[stacks 03FH "part (2) at one module, for the morphism of big sites f_big at each of \
τ = Zariski, étale, smooth, syntomic, fppf",
  stacks 03LC "part (1) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, for the big \
sites, at one module: f_big^*(𝓖^a) ≅ (f^*𝓖)^a"]
public noncomputable def associatedModuleBaseObjPullbackIso (𝓕 : Y.Modules) :
    (baseAssociatedModule B X hX τ).obj ((Scheme.Modules.pullback f).obj 𝓕) ≅
      (SheafOfModules.pullback.{u} (baseStructureComparison B hX hY f τ)).obj
        ((baseAssociatedModule B Y hY τ).obj 𝓕) :=
  (associatedModuleBasePullbackIso B hX hY f τ).app 𝓕

end AlgebraicGeometry.BigFppfOver

end
