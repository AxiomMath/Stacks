module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence

/-!
# Quasi-coherence of `𝓕^a` on each of the five big sites

Stacks 03DV, clause (1), says that for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` the
associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕` is a quasi-coherent `𝒪`-module on
the big site `(Sch/S)_τ` in the sense of Modules on Sites, Definition 03DL.
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence` proves it for
`τ = fppf`; this file proves it for all five `τ` at once.

The source's argument is run at `τ` unchanged.  Choose a Zariski covering `{V_i → S}` of `S` on
which `𝓕` is presented; its image covers the final object of `(Sch/S)_τ` for every `τ`, because
the members are open immersions and
`AlgebraicGeometry.BigFppfOver.coverPreserving_baseOpensToBig` carries Zariski coverings into
each of the five localized topologies.  On each member the presentation of `𝓕|_{V_i}` is
transported by the localized associated-module functor, which is again a left adjoint and again
carries the unit object to the unit object — the inclusion `Over.post` of the small Zariski site
is final, and finality does not see the topology.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseSliceStructureMap`: the comparison of structure sheaves of
  the localization at an open `V` of `S` of the morphism of ringed sites
  `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`.

## Main results

* `AlgebraicGeometry.BigFppfOver.coversTop_baseOpensToBig`: the image of a family of opens
  covering the final object of the small Zariski site of `S` covers the final object of each of
  the five big sites.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOverObjIso`: `(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)_τ}`,
  the step Stacks 03DV leaves implicit, for each of the five sites.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`:
  **Stacks 03DV, clause (1), at every `τ`.**

## Implementation notes

The index type of the covering family of `SheafOfModules.QuasicoherentData` lies in the universe
of the objects of the site, which for the big category of schemes over `S` is `Type (u + 1)`
while the opens of `S` lie in `Type u`; `AlgebraicGeometry.BigFppfOver.coversTop_baseOpensToBig`
is therefore also recorded at a `ULift` index, exactly as in the fppf file, and for the same
reason: as a field of the structure its tactic proof is elaborated against the structure's
expected type and does not terminate within the heartbeat budget.

The sheafification data of each slice of each of the five sites is recorded here as an instance
rather than looked up: `AlgebraicGeometry.BigFppfOver.hasWeakSheafify_over` and
`AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_over` are theorems, and
`SheafOfModules.QuasicoherentData.isQuasicoherentOnSite` asks for them on every slice.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on each of the five big sites of `S` have a left exact sheafification,
the big category of schemes over `S` being essentially small. -/
public instance hasSheafify_baseOverTopology (τ : SiteKind) :
    HasSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Abelian presheaves on every localization of each of the five big sites of `S` at an object
have a left exact sheafification. -/
public instance hasSheafify_baseOver (τ : SiteKind) (X : BigFppfOver B S hS) :
    HasSheafify ((baseOverTopology B S hS τ).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on every localization of each of the five big sites
over `S` at an object are the locally bijective maps:
`AlgebraicGeometry.BigFppfOver.wEqualsLocallyBijective_over`, as an instance. -/
public instance wEqualsLocallyBijective_baseOver (τ : SiteKind) (X : BigFppfOver B S hS) :
    ((baseOverTopology B S hS τ).over X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_over B S hS τ X

/-- **The image of a Zariski covering of `S` covers each of the five big sites of `S`.**  A family
of opens of `S` covering the final object of the small Zariski site cuts out a covering sieve of
the open `⊤`, whose image is covering for every `τ` because the inclusion is cover preserving
(`AlgebraicGeometry.BigFppfOver.coverPreserving_baseOpensToBig`), and `⊤` is a final object of
the big fppf category over `S`. -/
public theorem coversTop_baseOpensToBig (τ : SiteKind) {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (baseOverTopology B S hS τ).CoversTop (fun i ↦ (opensToBig B S hS).obj (V i)) := by
  rw [(baseOverTopology B S hS τ).coversTop_iff_of_isTerminal _ (isTerminalOpensObjTop B S hS)]
  refine (baseOverTopology B S hS τ).superset_covering ?_
    ((coverPreserving_baseOpensToBig B S hS τ).cover_preserve (hV ⊤))
  rintro Z f ⟨W, g, h, ⟨i, ⟨c⟩⟩, rfl⟩
  exact ⟨i, ⟨h ≫ (opensToBig B S hS).map c⟩⟩

/-- `AlgebraicGeometry.BigFppfOver.coversTop_baseOpensToBig` with the index type of the family
raised to the universe of the objects of the big site, which is the universe in which
`SheafOfModules.QuasicoherentData` indexes its covering family. -/
public theorem coversTop_baseOpensToBig_ulift (τ : SiteKind) {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (baseOverTopology B S hS τ).CoversTop
      (fun i : ULift.{u + 1} I ↦ (opensToBig B S hS).obj (V i.down)) := by
  refine coversTop_baseOpensToBig B S hS τ (fun i : ULift.{u + 1} I ↦ V i.down) (fun U ↦ ?_)
  refine (Opens.grothendieckTopology ↥S).superset_covering ?_ (hV U)
  rintro Z f ⟨i, hi⟩
  exact ⟨ULift.up i, hi⟩

/-- The inclusion of the small Zariski site of `S` preserves `1`-hypercovers into each of the
five big sites: it is cover preserving into each of them, and it preserves fibre products.  This
is what makes `CategoryTheory.Over.post` of the inclusion continuous into the localization at an
open of `S`, through Mathlib's `Over.post` instance for `PreservesOneHypercovers`. -/
public instance preservesOneHypercovers_baseOpensToBig (τ : SiteKind) :
    (opensToBig B S hS).PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ) :=
  Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_baseOpensToBig B S hS τ)

/-- Intersecting with an open `V` of `S` and then including into the localization at `V` of the
indicated big site is a continuous functor. -/
public instance isContinuous_baseStarPost (τ : SiteKind) (V : S.Opens) :
    (Over.star V ⋙ Over.post (opensToBig B S hS)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((baseOverTopology B S hS τ).over ((opensToBig B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology ↥S).over V) _

/-- Including into the big category of schemes over `S` and then taking the fibre product with an
open `V` of `S` is continuous into the localization at `V` of the indicated big site. -/
public instance isContinuous_baseOpensToBigStar (τ : SiteKind) (V : S.Opens) :
    (opensToBig B S hS ⋙ Over.star ((opensToBig B S hS).obj V)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((baseOverTopology B S hS τ).over ((opensToBig B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ (baseOverTopology B S hS τ) _

/-- The comparison of structure sheaves of the morphism of ringed sites
`((Sch/S)_τ / V, 𝒪) → (V_Zar, 𝒪_V)`, the localization at an open `V` of `S` of the inclusion of
the small Zariski site of `S`.  Its pullback is the associated-module functor of `(Sch/V)_τ`; the
fppf case is `AlgebraicGeometry.BigFppfOver.sliceStructureMap`. -/
public noncomputable abbrev baseSliceStructureMap (τ : SiteKind) (V : S.Opens) :
    (S.ringCatSheaf).over V ⟶
      ((Over.post (opensToBig B S hS)).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥S).over V)
        ((baseOverTopology B S hS τ).over ((opensToBig B S hS).obj V))).obj
        ((FibredSite.baseRingStructureSheaf B S hS τ).over ((opensToBig B S hS).obj V)) :=
  SheafOfModules.overComparison (baseStructureMap B S hS τ) V

/-- The pushforward of presheaves of modules along the localized comparison has a left adjoint:
the source of the localized continuous functor is a small category. -/
public instance presheafPushforward_baseSliceStructureMap_isRightAdjoint (τ : SiteKind)
    (V : S.Opens) :
    (PresheafOfModules.pushforward.{u} (baseSliceStructureMap B S hS τ V).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the localized comparison has a left adjoint. -/
public instance sheafPushforward_baseSliceStructureMap_isRightAdjoint (τ : SiteKind)
    (V : S.Opens) :
    (SheafOfModules.pushforward.{u} (baseSliceStructureMap B S hS τ V)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (baseSliceStructureMap B S hS τ V)).isRightAdjoint

/-- **Stacks 03DV, the step the source leaves implicit, for each of the five sites.**  The
associated module of the restriction of an `𝒪_S`-module to an open `V` of `S` is the restriction
of its associated module to the localization of `(Sch/S)_τ` at `V`.  Stated for
`SheafOfModules.pullback (baseStructureMap B S hS τ)`, which is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModule` by definition. -/
public noncomputable def baseAssociatedModuleOverIso (τ : SiteKind) (V : S.Opens) :
    SheafOfModules.overFunctor.{u} S.ringCatSheaf V ⋙
        SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V) ≅
      SheafOfModules.pullback.{u} (baseStructureMap B S hS τ) ⋙
        SheafOfModules.overFunctor.{u} (FibredSite.baseRingStructureSheaf B S hS τ)
          ((opensToBig B S hS).obj V) :=
  SheafOfModules.overFunctorPullbackIso.{u} (baseStructureMap B S hS τ) V
    (opensStarIso B S hS V) (opensStarIso_hom_app_left B S hS V)

/-- **Stacks 03DV, the step the source leaves implicit, at one module and each of the five
sites.**  `(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)_τ}`. -/
public noncomputable def baseAssociatedModuleOverObjIso (τ : SiteKind) (V : S.Opens)
    (𝓕 : S.Modules) :
    (SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V)).obj
        (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ≅
      ((baseAssociatedModule B S hS τ).obj 𝓕).over ((opensToBig B S hS).obj V) :=
  (baseAssociatedModuleOverIso B S hS τ V).app 𝓕

/-- **Stacks 03DV, the transport of a presentation to a member of the covering, at every `τ`.**  A
presentation of the restriction of an `𝒪_S`-module `𝓕` to an open `V` of `S` gives a presentation
of the restriction of `𝓕^a` to the localization of `(Sch/S)_τ` at `V`.

The associated-module functor of the localized site preserves colimits, being a left adjoint, and
carries the unit object to the unit object because `CategoryTheory.Over.post` of the inclusion is
final — a condition on the functor alone, so the same at every `τ`. -/
public noncomputable def basePresentationAssociatedModuleOver (τ : SiteKind) (V : S.Opens)
    {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) :
    (((baseAssociatedModule B S hS τ).obj 𝓕).over
      ((opensToBig B S hS).obj V)).Presentation :=
  (P.map (SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
        (baseSliceStructureMap B S hS τ V))).symm).ofIsIso
    (baseAssociatedModuleOverObjIso B S hS τ V 𝓕).hom

/-- **Stacks 03DV, the covering argument, at every `τ`.**  Quasi-coherent data for an
`𝒪_S`-module `𝓕` — a Zariski covering of `S` together with a presentation of `𝓕` on each member —
gives quasi-coherent data for `𝓕^a` on `(Sch/S)_τ`, on the image of the same covering. -/
public noncomputable def baseQuasicoherentDataAssociatedModule (τ : SiteKind) {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.QuasicoherentData.{u + 1} ((baseAssociatedModule B S hS τ).obj 𝓕) where
  I := ULift.{u + 1} q.I
  X i := (opensToBig B S hS).obj (q.X i.down)
  coversTop := coversTop_baseOpensToBig_ulift B S hS τ q.X q.coversTop
  presentation i :=
    basePresentationAssociatedModuleOver B S hS τ (q.X i.down) (q.presentation i.down)

/-- For every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` the associated module `𝓕^a` of a
quasi-coherent `𝒪_S`-module `𝓕` is a quasi-coherent `𝒪`-module on the big site `(Sch/S)_τ`, in
the sense of Modules on Sites, Definition 03DL (6). -/
@[stacks 03DV "part (1), every τ"]
public theorem isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent (τ : SiteKind)
    (𝓕 : S.Modules) (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    ((baseAssociatedModule B S hS τ).obj 𝓕).IsQuasicoherentOnSite :=
  (baseQuasicoherentDataAssociatedModule B S hS τ
    h.nonempty_quasicoherentData.some).isQuasicoherentOnSite

end BigFppfOver

end AlgebraicGeometry

end
