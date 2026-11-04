module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Quasi-coherence of `𝓕^a` on the small étale site

Stacks 03DV has two clauses.  Clause (1) says that the associated module `𝓕^a` of a
quasi-coherent `𝒪_S`-module is quasi-coherent on the big site `(Sch/S)_τ` for each of the five
`τ`, and is
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`.
Clause (2) says the same for the **small** sites `S_Zar` and `S_étale`, about the functor of
Definition 03DU (4).  **This file proves clause (2) at `τ = étale`.**

The image of a Zariski covering of `S` on which `𝓕` is presented covers the final object of
`S_étale`, and on each member the presentation of `𝓕|_{V_i}` is carried by the localized
associated-module functor to a presentation of `(𝓕^a)|_{V_i}`; Stacks 03DN,
`SheafOfModules.QuasicoherentData.isQuasicoherentOnSite`, then concludes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.opensStarIso`: the natural isomorphism `W ⊓ V ≅ W ×_S V` of
  functors into the localization of the small étale site of `S` at an open `V`.
* `AlgebraicGeometry.SmallEtale.sliceStructureMap`: the comparison of structure sheaves of the
  localization at `V` of the morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`.

## Main results

* `AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop` and
  `AlgebraicGeometry.SmallEtale.coversTop_opensToSmallEtale`: the open `⊤` is a final object of
  the small étale site of `S`, and the image of a Zariski covering of `S` covers it.
* `AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`: `(𝓕|_V)^a ≅ (𝓕^a)|_{V_étale}`, the
  step Stacks 03DV leaves implicit, on the small étale site.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`:
  **Stacks 03DV, clause (2), at `τ = étale`.**

## Implementation notes

The `τ = Zariski` half of clause (2) is
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`.

`SheafOfModules.QuasicoherentData` indexes its covering family by a type in the universe of the
objects of the site, `Type (u + 1)` for the small étale site of `S`, so the index type of a
Zariski covering is raised by `AlgebraicGeometry.SmallEtale.coversTop_opensToSmallEtale_ulift`.

The sheafification data of each slice of the small étale site is recorded here as an instance
rather than looked up, `SheafOfModules.QuasicoherentData.isQuasicoherentOnSite` asking for it on
every slice.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite limits and hypercovers -/

/-- The inclusion of the small Zariski site of `S` into the small étale site preserves finite
limits, being representably flat. -/
public instance preservesFiniteLimits_opensToSmallEtale :
    PreservesFiniteLimits (opensToSmallEtale B S hS) :=
  preservesFiniteLimits_of_flat _

/-- The inclusion of the small Zariski site of `S` into the small étale site preserves
`1`-hypercovers: it is cover preserving and preserves fibre products. -/
public instance preservesOneHypercovers_opensToSmallEtale :
    (opensToSmallEtale B S hS).PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opensToSmallEtale B S hS)

/-! ### The image of a Zariski covering covers the small étale site -/

/-- The open `⊤` of `S` is a final object of the small étale site of `S`. -/
public noncomputable def isTerminalOpensObjTop : IsTerminal (opensObj B S hS ⊤) :=
  IsTerminal.ofUniqueHom (fun _ ↦ homOfRangeLe B S hS ⊤ (by simp))
    (fun Z _ ↦ Subsingleton.elim
      (h := subsingleton_hom_opensToSmallEtale B S hS Z ⊤) _ _)

/-- **The image of a Zariski covering of `S` covers the small étale site of `S`.** -/
public theorem coversTop_opensToSmallEtale {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (topology B S hS).CoversTop (fun i ↦ (opensToSmallEtale B S hS).obj (V i)) := by
  rw [(topology B S hS).coversTop_iff_of_isTerminal _ (isTerminalOpensObjTop B S hS)]
  refine (topology B S hS).superset_covering ?_
    ((coverPreserving_opensToSmallEtale B S hS).cover_preserve (hV ⊤))
  rintro Z f ⟨W, g, h, ⟨i, ⟨c⟩⟩, rfl⟩
  exact ⟨i, ⟨h ≫ (opensToSmallEtale B S hS).map c⟩⟩

/-- `AlgebraicGeometry.SmallEtale.coversTop_opensToSmallEtale` with the index type of the family
raised to the universe of the objects of the small étale site, which is the universe in which
`SheafOfModules.QuasicoherentData` indexes its covering family. -/
public theorem coversTop_opensToSmallEtale_ulift {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (topology B S hS).CoversTop
      (fun i : ULift.{u + 1} I ↦ (opensToSmallEtale B S hS).obj (V i.down)) := by
  refine coversTop_opensToSmallEtale B S hS (fun i : ULift.{u + 1} I ↦ V i.down) (fun U ↦ ?_)
  refine (Opens.grothendieckTopology ↥S).superset_covering ?_ (hV U)
  rintro Z f ⟨i, hi⟩
  exact ⟨ULift.up i, hi⟩

/-! ### Intersection of opens is their fibre product in the small étale site -/

/-- The small étale site of `S` has a terminal object, the open `⊤`. -/
public instance hasTerminal_smallEtale : HasTerminal (SmallEtale B S hS) :=
  (isTerminalOpensObjTop B S hS).hasTerminal

/-- The small étale site of `S` has binary products: it has a terminal object and, by
`AlgebraicGeometry.hasPullbacks_smallEtale`, fibre products. -/
public instance hasBinaryProducts_smallEtale : HasBinaryProducts (SmallEtale B S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- There is at most one morphism from an object of the small étale site of `S` into a product of
two opens of `S`, there being at most one morphism into each factor. -/
public theorem subsingleton_hom_prodOpens (Z : SmallEtale B S hS) (V W : S.Opens)
    [HasBinaryProduct ((opensToSmallEtale B S hS).obj V)
      ((opensToSmallEtale B S hS).obj W)] :
    Subsingleton (Z ⟶ (opensToSmallEtale B S hS).obj V ⨯
      (opensToSmallEtale B S hS).obj W) :=
  ⟨fun _ _ ↦ prod.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- **The geometric content of Stacks 03DV on the small site, naturally.**  The two functors from
the small Zariski site of `S` to the localization of the small étale site at an open `V` —
intersect with `V`, and take the fibre product with `V` over `S` — are isomorphic. -/
public noncomputable def opensStarIso (V : S.Opens) :
    Over.star V ⋙ Over.post (opensToSmallEtale B S hS) ≅
      opensToSmallEtale B S hS ⋙ Over.star ((opensToSmallEtale B S hS).obj V) :=
  have hp : ∀ W : S.Opens, IsIso (prodComparison (opensToSmallEtale B S hS) V W) :=
    fun _ ↦ inferInstance
  NatIso.ofComponents
    (fun W ↦ Over.isoMk (@asIso _ _ _ _ _ (hp W))
      (Subsingleton.elim (h := subsingleton_hom_opensToSmallEtale B S hS _ V) _ _))
    (fun {_ Y} _ ↦ Over.OverMorphism.ext
      (Subsingleton.elim (h := subsingleton_hom_prodOpens B S hS _ V Y) _ _))

/-- The horizontal isomorphism of the square is the product comparison map of the inclusion. -/
public theorem opensStarIso_hom_app_left (V W : S.Opens) :
    ((opensStarIso B S hS V).hom.app W).left
      = prodComparison (opensToSmallEtale B S hS) V W := rfl

/-! ### Sheafification on the slices, and the localized morphism of ringed sites -/

/-- Abelian presheaves on every localization of the small étale site of `S` at an object have a
left exact sheafification, the small étale site being essentially small. -/
public instance hasSheafify_smallEtaleOver (X : SmallEtale B S hS) :
    HasSheafify ((topology B S hS).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on every localization of the small étale site of `S`
at an object are the locally bijective maps. -/
public instance wEqualsLocallyBijective_smallEtaleOver (X : SmallEtale B S hS) :
    ((topology B S hS).over X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Intersecting with an open `V` of `S` and then including into the localized small étale site
is a continuous functor. -/
public instance isContinuous_starPost (V : S.Opens) :
    (Over.star V ⋙ Over.post (opensToSmallEtale B S hS)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((topology B S hS).over ((opensToSmallEtale B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology ↥S).over V) _

/-- Including into the small étale site and then taking the fibre product with `V` over `S` is a
continuous functor. -/
public instance isContinuous_opensToSmallEtaleStar (V : S.Opens) :
    (opensToSmallEtale B S hS ⋙ Over.star ((opensToSmallEtale B S hS).obj V)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((topology B S hS).over ((opensToSmallEtale B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS) _

/-- The comparison of structure sheaves of the morphism of ringed sites
`(S_étale / V, 𝒪) → (V_Zar, 𝒪_V)`, the localization at an open `V` of `S` of the inclusion of the
small Zariski site of `S`.  Its pullback is the associated-module functor of `V_étale`. -/
public noncomputable abbrev sliceStructureMap (V : S.Opens) :
    (S.ringCatSheaf).over V ⟶
      ((Over.post (opensToSmallEtale B S hS)).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥S).over V)
        ((topology B S hS).over ((opensToSmallEtale B S hS).obj V))).obj
        ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj V)) :=
  SheafOfModules.overComparison (structureMap B S hS) V

/-- The pushforward of presheaves of modules along the localized comparison has a left adjoint. -/
public instance presheafPushforward_sliceStructureMap_isRightAdjoint (V : S.Opens) :
    (PresheafOfModules.pushforward.{u} (sliceStructureMap B S hS V).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the localized comparison has a left adjoint. -/
public instance sheafPushforward_sliceStructureMap_isRightAdjoint (V : S.Opens) :
    (SheafOfModules.pushforward.{u} (sliceStructureMap B S hS V)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (sliceStructureMap B S hS V)).isRightAdjoint

/-! ### Restriction of the associated module to a member of the covering -/

/-- **Stacks 03DV, the step the source leaves implicit, on the small étale site.**  The associated
module of the restriction of an `𝒪_S`-module to an open `V` of `S` is the restriction of its
associated module to the localization of `S_étale` at `V`.  Stated for
`SheafOfModules.pullback (structureMap B S hS)`, which is
`AlgebraicGeometry.SmallEtale.associatedModule` by definition. -/
public noncomputable def associatedModuleOverIso (V : S.Opens) :
    SheafOfModules.overFunctor.{u} S.ringCatSheaf V ⋙
        SheafOfModules.pullback.{u} (sliceStructureMap B S hS V) ≅
      SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
          ((opensToSmallEtale B S hS).obj V) :=
  SheafOfModules.overFunctorPullbackIso.{u} (structureMap B S hS) V
    (opensStarIso B S hS V) (opensStarIso_hom_app_left B S hS V)

/-- **Stacks 03DV, the step the source leaves implicit, at one module, on the small étale
site.**  `(𝓕|_V)^a ≅ (𝓕^a)|_{V_étale}`. -/
public noncomputable def associatedModuleOverObjIso (V : S.Opens) (𝓕 : S.Modules) :
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)).obj
        (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ≅
      ((associatedModule B S hS).obj 𝓕).over ((opensToSmallEtale B S hS).obj V) :=
  (associatedModuleOverIso B S hS V).app 𝓕

/-- **Stacks 03DV, the transport of a presentation to a member of the covering, on the small
étale site.**  A presentation of the restriction of an `𝒪_S`-module `𝓕` to an open `V` of `S`
gives a presentation of the restriction of `𝓕^a` to the localization of `S_étale` at `V`. -/
public noncomputable def presentationAssociatedModuleOver (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) :
    (((associatedModule B S hS).obj 𝓕).over
      ((opensToSmallEtale B S hS).obj V)).Presentation :=
  (P.map (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))).symm).ofIsIso
    (associatedModuleOverObjIso B S hS V 𝓕).hom

/-- **Stacks 03DV, the covering argument, on the small étale site.**  Quasi-coherent data for an
`𝒪_S`-module `𝓕` — a Zariski covering of `S` together with a presentation of `𝓕` on each member —
gives quasi-coherent data for `𝓕^a` on `S_étale`, on the image of the same covering. -/
public noncomputable def quasicoherentDataAssociatedModule {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.QuasicoherentData.{u + 1} ((associatedModule B S hS).obj 𝓕) where
  I := ULift.{u + 1} q.I
  X i := (opensToSmallEtale B S hS).obj (q.X i.down)
  coversTop := coversTop_opensToSmallEtale_ulift B S hS q.X q.coversTop
  presentation i :=
    presentationAssociatedModuleOver B S hS (q.X i.down) (q.presentation i.down)

/-- The associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕` is a quasi-coherent
`𝒪`-module on the small étale site `S_étale`, in the sense of Modules on Sites,
Definition 03DL (6).

The corresponding statement for the small Zariski site is
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`. -/
@[stacks 03DV "part (2) at τ = étale"]
public theorem isQuasicoherentOnSite_associatedModule_of_isQuasicoherent (𝓕 : S.Modules)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    ((associatedModule B S hS).obj 𝓕).IsQuasicoherentOnSite :=
  (quasicoherentDataAssociatedModule B S hS
    h.nonempty_quasicoherentData.some).isQuasicoherentOnSite

end SmallEtale

end AlgebraicGeometry

end
