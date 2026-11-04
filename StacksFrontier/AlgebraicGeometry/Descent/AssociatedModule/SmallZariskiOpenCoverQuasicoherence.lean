module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSite

/-!
# Quasi-coherence of `𝓕^a` on the small Zariski site

Stacks 03DV has two clauses.  Clause (1) says that the associated module `𝓕^a` of a
quasi-coherent `𝒪_S`-module is quasi-coherent on the big site `(Sch/S)_τ` for each of the five
`τ`, and is
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`.
Clause (2) says the same for the **small** sites `S_Zar` and `S_étale`, about the functor of
Definition 03DU (4).  The étale half is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`;
**this file proves the Zariski half, which completes clause (2).**

The source runs one argument for both clauses, and it is run here unchanged.  Choose a Zariski
covering `{V_i → S}` of `S` on which `𝓕` is presented; its image covers the final object of
`S_Zar`, because the inclusion of the small Zariski site is cover preserving and carries the
open `⊤` to a final object.  On each member the presentation of `𝓕|_{V_i}` is transported by the
localized associated-module functor, which is again a left adjoint and again carries the unit
object to the unit object, the localized inclusion being final.  Stacks 03DN,
`SheafOfModules.QuasicoherentData.isQuasicoherentOnSite`, then concludes.

At `τ = Zariski` the inclusion of the small Zariski site into `S_τ` is the inverse of the
open-image equivalence of Stacks 020X, so the three inputs the localization needs come from it
being an equivalence rather than from geometry: it preserves finite limits, which is what
identifies `V ⊓ W` with the product `V × W` inside `S_Zar` and so makes the two routes into the
localization at `V` agree; it is cover preserving
(`AlgebraicGeometry.SmallZariski.coverPreserving_opensToSmallZariski`), which gives both the
covering statement and the preservation of `1`-hypercovers that makes `CategoryTheory.Over.post`
of it continuous; and the hom-sets of `S_Zar` are subsingletons
(`AlgebraicGeometry.SmallZariski.isThin_smallZariski`), which is what the étale argument had to
get from an open immersion being a monomorphism.

## Main definitions

* `AlgebraicGeometry.SmallZariski.opensStarIso`: the natural isomorphism `W ⊓ V ≅ W × V` of
  functors into the localization of the small Zariski site of `S` at an open `V`.
* `AlgebraicGeometry.SmallZariski.sliceStructureMap`: the comparison of structure sheaves of the
  localization at `V` of the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)`.

## Main results

* `AlgebraicGeometry.SmallZariski.isTerminalOpensObjTop` and
  `AlgebraicGeometry.SmallZariski.coversTop_opensToSmallZariski`: the image of the open `⊤` is a
  final object of the small Zariski site of `S`, and the image of a Zariski covering of `S`
  covers it.
* `AlgebraicGeometry.SmallZariski.associatedModuleOverObjIso`: `(𝓕|_V)^a ≅ (𝓕^a)|_{V_Zar}`, the
  step Stacks 03DV leaves implicit, on the small Zariski site.
* `AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`:
  **Stacks 03DV, clause (2), at `τ = Zariski`.**

## Implementation notes

Clause (2) of the source quantifies over `τ ∈ {Zariski, étale}` — the two topologies for which
Definition 03DU (4) defines the functor at all — so with the étale half already proved the clause
is now complete.  Each half is nevertheless a statement about a different functor on a different
site, and the two clause strings record which.

`SheafOfModules.QuasicoherentData` indexes its covering family by a type in the universe of the
objects of the site.  The opens of the space of `S` lie in `Type u` and the objects of the small
Zariski site of `S` in `Type (u + 1)`, so the index type has to be raised; that is the only role
of `AlgebraicGeometry.SmallZariski.coversTop_opensToSmallZariski_ulift`, which is stated as its
own result rather than inline because as a field of the structure its tactic proof is elaborated
against the structure's expected type and does not terminate within the heartbeat budget.  This
is the same arrangement, for the same reason, as on the big sites and on the small étale site.

The sheafification data of each slice of the small Zariski site is recorded here as an instance
rather than looked up, `SheafOfModules.QuasicoherentData.isQuasicoherentOnSite` asking for it on
every slice.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The image of a Zariski covering covers the small Zariski site -/

/-- The open `⊤` is a final object of the opens of the space of `S`: every open is contained in
it, and an inclusion of opens is unique. -/
public noncomputable def isTerminalTopOpens : IsTerminal (⊤ : S.Opens) :=
  IsTerminal.ofUniqueHom (fun _ ↦ homOfLE le_top) (fun _ _ ↦ Subsingleton.elim _ _)

/-- The image of the open `⊤` is a final object of the small Zariski site of `S`, the inclusion
being an equivalence and `⊤` final among the opens. -/
public noncomputable def isTerminalOpensObjTop :
    IsTerminal ((opensToSmallZariski B S hS).obj ⊤) :=
  (isTerminalTopOpens S).isTerminalObj _

/-- **The image of a Zariski covering of `S` covers the small Zariski site of `S`.**  A family of
opens of `S` covering the final object of the opens of the space cuts out a covering sieve of the
open `⊤`, whose image is covering because the inclusion is cover preserving, and the image of `⊤`
is a final object of the small Zariski site. -/
public theorem coversTop_opensToSmallZariski {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (topology B S hS).CoversTop (fun i ↦ (opensToSmallZariski B S hS).obj (V i)) := by
  rw [(topology B S hS).coversTop_iff_of_isTerminal _ (isTerminalOpensObjTop B S hS)]
  refine (topology B S hS).superset_covering ?_
    ((coverPreserving_opensToSmallZariski B S hS).cover_preserve (hV ⊤))
  rintro Z f ⟨W, g, h, ⟨i, ⟨c⟩⟩, rfl⟩
  exact ⟨i, ⟨h ≫ (opensToSmallZariski B S hS).map c⟩⟩

/-- `AlgebraicGeometry.SmallZariski.coversTop_opensToSmallZariski` with the index type of the
family raised to the universe of the objects of the small Zariski site, which is the universe in
which `SheafOfModules.QuasicoherentData` indexes its covering family. -/
public theorem coversTop_opensToSmallZariski_ulift {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (topology B S hS).CoversTop
      (fun i : ULift.{u + 1} I ↦ (opensToSmallZariski B S hS).obj (V i.down)) := by
  refine coversTop_opensToSmallZariski B S hS (fun i : ULift.{u + 1} I ↦ V i.down) (fun U ↦ ?_)
  refine (Opens.grothendieckTopology ↥S).superset_covering ?_ (hV U)
  rintro Z f ⟨i, hi⟩
  exact ⟨ULift.up i, hi⟩

/-! ### Intersection of opens is their product in the small Zariski site -/

/-- **The geometric content of Stacks 03DV on the small Zariski site, naturally.**  The two
functors from the opens of the space of `S` to the localization of the small Zariski site at an
open `V` — intersect with `V`, and take the product with `V` — are isomorphic.  The inclusion is
an equivalence, so it preserves the binary product, and the two factorizations of an object into
`V` are equal, the site being thin. -/
public noncomputable def opensStarIso (V : S.Opens) :
    Over.star V ⋙ Over.post (opensToSmallZariski B S hS) ≅
      opensToSmallZariski B S hS ⋙ Over.star ((opensToSmallZariski B S hS).obj V) :=
  have hp : ∀ W : S.Opens, IsIso (prodComparison (opensToSmallZariski B S hS) V W) :=
    fun _ ↦ inferInstance
  NatIso.ofComponents
    (fun W ↦ Over.isoMk (@asIso _ _ _ _ _ (hp W)) (Subsingleton.elim _ _))
    (fun {_ _} _ ↦ Over.OverMorphism.ext (Subsingleton.elim _ _))

/-- The horizontal isomorphism of the square is the product comparison map of the inclusion. -/
public theorem opensStarIso_hom_app_left (V W : S.Opens) :
    ((opensStarIso B S hS V).hom.app W).left
      = prodComparison (opensToSmallZariski B S hS) V W := rfl

/-! ### Sheafification on the slices, and the localized morphism of ringed sites -/

/-- Abelian presheaves on every localization of the small Zariski site of `S` at an object have a
left exact sheafification, the small Zariski site being essentially small. -/
public instance hasSheafify_smallZariskiOver (X : SmallZariski B S hS) :
    HasSheafify ((topology B S hS).over X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on every localization of the small Zariski site of
`S` at an object are the locally bijective maps. -/
public instance wEqualsLocallyBijective_smallZariskiOver (X : SmallZariski B S hS) :
    ((topology B S hS).over X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Intersecting with an open `V` of `S` and then including into the localized small Zariski site
is a continuous functor. -/
public instance isContinuous_starPost (V : S.Opens) :
    (Over.star V ⋙ Over.post (opensToSmallZariski B S hS)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((topology B S hS).over ((opensToSmallZariski B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology ↥S).over V) _

/-- Including into the small Zariski site and then taking the product with `V` is a continuous
functor. -/
public instance isContinuous_opensToSmallZariskiStar (V : S.Opens) :
    (opensToSmallZariski B S hS ⋙ Over.star ((opensToSmallZariski B S hS).obj V)).IsContinuous
      (Opens.grothendieckTopology ↥S)
      ((topology B S hS).over ((opensToSmallZariski B S hS).obj V)) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS) _

/-- The comparison of structure sheaves of the morphism of ringed sites
`(S_Zar / V, 𝒪) → (V_Zar, 𝒪_V)`, the localization at an open `V` of `S` of the inclusion of the
small Zariski site.  Its pullback is the associated-module functor of `V_Zar`. -/
public noncomputable abbrev sliceStructureMap (V : S.Opens) :
    (S.ringCatSheaf).over V ⟶
      ((Over.post (opensToSmallZariski B S hS)).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥S).over V)
        ((topology B S hS).over ((opensToSmallZariski B S hS).obj V))).obj
        ((structureSheaf B S hS).over ((opensToSmallZariski B S hS).obj V)) :=
  SheafOfModules.overComparison (structureMap B S hS) V

/-- The pushforward of presheaves of modules along the localized comparison has a left adjoint:
the source of the localized continuous functor is a small category. -/
public instance presheafPushforward_sliceStructureMap_isRightAdjoint (V : S.Opens) :
    (PresheafOfModules.pushforward.{u} (sliceStructureMap B S hS V).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the localized comparison has a left adjoint. -/
public instance sheafPushforward_sliceStructureMap_isRightAdjoint (V : S.Opens) :
    (SheafOfModules.pushforward.{u} (sliceStructureMap B S hS V)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (sliceStructureMap B S hS V)).isRightAdjoint

/-! ### Restriction of the associated module to a member of the covering -/

/-- **Stacks 03DV, the step the source leaves implicit, on the small Zariski site.**  The
associated module of the restriction of an `𝒪_S`-module to an open `V` of `S` is the restriction
of its associated module to the localization of `S_Zar` at `V`.  Stated for
`SheafOfModules.pullback (structureMap B S hS)`, which is
`AlgebraicGeometry.SmallZariski.associatedModule` by definition. -/
public noncomputable def associatedModuleOverIso (V : S.Opens) :
    SheafOfModules.overFunctor.{u} S.ringCatSheaf V ⋙
        SheafOfModules.pullback.{u} (sliceStructureMap B S hS V) ≅
      SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
          ((opensToSmallZariski B S hS).obj V) :=
  SheafOfModules.overFunctorPullbackIso.{u} (structureMap B S hS) V
    (opensStarIso B S hS V) (opensStarIso_hom_app_left B S hS V)

/-- **Stacks 03DV, the step the source leaves implicit, at one module, on the small Zariski
site.**  `(𝓕|_V)^a ≅ (𝓕^a)|_{V_Zar}`. -/
public noncomputable def associatedModuleOverObjIso (V : S.Opens) (𝓕 : S.Modules) :
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)).obj
        (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ≅
      ((associatedModule B S hS).obj 𝓕).over ((opensToSmallZariski B S hS).obj V) :=
  (associatedModuleOverIso B S hS V).app 𝓕

/-- **Stacks 03DV, the transport of a presentation to a member of the covering, on the small
Zariski site.**  A presentation of the restriction of an `𝒪_S`-module `𝓕` to an open `V` of `S`
gives a presentation of the restriction of `𝓕^a` to the localization of `S_Zar` at `V`.

The associated-module functor of the localized site preserves colimits, being a left adjoint, and
carries the unit object to the unit object because `CategoryTheory.Over.post` of the inclusion is
final; so it carries the presentation of `𝓕|_V` to one of `(𝓕|_V)^a`, which is `(𝓕^a)|_{V_Zar}`
by `AlgebraicGeometry.SmallZariski.associatedModuleOverObjIso`. -/
public noncomputable def presentationAssociatedModuleOver (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) :
    (((associatedModule B S hS).obj 𝓕).over
      ((opensToSmallZariski B S hS).obj V)).Presentation :=
  (P.map (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
        (sliceStructureMap B S hS V))).symm).ofIsIso
    (associatedModuleOverObjIso B S hS V 𝓕).hom

/-- **Stacks 03DV, the covering argument, on the small Zariski site.**  Quasi-coherent data for an
`𝒪_S`-module `𝓕` — a Zariski covering of `S` together with a presentation of `𝓕` on each member —
gives quasi-coherent data for `𝓕^a` on `S_Zar`, on the image of the same covering. -/
public noncomputable def quasicoherentDataAssociatedModule {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.QuasicoherentData.{u + 1} ((associatedModule B S hS).obj 𝓕) where
  I := ULift.{u + 1} q.I
  X i := (opensToSmallZariski B S hS).obj (q.X i.down)
  coversTop := coversTop_opensToSmallZariski_ulift B S hS q.X q.coversTop
  presentation i :=
    presentationAssociatedModuleOver B S hS (q.X i.down) (q.presentation i.down)

/-- **Stacks 03DV, clause (2), at `τ = Zariski`.**  The associated module `𝓕^a` of a
quasi-coherent `𝒪_S`-module `𝓕` is a quasi-coherent `𝒪`-module on the small Zariski site `S_Zar`,
in the sense of Modules on Sites, Definition 03DL (6).

The clause string records exactly the scope proved.  Clause (2) of the source
quantifies over `τ ∈ {Zariski, étale}` — the two topologies for which Definition 03DU (4) defines
the functor at all — and this is the `τ = Zariski` half, for an arbitrary quasi-coherent `𝓕`; the
`τ = étale` half is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`, so with
this declaration clause (2) is complete.  Clause (1) of the source, at all five `τ`, is
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`. -/
@[stacks 03DV "part (2) at τ = Zariski"]
public theorem isQuasicoherentOnSite_associatedModule_of_isQuasicoherent (𝓕 : S.Modules)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    ((associatedModule B S hS).obj 𝓕).IsQuasicoherentOnSite :=
  (quasicoherentDataAssociatedModule B S hS
    h.nonempty_quasicoherentData.some).isQuasicoherentOnSite

end SmallZariski

end AlgebraicGeometry

end
