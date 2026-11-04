module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize

/-!
# The associated module of a quasi-coherent module, by the covering argument

Stacks 03DV proves that the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module is
quasi-coherent by choosing a Zariski covering `{S_i → S}` of `S` on which `𝓕` is the cokernel of
a map of free modules, transporting that presentation to each `(Sch/S_i)_τ`, and appealing to
Stacks 03DN.  Every ingredient of that argument is now available for `τ = fppf`: the transport is
`AlgebraicGeometry.BigFppfOver.associatedModuleOverObjIso`, the passage from a presentation to
the global presentation Stacks 03DL(6) quantifies over is
`SheafOfModules.Presentation.hasGlobalPresentation`, and Stacks 03DN itself is
`SheafOfModules.QuasicoherentData.isQuasicoherentOnSite`.

One statement was missing, and this file supplies it: the image of a Zariski covering family of
`S` covers the final object of the big fppf site of `S`.  The big fppf category over `S` has a
final object — the open `⊤`, through which every object factors uniquely — so this reduces to one
covering sieve, and that sieve is the image of the covering sieve of `⊤` cut out by the family,
which is covering by `AlgebraicGeometry.BigFppfOver.coverPreserving_opensToBig`.

The other apparent gap was the finality of the localization
`CategoryTheory.Over.post (AlgebraicGeometry.BigFppfOver.opensToBig B S hS)` at an open `V` of
`S`, which is what makes the localized comparison of structure sheaves
`AlgebraicGeometry.BigFppfOver.sliceStructureMap` carry the unit object to the unit object — hence
free modules to free modules, which is what transporting a presentation along the isomorphism
`(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)}` needs.  It needs no new declaration at all: the slice `Over V` of
the opens of `S` has a terminal object,
`AlgebraicGeometry.BigFppfOver.preservesFiniteLimits_opensToBig` and Mathlib's
`CategoryTheory.Limits.PreservesFiniteLimits.overPost` make the localized functor preserve it,
and a functor preserving the terminal object of a category that has one is final.
All three steps are instances; the only thing that was missing is the `public import` of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over`, which no module of the associated-module
chain imports.

## Main results

* `AlgebraicGeometry.BigFppfOver.coversTop_opensToBig`: the image of a family of opens covering
  the final object of the small Zariski site of `S` covers the final object of the big fppf site.
* `AlgebraicGeometry.BigFppfOver.presentationAssociatedModuleOver`: a presentation of `𝓕|_V`
  gives a presentation of the restriction of `𝓕^a` to the localization of the big fppf site
  at `V`.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`:
  **Stacks 03DV, clause (1), for `τ = fppf`** — the associated module of a quasi-coherent
  `𝒪_S`-module is quasi-coherent on `(Sch/S)_fppf` in the sense of Stacks 03DL(6).
* `AlgebraicGeometry.BigFppfOver.associatedModuleIsQuasicoherent`: the same statement in the
  shape `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent` in which the library
  carries it as a hypothesis.

## Implementation notes

Nothing here carries a `stacks` attribute, and nothing below is the whole of 03DV.  (The tag
itself is covered by three declarations, clause (1) at every `τ` by
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`
and clause (2) at its two `τ` by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent` and
`AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`.)
Its clause
(1) quantifies over `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, while
`AlgebraicGeometry.BigFppfOver.associatedModule` is the pullback along
`AlgebraicGeometry.BigFppfOver.structureMap`, which takes no `AlgebraicGeometry.SiteKind`
parameter and exists for the fppf topology alone; and clause (2), about `S_Zar` and `S_étale`, is
untouched by anything below.  What is proved is therefore clause (1) at `τ = fppf`, for an
arbitrary quasi-coherent `𝓕` — which is exactly
`AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent`, the hypothesis under which the
library states Stacks 0GNC, 0GNE, 06WV (3) and 03DX (1) at the big fppf site.

`SheafOfModules.QuasicoherentData` indexes its covering family by a type in the universe of the
objects of the site.  The objects of the small Zariski site of `S` lie in `Type u` and those of
the big fppf category over `S` in `Type (u + 1)`, so the index type of the covering family has to
be raised; that is the only role of `CategoryTheory.GrothendieckTopology.CoversTop` at a
`ULift` index in `AlgebraicGeometry.BigFppfOver.coversTop_opensToBig_ulift`.  The raising is
stated as its own result rather than inline: as a field of the
`SheafOfModules.QuasicoherentData` structure its tactic proof is elaborated against the
structure's expected type and does not terminate within the heartbeat budget.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The open `⊤` of `S` is a final object of the big fppf category over `S`: every object factors
through it, since the range of its structure morphism lies in `⊤`, and the factorization is
unique, an open immersion being a monomorphism. -/
public noncomputable def isTerminalOpensObjTop : IsTerminal (opensObj B S hS ⊤) :=
  IsTerminal.ofUniqueHom (fun _ ↦ homOfRangeLe B S hS ⊤ (by simp))
    (fun Z _ ↦ Subsingleton.elim (h := subsingleton_hom_opensObj B S hS Z ⊤) _ _)

/-- **The image of a Zariski covering of `S` covers the big fppf site of `S`.**  A family of
opens of `S` covering the final object of the small Zariski site cuts out a covering sieve of the
open `⊤`, whose image is covering because the inclusion is cover preserving, and `⊤` is a final
object of the big fppf category over `S`. -/
public theorem coversTop_opensToBig {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (topology B S hS).CoversTop (fun i ↦ (opensToBig B S hS).obj (V i)) := by
  rw [(topology B S hS).coversTop_iff_of_isTerminal _ (isTerminalOpensObjTop B S hS)]
  refine (topology B S hS).superset_covering ?_
    ((coverPreserving_opensToBig B S hS).cover_preserve (hV ⊤))
  rintro Z f ⟨W, g, h, ⟨i, ⟨c⟩⟩, rfl⟩
  exact ⟨i, ⟨h ≫ (opensToBig B S hS).map c⟩⟩

/-- `AlgebraicGeometry.BigFppfOver.coversTop_opensToBig` with the index type of the family raised
to the universe of the objects of the big fppf site, which is the universe in which
`SheafOfModules.QuasicoherentData` indexes its covering family. -/
public theorem coversTop_opensToBig_ulift {I : Type*} (V : I → S.Opens)
    (hV : (Opens.grothendieckTopology ↥S).CoversTop V) :
    (topology B S hS).CoversTop
      (fun i : ULift.{u + 1} I ↦ (opensToBig B S hS).obj (V i.down)) := by
  refine coversTop_opensToBig B S hS (fun i : ULift.{u + 1} I ↦ V i.down) (fun U ↦ ?_)
  refine (Opens.grothendieckTopology ↥S).superset_covering ?_ (hV U)
  rintro Z f ⟨i, hi⟩
  exact ⟨ULift.up i, hi⟩

/-- **Stacks 03DV, the transport of a presentation to a member of the covering.**  A presentation
of the restriction of an `𝒪_S`-module `𝓕` to an open `V` of `S` gives a presentation of the
restriction of `𝓕^a` to the localization of the big fppf site of `S` at `V`.

The associated-module functor of the localized site preserves colimits, being a left adjoint, and
carries the unit object to the unit object because `CategoryTheory.Over.post` of the inclusion is
final; so it carries the presentation of `𝓕|_V` to one of `(𝓕|_V)^a`, which is
`(𝓕^a)|_{(Sch/V)}` by `AlgebraicGeometry.BigFppfOver.associatedModuleOverObjIso`. -/
public noncomputable def presentationAssociatedModuleOver (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) :
    (((associatedModule B S hS).obj 𝓕).over ((opensToBig B S hS).obj V)).Presentation :=
  (P.map (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))).symm).ofIsIso
    (associatedModuleOverObjIso B S hS V 𝓕).hom

/-- **Stacks 03DV, the covering argument.**  Quasi-coherent data for an `𝒪_S`-module `𝓕` — a
Zariski covering of `S` together with a presentation of `𝓕` on each member — gives
quasi-coherent data for `𝓕^a` on the big fppf site of `S`, on the image of the same covering. -/
public noncomputable def quasicoherentDataAssociatedModule {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.QuasicoherentData.{u + 1} ((associatedModule B S hS).obj 𝓕) where
  I := ULift.{u + 1} q.I
  X i := (opensToBig B S hS).obj (q.X i.down)
  coversTop := coversTop_opensToBig_ulift B S hS q.X q.coversTop
  presentation i := presentationAssociatedModuleOver B S hS (q.X i.down) (q.presentation i.down)

/-- **Stacks 03DV, clause (1), for `τ = fppf`.**  The associated module `𝓕^a` of a quasi-coherent
`𝒪_S`-module `𝓕` is a quasi-coherent `𝒪`-module on `(Sch/S)_fppf` in the sense of
Stacks 03DL(6). -/
public theorem isQuasicoherentOnSite_associatedModule_of_isQuasicoherent (𝓕 : S.Modules)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    ((associatedModule B S hS).obj 𝓕).IsQuasicoherentOnSite :=
  (quasicoherentDataAssociatedModule B S hS
    h.nonempty_quasicoherentData.some).isQuasicoherentOnSite

/-- **Stacks 03DV, clause (1), for `τ = fppf`**, in the shape in which the library carries it as
a hypothesis: the associated module of every quasi-coherent `𝒪_S`-module is quasi-coherent on
`(Sch/S)_fppf`. -/
public theorem associatedModuleIsQuasicoherent : AssociatedModuleIsQuasicoherent B S hS :=
  fun M ↦ isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS M.obj M.property

end BigFppfOver

end AlgebraicGeometry

end
