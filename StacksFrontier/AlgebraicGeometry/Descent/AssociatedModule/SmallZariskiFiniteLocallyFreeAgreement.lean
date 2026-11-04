module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRingedSiteHomGeneral
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of `𝓕^a` on the small Zariski site

Descent, Lemma 05VG asserts, for each of the properties of modules of Modules on Sites,
Definitions 03DE, 03DL and 03ER, that a quasi-coherent `𝒪_S`-module `𝓕` has the property if and
only if `𝓕^a` has it as an `𝒪`-module on the site.  Finite local freeness, Definition 03DL (2),
is proved at the five **big** sites by
`AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff` and at the
**small étale** site by
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff`.  **This file proves
the clause at the small Zariski site, as an equivalence and with no quasi-coherence
hypothesis**, so the clause is now covered at every one of 05VG's seven comparison functors.

## The route, the pullback direction

The argument is the one that
`BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite` and
`SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite`
run, with the small Zariski site's own comparisons substituted.  Stacks 03DN at the small Zariski
site of `S`, in the form
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree`, produces a
Zariski covering of `S` on whose members `𝓕` is finite free; its image covers the final object of
`S_Zar` by `AlgebraicGeometry.SmallZariski.coversTop_opensToSmallZariski_ulift`; on each member
`(𝓕|_V)^a ≅ (𝓕^a)|_{V_Zar}` by
`AlgebraicGeometry.SmallZariski.associatedModuleOverObjIso`, the step Stacks 03DV leaves implicit,
and the localized associated-module functor carries a colimiting cofan of copies of the structure
sheaf to one, preserving colimits as a left adjoint and carrying the unit object to the unit
object; Stacks 03DN at `S_Zar` assembles the conclusion.  No quasi-coherence enters.

The generic route is unavailable for the reason
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseFiniteLocallyFreeComparison.lean`
records: `Stacks.Sheaves.LocalizedPullback.isFiniteLocallyFreeOnSite_pullbackTopos`, which is
Stacks 03DO for Definition 03DL (2) for a morphism of ringed *sites* presented by a left exact
continuous functor, is stated for `AlgebraicGeometry.RingedSite.{u, u, u}` and for
`AlgebraicGeometry.RingedSite.Hom`, while
`AlgebraicGeometry.smallZariskiRingedSite` is a `RingedSite.{u + 1, u, u}` and the comparison is
only a `AlgebraicGeometry.RingedSite.HomGeneral`.  That remains true at this commit.

## The route, the descent direction

Unlike the small étale site, the small Zariski site needs **no fpqc descent**:
`AlgebraicGeometry.smallZariskiSiteEquiv` is an equivalence of sites
`SmallZariski B S hS ≌ Opens ↥S` which is a dense subsite inclusion in both directions.  Stacks
03DN at `S_Zar` produces a family `Z` covering the final object on whose members the restriction
of `𝓕^a` is finite free; the open images of the `Z i` cover the final object of the opens of `S`
(`CategoryTheory.GrothendieckTopology.coversTop_inverse_obj`), and the unit of the equivalence
gives a morphism from the image in `S_Zar` of the open image of `Z i` back to `Z i`.  Finite
freeness of a restriction is inherited along any arrow of the site, so it moves to that image,
where `AlgebraicGeometry.SmallZariski.associatedModuleOverObjIso` rewrites `(𝓕^a)|_{V_Zar}` as
`(𝓕|_V)^a`, and `Stacks.Sheaves.GlobalTypeComparison.isFiniteFree_iff` reflects finite freeness
down to `𝓕|_V`.

The single statement that step needed, and that the tree lacked, is that the **localized**
comparison `SheafOfModules.pullback (AlgebraicGeometry.SmallZariski.sliceStructureMap B S hS V)`
is fully faithful; it is supplied here, in the stronger form that it is an *equivalence*
(`AlgebraicGeometry.SmallZariski.isEquivalence_pullback_sliceStructureMap`), by
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOverOfIso` at the open-image equivalence of
sites and the invertible structure map of Remark 03FH.  Its unlocalized counterpart is
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModule`.

The two sites here are `RingedSite.{u + 1, u, u}` and `RingedSite.{u, u, u}`, so the localized
statement needs `Stacks.SheafOfModules.InternalHom.siteEquivModulesOver` for ringed sites that do
not share their object and morphism universes.  Nothing in the construction forces a shared
binder: `siteEquivModulesOver` and the `psiOfIso` group are stated for two sites with
independent object and morphism universes, sharing only the universe of the sections, which the
structure map relates.  Only the internal-Hom statements further down that module keep the
shared binder, and they need it.

The index universes do not match either way round and are handled in both directions.  Stacks
03DN at `S_Zar` wants an index in `Type (u + 1)`, which the pullback direction reaches by
`ULift`; it produces one there, which the descent direction must bring down to the `Type u` that
Stacks 03DN on the opens of `S` wants, and does by replacing the family with the subtype of
`S.Opens` cut out by finite freeness
(`CategoryTheory.GrothendieckTopology.CoversTop.of_exists_hom`).

## Main results

* `AlgebraicGeometry.SmallZariski.exists_isColimitCofan_associatedModuleOver`: a finite free cofan
  of `𝓕|_V` gives one of `(𝓕^a)|_{V_Zar}`.
* `SmallZariski.isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite`:
  the pullback direction of the clause at the small Zariski site.
* `AlgebraicGeometry.SmallZariski.sliceModulesEquiv`,
  `AlgebraicGeometry.SmallZariski.isEquivalence_pushforward_sliceStructureMap` and
  `AlgebraicGeometry.SmallZariski.isEquivalence_pullback_sliceStructureMap`: the localization of
  Remark 03FH's comparison at an open of `S` is an equivalence of the two categories of sheaves
  of modules, in both directions.
* `AlgebraicGeometry.SmallZariski.exists_isColimitCofan_over_of_associatedModuleOver`: a finite
  free cofan of `(𝓕^a)|_Z` gives one of `𝓕|_V`, for `V` an open whose image maps to `Z`.
* `AlgebraicGeometry.SmallZariski.isFiniteLocallyFreeOnSite_of_associatedModule`: the descent
  direction of the clause at the small Zariski site.
* `AlgebraicGeometry.SmallZariski.isFiniteLocallyFreeOnSite_associatedModule_iff`:
  **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), at the small Zariski site, as
  an equivalence.**  This is the declaration that carries the `stacks` attribute; the two
  implications are left untagged, 05VG's clause asserting an equivalence and one implication of
  an equivalence not realizing it.  The convention is the one stated in the implementation notes
  of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesUnderComparison.lean`.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite free cofan of `𝓕|_V` gives a finite free cofan of `(𝓕^a)|_{V_Zar}`.**  The
localized associated-module functor of the small Zariski site preserves colimits, being a left
adjoint, and carries the unit object to the unit object; so it carries a colimiting cofan of
copies of the structure sheaf to one, and
`AlgebraicGeometry.SmallZariski.associatedModuleOverObjIso` moves the result to the restriction
of `𝓕^a`. -/
public theorem exists_isColimitCofan_associatedModuleOver (V : S.Opens) (𝓕 : S.Modules)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit (S.ringCatSheaf.over V) ⟶
        SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V,
      Nonempty (IsColimit (Cofan.mk (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit ((structureSheaf B S hS).over ((opensToSmallZariski B S hS).obj V)) ⟶
        ((associatedModule B S hS).obj 𝓕).over ((opensToSmallZariski B S hS).obj V),
      Nonempty (IsColimit (Cofan.mk
        (((associatedModule B S hS).obj 𝓕).over ((opensToSmallZariski B S hS).obj V)) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  let Φ := SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)
  let u := asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))
  let e := associatedModuleOverObjIso B S hS V 𝓕
  refine ⟨n, fun b => (u.inv ≫ Φ.map (ι b)) ≫ e.hom, ⟨?_⟩⟩
  exact (Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap Φ u ι hc).ofIsoColimit
    (Cocones.ext e (fun _ => rfl))

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2): the pullback direction, at
the small Zariski site.**  If an `𝒪_S`-module `𝓕` is finite locally free on the small Zariski
site of `S` presented by the opens of its space, then its associated module `𝓕^a` is finite
locally free as an `𝒪`-module on `S_Zar`.

The source's argument: a Zariski covering of `S` on whose members `𝓕` is finite free is produced
by Stacks 03DN, its image covers the final object of `S_Zar` by
`AlgebraicGeometry.SmallZariski.coversTop_opensToSmallZariski_ulift`, on each member the
restriction of `𝓕^a` is finite free by
`AlgebraicGeometry.SmallZariski.exists_isColimitCofan_associatedModuleOver`, and Stacks 03DN at
`S_Zar` assembles the conclusion.  No quasi-coherence enters this half.

This is one implication of 05VG's clause for 03DL (2), which asserts an equivalence; the
equivalence is `AlgebraicGeometry.SmallZariski.isFiniteLocallyFreeOnSite_associatedModule_iff`
below, which carries the attribute. -/
public theorem isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite
    (𝓕 : S.Modules)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      ((AlgebraicGeometry.SmallZariski.associatedModule B S hS).obj 𝓕) := by
  obtain ⟨I, V, hV, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      S.zariskiRingedSite 𝓕).1 h
  exact (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
    (smallZariskiRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)).2
      ⟨ULift.{u + 1} I, fun i => (opensToSmallZariski B S hS).obj (V i.down),
        coversTop_opensToSmallZariski_ulift B S hS V hV,
        fun i => exists_isColimitCofan_associatedModuleOver B S hS (V i.down) 𝓕 (hfree i.down)⟩

/-! ### The localized comparison is an equivalence -/

/-- The open-image equivalence of Stacks 020X, read from the opens of the space of `S` to the
small Zariski site, so that its forward functor is the inclusion
`AlgebraicGeometry.SmallZariski.opensToSmallZariski` and its inverse the open-image functor. -/
public noncomputable abbrev opensSiteEquiv : S.Opens ≌ SmallZariski B S hS :=
  (smallZariskiSiteEquiv B S hS).symm

/-- The inclusion of the opens of the space of `S` into the small Zariski site is continuous,
at the spelling `AlgebraicGeometry.SmallZariski.opensSiteEquiv` presents it with. -/
public instance isContinuous_opensSiteEquiv_functor :
    (opensSiteEquiv B S hS).functor.IsContinuous
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  inferInstanceAs ((opensToSmallZariski B S hS).IsContinuous _ _)

/-- The open-image functor is continuous, at the spelling `opensSiteEquiv` presents it with. -/
public instance isContinuous_opensSiteEquiv_inverse :
    (opensSiteEquiv B S hS).inverse.IsContinuous
      (topology B S hS) (Opens.grothendieckTopology ↥S) :=
  inferInstanceAs ((smallZariskiToOpens B S hS).IsContinuous _ _)

/-- The open-image functor is a dense subsite inclusion, at the spelling `opensSiteEquiv`
presents it with. -/
public instance isDenseSubsite_opensSiteEquiv_inverse :
    (opensSiteEquiv B S hS).inverse.IsDenseSubsite
      (topology B S hS) (Opens.grothendieckTopology ↥S) :=
  inferInstanceAs ((smallZariskiToOpens B S hS).IsDenseSubsite _ _)

/-- **Sheaves of `𝒪`-modules on the slice of `S_Zar` at an open `V` of `S` and sheaves of
`𝒪_S`-modules on the slice of the opens of `S` at `V` agree.**  This is
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOverOfIso` for the open-image equivalence of
sites of Stacks 020X and the structure-sheaf comparison of Remark 03FH, which is invertible at
`τ = Zariski` by `AlgebraicGeometry.SmallZariski.isIso_structureMap`.

The two sites have different object universes — `SmallZariski B S hS` is a `Type (u + 1)` and
`S.Opens` a `Type u` — which is why the equivalence of slices is taken at the universes of
`siteEquivModulesOverOfIso` rather than at a shared binder.  The invertibility of the structure
map is passed by hand, for the reason the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence` give. -/
public noncomputable def sliceModulesEquiv (V : S.Opens) :
    SheafOfModules.{u} ((structureSheaf B S hS).over ((opensToSmallZariski B S hS).obj V)) ≌
      SheafOfModules.{u} (S.ringCatSheaf.over V) :=
  Stacks.SheafOfModules.InternalHom.siteEquivModulesOverOfIso
    (opensSiteEquiv B S hS) (structureMap B S hS) (hφ := isIso_structureMap B S hS) V

/-- **Restriction along the localized comparison of Remark 03FH is an equivalence.**  It is the
functor of `AlgebraicGeometry.SmallZariski.sliceModulesEquiv`. -/
public instance isEquivalence_pushforward_sliceStructureMap (V : S.Opens) :
    (SheafOfModules.pushforward.{u} (sliceStructureMap B S hS V)).IsEquivalence :=
  (sliceModulesEquiv B S hS V).isEquivalence_functor

/-- **The localized comparison `𝓖 ↦ 𝓖^a` on the slice at an open `V` of `S` is an
equivalence**, hence in particular fully faithful — the single statement the reverse direction
of 05VG's clause for 03DL (2) at the small Zariski site was owed.  It is the left adjoint of
`AlgebraicGeometry.SmallZariski.isEquivalence_pushforward_sliceStructureMap`, and a left adjoint
of an equivalence is an equivalence. -/
public instance isEquivalence_pullback_sliceStructureMap (V : S.Opens) :
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)).IsEquivalence :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u}
    (sliceStructureMap B S hS V)).isEquivalence_left_of_isEquivalence_right

/-! ### The descent direction -/

/-- **A finite free cofan of `(𝓕^a)|_Z` gives one of `𝓕|_V`**, for an open `V` of `S` whose
image in `S_Zar` admits a morphism to `Z`.

Finite freeness of a restriction is inherited along any arrow of the site
(`Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`), so the hypothesis moves from `Z` to
`(opensToSmallZariski B S hS).obj V`, where
`AlgebraicGeometry.SmallZariski.associatedModuleOverObjIso` rewrites it as finite freeness of
`(𝓕|_V)^a`; and `Stacks.Sheaves.GlobalTypeComparison.isFiniteFree_iff` reflects that down to
`𝓕|_V`, the localized comparison being fully faithful and colimit-preserving. -/
public theorem exists_isColimitCofan_over_of_associatedModuleOver (V : S.Opens)
    (Z : SmallZariski B S hS) (a : (opensToSmallZariski B S hS).obj V ⟶ Z) (𝓕 : S.Modules)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit ((structureSheaf B S hS).over Z) ⟶
        ((associatedModule B S hS).obj 𝓕).over Z,
      Nonempty (IsColimit (Cofan.mk (((associatedModule B S hS).obj 𝓕).over Z) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit (S.ringCatSheaf.over V) ⟶
        SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V,
      Nonempty (IsColimit (Cofan.mk (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ι)) := by
  have hres : SheafOfModules.IsFiniteFree
      ((structureSheaf B S hS).over ((opensToSmallZariski B S hS).obj V))
      (((associatedModule B S hS).obj 𝓕).over ((opensToSmallZariski B S hS).obj V)) :=
    (SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
      (Stacks.SheafOfModules.exists_isColimitCofan_over_of_le _ a h)
  rw [← SheafOfModules.isFiniteFree_iff_exists_isColimit]
  refine (Stacks.Sheaves.GlobalTypeComparison.isFiniteFree_iff
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V)))
    (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V)).2 ?_
  exact Stacks.SheafOfModules.isFiniteFree_of_iso
    (associatedModuleOverObjIso B S hS V 𝓕).symm hres

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2): the descent direction, at
the small Zariski site.**  If `𝓕^a` is finite locally free as an `𝒪`-module on `S_Zar`, then the
`𝒪_S`-module `𝓕` is finite locally free on the small Zariski site of `S`.

Unlike the small étale site, the small Zariski site needs no fpqc descent.  Stacks 03DN produces
a family `Z` of objects of `S_Zar` covering its final object on whose members the restriction of
`𝓕^a` is finite free; `AlgebraicGeometry.smallZariskiSiteEquiv` is an equivalence of sites which
is a dense subsite inclusion in both directions, so the open images of the `Z i` cover the final
object of the opens of `S` (`CategoryTheory.GrothendieckTopology.coversTop_inverse_obj`) and the
unit of that equivalence provides, for each `i`, a morphism from the image in `S_Zar` of the open
image of `Z i` back to `Z i`.  Finite freeness of `𝓕` over that open then follows from
`AlgebraicGeometry.SmallZariski.exists_isColimitCofan_over_of_associatedModuleOver`.

The covering family produced that way is indexed by a `Type (u + 1)`, the objects of `S_Zar`
living a universe above the opens of the space, whereas Stacks 03DN on the opens of `S` asks for
an index in `Type u`; so the family is finally replaced by the subtype of `S.Opens` cut out by
finite freeness, which is a `Type u` and which the first family maps into by identities, using
`CategoryTheory.GrothendieckTopology.CoversTop.of_exists_hom`.

No quasi-coherence enters. -/
public theorem isFiniteLocallyFreeOnSite_of_associatedModule (𝓕 : S.Modules)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓕)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓕 := by
  classical
  obtain ⟨I, Z, hZ, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      (smallZariskiRingedSite B S hS) ((associatedModule B S hS).obj 𝓕)).1 h
  let P : S.Opens → Prop := fun W => ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
    SheafOfModules.unit (S.ringCatSheaf.over W) ⟶
      SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 W,
    Nonempty (IsColimit (Cofan.mk (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 W) ι))
  have hP : ∀ i : I, P ((smallZariskiToOpens B S hS).obj (Z i)) := fun i =>
    exists_isColimitCofan_over_of_associatedModuleOver B S hS _ (Z i)
      ((smallZariskiSiteEquiv B S hS).unitIso.inv.app (Z i)) 𝓕 (hfree i)
  have hcov : (Opens.grothendieckTopology ↥S).CoversTop
      (fun i : I => (smallZariskiToOpens B S hS).obj (Z i)) :=
    GrothendieckTopology.coversTop_inverse_obj (opensSiteEquiv B S hS) hZ
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
    S.zariskiRingedSite 𝓕).2 ⟨{W : S.Opens // P W}, Subtype.val, ?_, fun W => W.2⟩
  exact hcov.of_exists_hom fun i => ⟨⟨_, hP i⟩, ⟨𝟙 _⟩⟩

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), at the small Zariski site,
as an equivalence.**  An `𝒪_S`-module `𝓕` is finite locally free on the small Zariski site of `S`
if and only if `𝓕^a` is finite locally free as an `𝒪`-module on `S_Zar`.

The `only if` half is
`SmallZariski.isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite` and the
`if` half is
`AlgebraicGeometry.SmallZariski.isFiniteLocallyFreeOnSite_of_associatedModule`.  **Neither needs
quasi-coherence**, so this is the clause over a weaker hypothesis than the source's, which
carries it: at `τ = Zariski` the comparison of Remark 03FH is an equivalence of ringed sites and
its localization at an open of `S` is one too, so no restriction to the quasi-coherent modules
is needed.

The clause string records the scope: this is clause 03DL (2) of 05VG at the **small** site for
`τ = Zariski`.  The small étale site is
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff` and the five big
sites `(Sch/S)_τ` are
`AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff`; with this
statement the clause is covered at every one of 05VG's seven comparison functors. -/
@[stacks 05VG "finite locally free (03DL (2)), small site at τ = Zariski, at the comparison \
functor of 03DX itself"]
public theorem isFiniteLocallyFreeOnSite_associatedModule_iff (𝓕 : S.Modules) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓕) :=
  ⟨isFiniteLocallyFreeOnSite_associatedModule_of_isFiniteLocallyFreeOnSite B S hS 𝓕,
    isFiniteLocallyFreeOnSite_of_associatedModule B S hS 𝓕⟩

end AlgebraicGeometry.SmallZariski

end
