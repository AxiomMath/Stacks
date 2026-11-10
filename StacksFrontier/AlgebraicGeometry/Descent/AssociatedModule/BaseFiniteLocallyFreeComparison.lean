module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral

/-!
# Finite local freeness of `𝓕^a` on each of the five big sites

Descent, Lemma 05VG asserts, for each of the fifteen properties of modules of Modules on Sites,
Definitions 03DE, 03DL and 03ER, that a quasi-coherent `𝒪_S`-module `𝓕` has the property if and
only if `𝓕^a` has it as an `𝒪`-module on `(Sch/S)_τ`.  Finite local freeness, Definition
03DL (2), is one of the clauses the source claims; it is *not* among the ones the library has,
and `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesUnderComparison.lean` records why —
the generic route, Modules on Sites, Lemma 03DO for a morphism of ringed topoi, is not available
at this level of generality.

**This file proves the `only if` half of that clause, at every one of the five big sites, with no
hypothesis beyond the one the clause carries**: if `𝓕` is finite locally free on the small
Zariski site of `S`, then `𝓕^a` is finite locally free on `(Sch/S)_τ`.

The generic route is unavailable for a reason that is a universe constraint rather than a gap in
the mathematics: `Stacks.Sheaves.LocalizedPullback.isFiniteLocallyFreeOnSite_pullbackTopos`,
which is 03DO for 03DL (2) for a morphism of ringed *sites* presented by a left exact continuous
functor, is stated for `AlgebraicGeometry.RingedSite.{u, u, u}` — all three universes equal — and
the big site of a scheme is `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, its objects living one
universe above its morphisms.  So the argument is run here directly, at the big site, exactly as
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseOpenCoverQuasicoherence.lean` runs
the argument of Stacks 03DV for quasi-coherence rather than citing a generic statement.

The three steps are the source's own, and each is a statement in the library:

* finite local freeness may be tested on the members of any family covering the final object,
  `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree` (Stacks 03DN),
  used at the small Zariski site of `S` to produce the covering family and at the big `τ`-site to
  consume it;
* the image of a Zariski covering of `S` covers the final object of each of the five big sites,
  `AlgebraicGeometry.BigFppfOver.coversTop_baseOpensToBig_ulift`;
* on each member, `(𝓕|_V)^a ≅ (𝓕^a)|_{(Sch/V)_τ}`,
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOverObjIso` (the step Stacks 03DV leaves
  implicit), and the localized associated-module functor carries a finite free module to a finite
  free module because it preserves colimits, being a left adjoint, and carries the unit object to
  the unit object.

That last step is `Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap`, the preservation half
of the global clauses of 05VG; only the preservation half is used, so no fullness or
faithfulness of the localized associated-module functor is needed — which is why the direction
proved here is the one that comes for free and the converse does not.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_isColimitCofan_baseAssociatedModuleOver`: a finite free
  cofan of `𝓕|_V` gives one of `(𝓕^a)|_{(Sch/V)_τ}`.
* `BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite`:
  **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), the pullback direction, at the
  big site `(Sch/S)_τ` for every `τ`.**  It carries no `stacks` attribute: 05VG's clause is an
  equivalence and this is one implication of it.

## Coverage limits

The converse — that `𝓕` is finite locally free as soon as `𝓕^a` is — is **not** proved here, and
it is the half that carries the mathematics: it is the descent of finite local freeness along the
`τ`-covering of `S` that trivializes `𝓕^a`.  It **is** proved, at every `τ`, in a downstream
module: `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/`
`BigSiteFiniteLocallyFreeAgreement.lean`) is the clause as an equivalence, and it is that module
rather than this one that carries the 05VG attribute for 03DL (2); the parenthetical of
Descent, Lemma 0GNE (3) is proved there too, as
`…isFiniteLocallyFreeOnSite_restrictTopology_iff`.  What follows explains why the converse is
not proved in this module.  Its inputs are all in the library (Stacks 05B2,
`AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover`; Stacks 05VG for 03DE (2) at the
big site, `AlgebraicGeometry.BigFppfOver.isFiniteFree_iff_baseAssociatedModule`; and Stacks
03DX (1) at `τ = fppf`,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`), but what joins
them is the `τ`-analogue of Stacks 03DV functorial in an **arbitrary object** of the big site —
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, which exists at `τ = fppf`
only, whereas the result below needs only the analogue at an **open of `S`**, which
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOverObjIso` supplies at every `τ`.  No clause
of this file claims the converse, and no `05VG` attribute here is to be read as claiming it: the
attribute's clause string records the direction proved.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite free cofan of `𝓕|_V` gives a finite free cofan of `(𝓕^a)|_{(Sch/V)_τ}`.**  The
localized associated-module functor of each of the five big sites preserves colimits, being a
left adjoint, and carries the unit object to the unit object; so it carries a colimiting cofan of
copies of the structure sheaf to one, and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOverObjIso` moves the result to the
restriction of `𝓕^a`. -/
public theorem exists_isColimitCofan_baseAssociatedModuleOver (τ : SiteKind) (V : S.Opens)
    (𝓕 : S.Modules)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit (S.ringCatSheaf.over V) ⟶
        SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V,
      Nonempty (IsColimit (Cofan.mk (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit ((FibredSite.baseRingStructureSheaf B S hS τ).over
          ((opensToBig B S hS).obj V)) ⟶
        ((baseAssociatedModule B S hS τ).obj 𝓕).over ((opensToBig B S hS).obj V),
      Nonempty (IsColimit (Cofan.mk
        (((baseAssociatedModule B S hS τ).obj 𝓕).over ((opensToBig B S hS).obj V)) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V)) :=
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (baseSliceStructureMap B S hS τ V)).leftAdjoint_preservesColimits
  let Φ := SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V)
  let u := asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
    (baseSliceStructureMap B S hS τ V))
  let e := baseAssociatedModuleOverObjIso B S hS τ V 𝓕
  refine ⟨n, fun b => (u.inv ≫ Φ.map (ι b)) ≫ e.hom, ⟨?_⟩⟩
  exact (Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap Φ u ι hc).ofIsoColimit
    (Cocone.ext e (fun _ => rfl))

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2): the pullback direction, at
the big site `(Sch/S)_τ` for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  If an
`𝒪_S`-module `𝓕` is finite locally free on the small Zariski site of `S`, then its associated
module `𝓕^a` is finite locally free as an `𝒪`-module on `(Sch/S)_τ`, in the sense of Modules on
Sites, Definition 03DL (2).

The source's argument, run at `τ` unchanged: a Zariski covering of `S` on whose members `𝓕` is
finite free is produced by Stacks 03DN at the small Zariski site, its image covers the final
object of `(Sch/S)_τ` for every `τ`, on each member the restriction of `𝓕^a` is finite free by
`AlgebraicGeometry.BigFppfOver.exists_isColimitCofan_baseAssociatedModuleOver`, and Stacks 03DN
at the big `τ`-site assembles the conclusion.

**No `stacks` attribute is carried**, and that is the project's own rule rather than caution:
05VG's clause for 03DL (2) asserts an *equivalence*, and this is one implication of it.  The
convention is the one stated in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalTypesUnderComparison.lean` for the forward
implications of the other local clauses — "half of an equivalence does not realize the clause".
The same applies to Descent, Lemma 0GNE (3), whose parenthetical is the three-way equivalence
across the Zariski, étale and fppf topologies: this implication is a step towards it and not a
clause of it.  Both equivalences are proved in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/`
`BigSiteFiniteLocallyFreeAgreement.lean`, which consumes this declaration as their `only if`
half and carries the two attributes. -/
public theorem isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite
    (τ : SiteKind) (𝓕 : S.Modules)
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      ((baseAssociatedModule B S hS τ).obj 𝓕) := by
  obtain ⟨I, V, hV, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      S.zariskiRingedSite 𝓕).1 h
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
    (baseRingedSite B S hS τ) ((baseAssociatedModule B S hS τ).obj 𝓕)).2
      ⟨ULift.{u + 1} I, fun i => (opensToBig B S hS).obj (V i.down),
        coversTop_baseOpensToBig_ulift B S hS τ V hV, fun i => ?_⟩
  exact exists_isColimitCofan_baseAssociatedModuleOver B S hS τ (V i.down) 𝓕 (hfree i.down)

end BigFppfOver

end AlgebraicGeometry

end
