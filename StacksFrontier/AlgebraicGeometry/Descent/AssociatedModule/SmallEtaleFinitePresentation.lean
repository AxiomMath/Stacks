module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation across the small étale comparison

Let `S` be a scheme and let `𝓕 ↦ 𝓕^a` be the associated-module functor
`AlgebraicGeometry.SmallEtale.associatedModule` of Stacks 03DU (4) for the small étale site of
`S`, the pullback of modules along the morphism of ringed sites `(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`.
This file proves, for a quasi-coherent `𝒪_S`-module `𝓕`, that `𝓕` is of finite presentation
exactly when `𝓕^a` is, in the categorical sense of Modules on Sites, Definition 03DL (7).  That
is the clause 03DL (7) of Descent, Lemma 05VG for the small étale site, which Modules on Sites,
Lemma 03DM does not give: the comparison of Stacks 03DX (2) is an equivalence of the categories
of *quasi-coherent* modules and not an equivalence of ringed topoi, so the transport of
`Stacks.Sheaves.LocalTypeComparison` does not apply to it.

The argument is the one of
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`, which
is Stacks 03DV (2), with the finiteness of the index types carried along: quasi-coherent data
for `𝓕` is a Zariski covering of `S` together with a presentation of `𝓕` on each member, the
image of that covering under the inclusion of the small Zariski site covers the small étale site
(`AlgebraicGeometry.SmallEtale.coversTop_opensToSmallEtale_ulift`), and the associated-module
functor of the localization at a member carries a presentation there to one of the restriction of
`𝓕^a`.  Each step preserves the two index types on the nose, so a *finite* presentation goes to a
finite one; that is
`Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation_isFinite` together with the
`SheafOfModules.Presentation.IsFinite` instance for transport along an isomorphism.

## Main definitions

* `AlgebraicGeometry.SmallEtale.finitePresentationAssociatedModuleOver` is the presentation of
  the restriction of `𝓕^a` to the localization of `S_étale` at an open `V` of `S` obtained from a
  finite presentation of `𝓕|_V`; it is again finite.
* `AlgebraicGeometry.SmallEtale.finitePresentationDataAssociatedModule` is the resulting
  quasi-coherent datum for `𝓕^a`, on the image of the same covering.

## Main results

* `AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_of_isFinitePresentation`:
  the forward half — the associated module of a module of finite presentation is of finite
  presentation.  No quasi-coherence is needed.
* `AlgebraicGeometry.SmallEtale.isFinitePresentation_of_presentation_associatedModule`: the
  reflection step — a quasi-coherent `𝓕` whose `𝓕^a` has a finite *global* presentation is of
  finite presentation.
* `AlgebraicGeometry.SmallEtale.isFinitePresentation_of_isFinitePresentation_associatedModule`:
  the reverse half, by fpqc descent along the covering family that finite presentation of `𝓕^a`
  supplies.
* `AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff`: **Stacks 05VG for
  Modules on Sites, Definition 03DL (7) at `τ = étale` on the small site.**

## Implementation notes

Only `AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff` carries the
`stacks` attribute: Stacks 05VG asserts an *equivalence* of the two conditions, and a single
implication does not realize the clause.

The forward implication is the analogue, for 03DL (7), of Modules on Sites, Lemma 03DO, and it
holds because the associated-module functor is a left adjoint and takes the unit sheaf of rings
to the unit sheaf of rings.

The reverse implication does **not** go through Stacks 08HD, whose converse needs the
zero-detection assertion of Stacks 08H8 for an arbitrary `𝒪_S`-module — unavailable here, and
provably not reducible to the quasi-coherent case; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteType.lean`.  It goes
through fpqc descent on `S` instead.  Finite presentation of `𝓕^a` is a covering family of the
final object of `S_étale` together with a finite presentation over each member; the structure
morphisms of such a family are an fpqc covering of `S`, with no refinement step
(`AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover`), and
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictObjIso` identifies the restriction over
a member with the associated module of the pullback along its structure morphism.  So the
reflection step applies to each pullback, and Stacks 05B0 descends the conclusion.

The reflection step itself is where full faithfulness of `𝓕 ↦ 𝓕^a` on the quasi-coherent
modules (Stacks 0GN7) is used, and it is why quasi-coherence appears in the reverse half but
not in the forward one.

The quasi-coherent datum produced below indexes its covering family in `Type (u + 1)`, the
universe of the objects of the small étale site, while the datum consumed indexes in `Type u`,
the universe of the opens of `S`.  That is the universe convention of
`SheafOfModules.QuasicoherentData` — the index type lives in the object universe of the site —
and it is why the index type is raised by `ULift`, exactly as in
`AlgebraicGeometry.SmallEtale.quasicoherentDataAssociatedModule`.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The transport of a finite presentation to a member of the covering, on the small étale
site.**  A finite presentation of the restriction of an `𝒪_S`-module `𝓕` to an open `V` of `S`
gives a finite presentation of the restriction of `𝓕^a` to the localization of `S_étale` at `V`.

This is `AlgebraicGeometry.SmallEtale.presentationAssembledOver`-style transport along the
associated-module functor of the localized site, which preserves finite colimits and carries the
unit object to the unit object, followed by
`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`. -/
noncomputable def finitePresentationAssociatedModuleOver (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) [P.IsFinite] :
    (((associatedModule B S hS).obj 𝓕).over
      ((opensToSmallEtale B S hS).obj V)).Presentation :=
  (Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation P
      (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
        (sliceStructureMap B S hS V))).symm).ofIsIso
    (associatedModuleOverObjIso B S hS V 𝓕).hom

/-- The presentation of `AlgebraicGeometry.SmallEtale.finitePresentationAssociatedModuleOver` is
finite: both transports preserve the index types of generators and relations. -/
instance isFinite_finitePresentationAssociatedModuleOver (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) [P.IsFinite] :
    (finitePresentationAssociatedModuleOver B S hS V P).IsFinite :=
  let := Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation_isFinite P
    (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))).symm
  inferInstanceAs ((Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation P
      (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
        (sliceStructureMap B S hS V))).symm).ofIsIso
    (associatedModuleOverObjIso B S hS V 𝓕).hom).IsFinite

/-- **The covering argument for finite presentation, on the small étale site.**  Quasi-coherent
data for an `𝒪_S`-module `𝓕` whose presentations are finite give quasi-coherent data for `𝓕^a`
on `S_étale`, on the image of the same covering, whose presentations are again finite. -/
noncomputable def finitePresentationDataAssociatedModule {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕)
    (hq : q.IsFinitePresentation) :
    SheafOfModules.QuasicoherentData.{u + 1} ((associatedModule B S hS).obj 𝓕) where
  I := ULift.{u + 1} q.I
  X i := (opensToSmallEtale B S hS).obj (q.X i.down)
  coversTop := coversTop_opensToSmallEtale_ulift B S hS q.X q.coversTop
  presentation i :=
    let := hq.isFinite_presentation i.down
    finitePresentationAssociatedModuleOver B S hS (q.X i.down) (q.presentation i.down)

/-- The quasi-coherent datum of
`AlgebraicGeometry.SmallEtale.finitePresentationDataAssociatedModule` is a finite presentation. -/
instance isFinitePresentation_finitePresentationDataAssociatedModule {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕)
    (hq : q.IsFinitePresentation) :
    (finitePresentationDataAssociatedModule B S hS q hq).IsFinitePresentation where
  isFinite_presentation i :=
    let := hq.isFinite_presentation i.down
    isFinite_finitePresentationAssociatedModuleOver B S hS (q.X i.down) (q.presentation i.down)

/-- **The forward half of Stacks 05VG for Modules on Sites, Definition 03DL (7) at `τ = étale`
on the small site.**  The associated module `𝓕^a` of an `𝒪_S`-module `𝓕` of finite presentation
is an `𝒪`-module of finite presentation on the small étale site `S_étale`.

The reverse implication, which is what makes 05VG an equivalence for this clause, is not proved
here. -/
theorem isFinitePresentation_associatedModule_of_isFinitePresentation (𝓕 : S.Modules)
    (h : SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓕) :
    ((associatedModule B S hS).obj 𝓕).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := h.exists_quasicoherentData
  exact ⟨finitePresentationDataAssociatedModule B S hS q hq,
    isFinitePresentation_finitePresentationDataAssociatedModule B S hS q hq⟩

/-! ### Reflection of a finite presentation -/

/-- A free `𝒪_S`-module is quasi-coherent: it is a coproduct of copies of `𝒪_S`. -/
theorem isQuasicoherent_free (I : Type u) :
    (SheafOfModules.free (R := S.ringCatSheaf) I).IsQuasicoherent := by
  show (∐ fun _ : I ↦ SheafOfModules.unit S.ringCatSheaf).IsQuasicoherent
  exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma _

/-- **A finite global presentation of `𝓕^a` is reflected to one of `𝓕`.**  Let `𝓕` be a
quasi-coherent `𝒪_S`-module whose associated module on `S_étale` is the cokernel of a morphism
between free modules on finite index types.  Then `𝓕` is of finite presentation.

The morphism of free modules on `S_étale` comes from a morphism `β` of free `𝒪_S`-modules on the
same two index types, by fullness of `𝓕 ↦ 𝓕^a` on free modules
(`AlgebraicGeometry.SmallEtale.exists_associatedModule_map_free`).  The associated module of
`coker β` is then the given cokernel, by
`SheafOfModules.nonempty_iso_pullbackObj_cokernel_free`, hence is isomorphic to `𝓕^a`; both
`coker β` and `𝓕` are quasi-coherent, so full faithfulness of `𝓕 ↦ 𝓕^a` on the quasi-coherent
modules (Stacks 0GN7) turns that into an isomorphism `coker β ≅ 𝓕` downstairs.  The tautological
presentation of `coker β` has the two given finite index types, and transports along it. -/
theorem isFinitePresentation_of_presentation_associatedModule (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕)
    (P : ((associatedModule B S hS).obj 𝓕).Presentation) (hP : P.IsFinite) :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓕 := by
  let := hP
  let := h𝓕
  let : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : (SheafOfModules.free (R := S.ringCatSheaf) P.relations.I).IsQuasicoherent :=
    isQuasicoherent_free S P.relations.I
  let : (SheafOfModules.free (R := S.ringCatSheaf) P.generators.I).IsQuasicoherent :=
    isQuasicoherent_free S P.generators.I
  set α : SheafOfModules.free (R := structureSheaf B S hS) P.relations.I ⟶
      SheafOfModules.free P.generators.I :=
    (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π with hα
  have hπ : α ≫ P.generators.π = 0 := by simp [hα]
  have hc : IsColimit (CokernelCofork.ofπ P.generators.π hπ) := P.isColimit
  obtain ⟨β, hβ⟩ := exists_associatedModule_map_free B S hS P.generators.I P.relations.I
    ((SheafOfModules.pullbackObjFreeIso (structureMap B S hS) P.relations.I).hom ≫ α ≫
      (SheafOfModules.pullbackObjFreeIso (structureMap B S hS) P.generators.I).inv)
  have hQ : (cokernel β).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel (X := S) β
  obtain ⟨e⟩ := SheafOfModules.nonempty_iso_pullbackObj_cokernel_free
    (structureMap B S hS) α β hβ hπ hc
  let e' : (⟨cokernel β, hQ⟩ :
        (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) ≅ ⟨𝓕, h𝓕⟩ :=
    (fullyFaithfulAssociatedModuleQcoh' B S hS).preimageIso e
  let eM : cokernel β ≅ 𝓕 := (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso e'
  have : IsIso eM.hom := ⟨eM.inv, eM.hom_inv_id, eM.inv_hom_id⟩
  let Pc : (cokernel β).Presentation :=
    SheafOfModules.presentationOfIsCokernelFree β (cokernel.π β) (cokernel.condition β)
      (cokernelIsCokernel β)
  have : Pc.IsFinite :=
    ⟨⟨inferInstanceAs (Finite P.generators.I)⟩, ⟨inferInstanceAs (Finite P.relations.I)⟩⟩
  have : (Pc.ofIsIso eM.hom).IsFinite :=
    ⟨⟨inferInstanceAs (Finite P.generators.I)⟩, ⟨inferInstanceAs (Finite P.relations.I)⟩⟩
  exact Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation
    (Pc.ofIsIso eM.hom)

/-! ### The reverse half, by fpqc descent -/

/-- A covering family of the final object of `S_étale`, read as an fpqc covering of the scheme
`S`.  This is `AlgebraicGeometry.SmallEtale.coveringHypercover` together with
`AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover`. -/
def coveringFpqcCover {I : Type w} (X : I → SmallEtale B S hS)
    (hX : (topology B S hS).CoversTop X) : S.Cover.{w} Scheme.fpqcPrecoverage where
  toPreZeroHypercover := coveringHypercover B S hS X
  mem₀ := presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS X hX

/-- **The reverse half of Stacks 05VG for Modules on Sites, Definition 03DL (7) at `τ = étale`
on the small site.**  A quasi-coherent `𝒪_S`-module whose associated module on `S_étale` is of
finite presentation is itself of finite presentation.

Finite presentation of `𝓕^a` supplies a covering family `U i` of the final object of `S_étale`
and a finite presentation of `(𝓕^a)|_{S_étale/U i}` for each `i`.  Reindexing along the
localization equivalence of Stacks 04M0 reads that as a finite presentation of
`(𝓕^a)|_{(Y i)_étale}` for `Y i` the scheme of `U i`, which
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictObjIso` identifies with the associated
module of the pullback `f i ^* 𝓕` along the structure morphism.  The reflection step
`AlgebraicGeometry.SmallEtale.isFinitePresentation_of_presentation_associatedModule` makes each
`f i ^* 𝓕` of finite presentation, and the structure morphisms form an fpqc covering of `S`
(`AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover`), so Stacks
05B0 descends finite presentation to `𝓕`. -/
theorem isFinitePresentation_of_isFinitePresentation_associatedModule (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕)
    (h : ((associatedModule B S hS).obj 𝓕).IsFinitePresentation) :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓕 := by
  let := h𝓕
  obtain ⟨q, hq⟩ := h.exists_quasicoherentData
  refine AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover 𝓕
    (coveringFpqcCover B S hS q.X q.coversTop) fun i ↦ ?_
  let := hq.isFinite_presentation i
  let : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify (topology B (objScheme B S hS (q.X i))
      (contains_objScheme B S hS (q.X i))) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : (objRestrictFunctor B S hS (q.X i)).IsEquivalence :=
    inferInstanceAs ((objRestrictEquivalence B S hS (q.X i)).functor.IsEquivalence)
  have hf : (coveringFpqcCover B S hS q.X q.coversTop).f i = objHom B S hS (q.X i) := rfl
  rw [hf]
  have hqc : ((Scheme.Modules.pullback (objHom B S hS (q.X i))).obj 𝓕).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (objHom B S hS (q.X i)) 𝓕 h𝓕
  let e2 := (associatedModuleObjRestrictObjIso B S hS (q.X i) 𝓕).symm
  have := Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation_isFinite (q.presentation i)
    (objRestrictFunctor B S hS (q.X i)) (Iso.refl _)
  exact isFinitePresentation_of_presentation_associatedModule B (objScheme B S hS (q.X i))
    (contains_objScheme B S hS (q.X i))
    ((Scheme.Modules.pullback (objHom B S hS (q.X i))).obj 𝓕) hqc
    ((Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation (q.presentation i)
      (objRestrictFunctor B S hS (q.X i)) (Iso.refl _)).ofIsIso e2.hom) inferInstance

/-- **Stacks 05VG for Modules on Sites, Definition 03DL (7) at `τ = étale` on the small
site.**  A quasi-coherent `𝒪_S`-module is of finite presentation if and only if its associated
module on the small étale site of `S` is of finite presentation.

The forward implication is
`AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_of_isFinitePresentation`
and needs no quasi-coherence; the reverse one is
`AlgebraicGeometry.SmallEtale.isFinitePresentation_of_isFinitePresentation_associatedModule`,
which goes through the reflection step and fpqc descent on `S`. -/
@[stacks 05VG "finite presentation; the local clause 03DL (7) of the small-site comparison at \
τ = étale, for a quasi-coherent module on a scheme, with the comparison read as the \
associated-module functor of Stacks 03DU (4) rather than as a morphism of ringed topoi"]
theorem isFinitePresentation_associatedModule_iff (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓕 ↔
      ((associatedModule B S hS).obj 𝓕).IsFinitePresentation :=
  ⟨isFinitePresentation_associatedModule_of_isFinitePresentation B S hS 𝓕,
    isFinitePresentation_of_isFinitePresentation_associatedModule B S hS 𝓕 h𝓕⟩

end SmallEtale

end AlgebraicGeometry

end
