module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.SmallZariskiModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallAffineDenseSubsite

/-!
# The associated-module functor of the small Zariski site of a scheme

Stacks Definition 03DU (4) is the sheaf of `𝒪`-modules `𝓕 ↦ 𝓕^a` on the **small** site `S_τ`,
for `τ ∈ {Zariski, étale}`.  The étale half is
`AlgebraicGeometry.SmallEtale.associatedModule`; **this module supplies the Zariski half**, as
the pullback along the morphism of ringed sites, which is the description Remark 03FH (1) gives
of the construction.

The construction is the one the small étale site uses, over the inclusion of the small Zariski
site of `S` into `S_τ`.  At `τ = Zariski` that inclusion is an *equivalence* — it is the inverse
of `AlgebraicGeometry.smallZariskiSiteEquiv`, the open-image comparison of Stacks 020X — so every
property the construction asks of it is a property of an equivalence of sites and nothing
geometric is used below.  Concretely: it is continuous because
`AlgebraicGeometry.smallZariskiSiteEquiv_inverse_isDenseSubsite` says so; it preserves finite
limits and is final because an equivalence does; and its structure-sheaf comparison is the
isomorphism `AlgebraicGeometry.smallZariskiStructureSheaf_iso`, read as a morphism into the
pushforward.

That last point is what makes the functor below the *right* one.  The coefficient sheaf of
Definition 03DU (2) at `τ = Zariski` is `T/S ↦ Γ(T, 𝒪_T)`, which is
`AlgebraicGeometry.SmallZariski.structureSheaf`; it is *isomorphic* to `S.ringCatSheaf` and not
equal to it, so reading `S_Zar` as `S.Opens` with `S.ringCatSheaf` and offering `𝟭 S.Modules`
would state a different theorem.  The pullback along
the comparison is the construction the source names, and it is what is built here.

## Main definitions

* `AlgebraicGeometry.SmallZariski.opensToSmallZariski`: the small Zariski site of `S` read as the
  opens of the space of `S`, i.e. the inverse of the open-image equivalence of Stacks 020X.
* `AlgebraicGeometry.SmallZariski.structureMap`: the comparison of structure sheaves, the ring
  half of the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)`.
* `AlgebraicGeometry.SmallZariski.associatedModule`: **Stacks 03DU (4) at `τ = Zariski`**, the
  associated-module functor `𝓕 ↦ 𝓕^a`,
  `S.Modules ⥤ SheafOfModules (SmallZariski.structureSheaf B S hS)`, as the pullback along the
  morphism of ringed sites.  The same clause in the shape of the sections formula
  `T ↦ Γ(T, f^*𝓕)` is `AlgebraicGeometry.SmallZariski.associatedModuleOfSections`, and the two
  descriptions are identified by
  `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`.
* `AlgebraicGeometry.SmallZariski.restrictModule`: its right adjoint, restriction along that
  inclusion.
* `AlgebraicGeometry.SmallZariski.associatedModuleAdjunction`: the adjunction between them.

## Main results

* `AlgebraicGeometry.SmallZariski.coverPreserving_opensToSmallZariski`: the inclusion is cover
  preserving.
* `AlgebraicGeometry.SmallZariski.isThin_smallZariski`: there is at most one morphism between two
  objects of the small Zariski site, that site being equivalent to a lattice of opens.
* `AlgebraicGeometry.SmallZariski.hasWeakSheafify_smallZariski` and
  `AlgebraicGeometry.SmallZariski.wEqualsLocallyBijective_smallZariski`: abelian presheaves on
  the small Zariski site sheafify and the weak equivalences are the locally bijective maps.
  These are what make the pullback of sheaves of modules exist.
* `AlgebraicGeometry.SmallZariski.preservesColimitsOfSize_associatedModule`: the
  associated-module functor preserves all colimits.
* `AlgebraicGeometry.SmallZariski.isIso_pullbackObjUnitToUnit`: it takes the unit object to the
  unit object, the inclusion being final.

## Implementation notes

`AlgebraicGeometry.SmallZariski.associatedModule` is the functor of clause (4), built as the
pullback along the morphism of ringed sites, as at `τ = étale`.  Clause (4) also names `𝓕^a` by
the sections formula `(f : T → S) ↦ Γ(T, f^*𝓕)`, and that shape of it is the sections-defined
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections` of
`StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAssociatedModule`.  The two agree:
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections` of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiSectionsIso` identifies them,
which is Remark 03FH (1).  The identification does not go through part (2) of
Stacks 070S, the morphism of ringed sites being an equivalence here; the big-site half of that
comparison is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`.

`AlgebraicGeometry.smallZariskiModuleEquiv` already identifies
`SheafOfModules (SmallZariski.structureSheaf B S hS)` with `S.Modules`, so the functor below is
an equivalence; that is a *theorem about* it and not its definition.  Defining `𝓕^a` as the
inverse of that equivalence would make Remark 03FH's "the construction `𝓕 ↦ 𝓕^a` is the pullback
under `id_{τ,Zar}`" true by fiat rather than by construction; so the pullback is taken, exactly
as at `τ = étale`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The small Zariski site read as the opens of the space -/

/-- The opens of the space of `S` inside the small Zariski site of `S`: the inverse of the
open-image equivalence of Stacks 020X.  This is the inclusion of the small Zariski site into
`S_τ` at `τ = Zariski`, where it happens to be an equivalence. -/
public noncomputable abbrev opensToSmallZariski : S.Opens ⥤ SmallZariski B S hS :=
  (smallZariskiSiteEquiv B S hS).inverse

/-- **The inclusion of the small Zariski site of `S` into `S_Zar` is cover preserving.**  It is
continuous, being the inverse of an equivalence of sites which is a dense subsite in both
directions, and for a continuous functor the two notions agree. -/
public theorem coverPreserving_opensToSmallZariski :
    CoverPreserving (Opens.grothendieckTopology ↥S) (topology B S hS)
      (opensToSmallZariski B S hS) :=
  CategoryTheory.Functor.isContinuous_iff_coverPreserving.1 inferInstance

/-- The inclusion preserves `1`-hypercovers: it is cover preserving and preserves fibre
products.  This is what makes `CategoryTheory.Over.post` of it continuous into the localization
at an open of `S`, through Mathlib's `Over.post` instance for `PreservesOneHypercovers`. -/
public instance preservesOneHypercovers_opensToSmallZariski :
    (opensToSmallZariski B S hS).PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opensToSmallZariski B S hS)

/-- **There is at most one morphism between two objects of the small Zariski site of `S`.**  The
site is equivalent to the lattice of opens of the space of `S`, in which a morphism is an
inequality. -/
public instance isThin_smallZariski : Quiver.IsThin (SmallZariski B S hS) :=
  fun _ _ => ⟨fun _ _ => (smallZariskiSiteEquiv B S hS).functor.map_injective
    (Subsingleton.elim _ _)⟩

/-- The small Zariski site of `S` has binary products, being equivalent to the lattice of opens
of the space of `S`, where they are intersections. -/
public noncomputable instance hasBinaryProducts_smallZariski :
    HasBinaryProducts (SmallZariski B S hS) :=
  Adjunction.hasLimitsOfShape_of_equivalence (smallZariskiSiteEquiv B S hS).functor

/-! ### Sheafification on the small Zariski site -/

/-- Abelian presheaves on the small Zariski site of `S` have a sheafification, the site being
essentially small. -/
public instance hasWeakSheafify_smallZariski :
    HasWeakSheafify (topology B S hS) AddCommGrpCat.{u} := by
  have : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  infer_instance

/-- Weak equivalences of abelian presheaves on the small Zariski site of `S` are the locally
bijective maps. -/
public instance wEqualsLocallyBijective_smallZariski :
    (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-! ### The morphism of ringed sites and the associated-module functor -/

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S`
into `S_Zar`: over an open `U` it is the identification of the sections of `𝒪_S` over `U` with
the global functions of the open subscheme `U`, which is
`AlgebraicGeometry.smallZariskiStructureSheaf_iso` read as a morphism into the pushforward.
Together with the continuity of the inclusion this is the morphism of ringed sites
`(S_Zar, 𝒪) → (S_Zar, 𝒪_S)`. -/
public noncomputable def structureMap :
    S.ringCatSheaf ⟶ ((opensToSmallZariski B S hS).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS)).obj (structureSheaf B S hS) :=
  ObjectProperty.homMk (smallZariskiStructureSheaf_iso B S hS).inv.hom

/-- The pushforward of presheaves of modules along the structure-sheaf comparison of the small
Zariski site has a left adjoint. -/
public instance presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the morphism of ringed sites of the small
Zariski site has a left adjoint. -/
public instance sheafPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (structureMap B S hS)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS)).isRightAdjoint

/-- **Stacks 03DU (4), at `τ = Zariski`.**  The associated-module functor of the small Zariski
site of `S`: the pullback of sheaves of modules along the morphism of ringed sites
`(S_Zar, 𝒪) → (S_Zar, 𝒪_S)`.

This is the functor of clause (4), as the pullback of Remark 03FH (1), like its étale
counterpart `AlgebraicGeometry.SmallEtale.associatedModule`.  The sections formula
`T ↦ Γ(T, f^*𝓕)` by which the source also names it is
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections`, and the two descriptions are
identified by `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`, which is
Remark 03FH (1) for the morphism `id_{small, Zar, Zar}`. -/
@[stacks 03DU "associated module on the small site, clause (4) at τ = Zariski, functor only"]
public noncomputable def associatedModule :
    S.Modules ⥤ SheafOfModules.{u} (structureSheaf B S hS) :=
  SheafOfModules.pullback.{u} (structureMap B S hS)

/-- Restriction of a sheaf of modules on the small Zariski site of `S` along the inclusion of
the opens of the space of `S`, the right adjoint of the associated-module functor. -/
public noncomputable def restrictModule :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤ S.Modules :=
  SheafOfModules.pushforward.{u} (structureMap B S hS)

/-- The associated-module functor of the small Zariski site is left adjoint to restriction. -/
public noncomputable def associatedModuleAdjunction :
    associatedModule B S hS ⊣ restrictModule B S hS :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)

/-- The associated-module functor of the small Zariski site is a left adjoint. -/
public instance isLeftAdjoint_associatedModule :
    (associatedModule B S hS).IsLeftAdjoint :=
  (associatedModuleAdjunction B S hS).isLeftAdjoint

/-- **Stacks 03DC, applied.**  The associated-module functor of the small Zariski site preserves
all colimits, being a left adjoint. -/
public noncomputable instance preservesColimitsOfSize_associatedModule.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (associatedModule B S hS) :=
  (associatedModuleAdjunction B S hS).leftAdjoint_preservesColimits

/-- The pullback of the unit object along the morphism of ringed sites of the small Zariski site
is an isomorphism, the inclusion being final. -/
public instance isIso_pullbackObjUnitToUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS)) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

end AlgebraicGeometry.SmallZariski

end
