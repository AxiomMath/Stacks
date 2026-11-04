module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCoversTop
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.SmallModelSitePullbackQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-coherent clause of Modules on Sites 03DO for the projection `π_F`

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`, and let `π_F : (Sh(𝒳_étale), 𝒪_𝒳) ⟶ (Sh(F_étale), 𝒪_F)` be the morphism of ringed topoi of
Stacks 073M, `AlgebraicGeometry.Space.projectionRingedToposHom`.  **Stacks 03DO**, clause (6),
asserts for an arbitrary morphism of ringed topoi that the pullback of a quasi-coherent module is
quasi-coherent; this file is that clause for `π_F`, unconditionally.

## The route

The source proves 03DO by the method of Section 03DG: a property of modules preserved by pullback
along a morphism of ringed *sites* is preserved by pullback along any morphism of ringed topoi
presented by one.  `π_F` is presented by a morphism of sites, namely the functor
`u_F : F_étale ⥤ 𝒳` of Stacks 073M (`AlgebraicGeometry.Space.restrictionFunctor`,
`AlgebraicGeometry.Space.restrictionFunctor_isMorphismOfSites`), so the method applies to it
directly and no appeal to Stacks 03CR is needed.

Two things obstruct reading the method off
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom` at `π_F`, and both
are removed here.

**No final object on either site.** Section 03DG runs its reduction on sites that *have all
finite limits*, taking the family `{u(W_i)}` to cover the final object because `u` carries the
final object of the target site to the final object of the source site.  No final object is
available on either site here: the small étale site of an algebraic space `F` has one only when
`F` is representable (`AlgebraicGeometry.Space.hasTerminal_smallEtale_yoneda`), and
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBinaryProducts.lean` records that its binary
products are deliberately *not* obtained from a terminal object and pullbacks.  What is true is
that every object of `𝒳` is *covered* by objects in the image of `u_F`, which is
`AlgebraicGeometry.Space.restrictionFunctor_coversTop`, and that is the hypothesis
`isQuasicoherentOnSite_pullbackTopos_ofHom` asks for;
`AlgebraicGeometry.Space.coversTop_restrictionFunctor_obj` below is the same statement for an
arbitrary covering family, which is Section 03DG's condition (3) with no final object anywhere.

**The universes.** `isQuasicoherentOnSite_pullbackTopos_ofHom` is stated for a morphism of ringed
sites in the sense of `AlgebraicGeometry.RingedSite.Hom`, whose two endpoints are an
`AlgebraicGeometry.RingedSite.{u, u, u}` — objects, morphisms and sections of the structure sheaf
in one universe.  The small étale site of an algebraic space is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` and the inherited étale site of `𝒳` an
`AlgebraicGeometry.RingedSite.{v, w, u}`, so `π_F` is not one; it is an
`AlgebraicGeometry.RingedSite.HomGeneral`, which is what
`AlgebraicGeometry.Space.projectionRingedSiteHomGeneral` records.  The passage from one to the
other is
`Stacks.SheafOfModules.SmallModelSite.isQuasicoherentOnSite_pullbackToposGeneral_of_coversTop`,
the quasi-coherent clause of 03DO at independent site universes, proved on the equi-universe
models of the two sites and read back across them.

## Main definitions

* `AlgebraicGeometry.Space.projectionRingedSiteHomGeneral`: **`π_F` as a morphism of ringed sites
  in the sense of Stacks 03AD part (2)**, at independent object and morphism universes.  Its
  structure map is the identification `𝒪_F = u_{F,*} 𝒪_𝒳` of Stacks 073M,
  `AlgebraicGeometry.Space.inverseImage_structureSheaf_eq`.

## Main results

* `AlgebraicGeometry.Space.coversTop_restrictionFunctor_obj`: **the covering half of Section
  03DG's condition (3) for `π_F`**, with no final object on either site. If `{W_i}` covers the
  top of the small étale site of `F`, then `{u_F(W_i)}` covers the top of the inherited étale
  site of `𝒳`.
* `AlgebraicGeometry.Space.projectionRingedToposHom_eq_homGeneral`: the morphism of ringed topoi
  of Stacks 073M *is* the one induced by that morphism of ringed sites, by `rfl`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionPullbackToposGeneral`: the
  quasi-coherent clause of Stacks 03DO for the pullback along `π_F` taken over its site
  presentation, `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionPullbackModules`: **the quasi-coherent
  clause of Modules on Sites 03DO for `π_F`**, for
  `AlgebraicGeometry.RingedToposHom.pullbackModules` and with no hypothesis beyond
  quasi-coherence of the module.

## Implementation notes

**The two pullbacks.** The two constructions of `f^*` on sheaves of modules — Stacks 03D6 part
(2) over the four-field morphism of ringed topoi, which is
`AlgebraicGeometry.RingedToposHom.pullbackModules`, and the same over the site presentation,
which is `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral` — are identified by
uniqueness of left adjoints from
`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposIsoGeneral`, which compares the two
pushforwards.  That comparison is available because the morphism of ringed topoi of Stacks 073M
is, on the nose, the one the morphism of ringed sites induces: the three data of the geometric
morphism are the canonical direct image, the canonical sheaf pullback and the canonical
adjunction on both sides, left exactness of the pullback is a `Prop`, and the two structure maps
are the same term.  That is `projectionRingedToposHom_eq_homGeneral`.

**Universes.** The module universe is the universe `u` of the sections of the two structure
sheaves, as it is for every statement about `AlgebraicGeometry.RingedToposHom.pullbackModules`
of `π_F`; `𝒳` keeps its own two universes `v` and `w`.  It *is* an instance of the module
universe of `AlgebraicGeometry.Space.ProjectionPullbackPreservesQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasicoherentRestrictionDescentInputs.lean`, which is
`max u m`: `m := u` gives `u`.  The passage from the conclusion below to that Prop is
`AlgebraicGeometry.Space.projectionPullbackPreservesQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/Stacks/ProjectionModulePullbackQuasicoherent.lean`, which
identifies `AlgebraicGeometry.RingedToposHom.pullbackModules` of `π_F` with the chosen left
adjoint `AlgebraicGeometry.Space.projectionModulePullback` of restriction by uniqueness of left
adjoints.  A left adjoint of restriction exists without a module universe dominating
`u + 1`.
`AlgebraicGeometry.Space.isRightAdjoint_moduleRestriction'` is stated at `max u m`, hence at `u`,
through `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall`, which asks only essential
smallness of the source site and local smallness of the target in the module universe — the same
`EssentiallySmall.{u}`/`LocallySmall.{u}` instances the proof below installs.  What is pinned
above `u + 1` is neither the adjoint nor that Prop but `hunit`
(`AlgebraicGeometry.Space.isIso_unit_moduleRestriction`), which needs the direct image of sheaves
of modules, and so the two conditional 0GQD statements that go through it.

**The instances are restated at the projections of the ringed site.** Essential smallness of
`𝒳`, local smallness, sheafification of abelian presheaves and local bijectivity are all
available for the inherited étale site, but at the spelling
`AlgebraicGeometry.BigFppfOver.associatedTopology`; instance search does not unfold the
projections of `AlgebraicGeometry.FibredSite.ringedSite`, which is a `def`, so each is
reintroduced as a local instance at the projected spelling.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hF : IsAlgebraicSpace B S hS F)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)

/-! ### The covering half of Section 03DG's condition (3) for `π_F` -/

include hp hF in
/-- The images of a family covering the top cover the top, for the functor `u_F` of
Stacks 073M. If `{W_i}` is a family of étale charts of the algebraic space `F` covering the top
of its small étale site, then `{u_F(W_i)}` covers the top of the inherited étale site of a
category fibred in groupoids `𝒳` representable by `F`.

This is the covering half of Section 03DG's condition (3) for the projection `π_F`, and neither
site has a final object. The two inputs are the continuity of `u_F`
(`AlgebraicGeometry.Space.restrictionFunctor_isContinuous`, Stacks 073M) and the fact that the
family of *all* images of `u_F` covers the top
(`AlgebraicGeometry.Space.restrictionFunctor_coversTop`, which is the étale atlas of `F` read on
the site); transitivity of `CategoryTheory.GrothendieckTopology.CoversTop` along a continuous
functor, `Stacks.CategoryTheory.coversTop_map_of_coversTop_obj`, assembles them. -/
theorem coversTop_restrictionFunctor_obj {I : Type*} {W : I → SmallEtale B S hS F}
    (hW : (SmallEtale.topology B S hS F).CoversTop W) :
    (BigFppfOver.associatedTopology B S hS p .etale).CoversTop fun i =>
      (restrictionFunctor B S hS F p e).obj (W i) :=
  let := restrictionFunctor_isContinuous B S hS F p hp e
  Stacks.CategoryTheory.coversTop_map_of_coversTop_obj (restrictionFunctor B S hS F p e)
    (restrictionFunctor_coversTop B S hS F p hF hp e) hW

/-! ### `π_F` as a morphism of ringed sites -/

/-- The size and sheafification instances on the two sites, which hold on the nose for `π_F`,
may be assumed when proving a `Prop`. -/
private theorem instances_of_equivalenceOver
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    {P : Prop}
    (h : ∀ [EssentiallySmall.{u} 𝒳]
      [EssentiallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C]
      [LocallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C]
      [EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C]
      [HasWeakSheafify (FibredSite.ringedSite B S hS p hp .etale).J AddCommGrpCat.{u}]
      [(FibredSite.ringedSite B S hS p hp .etale).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [HasWeakSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
      [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
        AddCommGrpCat.{u}], P) : P := by
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  let : EssentiallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
    essentiallySmall_of_equivalenceOver B S hS F p e
  let : LocallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
    inferInstanceAs (LocallySmall.{u} 𝒳)
  let : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
  let : HasWeakSheafify (FibredSite.ringedSite B S hS p hp .etale).J AddCommGrpCat.{u} :=
    FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
  let : (FibredSite.ringedSite B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
  let : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J
      AddCommGrpCat.{u} :=
    FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
  let : (FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
  exact h

/-- **The projection `π_F` of Stacks 073M as a morphism of ringed sites**, in the sense of
Stacks 03AD part (2), at independent object and morphism universes.

The functor is `u_F : F_étale ⥤ 𝒳` of Stacks 073M, which is a morphism of sites by
`AlgebraicGeometry.Space.restrictionFunctor_isMorphismOfSites`, and the structure map in
direct-image form is the identification `𝒪_F = u_{F,*}𝒪_𝒳` of Stacks 073M,
`AlgebraicGeometry.Space.inverseImage_structureSheaf_eq`: restriction along `u_F` carries the
structure sheaf of `𝒳` to the structure sheaf of the small étale site of `F` on the nose, both
sending a chart to the ring of global functions on its underlying scheme.

This is an `AlgebraicGeometry.RingedSite.HomGeneral` and not an
`AlgebraicGeometry.RingedSite.Hom`: the latter asks the objects and the morphisms of both sites
to share a universe, which neither the small étale site of `F` nor the inherited étale site of
`𝒳` does. -/
def projectionRingedSiteHomGeneral :
    RingedSite.HomGeneral (FibredSite.ringedSite B S hS p hp .etale)
      (smallEtaleRingedSite B S hS F hF) where
  u := restrictionFunctor B S hS F p e
  isMorphismOfSites := restrictionFunctor_isMorphismOfSites B S hS F p hF hp e
  fsharp := eqToHom (inverseImage_structureSheaf_eq B S hS F p hp e hF).symm

/-- **The morphism of ringed topoi of Stacks 073M is the one induced by the morphism of ringed
sites above**, on the nose.

Both geometric morphisms are the canonical direct image, the canonical sheaf pullback and the
canonical adjunction between them; left exactness of the pullback is a `Prop`, so the two
witnesses of it do not distinguish the two; and the two structure maps are the same term, the
structure map of `AlgebraicGeometry.Space.projectionRingedSiteHomGeneral` followed by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`.

This is what makes the comparison of the two pullbacks of sheaves of modules available at `π_F`,
through `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposIsoGeneral`. -/
theorem projectionRingedToposHom_eq_homGeneral :
    projectionRingedToposHom B S hS F p hp hF e =
      (projectionRingedSiteHomGeneral B S hS F p hp hF e).toRingedToposHom := rfl

open Stacks.SheafOfModules.SmallModelSite in
include hp hF in
/-- **The quasi-coherent clause of Modules on Sites 03DO for `π_F`, over its site
presentation.** The pullback along `π_F` of a quasi-coherent `𝒪_F`-module is a quasi-coherent
`𝒪_𝒳`-module, the pullback being Stacks 03D6 part (2) taken over the presentation of `π_F` by
the morphism of sites `u_F`, `AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`.

This is
`Stacks.SheafOfModules.SmallModelSite.isQuasicoherentOnSite_pullbackToposGeneral_of_coversTop`
at `π_F`: its two hypotheses are that `u_F` is a morphism of sites, which is Stacks 073M, and
that the images of `u_F` cover the top of the inherited étale site, which is the étale atlas of
`F` read on the site, `AlgebraicGeometry.Space.restrictionFunctor_coversTop`. Neither site is
asked to have finite limits or a final object, and neither is asked to have its objects in the
universe of the sections of its structure sheaf. -/
theorem isQuasicoherentOnSite_projectionPullbackToposGeneral
    (G : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (hG : G.IsQuasicoherentOnSite) :
    letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
    letI : EssentiallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
      essentiallySmall_of_equivalenceOver B S hS F p e
    letI : LocallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
      letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
      inferInstanceAs (LocallySmall.{u} 𝒳)
    letI : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C :=
      inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
    letI : HasWeakSheafify (FibredSite.ringedSite B S hS p hp .etale).J AddCommGrpCat.{u} :=
      letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
      FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
    letI : (FibredSite.ringedSite B S hS p hp .etale).J.WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
    (((projectionRingedSiteHomGeneral B S hS F p hp hF e).toRingedToposSiteHom
      ).pullbackToposGeneral.obj G).IsQuasicoherentOnSite := by
  refine instances_of_equivalenceOver B S hS F p hp hF e ?_
  exact isQuasicoherentOnSite_pullbackToposGeneral_of_coversTop
    ((projectionRingedSiteHomGeneral B S hS F p hp hF e).toRingedToposSiteHom)
    (restrictionFunctor_isMorphismOfSites B S hS F p hF hp e)
    (restrictionFunctor_coversTop B S hS F p hF hp e) G hG


include hp hF in
/-- The pullback of a quasi-coherent module along the projection `π_F` of Stacks 073M is
quasi-coherent: the pullback along `π_F` of a quasi-coherent `𝒪_F`-module is a quasi-coherent
`𝒪_𝒳`-module.

Here `π_F^*` is `AlgebraicGeometry.RingedToposHom.pullbackModules` of
`AlgebraicGeometry.Space.projectionRingedToposHom`, which is Stacks 03D6 part (2) at the
morphism of ringed topoi of Stacks 073M, and quasi-coherence is Stacks 03DL (6) tested on a
covering of every object, `SheafOfModules.IsQuasicoherentOnSite`.

The proof is `AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionPullbackToposGeneral`,
which is the same assertion for the pullback taken over the site presentation of `π_F`, carried
across the identification of the two pullbacks: both are left adjoints, the two pushforwards
agree by `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposIsoGeneral` — applicable
because of `AlgebraicGeometry.Space.projectionRingedToposHom_eq_homGeneral` — and so uniqueness
of left adjoints identifies them. -/
theorem isQuasicoherentOnSite_projectionPullbackModules
    (G : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (hG : G.IsQuasicoherentOnSite) :
    letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
    letI : EssentiallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
      essentiallySmall_of_equivalenceOver B S hS F p e
    letI : LocallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
      letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
      inferInstanceAs (LocallySmall.{u} 𝒳)
    letI : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C :=
      inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
    letI : HasWeakSheafify (FibredSite.ringedSite B S hS p hp .etale).J AddCommGrpCat.{u} :=
      letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
      FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
    letI : (FibredSite.ringedSite B S hS p hp .etale).J.WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
    letI : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J
        AddCommGrpCat.{u} :=
      letI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
      FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
    letI : (FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
    (((projectionRingedToposHom B S hS F p hp hF e).toModulesHom.pullbackModules).obj
      G).IsQuasicoherentOnSite := by
  refine instances_of_equivalenceOver B S hS F p hp hF e ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Adjunction.leftAdjointUniq
      ((RingedToposHom.pullbackAdjPushforwardModules
        (projectionRingedToposHom B S hS F p hp hF e)).ofNatIsoRight
          (projectionRingedSiteHomGeneral B S hS F p hp hF e).pushforwardToposIsoGeneral)
      (((projectionRingedSiteHomGeneral B S hS F p hp hF e).toRingedToposSiteHom
        ).pullbackPushforwardAdjunctionToposGeneral)).app G).symm ?_
  exact isQuasicoherentOnSite_projectionPullbackToposGeneral B S hS F p hp hF e G hG

end AlgebraicGeometry.Space

end
