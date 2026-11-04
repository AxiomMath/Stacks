module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherentOfHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceOfUniv
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism

/-!
# Pullback preserves quasi-coherence at independent site universes, through the model

`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom` is the
quasi-coherent clause of Stacks 03DO for a morphism of ringed sites whose images cover the top
of the source site — no finite limits, no final object. It is pinned, as the whole localization
theory of Stacks 03CF and 04J0 is, to an `AlgebraicGeometry.RingedSite.{u, u, u}`: the objects
of both sites, their morphisms and the sections of both structure sheaves in one universe. Every
site of schemes in this development has its objects one universe above its morphisms, so that
statement applies to none of them.

This file carries it over to a morphism of ringed topoi presented by a morphism of sites between
two sites that are merely **essentially small in the universe of the sections of their structure
sheaves**, with their objects and their morphisms otherwise free. The route is the one Stacks
07TI is proved by on the total Zariski site of a simplicial scheme
(`StacksFrontier/AlgebraicGeometry/Simplicial/ZariskiPullbackQuasicoherent.lean`): transport the
morphism to the equi-universe models of the two sites, where it *is* an
`AlgebraicGeometry.RingedSite.Hom`, apply the clause there, and carry the conclusion back. The
four steps that route needs are proved here once and for all, in place of the bespoke copies the
Zariski case has.

## The model, and what the transport costs

The model is `Stacks.SheafOfModules.SmallModelSite.ringedSite`: the small model of the underlying
category in the universe `u` of the sections, with the induced topology and the direct image of
the structure sheaf. It is a genuinely small site, so *every* typeclass hypothesis the clause of
03DO has — sheafification of abelian presheaves, local bijectivity, essential smallness of the
slices, and the same on every slice — is an unconditional instance on it, and the statement below
carries none of them for the models.

The one step that is not formal is the passage of quasi-coherence between a site and its model,
in both directions. `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff`
does it when the two sites share their universe of objects, which a site and its model do only
when the objects of the site already lie in `Type u`; that is why the Zariski case goes through
and a site of schemes does not. Worse, that statement is available only at the *balanced* module
universe `max u u' v v' w n`, which contains both sites: for the small étale site of an algebraic
space it is `u + 1`, while the modules of that development have their sections in `Type u`, so
the transport cannot even be stated at the module universe the consumer needs.

`Stacks.SheafOfModules.MixedObjectUniverse.isQuasicoherentOnSite_transport_iff` below removes
that restriction. Quasi-coherence is invariant under raising the universe of the sections by an
arbitrary amount, in both directions
(`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'` and
`SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'`), and raising the sections
commutes with restriction along the model equivalence
(`Stacks.SheafOfModules.MixedObjectUniverse.pushforwardUliftIso`); so the module is raised to the
balanced universe, transported there, and lowered again on the other side.

## Main definitions

* `Stacks.SheafOfModules.SmallModelSite.modelFunctor` and `.modelSharp`: the functor
  `e_D ⋙ u ⋙ e_C⁻¹` between the two models and its structure map.
* `Stacks.SheafOfModules.SmallModelSite.modelSiteHom`: **the morphism of ringed sites between the
  equi-universe models** attached to a morphism of ringed topoi presented by a morphism of sites.
* `Stacks.SheafOfModules.SmallModelSite.modelPullbackIso` and `.modelPullbackObjIso`: **the
  pullback along the morphism of the models is the pullback along the given morphism conjugated
  by the two model equivalences of sheaves of modules.**

## Main results

* `Stacks.SheafOfModules.MixedObjectUniverse.isQuasicoherentOnSite_transport_iff`: clause (6) of
  Stacks 03DL is invariant under an equivalence of ringed sites, at a module universe unrelated
  to the four universes of the two sites.
* `Stacks.SheafOfModules.SmallModelSite.modelSiteHom_pushforwardTopos_eq`: the pushforward along
  the morphism of the models *is* the conjugate of the pushforward along the given morphism.
* `Stacks.SheafOfModules.SmallModelSite.coversTop_modelSiteHom_u_obj`: the covering hypothesis
  transported to the models.
* `Stacks.SheafOfModules.SmallModelSite.isQuasicoherentOnSite_pullbackToposGeneral_of_coversTop`:
  **the quasi-coherent clause of Stacks 03DO at independent site universes.**

## Implementation notes

The equality of pushforwards holds by `rfl`, and `modelSharp` is chosen precisely so that it
does: the pushforward of sheaves of modules along a composite of continuous functors is the
pushforward along the composite on the nose (Mathlib's `SheafOfModules.pushforwardComp` is
`Iso.refl`), each half of the model equivalence of sheaves of modules is itself a pushforward,
and `modelSharp` is the structure map that the composite produces. The pullback statements are
then uniqueness of left adjoints, with the equality of right adjoints inserted as an
`CategoryTheory.eqToIso`, exactly as in the Zariski case.

That the functor between the models is a morphism of sites is Stacks 03CB applied to three
factors: either half of an equivalence of sites is one by
`IsMorphismOfSites.ofIsDenseSubsite`, whose limit hypothesis holds because the indexing comma
categories are essentially small at `u`, and the middle factor is the hypothesis `hf`.

No `@[stacks]` attribute is carried. The library's
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos` holds the 03DO and 03DG
attributes, and the statement below has the extra hypothesis that the images of the functor cover
the top of the source site, which Stacks 03DO does not have; it is strictly more general in the
universes and in the finite-limit hypotheses and strictly less general in that one, so neither
supersedes the other. This follows the policy recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocalizedPullbackQuasicoherentOfHom.lean`.

The generic content lives in this file, under the stacks tree, rather than under
`StacksFrontier/CategoryTheory/`, because two of its inputs do:
`Stacks.SheafOfModules.SmallModelSite.ringedSite` in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfHom.lean` and
`Stacks.SheafOfModules.MixedObjectUniverse.pushforwardUliftIso` in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsModules/QuasicoherentImpliesLocal.lean`.

## References

* [Stacks Project, Tag 03CB](https://stacks.math.columbia.edu/tag/03CB)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.SmallModelSite

universe u o₁ m₁ o₂ m₂

namespace Stacks.SheafOfModules.MixedObjectUniverse

section Transport

universe w n

variable {C : Type o₁} [Category.{m₁} C] {C' : Type o₂} [Category.{m₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsDenseSubsite J J']
  (R : Sheaf J RingCat.{w})

/-- Quasi-coherence is invariant under raising the universe of the sections. -/
private theorem isQuasicoherentOnSite_uliftForPresentation_iff.{a, b, c, d, t}
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{c}}
    {M : SheafOfModules.{d} R} :
    (SheafOfModules.uliftForPresentation.{a, b, c, d, t} M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation',
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'⟩

/-- **Clause (6) of Stacks 03DL is invariant under an equivalence of ringed sites, at a module
universe unrelated to the four universes of the two sites.**  A sheaf of modules is
quasi-coherent exactly when its reindexing along the equivalence, over the transported sheaf of
rings, is quasi-coherent.

This is `Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff'` with the module
universe freed from the universes of the two sites.  That statement is available only at the
balanced universe `max o₁ o₂ m₁ m₂ w n`, which is the universe in which a global presentation
indexes its coproducts on either site; a site whose objects lie above the sections of its
structure sheaf therefore cannot use it at the module universe of its own modules.  Here the
module is raised to the balanced universe, where that statement applies, and lowered again on
the other side: quasi-coherence is invariant under raising the sections by an arbitrary amount,
and raising the sections commutes with restriction along the equivalence. -/
theorem isQuasicoherentOnSite_transport_iff (M : SheafOfModules.{n} R) :
    (((SheafOfModules.pushforward.{n}
        (𝟙 (Stacks.SheafOfModules.reindexRing J' e R))).obj M).IsQuasicoherentOnSite) ↔
      M.IsQuasicoherentOnSite := by
  have iso := pushforwardUliftIso.{o₁, m₁, o₂, m₂, w, n, max o₁ o₂ m₁ m₂ w n}
    (𝟙 (Stacks.SheafOfModules.reindexRing J' e R)) M
  exact (isQuasicoherentOnSite_uliftForPresentation_iff.{o₂, m₂, w, n,
      max o₁ o₂ m₁ m₂ w n}).symm.trans <|
    (Iff.intro (SheafOfModules.IsQuasicoherentOnSite.of_iso iso.symm)
      (SheafOfModules.IsQuasicoherentOnSite.of_iso iso)).trans <|
    (SiteTransport.isQuasicoherentOnSite_transport_iff'.{o₁, m₁, o₂, m₂, w, n}
      (J := J) (J' := J') e R _).trans
      isQuasicoherentOnSite_uliftForPresentation_iff.{o₁, m₁, w, n, max o₁ o₂ m₁ m₂ w n}

end Transport

end Stacks.SheafOfModules.MixedObjectUniverse

namespace Stacks.SheafOfModules.SmallModelSite

variable {X : RingedTopos.{m₁, o₁, u}} {Y : RingedTopos.{m₂, o₂, u}}
  [EssentiallySmall.{u} X.C] [EssentiallySmall.{u} Y.C]

/-- The functor underlying the morphism of the equi-universe models: the model equivalence of the
target site, the functor of the given morphism, and the inverse of the model equivalence of the
source site. -/
def modelFunctor (f : RingedToposSiteHom X Y) :
    SmallModel.{u} Y.C ⥤ SmallModel.{u} X.C :=
  (equivalence.{u} (C := Y.C)).functor ⋙ f.u ⋙ (equivalence.{u} (C := X.C)).inverse

/-- **The functor between the equi-universe models is a morphism of sites.**  It is a composite
of three: either half of an equivalence of sites is one by
`IsMorphismOfSites.ofIsDenseSubsite`, and the middle factor is the hypothesis.  Stacks 03CB
composes them.

The limit hypothesis of `IsMorphismOfSites.ofIsDenseSubsite` is discharged by essential
smallness of the indexing comma categories, the models being small and the two sites locally
small; it is passed positionally, there being no `ringedSite`-level restatement of the
dense-subsite instances of `Stacks.SheafOfModules.SmallModelSite`. -/
theorem modelFunctor_isMorphismOfSites (f : RingedToposSiteHom X Y)
    (hf : IsMorphismOfSites.{u} f.u Y.J X.J) :
    IsMorphismOfSites.{u} (modelFunctor f) (topology.{u} Y.J) (topology.{u} X.J) :=
  let _h1 : IsMorphismOfSites.{u} (equivalence.{u} (C := Y.C)).functor
      (topology.{u} Y.J) Y.J :=
    @IsMorphismOfSites.ofIsDenseSubsite _ _ _ _ _ _ _
      (functor_isContinuous.{u} Y.J) (functor_isDenseSubsite.{u} Y.J)
      (fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _)
  let _h3 : IsMorphismOfSites.{u} (equivalence.{u} (C := X.C)).inverse X.J
      (topology.{u} X.J) :=
    @IsMorphismOfSites.ofIsDenseSubsite _ _ _ _ _ _ _
      (inverse_isContinuous.{u} X.J) (inverse_isDenseSubsite.{u} X.J)
      (fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _)
  let _h4 : IsMorphismOfSites.{u} (f.u ⋙ (equivalence.{u} (C := X.C)).inverse) Y.J
      (topology.{u} X.J) :=
    isMorphismOfSites_comp.{u} (topology.{u} X.J) X.J Y.J f.u
      (equivalence.{u} (C := X.C)).inverse
  isMorphismOfSites_comp.{u} (topology.{u} X.J) Y.J (topology.{u} Y.J)
    (equivalence.{u} (C := Y.C)).functor (f.u ⋙ (equivalence.{u} (C := X.C)).inverse)

/-- The structure map of the morphism of the equi-universe models, on underlying presheaves of
commutative rings: the structure map of the given morphism, whiskered with the model equivalence
of the target site, followed by restriction along the counit of the model equivalence of the
source site.

It is this composite and not another because it is the structure map that the composite of the
three pushforwards of sheaves of modules produces, which is what makes
`Stacks.SheafOfModules.SmallModelSite.modelSiteHom_pushforwardTopos_eq` hold by `rfl`. -/
def modelSharp (f : RingedToposSiteHom X Y) :
    (ringedSite.{u} Y.J Y.O).O.obj ⟶
      (modelFunctor f).op ⋙ (ringedSite.{u} X.J X.O).O.obj :=
  Functor.whiskerLeft (equivalence.{u} (C := Y.C)).functor.op f.fSharp.hom ≫
    Functor.whiskerLeft ((equivalence.{u} (C := Y.C)).functor.op ⋙ f.u.op)
      (Functor.whiskerRight (NatTrans.op (equivalence.{u} (C := X.C)).counit) X.O.obj)

/-- **The morphism of ringed sites between the equi-universe models of the two sites.**  Its
functor is `Stacks.SheafOfModules.SmallModelSite.modelFunctor` and its structure map is
`Stacks.SheafOfModules.SmallModelSite.modelSharp`.

Unlike the given morphism, this is an `AlgebraicGeometry.RingedSite.Hom`: both endpoints have
their objects, their morphisms and the sections of their structure sheaves in one universe, which
is the shape the localization of a morphism at an object, Stacks 04J0, is available in. -/
def modelSiteHom (f : RingedToposSiteHom X Y) (hf : IsMorphismOfSites.{u} f.u Y.J X.J) :
    AlgebraicGeometry.RingedSite.Hom (ringedSite.{u} X.J X.O) (ringedSite.{u} Y.J Y.O) where
  u := modelFunctor f
  isMorphismOfSites := (modelFunctor_isMorphismOfSites f hf).toSmallIsMorphismOfSites
  fsharp := ObjectProperty.homMk (modelSharp f)

section Pullback

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The pushforward along the morphism of the equi-universe models is the conjugate, by the two
model equivalences of sheaves of modules, of the pushforward along the given morphism.**  Both
sides are Mathlib's `SheafOfModules.pushforward` along `e_D ⋙ u ⋙ e_C⁻¹` with the same structure
map: a composite of pushforwards is the pushforward of the composite on the nose, and
`Stacks.SheafOfModules.SmallModelSite.modelSharp` was chosen to be the composite that arises. -/
theorem modelSiteHom_pushforwardTopos_eq (f : RingedToposSiteHom X Y)
    (hf : IsMorphismOfSites.{u} f.u Y.J X.J) :
    (modelSiteHom f hf).toRingedToposSiteHom.pushforwardTopos =
      (modulesEquivalence.{u} X.J X.O).inverse ⋙ f.pushforwardTopos ⋙
        (modulesEquivalence.{u} Y.J Y.O).functor :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Pullback of sheaves of modules commutes with the passage to the equi-universe models.**
The pullback along `Stacks.SheafOfModules.SmallModelSite.modelSiteHom` is the pullback along the
given morphism conjugated by the two model equivalences of sheaves of modules.

Both sides are left adjoints — on the right of the composite of three adjunctions, the model
equivalence of the target taken backwards, the given pullback, and the model equivalence of the
source — and the two right adjoints are equal by
`Stacks.SheafOfModules.SmallModelSite.modelSiteHom_pushforwardTopos_eq`, so this is uniqueness of
left adjoints. -/
def modelPullbackIso (f : RingedToposSiteHom X Y)
    (hf : IsMorphismOfSites.{u} f.u Y.J X.J) :
    (modelSiteHom f hf).toRingedToposSiteHom.pullbackTopos ≅
      ((modulesEquivalence.{u} Y.J Y.O).inverse ⋙ f.pullbackToposGeneral) ⋙
        (modulesEquivalence.{u} X.J X.O).functor :=
  Adjunction.leftAdjointUniq
    (modelSiteHom f hf).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    (Adjunction.ofNatIsoRight
      ((((modulesEquivalence.{u} Y.J Y.O).symm.toAdjunction).comp
        f.pullbackPushforwardAdjunctionToposGeneral).comp
          (modulesEquivalence.{u} X.J X.O).toAdjunction)
      (eqToIso (modelSiteHom_pushforwardTopos_eq f hf).symm))

/-- **Pullback of sheaves of modules commutes with the passage to the equi-universe models, at
one module.**  This is `Stacks.SheafOfModules.SmallModelSite.modelPullbackIso` with the unit of
the model equivalence of the target used to remove the round trip `e_D⁻¹ e_D M`. -/
def modelPullbackObjIso (f : RingedToposSiteHom X Y)
    (hf : IsMorphismOfSites.{u} f.u Y.J X.J)
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (modelSiteHom f hf).toRingedToposSiteHom.pullbackTopos.obj
        ((modulesEquivalence.{u} Y.J Y.O).functor.obj M) ≅
      (modulesEquivalence.{u} X.J X.O).functor.obj (f.pullbackToposGeneral.obj M) :=
  (modelPullbackIso f hf).app ((modulesEquivalence.{u} Y.J Y.O).functor.obj M) ≪≫
    (modulesEquivalence.{u} X.J X.O).functor.mapIso
      (f.pullbackToposGeneral.mapIso ((modulesEquivalence.{u} Y.J Y.O).unitIso.app M).symm)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The images of the functor of the morphism of the models cover the top of the model of the
source site**, as soon as the images of the given functor cover the top of the source site.

This is the hypothesis of
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom_of_coversTop`, read
on the models. The family of all images of the given functor is carried to the model by
`Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj`, whose index type is free, and the
resulting family is refined to one indexed by the objects of the model of the target site because
every object of the target site is isomorphic to the image of a model object. -/
theorem coversTop_modelSiteHom_u_obj (f : RingedToposSiteHom X Y)
    (hf : IsMorphismOfSites.{u} f.u Y.J X.J) (hu : X.J.CoversTop f.u.obj) :
    (ringedSite.{u} X.J X.O).J.CoversTop (modelSiteHom f hf).u.obj := by
  intro A
  refine (topology.{u} X.J).superset_covering ?_
    (Stacks.SheafOfModules.SiteTransport.coversTop_inverse_obj (equivalence.{u} (C := X.C)) hu A)
  rintro Z g ⟨W, ⟨b⟩⟩
  exact ⟨(equivalence.{u} (C := Y.C)).inverse.obj W,
    ⟨b ≫ (equivalence.{u} (C := X.C)).inverse.map
      (f.u.map ((equivalence.{u} (C := Y.C)).counitIso.inv.app W))⟩⟩

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The quasi-coherent clause of Stacks 03DO at independent site universes.**  Let
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi presented by a functor
`u : D ⥤ C` which is a morphism of sites, with the objects and the morphisms of the two sites in
universes unrelated to each other and to the universe `u` of the sections of the two structure
sheaves, both sites being essentially small in that universe.  If the images of `u` cover the top
of `C`, then the pullback along `f` of a quasi-coherent sheaf of `O_D`-modules is quasi-coherent.

Neither site is asked to have finite limits or a final object, which is what
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos` asks for, and neither is
asked to have its objects in the universe of the sections, which is what
`Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom_of_coversTop` asks for.

The proof is the transport: quasi-coherence of the module is carried to the equi-universe model
of `D`, the clause of 03DO for a morphism of ringed sites applies to
`Stacks.SheafOfModules.SmallModelSite.modelSiteHom` there, the conclusion is identified with the
transport of the pullback by
`Stacks.SheafOfModules.SmallModelSite.modelPullbackObjIso`, and quasi-coherence is carried back
to `C`. -/
theorem isQuasicoherentOnSite_pullbackToposGeneral_of_coversTop (f : RingedToposSiteHom X Y)
    (hf : IsMorphismOfSites.{u} f.u Y.J X.J) (hu : X.J.CoversTop f.u.obj)
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : M.IsQuasicoherentOnSite) :
    (f.pullbackToposGeneral.obj M).IsQuasicoherentOnSite := by
  refine (MixedObjectUniverse.isQuasicoherentOnSite_transport_iff
    (J := X.J) (J' := topology.{u} X.J) (equivalence.{u} (C := X.C))
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.pullbackToposGeneral.obj M)).1 ?_
  refine _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso (modelPullbackObjIso f hf M) ?_
  exact Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom_of_coversTop
    (modelSiteHom f hf) (coversTop_modelSiteHom_u_obj f hf hu)
    ((MixedObjectUniverse.isQuasicoherentOnSite_transport_iff
      (J := Y.J) (J' := topology.{u} Y.J) (equivalence.{u} (C := Y.C))
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M).2 hM)

end Pullback

end Stacks.SheafOfModules.SmallModelSite

end
