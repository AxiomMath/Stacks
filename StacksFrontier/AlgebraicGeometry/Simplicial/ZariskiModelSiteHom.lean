module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCoversTop
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiEquiUniverseModel
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism

/-!
# A morphism of ringed sites between the equi-universe models of two total Zariski sites

A morphism of simplicial schemes `f : V ⟶ U` induces the degreewise inverse image of opens
`AlgebraicGeometry.SimplicialScheme.zariskiPullback f : U_Zar ⥤ V_Zar`, and with the structure
map `f♯` of `AlgebraicGeometry.SimplicialScheme.zariskiSharp` this is a morphism of the two
Zariski ringed *topoi*. It is not a `AlgebraicGeometry.RingedSite.Hom`, which is declared only
for a ringed site whose objects, morphisms and sections of the structure sheaf share one
universe: an object of the total Zariski site is an open subset of a scheme, so the objects lie
in `Type u`, while a morphism carries a map of simplicial degrees, so the morphisms lie in
`Type 0`.

This file transports it to the equi-universe models of
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite`, where it *is* a
`AlgebraicGeometry.RingedSite.Hom`, and which is therefore the form in which the localization
theory of Stacks 03CF and Stacks 04J0 applies to it.

The underlying functor is `e_U ⋙ f⁻¹ ⋙ e_V⁻¹`, where `e_X` is the model equivalence. It is a
morphism of sites by Stacks 03CB, composing the two halves of an equivalence of sites
(`IsMorphismOfSites.ofIsDenseSubsite`, applied to the dense-subsite instances of the model
equivalence) with Stacks 09VN for the degreewise inverse image
(`Stacks.Topology.Simplicial.SimplicialOpen.pullback_isMorphismOfSites_large`). The structure
map is `f♯` whiskered with the model equivalence of the target, followed by the counit of the
model equivalence of the source, which is what identifies the direct image of the model
structure sheaf of `V` along the composite with the direct image of `𝒪_V` along `f⁻¹`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.zariskiModelEquivalence`: the model equivalence of the
  total Zariski site.
* `AlgebraicGeometry.SimplicialScheme.zariskiModelPullback`: the underlying functor
  `e_U ⋙ f⁻¹ ⋙ e_V⁻¹` of the morphism of models.
* `AlgebraicGeometry.SimplicialScheme.zariskiModelSharp`: its structure map, on underlying
  presheaves of commutative rings.
* `AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom`: **the morphism of ringed sites
  `model(V_Zar) ⟶ model(U_Zar)` attached to a morphism of simplicial schemes.**

## Main results

* `AlgebraicGeometry.SimplicialScheme.zariskiModelPullback_isMorphismOfSites`: the underlying
  functor is a morphism of sites.
* `AlgebraicGeometry.SimplicialScheme.exists_hom_zariskiModelSiteHom`: every object of the
  model of `V_Zar` admits an arrow into the image of the functor. This is the hypothesis of
  `Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom`, the form of
  Stacks 04J0 that asks for no terminal object; the total Zariski site has none, and neither
  does its model.

## Implementation notes

Instance search does not unfold
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite`, so the continuity and
dense-subsite arguments of `IsMorphismOfSites.ofIsDenseSubsite` are passed positionally rather
than found: there is no `ringedSite`-level restatement of the dense-subsite instance of
`Stacks.SheafOfModules.SmallModelSite`.

The three `IsMorphismOfSites` hypotheses of `isMorphismOfSites_comp` are likewise supplied as
local instances in the order the composite needs them, the functor being composed as
`e_U ⋙ (f⁻¹ ⋙ e_V⁻¹)`.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03CB](https://stacks.math.columbia.edu/tag/03CB)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
* [Stacks Project, Tag 09VN](https://stacks.math.columbia.edu/tag/09VN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.SmallModelSite

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- The model equivalence of the total Zariski site of a simplicial scheme: the equivalence
between the small model of the site, which is the underlying category of
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite`, and the site itself. -/
public noncomputable abbrev zariskiModelEquivalence (X : SimplicialObject Scheme.{u}) :
    SmallModel.{u} (ZariskiOpen X) ≌ ZariskiOpen X :=
  Stacks.SheafOfModules.SmallModelSite.equivalence.{u} (C := ZariskiOpen X)

/-- The functor underlying the morphism of the equi-universe models induced by a morphism of
simplicial schemes: the model equivalence of the target, the degreewise inverse image of opens,
and the inverse of the model equivalence of the source. -/
public noncomputable def zariskiModelPullback (f : V ⟶ U) :
    SmallModel.{u} (ZariskiOpen U) ⥤ SmallModel.{u} (ZariskiOpen V) :=
  (zariskiModelEquivalence U).functor ⋙ zariskiPullback f ⋙
    (zariskiModelEquivalence V).inverse

/-- **The functor between the equi-universe models is a morphism of sites.** It is the
composite of three: either half of an equivalence of sites is one, by
`IsMorphismOfSites.ofIsDenseSubsite`, and the degreewise inverse image of opens is one by
Stacks 09VN. Stacks 03CB composes them. -/
public theorem zariskiModelPullback_isMorphismOfSites (f : V ⟶ U) :
    IsMorphismOfSites.{u} (zariskiModelPullback f) (topology.{u} (zariskiTopology U))
      (topology.{u} (zariskiTopology V)) :=
  let _h1 : IsMorphismOfSites.{u} (zariskiModelEquivalence U).functor
      (topology.{u} (zariskiTopology U)) (zariskiTopology U) :=
    @IsMorphismOfSites.ofIsDenseSubsite _ _ _ _ _ _ _
      (functor_isContinuous.{u} (zariskiTopology U))
      (functor_isDenseSubsite.{u} (zariskiTopology U)) (fun _ => inferInstance)
  let _h2 : IsMorphismOfSites.{u} (zariskiPullback f) (zariskiTopology U)
      (zariskiTopology V) :=
    Stacks.Topology.Simplicial.SimplicialOpen.pullback_isMorphismOfSites_large.{u, u}
      (Functor.whiskerRight f Scheme.forgetToTop)
  let _h3 : IsMorphismOfSites.{u} (zariskiModelEquivalence V).inverse (zariskiTopology V)
      (topology.{u} (zariskiTopology V)) :=
    @IsMorphismOfSites.ofIsDenseSubsite _ _ _ _ _ _ _
      (inverse_isContinuous.{u} (zariskiTopology V))
      (inverse_isDenseSubsite.{u} (zariskiTopology V)) (fun _ => inferInstance)
  let _h4 : IsMorphismOfSites.{u} (zariskiPullback f ⋙ (zariskiModelEquivalence V).inverse)
      (zariskiTopology U) (topology.{u} (zariskiTopology V)) :=
    isMorphismOfSites_comp.{u} (topology.{u} (zariskiTopology V)) (zariskiTopology V)
      (zariskiTopology U) (zariskiPullback f) (zariskiModelEquivalence V).inverse
  isMorphismOfSites_comp.{u} (topology.{u} (zariskiTopology V)) (zariskiTopology U)
    (topology.{u} (zariskiTopology U)) (zariskiModelEquivalence U).functor
    (zariskiPullback f ⋙ (zariskiModelEquivalence V).inverse)

/-- The structure map of the morphism of the equi-universe models, on underlying presheaves of
commutative rings: the structure map `f♯` of the morphism of simplicial schemes, whiskered with
the model equivalence of the target, followed by the restriction along the counit of the model
equivalence of the source. -/
public noncomputable def zariskiModelSharp (f : V ⟶ U) :
    (zariskiModelRingedSite U).O.obj ⟶
      (zariskiModelPullback f).op ⋙ (zariskiModelRingedSite V).O.obj :=
  Functor.whiskerLeft (zariskiModelEquivalence U).functor.op (zariskiSharp f).hom ≫
    Functor.whiskerLeft
      ((zariskiModelEquivalence U).functor.op ⋙ (zariskiPullback f).op)
      (Functor.whiskerRight (NatTrans.op (zariskiModelEquivalence V).counit)
        (structureSheaf V).obj)

/-- **A morphism of simplicial schemes induces a morphism of the equi-universe models of the
two total Zariski ringed sites.** The functor is
`AlgebraicGeometry.SimplicialScheme.zariskiModelPullback` and the structure map is
`AlgebraicGeometry.SimplicialScheme.zariskiModelSharp`.

Unlike the morphism of ringed topoi
`AlgebraicGeometry.SimplicialScheme.zariskiRingedToposHom`, this is a morphism of ringed sites
in the sense of Stacks 03AD part (2), whose two endpoints have their objects, their morphisms
and the sections of their structure sheaves in one universe. That is the shape the localization
of a morphism at an object, Stacks 04J0, is available in. -/
public noncomputable def zariskiModelSiteHom (f : V ⟶ U) :
    AlgebraicGeometry.RingedSite.Hom (zariskiModelRingedSite V) (zariskiModelRingedSite U) where
  u := zariskiModelPullback f
  isMorphismOfSites :=
    (zariskiModelPullback_isMorphismOfSites f).toSmallIsMorphismOfSites
  fsharp := ObjectProperty.homMk (zariskiModelSharp f)

/-- **Every object of the model of `V_Zar` admits an arrow into the image of the functor.** This
is the hypothesis of the form of Stacks 04J0 that asks for no terminal object; it is
`AlgebraicGeometry.SimplicialScheme.exists_hom_zariskiPullback` carried across the two model
equivalences. -/
public theorem exists_hom_zariskiModelSiteHom (f : V ⟶ U) (A : (zariskiModelRingedSite V).C) :
    ∃ T : (zariskiModelRingedSite U).C,
      Nonempty (A ⟶ (zariskiModelSiteHom f).u.obj T) := by
  obtain ⟨T, ⟨g⟩⟩ :=
    exists_hom_zariskiPullback f ((zariskiModelEquivalence V).functor.obj A)
  exact ⟨(zariskiModelEquivalence U).inverse.obj T,
    ⟨(zariskiModelEquivalence V).unit.app A ≫ (zariskiModelEquivalence V).inverse.map
      (g ≫ (zariskiPullback f).map ((zariskiModelEquivalence U).counitIso.inv.app T))⟩⟩

end AlgebraicGeometry.SimplicialScheme

end
