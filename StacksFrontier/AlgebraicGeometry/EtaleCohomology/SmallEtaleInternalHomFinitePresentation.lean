module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FinitePresentationKernel
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# The internal Hom out of a module of finite presentation on the small étale site

Clause (6) of Stacks 0GNB asserts that the internal Hom `𝓗om_𝒪(𝓕, 𝓖)` of two `𝒪`-modules on the
small étale site of a scheme `S` is quasi-coherent as soon as `𝓕` is **of finite presentation** —
Stacks 03DL (7), the condition that every object of the site be covered by objects on which `𝓕` is
the cokernel of a map of finite free modules — and `𝓖` is quasi-coherent.  This file proves that
clause.

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleInternalHomPresentation.lean` proves it
for a `𝓕` carrying such a presentation on the site itself,
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_presentation`, and
deliberately carries no attribute, that hypothesis being strictly stronger than 03DL (7).  What is
added here is the passage from the local hypothesis to that global one, and it is no new
mathematics: quasi-coherence is local on the site (Stacks 03DN), so it is enough to see that on an
object `V` carrying a finite global presentation of `𝓕` the restriction of `𝓗om_𝒪(𝓕, 𝓖)` is
quasi-coherent, and that restriction is the internal Hom of the restrictions on the small étale
site of the *scheme* of `V`, where the global-presentation result applies.

Three comparisons carry out that passage.

* The internal Hom commutes with restriction to a localized site — Stacks 0E8H,
  `Stacks.SheafOfModules.InternalHom.internalHomOverIso`, which is stated for the presheaf
  `internalHom` of Stacks 03EM and is read here as a statement about
  `AlgebraicGeometry.RingedSite.internalHomSheaf` on the localized ringed site.
* The internal Hom is carried along an equivalence of ringed sites —
  `Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` — applied to the localization
  equivalence `AlgebraicGeometry.SmallEtale.localizationEquivalence`, which identifies the
  localization of `S_étale` at `V` with the small étale site of the scheme of `V` *as a ringed
  site*, on the nose
  (`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`).
* A finite global presentation is carried along that same equivalence, which is the finite
  analogue of `Stacks.SheafOfModules.hasGlobalPresentation_reindex`.

## Main definitions

* `AlgebraicGeometry.RingedSite.overSite`: the localization
  `AlgebraicGeometry.RingedSite.over` of a ringed site at an object, written out and therefore
  *reducible*.  `AlgebraicGeometry.RingedSite.overSite_eq` records that it is that localization;
  what the spelling buys is that instance search can see the category and the structure sheaf of
  the slice through it, which it cannot through a `def`.  This is the device
  `AlgebraicGeometry.smallEtaleRingedSite` is an `abbrev` for.
* `AlgebraicGeometry.SmallEtale.objRestrictStructureMap`: the structure map of the localization
  comparison of the small étale site, the identity.

## Main results

* `Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex`: reindexing along an equivalence of
  ringed sites carries a finite global presentation to a finite global presentation.
* `AlgebraicGeometry.SmallEtale.objRestrictInternalHomSheafIso`: **the crossover
  `𝒢 ↦ 𝒢|_{Y_étale}` of `AlgebraicGeometry.SmallEtale.objRestrict` carries
  `AlgebraicGeometry.SmallEtale.internalHomSheaf` to
  `AlgebraicGeometry.SmallEtale.internalHomSheaf`**, at the module universe of the schemes.  This
  is Stacks 0E8H followed by the transport along the localization equivalence, both read down the
  universe lift of the module sections.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf`: **clause (6) of Stacks
  0GNB**.

## Implementation notes

The module universe is the one of the schemes, `u`, which is the universe in which the other five
clauses of Stacks 0GNB are stated.  The internal Hom of the small étale *ringed* site raises it to
`u + 1`, the objects of the site forming a type in `Type (u + 1)`, and
`AlgebraicGeometry.SmallEtale.internalHomSheaf` is its descent along
`Stacks.SheafOfModules.moduleULift`.  Both comparisons above are therefore built at `u + 1`, where
`AlgebraicGeometry.RingedSite.internalHomSheaf` lives, and brought down by full faithfulness of
that lift; `Stacks.SheafOfModules.pushforwardUliftIso` is what commutes the lift past the two
restriction functors making up the crossover.

`Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex` is the proof of
`Stacks.SheafOfModules.hasGlobalPresentation_reindex` with its appeal to
`Stacks.SheafOfModules.hasGlobalPresentation_map` replaced by one to
`Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor`; the
comparison isomorphisms it feeds that transport are the same.

`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_presentation` consumes a
presentation at the module universe `u`, whereas `SheafOfModules.HasFiniteGlobalPresentation`
presents the universe lift of the module, its two coproducts and its cokernel being taken in
`max u v w m`, which on this site is `u + 1`.  The exchange is
`SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation'`, which produces a
Mathlib `SheafOfModules.Presentation` — a presentation at `u` on the nose — and is available here
because the small étale site of a scheme has `AddCommGrpCat.{u}`-sheafification.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.RingedSite

/-- **The localization of a ringed site at an object, written out.**  This is
`AlgebraicGeometry.RingedSite.over` (`AlgebraicGeometry.RingedSite.overSite_eq`); being an
`abbrev` it is reducible, so instance search sees that the underlying category of the
localization is the slice category and that its structure sheaf is the restricted one, which it
does not see through `AlgebraicGeometry.RingedSite.over` — a `def`.  Statements about the
localization phrased through the latter cannot find the instances of the slice at all. -/
abbrev overSite (X : RingedSite.{u, v, w}) (U : X.C) : RingedSite.{max u v, v, w} where
  C := Over U
  J := X.J.over U
  O := X.O.over U

/-- `AlgebraicGeometry.RingedSite.overSite` is the localization
`AlgebraicGeometry.RingedSite.over`. -/
theorem overSite_eq (X : RingedSite.{u, v, w}) (U : X.C) : X.overSite U = X.over U := rfl

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

/-- **Reindexing along an equivalence of ringed sites carries finite global presentations to
finite global presentations.**  A finite global presentation, Stacks 03DE (7), is a cokernel of a
map between *finite* coproducts of copies of the structure sheaf, all three expressed by
universal properties; reindexing along an equivalence of sites matching the structure sheaves is
an equivalence of module categories, so it carries all three.

This is `Stacks.SheafOfModules.hasGlobalPresentation_reindex` with the finiteness of the two index
types kept, and the comparison isomorphisms it supplies to the transport are the same. -/
theorem hasFiniteGlobalPresentation_reindex (e : C' ≌ C) [e.functor.IsContinuous J' J]
    [e.inverse.IsContinuous J J'] (R : Sheaf J RingCat.{w}) (M : _root_.SheafOfModules.{w} R)
    (h : M.HasFiniteGlobalPresentation) :
    ((_root_.SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj
      M).HasFiniteGlobalPresentation := by
  let φ : reindexRing J' e R ⟶
      (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R := 𝟙 _
  let F₀ := _root_.SheafOfModules.pushforward.{w} φ
  let eHi : _root_.SheafOfModules.{max u v w} R ≌
      _root_.SheafOfModules.{max u v w} (reindexRing J' e R) := reindexEquivalence e R
  let F := eHi.functor
  let : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  have hF : PreservesColimitsOfSize.{max u v w, max u v w} F := inferInstance
  have hF₀ : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hU : F₀.obj (_root_.SheafOfModules.unit R) ≅
      _root_.SheafOfModules.unit (reindexRing J' e R) := Iso.refl _
  have hη₁ : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (_root_.SheafOfModules.unit R)) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit (reindexRing J' e R)) :=
    pushforwardUliftIso.{u, v, w, w, max u v w} φ (_root_.SheafOfModules.unit R) ≪≫
      _root_.SheafOfModules.uliftForPresentationMapIso.{u, v, w, w, max u v w} hU
  have hηM : F.obj (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} (F₀.obj M) :=
    pushforwardUliftIso.{u, v, w, w, max u v w} φ M
  exact FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor M (F₀.obj M)
    hF hF₀ hη₁ hηM h

/-- The relations of a presentation of a sheaf of modules annihilate its generators: the
presenting map factors through the kernel of the generating epimorphism. -/
theorem presentation_relations_comp_generators {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : _root_.SheafOfModules.{w} R} (P : M.Presentation) :
    ((_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π) ≫ P.generators.π = 0 := by
  rw [Category.assoc, kernel.condition, comp_zero]

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (V : SmallEtale B S hS)

/-- The localization of the small étale ringed site of `S` at an object `V`, with its universes
pinned: the objects of the slice lie in `Type (u + 1)`, as the objects of the site do, and
`max (u + 1) u` is written `u + 1` so that the instances of the site are found at this
spelling. -/
abbrev objRestrictSlice : RingedSite.{u + 1, u, u} :=
  (smallEtaleRingedSite B S hS).overSite V

/-- The small étale ringed site of the scheme underlying an object `V` of the small étale site
of `S`. -/
abbrev objSchemeRingedSite : RingedSite.{u + 1, u, u} :=
  smallEtaleRingedSite B (objScheme B S hS V) (contains_objScheme B S hS V)

/-- **The structure map of the localization comparison of the small étale site: the identity.**
The localization equivalence `AlgebraicGeometry.SmallEtale.localizationEquivalence` matches the
two structure sheaves on the nose
(`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`), so no comparison has to be
made. -/
def objRestrictStructureMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf (objSchemeRingedSite B S hS V).O) ⟶
    ((localizationEquivalence B S hS V).functor.sheafPushforwardContinuous RingCat.{u}
      (objSchemeRingedSite B S hS V).J (objRestrictSlice B S hS V).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (objRestrictSlice B S hS V).O) :=
  𝟙 _

/-- The structure map of the localization comparison is invertible: it is the identity. -/
instance isIso_objRestrictStructureMap : IsIso (objRestrictStructureMap B S hS V) := by
  change IsIso (𝟙 _)
  infer_instance

variable
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS).O))

/-- The crossover carries the internal Hom to the internal Hom, at the raised module universe
`u + 1` where the internal Hom of the small étale *ringed* site lives.

The chain is: the universe lift commutes with the two restriction functors the crossover is made
of (`Stacks.SheafOfModules.pushforwardUliftIso`), the lift of
`AlgebraicGeometry.SmallEtale.internalHomSheaf` is
`AlgebraicGeometry.RingedSite.internalHomSheaf`
(`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso`), the latter commutes with
restriction to the localization at `V` (Stacks 0E8H,
`AlgebraicGeometry.RingedSite.internalHomSheafOverIso`), and it is carried along the localization
equivalence (`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso`). -/
def moduleULiftObjRestrictInternalHomSheafIso :
    (Stacks.SheafOfModules.moduleULift.{u + 1, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (objSchemeRingedSite B S hS V).O)).obj
        ((objRestrict B S hS V).obj (internalHomSheaf B S hS F G)) ≅
      RingedSite.internalHomSheaf (objSchemeRingedSite B S hS V)
        ((objRestrict B S hS V).obj F) ((objRestrict B S hS V).obj G) :=
  (Stacks.SheafOfModules.pushforwardUliftIso (objRestrictStructureMap B S hS V)
      ((internalHomSheaf B S hS F G).over V)).symm ≪≫
    (SheafOfModules.pushforward.{u + 1} (objRestrictStructureMap B S hS V)).mapIso
      ((Stacks.SheafOfModules.pushforwardUliftIso
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).over V))
          (internalHomSheaf B S hS F G)).symm ≪≫
        (SheafOfModules.overFunctor.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS).O) V).mapIso
          (moduleULiftInternalHomSheafIso B S hS F G) ≪≫
        RingedSite.internalHomSheafOverIso (smallEtaleRingedSite B S hS) V F G) ≪≫
    Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso
      (X := objRestrictSlice B S hS V) (Y := objSchemeRingedSite B S hS V)
      (localizationEquivalence B S hS V) (objRestrictStructureMap B S hS V) (F.over V) (G.over V)

/-- **The crossover `𝒢 ↦ 𝒢|_{Y_étale}` carries the internal Hom of the small étale site of `S` to
the internal Hom of the small étale site of the scheme `Y` of `V`**, at the module universe of
the schemes.

This is `AlgebraicGeometry.SmallEtale.moduleULiftObjRestrictInternalHomSheafIso` read down the
universe lift of the module sections, which is fully faithful. -/
def objRestrictInternalHomSheafIso :
    (objRestrict B S hS V).obj (internalHomSheaf B S hS F G) ≅
      internalHomSheaf B (objScheme B S hS V) (contains_objScheme B S hS V)
        ((objRestrict B S hS V).obj F) ((objRestrict B S hS V).obj G) :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (objSchemeRingedSite B S hS V).O)).preimageIso
    (moduleULiftObjRestrictInternalHomSheafIso B S hS V F G ≪≫
      (moduleULiftInternalHomSheafIso B (objScheme B S hS V) (contains_objScheme B S hS V)
        ((objRestrict B S hS V).obj F) ((objRestrict B S hS V).obj G)).symm)

/-- **A finite global presentation crosses over**: a finite global presentation of the restriction
of `𝓕` to the localization at `V` is one of its crossover restriction to the small étale site of
the scheme of `V`, the two ringed sites being the same. -/
theorem hasFiniteGlobalPresentation_objRestrict
    (hF : (F.over V).HasFiniteGlobalPresentation) :
    ((objRestrict B S hS V).obj F).HasFiniteGlobalPresentation :=
  Stacks.SheafOfModules.hasFiniteGlobalPresentation_reindex
    (localizationEquivalence B S hS V) ((structureSheaf B S hS).over V) (F.over V) hF

/-- **Clause (6) of Stacks 0GNB on an object carrying a finite global presentation of `𝓕`.**  If
the restriction of `𝓕` to the localization at `V` has a finite global presentation and `𝓖` is
quasi-coherent, then the restriction of `𝓗om_𝒪(𝓕, 𝓖)` to that localization is quasi-coherent.

The presentation crosses over to the small étale site of the scheme of `V`, where it becomes a
`SheafOfModules.Presentation` — a presentation at the module universe of the schemes — and
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf_of_presentation` applies to
the crossover restrictions; the conclusion returns through
`AlgebraicGeometry.SmallEtale.objRestrictInternalHomSheafIso` and the invariance of
quasi-coherence under the crossover. -/
theorem isQuasicoherentOnSite_internalHomSheaf_of_hasFiniteGlobalPresentation
    (hF : (F.over V).HasFiniteGlobalPresentation) (hG : G.IsQuasicoherentOnSite) :
    ((internalHomSheaf B S hS F G).over V).IsQuasicoherentOnSite := by
  obtain ⟨p, hp⟩ := SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation'
    (hasFiniteGlobalPresentation_objRestrict B S hS V F hF)
  have := hp
  have : Finite p.generators.I := hp.isFiniteType_generators.finite
  have : Finite p.relations.I := hp.isFiniteType_relations.finite
  have hG' : ((objRestrict B S hS V).obj G).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_objRestrict_iff B S hS V G).2
      (Stacks.SheafOfModules.isQuasicoherent_over G hG V)
  have key := isQuasicoherentOnSite_internalHomSheaf_of_presentation B
    (objScheme B S hS V) (contains_objScheme B S hS V)
    ((objRestrict B S hS V).obj G)
    (a := (SheafOfModules.freeHomEquiv _).symm p.relations.s ≫ kernel.ι p.generators.π)
    (b := p.generators.π)
    (fun i => (SheafOfModules.freeCofan p.generators.I).inj i)
    (SheafOfModules.isColimitFreeCofan p.generators.I)
    (fun i => (SheafOfModules.freeCofan p.relations.I).inj i)
    (SheafOfModules.isColimitFreeCofan p.relations.I)
    (Stacks.SheafOfModules.presentation_relations_comp_generators p) p.isColimit hG'
  exact (isQuasicoherentOnSite_objRestrict_iff B S hS V (internalHomSheaf B S hS F G)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (objRestrictInternalHomSheafIso B S hS V F G).symm key)

/-- **Clause (6) of Stacks 0GNB.**  The internal Hom `𝓗om_𝒪(𝓕, 𝓖)` of two `𝒪`-modules on the
small étale site of a scheme `S` is quasi-coherent when `𝓕` is of finite presentation — Stacks
03DL (7) — and `𝓖` is quasi-coherent.

Quasi-coherence is local on the site (Stacks 03DN), so it is enough to produce a covering family
of the final object on whose members the restriction of the internal Hom is quasi-coherent, and
the objects carrying a finite global presentation of `𝓕` form one, by the finite-presentation
hypothesis itself.  On such an object the conclusion is
`isQuasicoherentOnSite_internalHomSheaf_of_hasFiniteGlobalPresentation` of this namespace. -/
@[stacks 0GNB "clause (6): the internal Hom out of a module of finite presentation is \
  quasi-coherent, small site at τ = étale"]
theorem isQuasicoherentOnSite_internalHomSheaf (hF : F.IsFinitePresentationOnSite)
    (hG : G.IsQuasicoherentOnSite) :
    (internalHomSheaf B S hS F G).IsQuasicoherentOnSite := by
  have := hF
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
      (internalHomSheaf B S hS F G)).2
    ⟨{ W : SmallEtale B S hS // (F.over W).HasFiniteGlobalPresentation }, Subtype.val, ?_, ?_⟩
  · intro W
    obtain ⟨I, Vs, f, hf, hVs⟩ :=
      SheafOfModules.IsFinitePresentationOnSite.locally_hasFiniteGlobalPresentation (F := F) W
    refine (topology B S hS).superset_covering ?_ hf
    refine (Sieve.generate_le_iff _ _).mpr ?_
    intro Z g hg
    obtain ⟨i⟩ := hg
    exact ⟨⟨Vs i, hVs i⟩, ⟨𝟙 _⟩⟩
  · intro i
    exact isQuasicoherentOnSite_internalHomSheaf_of_hasFiniteGlobalPresentation B S hS i.1 F G
      i.2 hG

end AlgebraicGeometry.SmallEtale

end
