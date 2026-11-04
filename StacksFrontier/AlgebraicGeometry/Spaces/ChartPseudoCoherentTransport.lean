module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOpenSliceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Restriction
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# Pseudo-coherence across the represented-space comparisons at an étale chart

Let `X` be an algebraic space over a scheme `S` and let `U` be an étale scheme chart of `X`.
Three ringed sites are in play, and they are all the same ringed site up to canonical
comparison:

* the localization `(X_étale/U, 𝒪_X|_U)` of the small étale ringed site of `X` at `U`, which is
  what the locality of pseudo-coherence (Stacks 08FU (3),
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction`) hands over;
* the small étale ringed site of the algebraic space *represented by* `U`, to which the first is
  identified by Stacks 04M0
  (`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`, with the structure sheaves
  agreeing by `AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`);
* the small étale ringed site of the *scheme* underlying `U`, to which the second is identified
  by `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, with the structure sheaves
  agreeing by `AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`.

This file carries `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` and
`AlgebraicGeometry.RingedSite.IsPseudoCoherent` — the two clauses of Stacks 08FT part (3) for an
object of the derived category — across both comparisons, in both directions, with no
mathematical hypothesis beyond what the comparisons themselves need.

## Main definitions

* `AlgebraicGeometry.Space.chartLocalizationReindex` and
  `AlgebraicGeometry.Space.chartLocalizationModulesEquivalence`: the reindexing of
  `𝒪_X|_U`-modules along Stacks 04M0, and the equivalence of module categories it is the functor
  of.
* `AlgebraicGeometry.Space.representedSchemeReindex` and
  `AlgebraicGeometry.Space.representedSchemeModulesEquivalence`: the same for the comparison
  between a representable algebraic space and its scheme.
* `AlgebraicGeometry.Space.representedRingedSite` and
  `AlgebraicGeometry.Space.representedSchemeRingedSite`: the two small étale ringed sites that
  comparison relates.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartLocalizationReindex_iff` and
  `AlgebraicGeometry.Space.isPseudoCoherent_chartLocalizationReindex_iff`:
  **pseudo-coherence crosses Stacks 04M0**, in both directions and in both degree forms.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedSchemeReindex_iff` and
  `AlgebraicGeometry.Space.isPseudoCoherent_representedSchemeReindex_iff`:
  **pseudo-coherence crosses the comparison of a representable algebraic space with its
  scheme**, in both directions and in both degree forms.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff` and
  `AlgebraicGeometry.Space.isPseudoCoherent_chartSchemeReindex_iff`: **the two composed**,
  taking the localization of the small étale site of `X` at a chart to the small étale site of
  the chart's scheme.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_pushforwardPushforwardEquivalence_inverse` and
  `...isPseudoCoherent_of_pushforwardPushforwardEquivalence_functor`: the all-degrees
  companions of the transport of pseudo-coherence along an arbitrary equivalence of ringed
  sites, built on
  `AlgebraicGeometry.RingedSite.isPseudoCoherent_mapDerivedCategory_of_hypotheses`, the
  all-degrees form of the generic transport along an exact functor with an exact localization
  square.
* `CategoryTheory.GrothendieckTopology.coversTop_functor_obj_of_equivalence`: the image of an
  equivalence of categories covers the final object of any topology on its target.

## Why the transport needs no comparison of structure sheaves

The generic transport
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`
asks for a structure map `φ : O_D ⟶ e_* O_C` and an inverse one `ψ`, and asks `φ` to be
invertible.  At both comparisons here **all four structure maps are the identity**: the two
reindexings of each comparison are equalities of sheaves of rings, by `rfl`, in both
orientations — neither functor of either comparison changes the underlying scheme of an object,
and every structure sheaf in sight is the global regular functions on it.  So invertibility of
`φ` is free, `Stacks.SheafOfModules.reindexBackSharp` — the inverse structure map of
`Stacks.SheafOfModules.reindexEquivalence` — is itself the identity, and the first
compatibility of the two structure maps holds by `rfl`; the second is then
`Stacks.SheafOfModules.InternalHom.unit_of_counit`.  Nothing has to be transported along an
isomorphism of sheaves of rings, and no bridging comparison of module categories is built.

That is also what makes each statement an `iff` with a *single* functor.  The generic transport
concludes about the target of the equivalence of sites it is given, so the two directions are
taken at the two orientations of one comparison; the inverse transport of one orientation and
the forward reindexing of the other are literally the same functor because the structure map
they are taken along is the identity in both.

## Implementation notes

The all-degrees clause of Stacks 08FT (3) is **not** deduced degree by degree from the
`m`-pseudo-coherent clause: it asks for one complex which is `m`-pseudo-coherent for every `m`,
which a family of degreewise statements does not provide.  It is carried by its own transport,
proved here by applying the chain-level
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_mapHomologicalComplex` in every degree
to the degreewise image of that one complex.

The universes are not free.  `Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`, which the
generic transport is built from, is stated at a single `AlgebraicGeometry.RingedSite.{u, v, w}`;
the small étale ringed site of an algebraic space and that of a scheme over `Scheme.{u}` are
both `RingedSite.{u + 1, u, u}`, and so is the localization of either at an object, the object
universe `max (u + 1) u` of `AlgebraicGeometry.RingedSite.over` being `u + 1`.  The ringed sites
are therefore passed positionally with explicit universes.

Several facts are restated at the spellings the ringed sites use — continuity of each
comparison, sheafification and local bijectivity on the localization and on its iterated slices,
and the abelian structure of each module category.  In each case the content is imported and
only the spelling is new: the projections `.J` and `.ringSheaf` of a ringed site do not reduce
at instance transparency, and the ringed site of
`AlgebraicGeometry.RingedSite.sliceHasSheafify` and friends occurs in their conclusions only
through those projections, which instance search cannot invert.  They are applied explicitly for
that reason rather than synthesized.

`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is removed as an instance for this file: it
answers `Abelian (SheafOfModules …)` with the module universe left as the join of the universes
of the site, the rings and a free one, and a search reaching it first ends in a universe
constraint with no solution rather than in a recoverable failure.

No declaration here carries a `stacks` tag.  This is infrastructure — the transport of a
predicate across identifications already covered in the tree — and not a clause of Stacks 04M0,
08FT or 08FU.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY u v w d dX dY

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace CategoryTheory.GrothendieckTopology

/-- **The image of an equivalence covers the final object.**  For an equivalence `e : C' ≌ C` of
categories and any topology `J` on `C`, the family `fun W => e.functor.obj W` covers the final
object: every object `T` of `C` admits the isomorphism
`e.counitInv.app T : T ⟶ e.functor.obj (e.inverse.obj T)`, so the sieve of arrows factoring
through the image of `e.functor` is the maximal sieve. -/
theorem coversTop_functor_obj_of_equivalence {C : Type u} [Category.{v} C] {C' : Type uX}
    [Category.{vX} C'] (e : C' ≌ C) (J : GrothendieckTopology C) :
    J.CoversTop e.functor.obj := by
  intro Z
  refine J.superset_covering ?_ (J.top_mem Z)
  intro T _ _
  exact ⟨e.inverse.obj T, ⟨e.counitInv.app T⟩⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.RingedSite

/-! ### Pseudo-coherence in all degrees along a functor with an exact localization square -/

section AllDegrees

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (u : Y.C ⥤ X.C)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (G : ∀ W : Y.C, SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⥤
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))

/-- **Pseudo-coherence in all degrees transfers along an exact additive functor with an exact
localization square.**  This is
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses` for
Stacks 08FT part (3), second clause, instead of the first: a pseudo-coherent object of `D(O')`
is by definition the image of a *single* complex which is `m`-pseudo-coherent for every `m`, and
the degreewise image of that one complex under `F` is again `m`-pseudo-coherent for every `m`, by
`isPseudoCoherentComplexFrom_mapHomologicalComplex` applied in each degree.

The six functor-level typeclass hypotheses are explicit arguments for the reason recorded at
`isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`: at a concrete pair of ringed sites they
are stated at the spelling of the structure sheaves the functors were built with, and instance
search does not cross to the `AlgebraicGeometry.RingedSite.ringSheaf` spelling. -/
theorem isPseudoCoherent_mapDerivedCategory_of_hypotheses
    (hFadd' : F.Additive) (hFlim' : PreservesFiniteLimits F)
    (hFcolim' : PreservesFiniteColimits F)
    (hGadd' : ∀ W : Y.C, (G W).Additive)
    (hGlim' : ∀ W : Y.C, PreservesFiniteLimits (G W))
    (hGcolim' : ∀ W : Y.C, PreservesFiniteColimits (G W))
    (hu' : u.IsContinuous Y.J X.J) (hTop : X.J.CoversTop u.obj)
    (ηG : ∀ W : Y.C,
      (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : ∀ W : Y.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
        F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPseudoCoherent E) :
    haveI := hFadd'
    haveI := hFlim'
    haveI := hFcolim'
    X.IsPseudoCoherent (F.mapDerivedCategory.obj E) := by
  have := hFadd'
  have := hFlim'
  have := hFcolim'
  have := hGadd'
  have := hGlim'
  have := hGcolim'
  have := hu'
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K, fun m =>
    isPseudoCoherentComplexFrom_mapHomologicalComplex u F G hTop ηG sq K m (hK m), ⟨?_⟩⟩
  exact (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e

end AllDegrees

/-! ### Pseudo-coherence in all degrees across an equivalence of ringed sites -/

section Equivalence

variable {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
    𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
  [hφ : IsIso φ]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Pseudo-coherence in all degrees transports along an equivalence of ringed sites.**  The
all-degrees companion of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`,
with the same five inputs supplied in the same way; only the degree quantifier differs. -/
theorem isPseudoCoherent_pushforwardPushforwardEquivalence_inverse
    (hTop : X.J.CoversTop eqv.functor.obj)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPseudoCoherent E) :
    X.IsPseudoCoherent
      ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
          SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
            SheafOfModules.{w}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inverse.mapDerivedCategory.obj E) :=
  isPseudoCoherent_mapDerivedCategory_of_hypotheses eqv.functor
    (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inverse
    (fun W => (Stacks.SheafOfModules.InternalHom.siteEquivModulesOver.{u, v, w, w}
      eqv φ ψ H₁ H₂ W).inverse)
    inferInstance inferInstance inferInstance
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    inferInstance hTop
    (fun W => Stacks.SheafOfModules.InternalHom.siteEquivModulesOverInverseUnitIso
      eqv φ ψ H₁ H₂ W)
    (fun W => siteEquivModulesOverInverseSquare eqv φ ψ H₁ H₂ W) E hE

/-- **Pseudo-coherence in all degrees transports along an equivalence of ringed sites, in the
form a consumer uses.**  The all-degrees companion of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_pushforwardPushforwardEquivalence_functor`:
an object of `D(O_C)` is pseudo-coherent as soon as its image under the induced equivalence of
module categories is pseudo-coherent on `(D, O_D)`.

The two actions on derived categories are cancelled against each other by
`CategoryTheory.Equivalence.mapDerivedCategoryInverseFunctorObjIso`, and the representing
complex and its isomorphism are carried across the resulting isomorphism directly, the
all-degrees clause of Stacks 08FT (3) being `∃` of exactly those two data. -/
theorem isPseudoCoherent_of_pushforwardPushforwardEquivalence_functor
    (hTop : X.J.CoversTop eqv.functor.obj)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : Y.IsPseudoCoherent
      ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
          SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
            SheafOfModules.{w}
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).functor.mapDerivedCategory.obj E)) :
    X.IsPseudoCoherent E := by
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    isPseudoCoherent_pushforwardPushforwardEquivalence_inverse eqv φ ψ H₁ H₂ hTop _ hE
  exact ⟨K, hK, ⟨e ≪≫ (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapDerivedCategoryInverseFunctorObjIso E⟩⟩

end Equivalence

/-- Pseudo-coherence, in each degree and in all degrees, is invariant under the equivalence of
module categories of an equivalence of ringed sites whose two structure maps are inverse. -/
private theorem isPseudoCoherent_pushforwardPushforwardEquivalence_functor_iff
    {X Y : RingedSite.{u, v, w}} (eqv : Y.C ≌ X.C)
    [c₁ : eqv.functor.IsContinuous Y.J X.J] [c₂ : eqv.inverse.IsContinuous X.J Y.J]
    (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
        Functor.whiskerRight (NatTrans.op eqv.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    (H₁' : Functor.whiskerRight (NatTrans.op eqv.symm.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom)
    (H₂' : ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom ≫
        Functor.whiskerRight (NatTrans.op eqv.symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    [hφ : IsIso φ] [hψ : IsIso ψ]
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
    [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] :
    (∀ (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (m : ℤ),
      Y.IsPseudoCoherentFrom
          ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).functor
            |>.mapDerivedCategory.obj E) m ↔
        X.IsPseudoCoherentFrom E m) ∧
    ∀ E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      Y.IsPseudoCoherent
          ((SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).functor
            |>.mapDerivedCategory.obj E) ↔
        X.IsPseudoCoherent E := by
  have : eqv.symm.functor.IsContinuous X.J Y.J := c₂
  have : eqv.symm.inverse.IsContinuous Y.J X.J := c₁
  have hTop := CategoryTheory.GrothendieckTopology.coversTop_functor_obj_of_equivalence eqv X.J
  have hTop' := CategoryTheory.GrothendieckTopology.coversTop_functor_obj_of_equivalence
    eqv.symm Y.J
  exact ⟨fun E m => ⟨isPseudoCoherentFrom_of_pushforwardPushforwardEquivalence_functor eqv φ ψ
      H₁ H₂ hTop E m, isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse eqv.symm ψ φ
      H₁' H₂' hTop' E m⟩, fun E => ⟨isPseudoCoherent_of_pushforwardPushforwardEquivalence_functor
      eqv φ ψ H₁ H₂ hTop E, isPseudoCoherent_pushforwardPushforwardEquivalence_inverse eqv.symm ψ φ
      H₁' H₂' hTop' E⟩⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

/-! ### The ringed sites and the two comparisons -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The sheafification data of the slices and of the iterated slices of a ringed site, derived
-- from that of its first slices; these are the `local instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, imported here
-- and re-enabled, so that they are available at the localization of the small étale ringed site
-- of an algebraic space at a chart.
attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafify RingedSite.iterWEq RingedSite.iterHasSheafifyAll
  RingedSite.iterWEqAll

variable (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- The comparison functor of Stacks 04M0 is continuous, at the spellings of the two topologies
that the localized ringed site and `AlgebraicGeometry.Space.chartRingedSite` use. -/
instance isContinuous_chartLocalization_ringedSite :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.IsContinuous
      (chartRingedSite B S hS X U).J ((smallEtaleRingedSite B S hS X.1 X.2).over U).J :=
  isContinuous_chartLocalization_chartSpace B S hS X U

/-- The inverse of the comparison equivalence of Stacks 04M0 is continuous, being a dense
subsite inclusion by
`AlgebraicGeometry.Space.isDenseSubsite_chartLocalizationEquivalence_inverse`. -/
instance isContinuous_chartLocalizationInverse_ringedSite :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J (chartRingedSite B S hS X U).J :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)

/-- **The structure map of the equivalence of ringed sites of Stacks 04M0 is the identity**, in
the orientation whose source is the small étale site of the algebraic space represented by the
chart.  Its two sides are equal sheaves of rings by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`. -/
def chartLocalizationPhi : (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) ⟶
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.sheafPushforwardContinuous
      RingCat.{u} (chartRingedSite B S hS X U).J
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O) :=
  𝟙 _

/-- **The structure map of the equivalence of ringed sites of Stacks 04M0 is the identity in the
other orientation too**, whose source is the localization of the small étale site of the space
at the chart.  Both reindexings along the comparison are equalities, for the same reason: the
comparison and its inverse leave the underlying object of the big fppf site unchanged, and
either structure sheaf is the global regular functions on it. -/
def chartLocalizationSymmPhi :
    (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O) ⟶
      ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.sheafPushforwardContinuous
        RingCat.{u} ((smallEtaleRingedSite B S hS X.1 X.2).over U).J
        (chartRingedSite B S hS X U).J).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) :=
  𝟙 _

/-- The structure map of Stacks 04M0 is invertible, being the identity. -/
instance isIso_chartLocalizationPhi : IsIso (chartLocalizationPhi B S hS X U) :=
  inferInstanceAs
    (IsIso (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O)))

/-- The structure map of Stacks 04M0 in the other orientation is invertible, being the
identity. -/
instance isIso_chartLocalizationSymmPhi : IsIso (chartLocalizationSymmPhi B S hS X U) :=
  inferInstanceAs
    (IsIso (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)))

/-- **The second compatibility of the two structure maps of Stacks 04M0.**  It is
`Stacks.SheafOfModules.InternalHom.unit_of_counit`: the first compatibility — which holds by
`rfl`, the inverse structure map being `Stacks.SheafOfModules.reindexBackSharp` — together with
invertibility of the first structure map already determines it. -/
theorem chartLocalizationPhi_unit :
    (chartLocalizationPhi B S hS X U).hom ≫
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.op.whiskerLeft
          (@Stacks.SheafOfModules.reindexBackSharp _ _ _ _ _
            (chartRingedSite B S hS X U).J
            (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
            (isContinuous_chartLocalization_ringedSite B S hS X U)
            (isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
            (Stacks.SheafOfModules.Tensor.ringSheaf
              ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)).hom ≫
        Functor.whiskerRight
          (NatTrans.op (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O).obj :=
  @Stacks.SheafOfModules.InternalHom.unit_of_counit.{u + 1, u, u}
    ((smallEtaleRingedSite B S hS X.1 X.2).over U) (chartRingedSite B S hS X U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_ringedSite B S hS X U)
    (isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
    (chartLocalizationPhi B S hS X U) (isIso_chartLocalizationPhi B S hS X U) _ rfl

/-- **The second compatibility of the two structure maps of Stacks 04M0, in the other
orientation.**  Again `Stacks.SheafOfModules.InternalHom.unit_of_counit`. -/
theorem chartLocalizationSymmPhi_unit :
    (chartLocalizationSymmPhi B S hS X U).hom ≫
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.op.whiskerLeft
          (@Stacks.SheafOfModules.reindexBackSharp _ _ _ _ _
            ((smallEtaleRingedSite B S hS X.1 X.2).over U).J
            (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm
            (isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
            (isContinuous_chartLocalization_ringedSite B S hS X U)
            (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O)).hom ≫
        Functor.whiskerRight
          (NatTrans.op (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).obj :=
  @Stacks.SheafOfModules.InternalHom.unit_of_counit.{u + 1, u, u}
    (chartRingedSite B S hS X U) ((smallEtaleRingedSite B S hS X.1 X.2).over U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm
    (isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
    (isContinuous_chartLocalization_ringedSite B S hS X U)
    (chartLocalizationSymmPhi B S hS X U) (isIso_chartLocalizationSymmPhi B S hS X U) _ rfl

/-! ### Pseudo-coherence across Stacks 04M0 -/

/-- Sheafification on the localization of the small étale ringed site at a chart, at the
spelling `(X.over U).J` of the localized topology: this is
`AlgebraicGeometry.RingedSite.sliceHasSheafify`, applied explicitly because its ringed site
occurs in its conclusion only through the projections `.J` and `.C`, which instance search
cannot invert. -/
local instance hasSheafify_chartLocalization :
    HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).over U).J AddCommGrpCat.{u} :=
  RingedSite.sliceHasSheafify (smallEtaleRingedSite B S hS X.1 X.2) U

/-- Local bijectivity of the weak equivalences on the localization at a chart, at the localized
spelling, for the reason recorded at `hasSheafify_chartLocalization`. -/
local instance wEqualsLocallyBijective_chartLocalization :
    ((smallEtaleRingedSite B S hS X.1 X.2).over U).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  RingedSite.sliceWEqualsLocallyBijective (smallEtaleRingedSite B S hS X.1 X.2) U

/-- Sheafification on the iterated slices of the localization at a chart: this is
`AlgebraicGeometry.RingedSite.iterHasSheafifyAll`, which derives it from the data of the first
slices along `CategoryTheory.Over.iteratedSliceEquiv`, applied explicitly. -/
local instance hasSheafify_over_chartLocalization :
    ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      HasSheafify (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W)
        AddCommGrpCat.{u} :=
  RingedSite.iterHasSheafifyAll (smallEtaleRingedSite B S hS X.1 X.2) U

/-- Local bijectivity of the weak equivalences on the iterated slices of the localization at a
chart: `AlgebraicGeometry.RingedSite.iterWEqAll`, applied explicitly. -/
local instance wEqualsLocallyBijective_over_chartLocalization :
    ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  RingedSite.iterWEqAll (smallEtaleRingedSite B S hS X.1 X.2) U

/-- Sheafification on the iterated slices of the localization at a chart, in the weak form the
sheaves-of-modules API asks for.  Instance search does not turn a `∀`-quantified strong form
into a `∀`-quantified weak one, so the two are restated separately. -/
local instance hasWeakSheafify_over_chartLocalization :
    ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      HasWeakSheafify (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W)
        AddCommGrpCat.{u} :=
  fun _ => inferInstance

/-- The `𝒪_X|_U`-modules on the localization of the small étale site at a chart form an abelian
category, at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling of the localized sheaf of
rings. -/
local instance abelian_chartLocalizationModules :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)) :=
  inferInstanceAs (Abelian (SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)))

/-- The `𝒪`-modules on the small étale site of the algebraic space represented by a chart form
an abelian category, at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling. -/
local instance abelian_chartModules :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O)) :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (chartStructureRingSheaf B S hS X U)))

/-- **The equivalence of module categories of Stacks 04M0.**  The `𝒪_X|_U`-modules on the
localization of the small étale site of `X` at an étale scheme chart `U` are the `𝒪`-modules on
the small étale site of the algebraic space represented by `U`.

This is `Stacks.SheafOfModules.reindexEquivalence` at the equivalence of sites of Stacks 04M0,
available because the two structure sheaves agree on the nose by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`; no second encoding of it is
introduced here.  The arguments are passed positionally because the continuity of the comparison
is not found by synthesis at the spellings of the two topologies that the ringed sites use. -/
noncomputable abbrev chartLocalizationModulesEquivalence :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) :=
  @Stacks.SheafOfModules.reindexEquivalence _ _ _ _ _ _
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_ringedSite B S hS X U)
    (isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
    (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)

/-- **Reindexing along the comparison of Stacks 04M0.**  An `𝒪_X|_U`-module on the localization
of the small étale site of `X` at an étale scheme chart `U`, read as an `𝒪`-module on the small
étale site of the algebraic space represented by `U`.  It is
`SheafOfModules.pushforward` of the identity structure map
`AlgebraicGeometry.Space.chartLocalizationPhi`, by
`Stacks.SheafOfModules.reindexEquivalence_functor`. -/
noncomputable abbrev chartLocalizationReindex :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) :=
  (chartLocalizationModulesEquivalence B S hS X U).functor

/-- Reindexing along the comparison of Stacks 04M0 is additive: a pushforward of sheaves of
modules acts on a morphism by acting on its underlying map of presheaves. -/
local instance additive_chartLocalizationReindex :
    (chartLocalizationReindex B S hS X U).Additive where
  map_add := by intros; rfl

/-- **`m`-pseudo-coherence crosses the equivalence of Stacks 04M0, in both directions.**  Let `U`
be an étale scheme chart of an algebraic space `X` and let `E` be an object of the derived
category of `𝒪_X|_U`-modules on the localization `X_étale/U`.  Then `E` is `m`-pseudo-coherent
there exactly when its reindexing along the comparison of Stacks 04M0 is `m`-pseudo-coherent on
the small étale site of the algebraic space represented by `U`.

The reindexing functor is `SheafOfModules.pushforward` of the structure map
`AlgebraicGeometry.Space.chartLocalizationPhi`, which is the identity; it is the functor of
`Stacks.SheafOfModules.reindexEquivalence` at the equivalence of sites of Stacks 04M0, by
`Stacks.SheafOfModules.reindexEquivalence_functor`.

Both implications are
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`
and its consumer form, taken in the two orientations of the comparison: that transport concludes
about the *target* of the equivalence of sites it is given, so the implication into the chart is
taken at the symmetric equivalence.  That the same functor appears in both is the point of
`AlgebraicGeometry.Space.chartLocalizationSymmPhi` being the identity as well: the inverse
structure map of either orientation is `Stacks.SheafOfModules.reindexBackSharp`, which reduces
to the identity here, so the inverse transport of the symmetric orientation *is* the forward
reindexing. -/
theorem isPseudoCoherentFrom_chartLocalizationReindex_iff
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O))]
    (E : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)))
    (m : ℤ) :
    (chartRingedSite B S hS X U).IsPseudoCoherentFrom
        ((chartLocalizationReindex B S hS X U).mapDerivedCategory.obj E) m ↔
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).IsPseudoCoherentFrom E m :=
  (RingedSite.isPseudoCoherent_pushforwardPushforwardEquivalence_functor_iff.{u + 1, u, u, d, d}
    (X := (smallEtaleRingedSite B S hS X.1 X.2).over U) (Y := chartRingedSite B S hS X U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (c₁ := isContinuous_chartLocalization_ringedSite B S hS X U)
    (c₂ := isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
    (chartLocalizationPhi B S hS X U) _ rfl (chartLocalizationPhi_unit B S hS X U) rfl
    (chartLocalizationSymmPhi_unit B S hS X U) (hφ := isIso_chartLocalizationPhi B S hS X U)
    (hψ := isIso_chartLocalizationSymmPhi B S hS X U)).1 E m

/-- **Pseudo-coherence in all degrees crosses the equivalence of Stacks 04M0, in both
directions.**  The all-degrees companion of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_chartLocalizationReindex_iff`: an object of the
derived category of `𝒪_X|_U`-modules on the localization `X_étale/U` is pseudo-coherent exactly
when its reindexing along the comparison of Stacks 04M0 is pseudo-coherent on the small étale
site of the algebraic space represented by `U`.

Not deduced degree by degree from the previous theorem — the all-degrees clause of Stacks 08FT
(3) asks for a *single* complex which is `m`-pseudo-coherent for every `m`, which a family of
degreewise statements does not provide — but proved by the all-degrees transports
`AlgebraicGeometry.RingedSite.isPseudoCoherent_pushforwardPushforwardEquivalence_inverse` and
`...isPseudoCoherent_of_pushforwardPushforwardEquivalence_functor`, which carry that one complex
across. -/
theorem isPseudoCoherent_chartLocalizationReindex_iff
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O))]
    (E : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS X.1 X.2).over U).O))) :
    (chartRingedSite B S hS X U).IsPseudoCoherent
        ((chartLocalizationReindex B S hS X U).mapDerivedCategory.obj E) ↔
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).IsPseudoCoherent E :=
  (RingedSite.isPseudoCoherent_pushforwardPushforwardEquivalence_functor_iff.{u + 1, u, u, d, d}
    (X := (smallEtaleRingedSite B S hS X.1 X.2).over U) (Y := chartRingedSite B S hS X U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (c₁ := isContinuous_chartLocalization_ringedSite B S hS X U)
    (c₂ := isContinuous_chartLocalizationInverse_ringedSite B S hS X U)
    (chartLocalizationPhi B S hS X U) _ rfl (chartLocalizationPhi_unit B S hS X U) rfl
    (chartLocalizationSymmPhi_unit B S hS X U) (hφ := isIso_chartLocalizationPhi B S hS X U)
    (hψ := isIso_chartLocalizationSymmPhi B S hS X U)).2 E


/-! ### The small étale site of a representable algebraic space and of its scheme -/

variable (V : BigFppfOver B S hS)

/-- The small étale ringed site of the algebraic space represented by an object `V` of the big
fppf site over `S`. -/
noncomputable abbrev representedRingedSite : RingedSite.{u + 1, u, u} :=
  smallEtaleRingedSite B S hS (yoneda.obj V)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V)

/-- The small étale ringed site of the *scheme* underlying an object `V` of the big fppf site
over `S`, taken in the big étale site carried by the same category of schemes. -/
noncomputable abbrev representedSchemeRingedSite : RingedSite.{u + 1, u, u} :=
  AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj V) V.left.property

/-- The comparison functor of `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` is
continuous, at the spellings of the two topologies that the two ringed sites use. -/
instance isContinuous_representedSmallEtale_ringedSite :
    (representedSmallEtaleEquivalence B S hS V).functor.IsContinuous
      (representedRingedSite B S hS V).J (representedSchemeRingedSite B S hS V).J :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS V).functor.IsContinuous
    (SmallEtale.topology B S hS (yoneda.obj V))
    (representedSchemeSmallEtaleTopology B S hS V))

/-- The inverse of `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` is continuous,
being a dense subsite inclusion by
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse`. -/
instance isContinuous_representedSmallEtaleInverse_ringedSite :
    (representedSmallEtaleEquivalence B S hS V).inverse.IsContinuous
      (representedSchemeRingedSite B S hS V).J (representedRingedSite B S hS V).J :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS V).inverse.IsContinuous
    (representedSchemeSmallEtaleTopology B S hS V)
    (SmallEtale.topology B S hS (yoneda.obj V)))

/-- **The structure map of the comparison of the two small étale ringed sites is the identity**,
in the orientation whose source is the site of the representable algebraic space.  Its two sides
are equal sheaves of rings by
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`. -/
def representedSmallEtalePhi :
    (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O) ⟶
      ((representedSmallEtaleEquivalence B S hS V).functor.sheafPushforwardContinuous
        RingCat.{u} (representedRingedSite B S hS V).J
        (representedSchemeRingedSite B S hS V).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O) :=
  𝟙 _

/-- **The structure map of the comparison is the identity in the other orientation too**, whose
source is the small étale site of the scheme underlying `V`.  Both reindexings along the
comparison are equalities, for the same reason: neither functor of the comparison changes the
underlying scheme, and either structure sheaf is the global regular functions on it. -/
def representedSmallEtaleSymmPhi :
    (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O) ⟶
      ((representedSmallEtaleEquivalence B S hS V).inverse.sheafPushforwardContinuous
        RingCat.{u} (representedSchemeRingedSite B S hS V).J
        (representedRingedSite B S hS V).J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O) :=
  𝟙 _

/-- The structure map of the comparison is invertible, being the identity. -/
instance isIso_representedSmallEtalePhi : IsIso (representedSmallEtalePhi B S hS V) :=
  inferInstanceAs
    (IsIso (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O)))

/-- The structure map of the comparison in the other orientation is invertible, being the
identity. -/
instance isIso_representedSmallEtaleSymmPhi :
    IsIso (representedSmallEtaleSymmPhi B S hS V) :=
  inferInstanceAs
    (IsIso (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O)))

/-- **The first compatibility of the two structure maps of the comparison.**  With both of them
the identity it says that the structure sheaf of the small étale site of the scheme underlying
`V` carries the counit of the comparison to the identity, which it does because the comparison
does not change the underlying scheme of an object. -/
theorem representedSmallEtalePhi_counit :
    Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS V).counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O).obj =
      (representedSmallEtaleSymmPhi B S hS V).hom ≫
        (representedSmallEtaleEquivalence B S hS V).inverse.op.whiskerLeft
          (representedSmallEtalePhi B S hS V).hom :=
  rfl

/-- **The second compatibility of the two structure maps of the comparison.**  It is
`Stacks.SheafOfModules.InternalHom.unit_of_counit`: the first compatibility together with
invertibility of the first structure map already determines it. -/
theorem representedSmallEtalePhi_unit :
    (representedSmallEtalePhi B S hS V).hom ≫
        (representedSmallEtaleEquivalence B S hS V).functor.op.whiskerLeft
          (representedSmallEtaleSymmPhi B S hS V).hom ≫
        Functor.whiskerRight
          (NatTrans.op (representedSmallEtaleEquivalence B S hS V).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O).obj :=
  @Stacks.SheafOfModules.InternalHom.unit_of_counit.{u + 1, u, u}
    (representedSchemeRingedSite B S hS V) (representedRingedSite B S hS V)
    (representedSmallEtaleEquivalence B S hS V)
    (isContinuous_representedSmallEtale_ringedSite B S hS V)
    (isContinuous_representedSmallEtaleInverse_ringedSite B S hS V)
    (representedSmallEtalePhi B S hS V) (isIso_representedSmallEtalePhi B S hS V)
    (representedSmallEtaleSymmPhi B S hS V) (representedSmallEtalePhi_counit B S hS V)

/-- **The first compatibility of the two structure maps of the comparison, in the other
orientation**, for the same reason as `representedSmallEtalePhi_counit`. -/
theorem representedSmallEtaleSymmPhi_counit :
    Functor.whiskerRight
        (NatTrans.op (representedSmallEtaleEquivalence B S hS V).symm.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O).obj =
      (representedSmallEtalePhi B S hS V).hom ≫
        (representedSmallEtaleEquivalence B S hS V).functor.op.whiskerLeft
          (representedSmallEtaleSymmPhi B S hS V).hom :=
  rfl

/-- **The second compatibility of the two structure maps of the comparison, in the other
orientation.**  Again `Stacks.SheafOfModules.InternalHom.unit_of_counit`. -/
theorem representedSmallEtaleSymmPhi_unit :
    (representedSmallEtaleSymmPhi B S hS V).hom ≫
        (representedSmallEtaleEquivalence B S hS V).inverse.op.whiskerLeft
          (representedSmallEtalePhi B S hS V).hom ≫
        Functor.whiskerRight
          (NatTrans.op (representedSmallEtaleEquivalence B S hS V).symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O).obj :=
  @Stacks.SheafOfModules.InternalHom.unit_of_counit.{u + 1, u, u}
    (representedRingedSite B S hS V) (representedSchemeRingedSite B S hS V)
    (representedSmallEtaleEquivalence B S hS V).symm
    (isContinuous_representedSmallEtaleInverse_ringedSite B S hS V)
    (isContinuous_representedSmallEtale_ringedSite B S hS V)
    (representedSmallEtaleSymmPhi B S hS V)
    (isIso_representedSmallEtaleSymmPhi B S hS V)
    (representedSmallEtalePhi B S hS V) (representedSmallEtaleSymmPhi_counit B S hS V)

/-- **The equivalence of module categories of the comparison.**  The modules on the small étale
site of the scheme underlying `V` are the `𝒪`-modules on the small étale site of the algebraic
space represented by `V`.

This is `SheafOfModules.pushforwardPushforwardEquivalence` at
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` with both structure maps the
identity, which is `Stacks.SheafOfModules.reindexEquivalence` there — the inverse structure map
of that construction, `Stacks.SheafOfModules.reindexBackSharp`, being the identity here. -/
noncomputable abbrev representedSchemeModulesEquivalence :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O) ≌
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O) :=
  SheafOfModules.pushforwardPushforwardEquivalence
    (representedSmallEtaleEquivalence B S hS V)
    (representedSmallEtalePhi B S hS V) (representedSmallEtaleSymmPhi B S hS V)
    (representedSmallEtalePhi_counit B S hS V) (representedSmallEtalePhi_unit B S hS V)

/-- **Reindexing along the comparison.**  An `𝒪`-module on the small étale site of the algebraic
space represented by `V`, read as a module on the small étale site of the scheme underlying
`V`. -/
noncomputable abbrev representedSchemeReindex :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O) :=
  (representedSchemeModulesEquivalence B S hS V).inverse

/-- Reindexing along the comparison is additive: a pushforward of sheaves of modules acts on a
morphism by acting on its underlying map of presheaves. -/
local instance additive_representedSchemeReindex :
    (representedSchemeReindex B S hS V).Additive where
  map_add := by intros; rfl

/-- The `𝒪`-modules on the small étale site of a representable algebraic space form an abelian
category, at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling. -/
local instance abelian_representedModules :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O)) :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (representedStructureRingSheaf B S hS V)))

/-- The modules on the small étale site of the scheme underlying `V` form an abelian category,
at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling. -/
local instance abelian_representedSchemeModules :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O)) :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS V)))

/-- **`m`-pseudo-coherence crosses the comparison between the small étale site of a representable
algebraic space and the small étale site of its scheme, in both directions.**  An object `F` of
the derived category of `𝒪`-modules on the small étale site of the algebraic space represented by
`V` is `m`-pseudo-coherent exactly when its reindexing is `m`-pseudo-coherent on the small étale
site of the scheme underlying `V`.

As for Stacks 04M0, both implications are
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`
and its consumer form, taken in the two orientations of the comparison; the same functor appears
in both because both structure maps are the identity. -/
theorem isPseudoCoherentFrom_representedSchemeReindex_iff
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O))]
    (F : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O)))
    (m : ℤ) :
    (representedSchemeRingedSite B S hS V).IsPseudoCoherentFrom
        ((representedSchemeReindex B S hS V).mapDerivedCategory.obj F) m ↔
      (representedRingedSite B S hS V).IsPseudoCoherentFrom F m :=
  (RingedSite.isPseudoCoherent_pushforwardPushforwardEquivalence_functor_iff.{u + 1, u, u, d, d}
    (X := representedRingedSite B S hS V) (Y := representedSchemeRingedSite B S hS V)
    (representedSmallEtaleEquivalence B S hS V).symm
    (c₁ := isContinuous_representedSmallEtaleInverse_ringedSite B S hS V)
    (c₂ := isContinuous_representedSmallEtale_ringedSite B S hS V)
    (representedSmallEtaleSymmPhi B S hS V) (representedSmallEtalePhi B S hS V)
    (representedSmallEtaleSymmPhi_counit B S hS V) (representedSmallEtaleSymmPhi_unit B S hS V)
    (representedSmallEtalePhi_counit B S hS V) (representedSmallEtalePhi_unit B S hS V)
    (hφ := isIso_representedSmallEtaleSymmPhi B S hS V)
    (hψ := isIso_representedSmallEtalePhi B S hS V)).1 F m

/-- **Pseudo-coherence in all degrees crosses the comparison between the small étale site of a
representable algebraic space and the small étale site of its scheme, in both directions.**
The all-degrees companion of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_representedSchemeReindex_iff`, proved by the
all-degrees transports rather than degree by degree, for the reason recorded at
`AlgebraicGeometry.Space.isPseudoCoherent_chartLocalizationReindex_iff`. -/
theorem isPseudoCoherent_representedSchemeReindex_iff
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O))]
    (F : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O))) :
    (representedSchemeRingedSite B S hS V).IsPseudoCoherent
        ((representedSchemeReindex B S hS V).mapDerivedCategory.obj F) ↔
      (representedRingedSite B S hS V).IsPseudoCoherent F :=
  (RingedSite.isPseudoCoherent_pushforwardPushforwardEquivalence_functor_iff.{u + 1, u, u, d, d}
    (X := representedRingedSite B S hS V) (Y := representedSchemeRingedSite B S hS V)
    (representedSmallEtaleEquivalence B S hS V).symm
    (c₁ := isContinuous_representedSmallEtaleInverse_ringedSite B S hS V)
    (c₂ := isContinuous_representedSmallEtale_ringedSite B S hS V)
    (representedSmallEtaleSymmPhi B S hS V) (representedSmallEtalePhi B S hS V)
    (representedSmallEtaleSymmPhi_counit B S hS V) (representedSmallEtaleSymmPhi_unit B S hS V)
    (representedSmallEtalePhi_counit B S hS V) (representedSmallEtalePhi_unit B S hS V)
    (hφ := isIso_representedSmallEtaleSymmPhi B S hS V)
    (hψ := isIso_representedSmallEtalePhi B S hS V)).2 F


/-! ### The two comparisons composed: the slice at a chart and the chart's scheme -/

/-- **The algebraic space represented by an étale scheme chart is the Yoneda algebraic space of
the chart's object**, so the small étale ringed site of the chart space and the small étale
ringed site of the representable algebraic space of its object are *the same* ringed site.  This
is `AlgebraicGeometry.Space.chartSpace_eq_yoneda`, which is an `rfl`; the algebraicity
hypotheses are propositions, so the two structure instances agree. -/
theorem chartRingedSite_eq_representedRingedSite :
    chartRingedSite B S hS X U =
      representedRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U) :=
  rfl

/-- A derived-category model for the `𝒪`-modules on the small étale site of the representable
algebraic space of a chart's object, read off the one for the chart space; the two ringed sites
are equal by `AlgebraicGeometry.Space.chartRingedSite_eq_representedRingedSite`, but instance
search does not cross between the two spellings. -/
local instance hasDerivedCategory_representedRingedSite_ofChart
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O))] :
    HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (representedRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).O)) :=
  inferInstanceAs
    (HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O)))

/-- **`m`-pseudo-coherence crosses both represented-space comparisons at once, in both
directions.**  Let `U` be an étale scheme chart of an algebraic space `X`.  An object `E` of the
derived category of `𝒪_X|_U`-modules on the localization `X_étale/U` is `m`-pseudo-coherent
there exactly when its reindexing — first along Stacks 04M0 to the small étale site of the
algebraic space represented by `U`, then along
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` to the small étale site of the
*scheme* underlying `U` — is `m`-pseudo-coherent there.

This is the composite of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_chartLocalizationReindex_iff` with
`AlgebraicGeometry.Space.isPseudoCoherentFrom_representedSchemeReindex_iff` at the chart's
object; the two meet because the chart space *is* the Yoneda algebraic space of that object,
`AlgebraicGeometry.Space.chartRingedSite_eq_representedRingedSite`. -/
theorem isPseudoCoherentFrom_chartSchemeReindex_iff
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O))]
    [HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).O))]
    (E : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)))
    (m : ℤ) :
    (representedSchemeRingedSite B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).IsPseudoCoherentFrom
        ((representedSchemeReindex B S hS
            ((SmallEtale.toOver B S hS X.1).obj U)).mapDerivedCategory.obj
          ((chartLocalizationReindex B S hS X U).mapDerivedCategory.obj E)) m ↔
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).IsPseudoCoherentFrom E m :=
  (isPseudoCoherentFrom_representedSchemeReindex_iff B S hS
      ((SmallEtale.toOver B S hS X.1).obj U) _ m).trans
    (isPseudoCoherentFrom_chartLocalizationReindex_iff B S hS X U E m)

/-- **Pseudo-coherence in all degrees crosses both represented-space comparisons at once, in both
directions.**  The all-degrees companion of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff`, composed from the
all-degrees halves in the same way. -/
theorem isPseudoCoherent_chartSchemeReindex_iff
    [HasDerivedCategory.{d}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O))]
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O))]
    [HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).O))]
    (E : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS X.1 X.2).over U).O))) :
    (representedSchemeRingedSite B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).IsPseudoCoherent
        ((representedSchemeReindex B S hS
            ((SmallEtale.toOver B S hS X.1).obj U)).mapDerivedCategory.obj
          ((chartLocalizationReindex B S hS X U).mapDerivedCategory.obj E)) ↔
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).IsPseudoCoherent E :=
  (isPseudoCoherent_representedSchemeReindex_iff B S hS
      ((SmallEtale.toOver B S hS X.1).obj U) _).trans
    (isPseudoCoherent_chartLocalizationReindex_iff B S hS X U E)

end AlgebraicGeometry.Space

end
