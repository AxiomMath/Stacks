module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.LocallyQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# The finite part of a separated morphism locally of finite type

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is separated and
locally of finite type. Then the finite part `(X/Y)_fin` of `f` is an algebraic space over `S`
and its projection to `Y` is étale. This is Stacks 04QH.

## Main results

* `AlgebraicGeometry.Space.exists_chart_finiteOpenSubspacePresheaf_of_exists_chart`: an étale
  chart of the finite part of the maximal locally quasi-finite part of `f` is an étale chart of
  the finite part of `f` itself, whose composite with the projection to `Y` is étale.
* `AlgebraicGeometry.Space.isAlgebraicSpace_finiteOpenSubspacePresheaf_of_diagonal_of_chart`:
  the first conclusion of Stacks 04QH.
* `AlgebraicGeometry.Space.isEtale_baseMap_finiteOpenSubspacePresheaf_of_diagonal_of_chart`:
  the second conclusion of Stacks 04QH.
* `AlgebraicGeometry.Space.isSeparated_and_isLocallyQuasiFinite_locallyQuasiFinitePart`: the
  restriction of `f` to the maximal locally quasi-finite open subspace of its source is
  separated and locally quasi-finite.
* `AlgebraicGeometry.Space.isAlgebraicSpace_finiteOpenSubspacePresheaf` and
  `AlgebraicGeometry.Space.isEtale_baseMap_finiteOpenSubspacePresheaf` — Stacks 04QH: the two
  conclusions, with no hypotheses beyond separatedness and local finiteness of type.

## Implementation notes

The two conclusions are first proved from two inputs of the source's argument taken as
hypotheses, `hdiag` and `hchart`: the representability of the absolute diagonal of
`(X/Y)_fin`, which is Stacks 04PK, and the existence of a surjective étale chart of
`(X/Y)_fin` by a scheme étale over `Y` for a separated locally quasi-finite morphism, which is
Stacks 04QG. Both inputs are theorems of this library, so the hypotheses are discharged and
the two unconditional forms carry the tag; the conditional forms are kept because they are
what the argument actually uses.

The chart hypothesis is asked for at the restriction `f'` of
`f` to the maximal locally quasi-finite open subspace of its source, which is the morphism to
which the source applies Stacks 04QG: that restriction is separated, being the composite of an
open immersion with `f`, and locally quasi-finite by Stacks 04NW, and its finite part is
identified with that of `f` by Stacks 04PG. The identification carries the chart over and is
compatible with the two projections to `Y`, which is what makes the composite with the
projection étale; étaleness of the projection is then Stacks 03FS, condition (2).

## References

* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PF](https://stacks.math.columbia.edu/tag/04PF)
* [Stacks Project, Tag 04PG](https://stacks.math.columbia.edu/tag/04PG)
* [Stacks Project, Tag 04PK](https://stacks.math.columbia.edu/tag/04PK)
* [Stacks Project, Tag 04QG](https://stacks.math.columbia.edu/tag/04QG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open immersion of algebraic spaces over `S` is separated: each of its represented base
changes is an open immersion of schemes, hence separated. -/
private theorem isSeparated_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {j : F ⟶ G} (hj : IsOpenImmersion B S hS j) :
    IsSeparated B S hS j := by
  refine (isSeparated_iff_presheaf B S hS j hF hG hj.1).2 ⟨hj.1, fun T V g fst snd hs => ?_⟩
  change _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map snd)
  have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map snd) :=
    hj.2 g fst snd hs
  infer_instance

/-- The canonical map of Stacks 04PF between finite parts commutes with the two projections
to `Y`. -/
private theorem finiteOpenSubspaceMap_comp_baseMap {X' X Y : AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y) (hjf : j ≫ f = f')
    (hj : IsOpenImmersion B S hS j.hom) :
    (finiteOpenSubspaceMap B S hS j f' f hjf hj).1 ≫
        (finiteOpenSubspacePresheaf B S hS f).baseMap =
      (finiteOpenSubspacePresheaf B S hS f').baseMap := by
  ext T x
  apply yonedaEquiv.symm.injective
  change yonedaEquiv.symm ((finiteOpenSubspacePresheaf B S hS f).baseMap.app T
      ((finiteOpenSubspaceMap B S hS j f' f hjf hj).1.app T x)) =
    yonedaEquiv.symm ((finiteOpenSubspacePresheaf B S hS f').baseMap.app T x)
  rw [(finiteOpenSubspacePresheaf B S hS f).baseMap_spec T.unop,
    (finiteOpenSubspacePresheaf B S hS f').baseMap_spec T.unop]
  exact (congrArg (fun t => t.hom)
    ((finiteOpenSubspaceMap B S hS j f' f hjf hj).2.2 T.unop x).1).symm

/-- An étale chart of the finite part of the restriction of `f` to the maximal locally
quasi-finite open subspace of its source is an étale chart of the finite part of `f`, and its
composite with the projection of `(X/Y)_fin` to `Y` is again étale.

The hypothesis is Stacks 04QG for that restriction; the transport is the isomorphism of
Stacks 04PG, which is the canonical map of Stacks 04PF and therefore commutes with the two
projections to `Y`. -/
theorem exists_chart_finiteOpenSubspacePresheaf_of_exists_chart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hchart : ∃ (V : BigFppfOver B S hS)
      (p : yoneda.obj V ⟶ (finiteOpenSubspacePresheaf B S hS
        (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).toFunctor),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (finiteOpenSubspacePresheaf B S hS
            (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).baseMap) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p) :
    ∃ (V : BigFppfOver B S hS)
      (q : yoneda.obj V ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsEtale B S hS (q ≫ (finiteOpenSubspacePresheaf B S hS f).baseMap) := by
  obtain ⟨V, p, hpcomp, hpsurj, hpetale⟩ := hchart
  let e := finitePartIsoLocallyQuasiFinitePart B S hS f hf
  have hcomm : e.hom ≫ (finiteOpenSubspacePresheaf B S hS f).baseMap = _ :=
    finiteOpenSubspaceMap_comp_baseMap B S hS _ _ f rfl
      (isOpenImmersion_locallyQuasiFinitePartInclusion B S hS f hf)
  refine ⟨V, p ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom p hpsurj,
    MorphismProperty.RespectsIso.postcomp _ e.hom p hpetale, fun T φ hφ => ?_⟩
  have : MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Etale.{u} :=
    ⟨fun a b (_ : AlgebraicGeometry.Etale a) (_ : AlgebraicGeometry.Etale b) =>
      AlgebraicGeometry.Etale.etale_comp b (f := a)⟩
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  simpa only [Category.assoc, hcomm] using MorphismProperty.comp_mem _ _ _ hφ hpcomp

/-- **Stacks 04QH, the first conclusion, conditional on Stacks 04PK and Stacks 04QG.** The
finite part `(X/Y)_fin` of a separated morphism `f : X ⟶ Y` of algebraic spaces over `S` which
is locally of finite type is an algebraic space over `S`, given the representability of its
absolute diagonal and an étale chart of the finite part of the restriction of `f` to the
maximal locally quasi-finite open subspace of its source. -/
theorem isAlgebraicSpace_finiteOpenSubspacePresheaf_of_diagonal_of_chart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (_hsep : IsSeparated B S hS f.hom) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hdiag : yoneda.relativelyRepresentable
      (diag (finiteOpenSubspacePresheaf B S hS f).toFunctor))
    (hchart : ∃ (V : BigFppfOver B S hS)
      (p : yoneda.obj V ⟶ (finiteOpenSubspacePresheaf B S hS
        (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).toFunctor),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (finiteOpenSubspacePresheaf B S hS
            (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).baseMap) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p) :
    IsAlgebraicSpace B S hS (finiteOpenSubspacePresheaf B S hS f).toFunctor := by
  refine ⟨isSheaf_finiteOpenSubspacePresheaf B S hS f, hdiag, ?_⟩
  obtain ⟨V, q, hq, hqe, _⟩ :=
    exists_chart_finiteOpenSubspacePresheaf_of_exists_chart B S hS f hf hchart
  exact ⟨V, q, hq, hqe⟩

/-- **Stacks 04QH, the second conclusion, conditional on Stacks 04PK and Stacks 04QG.** The
projection `(X/Y)_fin ⟶ Y` of the finite part of a separated morphism `f : X ⟶ Y` of algebraic
spaces over `S` which is locally of finite type is étale, given the representability of the
absolute diagonal of `(X/Y)_fin` and an étale chart of the finite part of the restriction of
`f` to the maximal locally quasi-finite open subspace of its source. -/
theorem isEtale_baseMap_finiteOpenSubspacePresheaf_of_diagonal_of_chart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hdiag : yoneda.relativelyRepresentable
      (diag (finiteOpenSubspacePresheaf B S hS f).toFunctor))
    (hchart : ∃ (V : BigFppfOver B S hS)
      (p : yoneda.obj V ⟶ (finiteOpenSubspacePresheaf B S hS
        (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).toFunctor),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (finiteOpenSubspacePresheaf B S hS
            (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).baseMap) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p) :
    IsEtale B S hS (finiteOpenSubspacePresheaf B S hS f).baseMap :=
  (isEtale_iff_exists_source_chart B S hS
    (isAlgebraicSpace_finiteOpenSubspacePresheaf_of_diagonal_of_chart B S hS f hsep hf hdiag
      hchart)
    Y.property (finiteOpenSubspacePresheaf B S hS f).baseMap).2
    (exists_chart_finiteOpenSubspacePresheaf_of_exists_chart B S hS f hf hchart)

/-- The restriction of a separated morphism of algebraic spaces over `S` which is locally of
finite type to the maximal locally quasi-finite open subspace of its source is separated and
locally quasi-finite, so that Stacks 04QG applies to it.

This is the hypothesis `hchart` of
`AlgebraicGeometry.Space.isAlgebraicSpace_finiteOpenSubspacePresheaf_of_diagonal_of_chart`
reduced to Stacks 04QG as the source states it. -/
theorem isSeparated_and_isLocallyQuasiFinite_locallyQuasiFinitePart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsSeparated B S hS (locallyQuasiFinitePartInclusion B S hS f hf ≫ f).hom ∧
      IsLocallyQuasiFinite B S hS
        (locallyQuasiFinitePartInclusion B S hS f hf ≫ f).hom :=
  ⟨isSeparated_comp B S hS (locallyQuasiFinitePartInclusion B S hS f hf).hom f.hom
      (isSeparated_of_isOpenImmersion B S hS
        (locallyQuasiFinitePartSpace B S hS f hf).property X.property
        (isOpenImmersion_locallyQuasiFinitePartInclusion B S hS f hf)) hsep,
    isLocallyQuasiFinite_locallyQuasiFinitePart B S hS X.property Y.property f.hom hf⟩

/-- The étale chart of Stacks 04QG for the restriction of `f` to the maximal locally
quasi-finite open subspace of its source, which is separated and locally quasi-finite. -/
private theorem exists_chart_locallyQuasiFinitePart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    ∃ (V : BigFppfOver B S hS)
      (p : yoneda.obj V ⟶ (finiteOpenSubspacePresheaf B S hS
        (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).toFunctor),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
          (p ≫ (finiteOpenSubspacePresheaf B S hS
            (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).baseMap) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p :=
  exists_surjective_etale_chart_finiteOpenSubspacePresheaf B S hS
    (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)
    (isSeparated_and_isLocallyQuasiFinite_locallyQuasiFinitePart B S hS f hsep hf).1
    (isSeparated_and_isLocallyQuasiFinite_locallyQuasiFinitePart B S hS f hsep hf).2

/-- **Stacks 04QH, the first conclusion.** The finite part `(X/Y)_fin` of a separated morphism
`f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite type is an algebraic space
over `S`. -/
@[stacks 04QH "(X/Y)_fin is an algebraic space"]
theorem isAlgebraicSpace_finiteOpenSubspacePresheaf
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsAlgebraicSpace B S hS (finiteOpenSubspacePresheaf B S hS f).toFunctor :=
  isAlgebraicSpace_finiteOpenSubspacePresheaf_of_diagonal_of_chart B S hS f hsep hf
    (relativelyRepresentable_diag_finiteOpenSubspacePresheaf B S hS f)
    (exists_chart_locallyQuasiFinitePart B S hS f hsep hf)

/-- **Stacks 04QH, the second conclusion.** The projection `(X/Y)_fin ⟶ Y` of the finite part
of a separated morphism `f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite
type is étale. -/
@[stacks 04QH "(X/Y)_fin → Y is étale"]
theorem isEtale_baseMap_finiteOpenSubspacePresheaf
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsEtale B S hS (finiteOpenSubspacePresheaf B S hS f).baseMap :=
  isEtale_baseMap_finiteOpenSubspacePresheaf_of_diagonal_of_chart B S hS f hsep hf
    (relativelyRepresentable_diag_finiteOpenSubspacePresheaf B S hS f)
    (exists_chart_locallyQuasiFinitePart B S hS f hsep hf)

end AlgebraicGeometry.Space

end
