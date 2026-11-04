module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentAffineBase
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne

/-!
# The relative assassin containment locus over an arbitrary base

This file carries out the reduction with which the proof of Stacks 0CVV begins -- "the question
is local on `Y`" -- and so removes the hypothesis that the base be affine from
`AlgebraicGeometry.Space.isLocallyConstructible_relativeAssassinContainmentLocus_of_isAffine`.

## Main results

* `AlgebraicGeometry.Space.exists_baseRestriction_of_isOpenImmersion`: the restriction of an
  algebraic space to an open subobject of its base, as an open subspace of the source together
  with its structure morphism over that open subobject.
* `isLocallyConstructible_relativeAssassinContainmentLocus_of_isFinitePresentation`, in the
  namespace `AlgebraicGeometry.Space`: **Stacks 0CVV**, the containment locus over an arbitrary
  base is locally constructible.
* `isLocallyConstructible_relativeAssassinContainmentLocus_of_isQuasiCompact`, in the same
  namespace: the same statement with `U` an open subspace of `X` whose morphism to `V` is
  quasi-compact, which is the hypothesis the source makes.

## Implementation notes

Local constructibility is local on the base, so it is enough to check the locus on each affine
open `A` of `|V|`. Such an `A` is an object `V'` of the site with
`AlgebraicGeometry.Space.openSubobject`, the inclusion being an open immersion of schemes, and
the two reduction lemmas of the file pair as follows.

`AlgebraicGeometry.Space.relativeAssassinContainmentLocus_comp_schemeSpaceMap_of_isOpenImmersion`
compares the locus over `V'` with the locus over `V`, but only for a space already lying over
`V'`. The space lying over `V'` is `f⁻¹(V')`, built here as the fibre product of `f` with
`schemeSpaceMap ψ`: its projection to `X` is an open immersion because `schemeSpaceMap ψ` is one
(Stacks 02YW), it is étale for the same reason (Stacks 03FU), its structure morphism over `V'`
is of finite presentation because finite presentation is stable under base change
(Stacks 03XR), and its point set is exactly the part of `|X|` lying over `A` by the
image-preimage identity for a cartesian square.

`AlgebraicGeometry.Space.relativeAssassinContainmentLocus_modulePullback_inter` then replaces
`X` by `f⁻¹(V')` *over `A`*, which is all that is needed: the projection is surjective onto the
points of `X` above `A` and need not be surjective anywhere else. Intersecting with `A` is
harmless because the comparison is read back along the inclusion of `A`, whose range is `A`.

The hypothesis that `|U| → |V|` be quasi-compact is carried in its point-level form: the
intersection of `U` with the part of `|X|` lying over a quasi-compact open of `|V|` is
quasi-compact. Over an affine base this is compactness of `U`, which is the hypothesis of the
affine case; the two are matched here by the fact that the point map of an open immersion is an
open embedding, so compactness of its preimage of `U` is compactness of `U` intersected with
its range. That point-level form is what the main theorem of the file asks for, and it is
implied by the source's own hypothesis -- `U` an open subspace of `X` with `U → V`
quasi-compact -- through Stacks 0EMK, which is the corollary stated at the end of the file. The
general form is kept because `IsCompact U` would be strictly stronger over a non-quasi-compact
base, and because it is the form the induction on affine opens consumes.

Finite presentation of `F` is carried in the source's own form,
`SheafOfModules.IsFinitePresentationOnSite`, and it is transported to the open subspace by
Stacks 03DO: the inverse image along the projection of a module of finite presentation on the
small étale site is again of finite presentation, which is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`. The reading of that
condition on an affine étale chart, which the affine case needs, is carried out there by
`AlgebraicGeometry.Space.isFinitePresentation_baseChangeModule_of_isFinitePresentationOnSite`.

## References

* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 054C](https://stacks.math.columbia.edu/tag/054C)
* [Stacks Project, Tag 0EMK](https://stacks.math.columbia.edu/tag/0EMK)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point set of the algebraic space of an object of the site, seen inside the point set of
the algebraic space of a larger object along a morphism of the site, is the part of the latter
lying over the image of the underlying morphism of schemes. -/
theorem range_pointsMap_schemeSpaceMap {V' V : BigFppfOver B S hS} (ψ : V' ⟶ V) :
    Set.range (pointsMap B S hS (schemeSpace V').1 (schemeSpaceMap ψ).hom) =
      schemeSpacePointToScheme B S hS V ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map ψ).base := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨schemeSpacePointToScheme B S hS V' w,
      (schemeSpacePointToScheme_pointsMap B S hS ψ w).symm⟩
  · intro hy
    exact mem_range_pointsMap_yoneda_map B S hS ψ y hy

/-- Compactness of the inverse image of a set of points along an open immersion of algebraic
spaces is compactness of the intersection of that set with the range. -/
theorem isCompact_preimage_pointsMap_of_isOpenImmersion {X X' : AlgebraicSpaces B S hS}
    (ι : X' ⟶ X) (hι : IsOpenImmersion B S hS ι.hom) (U : Set (points B S hS X.1))
    (hU : IsCompact (U ∩ Set.range (pointsMap B S hS X'.1 ι.hom))) :
    IsCompact (pointsMap B S hS X'.1 ι.hom ⁻¹' U) := by
  have : Mono ι.hom := mono_of_isOpenImmersion B S hS ι.hom hι
  have hemb : IsOpenEmbedding (pointsMap B S hS X'.1 ι.hom) :=
    .of_continuous_injective_isOpenMap (continuous_pointsMap B S hS ι.hom)
      (pointsMap_injective_of_mono B S hS ι.hom)
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS ι.hom hι)
  rw [hemb.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range]
  exact hU

/-- **The restriction of an algebraic space to an open subobject of its base.** For
`f : X ⟶ schemeSpace V` and `ψ : V' ⟶ V` a morphism of the site whose underlying morphism of
schemes is an open immersion, the fibre product `f⁻¹(V')` is an open subspace of `X`, étale over
it, whose point set is the part of `|X|` lying over the image of `ψ`, and it is of finite
presentation over `V'` as soon as `X` is of finite presentation over `V`. -/
theorem exists_baseRestriction_of_isOpenImmersion {X : AlgebraicSpaces B S hS}
    {V' V : BigFppfOver B S hS} (ψ : V' ⟶ V)
    (hψ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ψ))
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom) :
    ∃ (X' : AlgebraicSpaces B S hS) (ι : X' ⟶ X) (g : X' ⟶ schemeSpace V'),
      IsOpenImmersion B S hS ι.hom ∧ IsEtale B S hS ι.hom ∧
        IsFinitePresentation B S hS g.hom ∧ ι ≫ f = g ≫ schemeSpaceMap ψ ∧
          Set.range (pointsMap B S hS X'.1 ι.hom) =
            (fun x => schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x)) ⁻¹'
              Set.range ((BigFppfOver.toScheme B S hS).map ψ).base := by
  have := hψ
  have hψoi : IsOpenImmersion B S hS (schemeSpaceMap ψ).hom :=
    isOpenImmersion_yoneda_map B S hS ψ hψ
  have hψet : IsEtale B S hS (schemeSpaceMap ψ).hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS ψ).2 inferInstance)
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f (schemeSpaceMap ψ)
  refine ⟨AlgebraicSpaces.fiberProduct B S hS f (schemeSpaceMap ψ), _, _,
    isOpenImmersion_of_isPullback B S hS sq.flip hψoi,
    isEtale_of_isPullback B S hS _ _ _ _ sq.flip hψet,
    MorphismProperty.of_isPullback
      (P := fun {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y) =>
        IsFinitePresentation B S hS k.hom) sq hf,
    sq.w, ?_⟩
  have hkey := preimage_image_pointsMap_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS sq.flip) Set.univ
  simp only [Set.image_univ, Set.preimage_univ] at hkey
  rw [← hkey, range_pointsMap_schemeSpaceMap B S hS ψ]
  rfl

/-- Let `V` be a scheme of the site, let `X` be an algebraic space of finite presentation over `V`,
let `F` be a quasi-coherent `𝒪_X`-module of finite presentation and let `U` be an open subset of
`|X|` whose map to `|V|` is quasi-compact. Then the set of points of `V` over which every point of
the relative assassin of `F` above that point lies in `U` is locally constructible.

Here `hUqc` is the point-level reading of "`U → V` is quasi-compact": the part of `U` lying over
a quasi-compact open of `|V|` is quasi-compact. -/
@[stacks 0CVV "with `U → V` quasi-compact read on the point sets"]
theorem isLocallyConstructible_relativeAssassinContainmentLocus_of_isFinitePresentation
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Set (points B S hS X.1)) (hUopen : IsOpen U)
    (hUqc : ∀ A : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      IsCompact (A : Set ((BigFppfOver.toScheme B S hS).obj V)) →
      IsCompact (U ∩ (fun x =>
          schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x)) ⁻¹'
        (A : Set ((BigFppfOver.toScheme B S hS).obj V)))) :
    IsLocallyConstructible (relativeAssassinContainmentLocus B S hS V f F U) := by
  rw [Topology.IsLocallyConstructible.iff_of_isOpenCover
    (U := fun A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens => A.1)
    (by exact iSup_affineOpens_eq_top ((BigFppfOver.toScheme B S hS).obj V))]
  intro A
  have hAaff : IsAffine A.1.toScheme := A.2
  have hAι : _root_.AlgebraicGeometry.IsOpenImmersion A.1.ι := inferInstance
  have hψmap : (BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V A.1.ι hAι) =
      A.1.ι := toScheme_map_openSubobjectHom B S hS V A.1.ι hAι
  have hψ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V A.1.ι hAι)) := by
    rw [hψmap]
    exact hAι
  obtain ⟨X', ι, g, hιoi, hιet, hgfp, hcomm, hrange⟩ :=
    exists_baseRestriction_of_isOpenImmersion B S hS
      (openSubobjectHom B S hS V A.1.ι hAι) hψ f hf
  have hfun : ((BigFppfOver.toScheme B S hS).map
        (openSubobjectHom B S hS V A.1.ι hAι)).base = A.1.ι.base := by rw [hψmap]
  have hrA : Set.range ((BigFppfOver.toScheme B S hS).map
        (openSubobjectHom B S hS V A.1.ι hAι)).base =
      (A.1 : Set ((BigFppfOver.toScheme B S hS).obj V)) := by
    rw [hfun]
    exact A.1.range_ι
  have hrange' : Set.range (pointsMap B S hS X'.1 ι.hom) =
      (fun x => schemeSpacePointToScheme B S hS V (pointsMap B S hS X.1 f.hom x)) ⁻¹'
        (A.1 : Set ((BigFppfOver.toScheme B S hS).obj V)) := by
    rw [hrange, hrA]
  have hinter := relativeAssassinContainmentLocus_modulePullback_inter B S hS V f F U ι hιet
    (A.1 : Set ((BigFppfOver.toScheme B S hS).obj V))
    (fun x hx => by rw [hrange']; exact hx)
  have hpre : ((BigFppfOver.toScheme B S hS).map
          (openSubobjectHom B S hS V A.1.ι hAι)).base ⁻¹'
        relativeAssassinContainmentLocus B S hS V (ι ≫ f)
          ((modulePullback B S hS ι).obj F) (pointsMap B S hS X'.1 ι.hom ⁻¹' U) =
      ((BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V A.1.ι hAι)).base ⁻¹'
        relativeAssassinContainmentLocus B S hS V f F U := by
    ext z
    have hz : ((BigFppfOver.toScheme B S hS).map
        (openSubobjectHom B S hS V A.1.ι hAι)).base z ∈
        (A.1 : Set ((BigFppfOver.toScheme B S hS).obj V)) := hrA ▸ Set.mem_range_self z
    simp only [Set.mem_preimage]
    exact ⟨fun h1 => ((Set.ext_iff.1 hinter _).1 ⟨h1, hz⟩).1,
      fun h1 => ((Set.ext_iff.1 hinter _).2 ⟨h1, hz⟩).1⟩
  have hbase := relativeAssassinContainmentLocus_comp_schemeSpaceMap_of_isOpenImmersion
    B S hS (openSubobjectHom B S hS V A.1.ι hAι) g hψ
    ((modulePullback B S hS ι).obj F) (pointsMap B S hS X'.1 ι.hom ⁻¹' U)
  rw [← hcomm] at hbase
  have hUcpt : IsCompact (pointsMap B S hS X'.1 ι.hom ⁻¹' U) := by
    refine isCompact_preimage_pointsMap_of_isOpenImmersion B S hS ι hιoi U ?_
    rw [hrange']
    exact hUqc A.1 A.2.isCompact
  have hres : IsLocallyConstructible
      (((BigFppfOver.toScheme B S hS).map (openSubobjectHom B S hS V A.1.ι hAι)).base ⁻¹'
        relativeAssassinContainmentLocus B S hS V f F U) := by
    rw [← hpre, ← hbase]
    exact isLocallyConstructible_relativeAssassinContainmentLocus_of_isAffine B S hS
      (openSubobject B S hS V A.1.ι hAι) hAaff g hgfp
      ((modulePullback B S hS ι).obj F)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS ι F hF)
      (isFinitePresentationOnSite_modulePullback B S hS ι F hFfp)
      (pointsMap B S hS X'.1 ι.hom ⁻¹' U)
      (hUopen.preimage (continuous_pointsMap B S hS ι.hom)) hUcpt
  rwa [hfun] at hres

/-- Let `V` be a scheme of the site, let `X` be an algebraic space of finite presentation over `V`,
let `F` be a quasi-coherent `𝒪_X`-module of finite presentation and let `U ⊆ X` be an open subspace
whose morphism to `V` is quasi-compact. Then the set of points of `V` over which every point of the
relative assassin of `F` above that point lies in `U` is locally constructible. -/
@[stacks 0CVV]
theorem isLocallyConstructible_relativeAssassinContainmentLocus_of_isQuasiCompact
    {X : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (hf : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompact B S hS (U.ι ≫ f.hom)) :
    IsLocallyConstructible (relativeAssassinContainmentLocus B S hS V f F
      (Set.range (pointsMap B S hS U.toFunctor U.ι))) := by
  refine isLocallyConstructible_relativeAssassinContainmentLocus_of_isFinitePresentation
    B S hS V f hf F hF hFfp _
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2) fun A hA => ?_
  have hAopen : IsOpen (schemeSpacePointToScheme B S hS V ⁻¹'
      (A : Set ((BigFppfOver.toScheme B S hS).obj V))) :=
    (schemePointsHomeomorph B S hS V).isOpen_preimage.2 A.isOpen
  have hAcpt : IsCompact (schemeSpacePointToScheme B S hS V ⁻¹'
      (A : Set ((BigFppfOver.toScheme B S hS).obj V))) :=
    (schemePointsHomeomorph B S hS V).isCompact_preimage.2 hA
  have hkey := isQuasiCompactMap_pointsMap B S hS hU.1 (schemeSpace V).2
    (U.ι ≫ f.hom) hUqc hAopen hAcpt
  rw [pointsMap_comp, Set.preimage_comp] at hkey
  have himg := hkey.image (continuous_pointsMap B S hS U.ι)
  rwa [Set.image_preimage_eq_inter_range, Set.inter_comm] at himg

end AlgebraicGeometry.Space

end
