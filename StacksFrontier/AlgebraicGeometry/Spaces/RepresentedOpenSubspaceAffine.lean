module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Affine and quasi-compact open subspaces of a represented algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`. An open
subspace `G` of the algebraic space `h_U = yoneda.obj U` is cut out by the open
`AlgebraicGeometry.Space.opensOfOpenSubspace` of `T`, the image of its points under the
homeomorphism `AlgebraicGeometry.Space.schemePointsHomeomorph` of Stacks 03BX. This file reads
two properties of `G` off that open:

* if `G` is an affine algebraic space, the open is an affine open of `T`;
* if the inclusion of `G` is quasi-compact (Stacks 03HE) and `T` is quasi-compact, the open is
  quasi-compact.

## Main results

* `AlgebraicGeometry.Space.coe_opensOfOpenSubspace`: the open of `T` attached to an open
  subspace is the image of its point set under `schemePointsHomeomorph`.
* `AlgebraicGeometry.Space.isAffineOpen_opensOfOpenSubspace`: an affine open subspace of `h_U`
  is cut out by an affine open of `T`.
* `AlgebraicGeometry.Space.isCompact_opensOfOpenSubspace`: an open subspace of `h_U` with
  quasi-compact inclusion is cut out by a quasi-compact open of `T`, when `T` is
  quasi-compact.
* `AlgebraicGeometry.Space.isClosed_image_and_isRetrocompact_compl`: when `T` is affine, a
  closed set of points of `h_U` whose open complement has quasi-compact inclusion has closed
  image in `T` with retrocompact complement.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The open of the representing scheme attached to an open subspace of `yoneda.obj U` is the
image of its point set under the homeomorphism of Stacks 03BX. -/
theorem coe_opensOfOpenSubspace (U : BigFppfOver B S hS) (G : Subfunctor (yoneda.obj U))
    (hG : IsOpenSubspace B S hS G) :
    (opensOfOpenSubspace B S hS U G hG : Set ((BigFppfOver.toScheme B S hS).obj U)) =
      schemePointsHomeomorph B S hS U '' Set.range (pointsMap B S hS G.toFunctor G.ι) :=
  rfl

/-- The open of the representing scheme attached to an open subspace of `yoneda.obj U` is the
image of any open immersion of site objects representing that subspace. -/
theorem coe_opensOfOpenSubspace_eq_range (U : BigFppfOver B S hS)
    (G : Subfunctor (yoneda.obj U)) (hG : IsOpenSubspace B S hS G) {V : BigFppfOver B S hS}
    (j : V ⟶ U) (e : yoneda.obj V ≅ G.toFunctor) (he : e.hom ≫ G.ι = yoneda.map j) :
    (opensOfOpenSubspace B S hS U G hG : Set ((BigFppfOver.toScheme B S hS).obj U)) =
      Set.range ((BigFppfOver.toScheme B S hS).map j) := by
  have hrange : Set.range (pointsMap B S hS G.toFunctor G.ι) =
      Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) := by
    rw [← he, pointsMap_comp, Set.range_comp,
      (bijective_pointsMap_of_isIso B S hS e.hom).2.range_eq, Set.image_univ]
  have hcomm : pointsToScheme B S hS U ∘ pointsMap B S hS (yoneda.obj V) (yoneda.map j) =
      (BigFppfOver.toScheme B S hS).map j ∘ pointsToScheme B S hS V :=
    funext (pointsToScheme_pointsMap_yoneda B S hS j)
  show pointsToScheme B S hS U '' _ = _
  rw [hrange, ← Set.range_comp, hcomm, Set.range_comp,
    (surjective_pointsToScheme B S hS V).range_eq, Set.image_univ]

/-- The open of the representing scheme attached to an affine open subspace of `yoneda.obj U`
is an affine open. -/
theorem isAffineOpen_opensOfOpenSubspace (U : BigFppfOver B S hS)
    (G : Subfunctor (yoneda.obj U)) (hG : IsOpenSubspace B S hS G)
    (hGaff : IsAffineSpace B S hS G.toFunctor) :
    IsAffineOpen (opensOfOpenSubspace B S hS U G hG) := by
  obtain ⟨V, j, e, hj, he⟩ := exists_openImmersion_of_isOpenSubspace B S hS U G hG
  obtain ⟨T', hT', ⟨i⟩⟩ := hGaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    IsAffine.of_isIso
      ((BigFppfOver.toScheme B S hS).mapIso (Yoneda.fullyFaithful.preimageIso (e ≪≫ i))).hom
  have hW : opensOfOpenSubspace B S hS U G hG = ((BigFppfOver.toScheme B S hS).map j).opensRange :=
    TopologicalSpace.Opens.ext ((coe_opensOfOpenSubspace_eq_range B S hS U G hG j e he).trans
      (Scheme.Hom.coe_opensRange _).symm)
  exact hW ▸ isAffineOpen_opensRange _

/-- When the representing scheme is quasi-compact, the open attached to an open subspace of
`yoneda.obj U` with quasi-compact inclusion is quasi-compact. -/
theorem isCompact_opensOfOpenSubspace (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (G : Subfunctor (yoneda.obj U)) (hG : IsOpenSubspace B S hS G)
    (hqc : IsQuasiCompact B S hS G.ι) :
    IsCompact (opensOfOpenSubspace B S hS U G hG : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  have hGqc : IsQuasiCompactSpace B S hS G.toFunctor :=
    (hqc _ (isAlgebraicSpace_yoneda B S hS U)
      (isQuasiCompact_yoneda_of_compact B S hS U inferInstance) (𝟙 _)).of_iso B S hS
      (asIso (pullback.snd (𝟙 _) G.ι))
  have := compactSpace_points_of_isQuasiCompactSpace B S hS hG.1 hGqc
  exact (isCompact_range (continuous_pointsMap B S hS G.ι)).image
    (schemePointsHomeomorph B S hS U).continuous

/-- Let `Z` be a closed set of points of `yoneda.obj U` whose open complement has
quasi-compact inclusion. When the scheme underlying `U` is affine, the image of `Z` under the
homeomorphism of Stacks 03BX is closed with retrocompact complement. -/
theorem isClosed_image_and_isRetrocompact_compl (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U))
    (Z : Set (points B S hS (yoneda.obj U))) (hZ : IsClosed Z)
    (hqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS (yoneda.obj U) hF).symm ⟨Zᶜ, hZ.isOpen_compl⟩).1.ι) :
    IsClosed (schemePointsHomeomorph B S hS U '' Z) ∧
      IsRetrocompact (schemePointsHomeomorph B S hS U '' Z)ᶜ := by
  set G := (openSubspacesOrderIso B S hS (yoneda.obj U) hF).symm ⟨Zᶜ, hZ.isOpen_compl⟩ with hGdef
  have hrange : Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) = Zᶜ := by
    rw [← openSubspacesOrderIso_apply B S hS _ hF, hGdef, OrderIso.apply_symm_apply]
  have hcompl : (schemePointsHomeomorph B S hS U '' Z)ᶜ =
      (opensOfOpenSubspace B S hS U G.1 G.2 : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
    rw [coe_opensOfOpenSubspace, hrange,
      Set.image_compl_eq (schemePointsHomeomorph B S hS U).bijective]
  exact ⟨(schemePointsHomeomorph B S hS U).isClosed_image.2 hZ,
    hcompl ▸ (isCompact_opensOfOpenSubspace B S hS U G.1 G.2 hqc).isRetrocompact
      (opensOfOpenSubspace B S hS U G.1 G.2).isOpen⟩

end AlgebraicGeometry.Space

end
