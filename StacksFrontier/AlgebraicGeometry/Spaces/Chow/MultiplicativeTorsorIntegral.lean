module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatUniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The inverse image of an integral closed subspace in the multiplicative torsor is integral

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor (`AlgebraicGeometry.Space.torsorOfInvertible`).  This
file proves clause (5) of Stacks 0EQG: **for an integral closed subspace `Z ⊆ X` the inverse image
`q^{-1}(Z) ⊆ T` is an integral closed subspace.**

## The argument

The source observes that `𝐆_m × Z` is integral when `Z` is.  In the present setting: `q^{-1}(Z)`
is smooth over `Z`, so it is reduced (Stacks 0GB3); it is a closed subspace of the decent space
`T`, so it is decent; and its points are the inverse image of the irreducible set `|Z|` under the
continuous map `|q|`, which is open, being flat and locally of finite presentation (Stacks 042S),
and whose fibres are irreducible, because over an affine chart `V` trivializing `ℒ` the base change
of `q` is `Spec 𝒪(V)[T, T⁻¹] ⟶ V`, whose fibres are spectra of rings `κ[T, T⁻¹]`.  The inverse
image of an irreducible set under an open map with irreducible fibres is irreducible
(`isIrreducible_preimage_of_isOpenMap`).

## Main results

* `isIrreducible_preimage_of_isOpenMap`: the topological lemma.
* `AlgebraicGeometry.Space.isIrreducible_preimage_singleton_torsorOfInvertibleProjection`: the
  fibres of `|q|` are irreducible.
* `AlgebraicGeometry.Space.torsorOfInvertiblePreimage`: `q^{-1}(Z)`, as an integral closed
  subspace of `T`.
* `AlgebraicGeometry.Space.torsorOfInvertible_clause_five`: **Stacks 0EQG, clause (5).**

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 004Z](https://stacks.math.columbia.edu/tag/004Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **The inverse image of an irreducible set under an open map with irreducible fibres is
irreducible**, as long as the set is contained in the image. -/
theorem isIrreducible_preimage_of_isOpenMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : IsOpenMap f) {S : Set β} (hS : IsIrreducible S)
    (hsurj : S ⊆ Set.range f) (hfib : ∀ y ∈ S, IsPreirreducible (f ⁻¹' {y})) :
    IsIrreducible (f ⁻¹' S) := by
  refine ⟨?_, fun u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩ => ?_⟩
  · obtain ⟨y, hy⟩ := hS.nonempty
    obtain ⟨x, rfl⟩ := hsurj hy
    exact ⟨x, hy⟩
  obtain ⟨y, hyS, ⟨a', ha'u, rfl⟩, ⟨b', hb'v, hb'⟩⟩ :=
    hS.2 (f '' u) (f '' v) (hf u hu) (hf v hv) ⟨f a, ha, a, hau, rfl⟩ ⟨f b, hb, b, hbv, rfl⟩
  obtain ⟨z, hz, hzu, hzv⟩ := hfib (f a') hyS u v hu hv ⟨a', rfl, ha'u⟩ ⟨b', hb', hb'v⟩
  refine ⟨z, ?_, hzu, hzv⟩
  change f z ∈ S
  rw [show f z = f a' from hz]
  exact hyS

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-- **The fibres of `|q| : |T| → |X|` are irreducible.**  Over an affine chart `V` trivializing
`ℒ`, with a point `v` over `x`, the fibre of `|q|` over `x` is the image of the fibre of
`Spec 𝒪(V)[T, T⁻¹] ⟶ V` over `v`, which is the spectrum of `κ(v)[T, T⁻¹]`. -/
theorem isIrreducible_preimage_singleton_torsorOfInvertibleProjection
    (x : points D.site D.base D.base_mem X) :
    IsIrreducible (pointsMap D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj
      (torsorOfInvertibleProjection D p hp L hL).hom ⁻¹' {x}) := by
  obtain ⟨V, hV, ⟨e⟩, v, hv⟩ := exists_affine_trivializing_chart D p hp L hL x
  have hqc := isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X V hV
  have sq := isPullback_torsorOfInvertible_chart_algebraicSpaces D p hp L hL V
  -- the fibre of `|q|` is the image of the fibre of `Spec 𝒜(V) ⟶ V` over `v`
  have hset : pointsMap D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj
      (torsorOfInvertibleProjection D p hp L hL).hom ⁻¹' {x} =
      pointsMap D.site D.base D.base_mem
          (yoneda.obj (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
            (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL)
            V))
          (torsorOfInvertibleChartToSpace D p hp L hL V) ''
        (pointsMap D.site D.base D.base_mem
          (yoneda.obj (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
            (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL)
            V))
          (yoneda.map (torsorOfInvertibleChartHom D p hp L hL V)) ⁻¹' {v}) := by
    ext t
    constructor
    · intro ht
      obtain ⟨w, hw1, hw2⟩ := exists_point_of_isPullback D.site D.base D.base_mem sq t v
        (ht.trans hv.symm)
      exact ⟨w, hw2, hw1⟩
    · rintro ⟨w, hw, rfl⟩
      change pointsMap D.site D.base D.base_mem _ _
        (pointsMap D.site D.base D.base_mem _ (torsorOfInvertibleChartToSpace D p hp L hL V) w) = x
      rw [← pointsMap_comp_apply, (isPullback_torsorOfInvertible_chart D p hp L hL V).w,
        pointsMap_comp_apply, show pointsMap D.site D.base D.base_mem _
          (yoneda.map (torsorOfInvertibleChartHom D p hp L hL V)) w = v from hw]
      exact hv
  rw [hset]
  refine IsIrreducible.image ?_ _ (continuous_pointsMap D.site D.base D.base_mem
    (torsorOfInvertibleChartToSpace D p hp L hL V)).continuousOn
  -- the fibre over `v`, read on the schemes
  rw [pointsMap_yoneda_eq_conj]
  have hsch := isIrreducible_preimage_singleton_specChartMap_laurentAlgebraSheaf D p hp L hL e hqc
    (schemePointsHomeomorph D.site D.base D.base_mem V.obj.left v)
  rw [← toScheme_map_affineChartSpecHom D.site D.base D.base_mem _
    (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL)] at hsch
  have h2 := hsch.image (schemePointsHomeomorph D.site D.base D.base_mem
      (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL)
        (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V)).symm
    (schemePointsHomeomorph D.site D.base D.base_mem
      (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL)
        (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V)).symm.continuous.continuousOn
  convert h2 using 1
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply, Set.mem_image]
  constructor
  · intro hw
    refine ⟨schemePointsHomeomorph D.site D.base D.base_mem
      (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL)
        (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL) V) w, ?_,
      (schemePointsHomeomorph D.site D.base D.base_mem
        (affineChartSpec D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
          (laurentAlgebraSheaf D p hp L hL) (sectionsBelowCutoff_laurentAlgebraSheaf D p hp L hL)
          V)).symm_apply_apply w⟩
    rw [← hw, Homeomorph.apply_symm_apply]
  · rintro ⟨w', hw', rfl⟩
    rw [Homeomorph.apply_symm_apply, hw', Homeomorph.symm_apply_apply]

/-- The inverse image under `|q|` of an irreducible set is irreducible. -/
private theorem isIrreducible_preimage_pointsMap_torsorOfInvertibleProjection
    {S : Set (points D.site D.base D.base_mem X)} (hS : IsIrreducible S) :
    IsIrreducible (pointsMap D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj
      (torsorOfInvertibleProjection D p hp L hL).hom ⁻¹' S) := by
  have hsm := (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).1
  exact isIrreducible_preimage_of_isOpenMap
    (isOpenMorphism_of_isFlat_of_isLocallyOfFinitePresentation D.site D.base D.base_mem
      (torsorOfInvertibleSpace D p hp L hL).property hp.1 _
      (isFlat_torsorOfInvertibleProjection D p hp L hL)
      (isLocallyOfFinitePresentation_of_isSmooth D.site D.base D.base_mem hsm)) hS
    (fun y _ => isSurjective_torsorOfInvertibleProjection D p hp L hL y)
    (fun y _ => (isIrreducible_preimage_singleton_torsorOfInvertibleProjection D p hp L hL
      y).isPreirreducible)

/-- The inverse image `q^{-1}(Z)` of a closed subspace is a closed subspace of `T`. -/
theorem isClosedSubspace_torsorOfInvertible_preimage (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) :
    IsClosedSubspace D.site D.base D.base_mem
      (Z.preimage (torsorOfInvertibleProjection D p hp L hL).hom) :=
  isClosedSubspace_preimage D.site D.base D.base_mem _ Z hp.1
    (torsorOfInvertibleSpace D p hp L hL).property hZ

/-- **The inverse image of an integral closed subspace in the multiplicative torsor is
integral.** -/
theorem isIntegralSpace_torsorOfInvertible_preimage
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsIntegralSpace D.site D.base D.base_mem
      (Z.subspace.preimage (torsorOfInvertibleProjection D p hp L hL).hom).toFunctor := by
  set q := (torsorOfInvertibleProjection D p hp L hL).hom with hqdef
  have hT := (torsorOfInvertibleSpace D p hp L hL).property
  have hP := isClosedSubspace_torsorOfInvertible_preimage D p hp L hL Z.subspace Z.isClosedSubspace
  have hsm := (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).1
  refine ⟨?_, ?_, ?_⟩
  · -- reduced: smooth over the reduced space `Z`
    have hsq := Subfunctor.isPullback_preimage q Z.subspace
    exact isReduced_of_isSmooth D.site D.base D.base_mem hP.1 Z.isClosedSubspace.1 _
      (isSmooth_of_isPullback hsq hP.1 hT Z.isClosedSubspace.1 hp.1 hsm) Z.isIntegralSpace.1
  · -- decent: a closed subspace of the decent space `T`
    exact isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood _ (isGood_torsorOfInvertible D p hp L hL)) hP
  · -- irreducible: the inverse image of `|Z|` under an open map with irreducible fibres
    have hemb := isEmbedding_pointsMap_of_isImmersion D.site D.base D.base_mem hT
      (Z.subspace.preimage q).ι (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hP.2)
    have hirr : IsIrreducible (Set.range (pointsMap D.site D.base D.base_mem _
        (Z.subspace.preimage q).ι)) := by
      rw [range_pointsMap_preimage_ι]
      exact isIrreducible_preimage_pointsMap_torsorOfInvertibleProjection D p hp L hL
        (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z)
    have := Subtype.irreducibleSpace hirr
    exact (hemb.toHomeomorph.irreducibleSpace_iff).2 inferInstance

/-- **If `X` is integral, so is `T`**: the case `Z = X` of clause (5), stated for `T` itself. -/
theorem isIntegralSpace_torsorOfInvertibleSpace
    (hX : IsIntegralSpace D.site D.base D.base_mem X) :
    IsIntegralSpace D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj := by
  set q := (torsorOfInvertibleProjection D p hp L hL).hom with hqdef
  have hT := (torsorOfInvertibleSpace D p hp L hL).property
  have hsm := (isSmoothOfRelativeDimension_torsorOfInvertibleProjection D p hp L hL).1
  refine ⟨isReduced_of_isSmooth D.site D.base D.base_mem hT hp.1 q hsm hX.1,
    D.isDecentSpace_of_isGood _ (isGood_torsorOfInvertible D p hp L hL), ?_⟩
  have : IrreducibleSpace (points D.site D.base D.base_mem X) := hX.2.2
  have h := isIrreducible_preimage_pointsMap_torsorOfInvertibleProjection D p hp L hL
    (IrreducibleSpace.isIrreducible_univ _)
  rw [Set.preimage_univ] at h
  exact (irreducibleSpace_def _).2 h

/-- **`q^{-1}(Z)` as an integral closed subspace of `T`**, for an integral closed subspace `Z`
of `X`. -/
def torsorOfInvertiblePreimage (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj where
  subspace := Z.subspace.preimage (torsorOfInvertibleProjection D p hp L hL).hom
  isClosedSubspace :=
    isClosedSubspace_torsorOfInvertible_preimage D p hp L hL Z.subspace Z.isClosedSubspace
  isIntegralSpace := isIntegralSpace_torsorOfInvertible_preimage D p hp L hL Z

/-- **Stacks 0EQG, clause (5).** If `Z ⊆ X` is an integral closed subspace, then
`q^{-1}(Z) ⊆ T` is an integral closed subspace. -/
@[stacks 0EQG "clause (5): q^{-1}(Z) is an integral closed subspace of T for Z an integral closed
subspace of X"]
theorem torsorOfInvertible_clause_five (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsClosedSubspace D.site D.base D.base_mem
        (Z.subspace.preimage (torsorOfInvertibleProjection D p hp L hL).hom) ∧
      IsIntegralSpace D.site D.base D.base_mem
        (Z.subspace.preimage (torsorOfInvertibleProjection D p hp L hL).hom).toFunctor :=
  ⟨isClosedSubspace_torsorOfInvertible_preimage D p hp L hL Z.subspace Z.isClosedSubspace,
    isIntegralSpace_torsorOfInvertible_preimage D p hp L hL Z⟩

end AlgebraicGeometry.Space

end
