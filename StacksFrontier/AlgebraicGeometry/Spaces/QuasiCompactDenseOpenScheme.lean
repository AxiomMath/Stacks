module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalDenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace

/-!
# A quasi-compact dense open subscheme

Stacks 086U gives a decent algebraic space a dense open subspace which is a scheme, and
Stacks 0BB9 records the same open subspace together with the finiteness of its irreducible
components.  Neither makes the open subspace *quasi-compact*.  This file supplies that: a
decent algebraic space over `S` whose space of points has finitely many irreducible components
has a dense open subspace which is a quasi-compact scheme.

The extra finiteness hypothesis is what makes quasi-compactness available, and it is used
only through the scheme-level statement
`AlgebraicGeometry.exists_opens_isCompact_genericPoints_subset`: a scheme with finitely many
irreducible components has a quasi-compact open containing every generic point, namely the
union of one affine open neighbourhood of each of the finitely many generic points.  An open
set containing every generic point of a quasi-sober space is dense, so shrinking the dense
open subscheme of Stacks 086U to this quasi-compact open keeps it dense.

## Main results

* `AlgebraicGeometry.exists_opens_isCompact_genericPoints_subset`: a scheme with finitely many
  irreducible components has a quasi-compact open containing all of its generic points.
* `AlgebraicGeometry.Space.exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace`:
  a decent algebraic space over `S` with finitely many irreducible components admits an open
  immersion with dense image from a presheaf represented by an object of the site whose
  underlying scheme is quasi-compact.
* `AlgebraicGeometry.Space.exists_isQuasiCompactSpace_isOpenImmersion_denseRange_of_isDecentSpace`
  is the same statement with quasi-compactness read as Stacks 03E3 for the represented
  algebraic space rather than as compactness of the representing scheme.

## Implementation notes

The quasi-compact open is not asked to be affine, and is not affine in general: one affine
open neighbourhood is chosen per generic point and their union is taken, which is
quasi-compact because the index set is finite but is a union of several affines.  Making it
affine would need the neighbourhoods to be pairwise disjoint, which can be arranged by first
removing the other irreducible components, but nothing below needs it.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Topological preliminaries -/

/-- **A scheme with finitely many irreducible components has a quasi-compact open containing
all of its generic points.**  A scheme is quasi-sober, so its generic points are in bijection
with its irreducible components and are therefore finite in number; one affine open
neighbourhood of each, united, is open, contains them all, and is quasi-compact because the
union is finite. -/
theorem exists_opens_isCompact_genericPoints_subset (T : Scheme.{u})
    (hfin : (irreducibleComponents T).Finite) :
    ∃ W : T.Opens, IsCompact (W : Set T) ∧ genericPoints T ⊆ (W : Set T) := by
  classical
  have hgen : (genericPoints T).Finite := genericPoints.finite hfin
  have _ : Finite (genericPoints T) := hgen.to_subtype
  choose A hAaff hAmem _ using fun x : genericPoints T =>
    exists_isAffineOpen_mem_and_subset (X := T) (x := x.1) (U := ⊤)
      (show x.1 ∈ (⊤ : T.Opens) from trivial)
  refine ⟨⨆ x : genericPoints T, A x, ?_, ?_⟩
  · rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x => (hAaff x).isCompact
  · intro x hx
    rw [TopologicalSpace.Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hAmem ⟨x, hx⟩⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### Point maps of open immersions -/

/-- **A decent algebraic space with finitely many irreducible components has a quasi-compact
dense open subscheme.**  Stacks 086U supplies a dense open subspace which is a scheme; its
representing scheme has finitely many irreducible components because the point map of an open
immersion is an open embedding and an open embedding does not increase the number of
irreducible components.  Shrinking that scheme to a quasi-compact open through all of its
generic points keeps the image dense, because such an open is dense in the chart and the
chart has dense image. -/
theorem exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hfin : (irreducibleComponents (points B S hS X)).Finite) :
    ∃ (A : BigFppfOver B S hS) (u : yoneda.obj A ⟶ X),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj A) ∧
      IsOpenImmersion B S hS u ∧
      DenseRange (pointsMap B S hS (yoneda.obj A) u) := by
  classical
  -- Stacks 086U: a dense open subspace which is a scheme.
  obtain ⟨G, hGopen, hGrep, hGdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hX hdec
  have _ : G.toFunctor.IsRepresentable := hGrep
  set A₀ : BigFppfOver B S hS := G.toFunctor.reprX with hA₀def
  set u₀ : yoneda.obj A₀ ⟶ X := G.toFunctor.reprW.hom ≫ G.ι with hu₀def
  have hu₀ : IsOpenImmersion B S hS u₀ :=
    MorphismProperty.RespectsIso.precomp _ G.toFunctor.reprW.hom G.ι hGopen.2
  have hu₀dense : DenseRange (pointsMap B S hS (yoneda.obj A₀) u₀) := by
    rw [DenseRange, hu₀def, pointsMap_comp,
      (pointsMap_surjective_of_isIso B S hS G.toFunctor.reprW.hom).range_comp]
    exact hGdense
  -- The representing scheme has finitely many irreducible components.
  have hemb₀ : Topology.IsOpenEmbedding (pointsMap B S hS (yoneda.obj A₀) u₀) :=
    have _ : Mono u₀ := mono_of_isOpenImmersion B S hS u₀ hu₀
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS u₀)
      (pointsMap_injective_of_mono B S hS u₀) (isOpenMap_pointsMap_of_isOpenImmersion B S hS u₀ hu₀)
  have hfin₀ : (irreducibleComponents (points B S hS (yoneda.obj A₀))).Finite :=
    finite_irreducibleComponents_of_isOpenEmbedding _ hemb₀ hfin
  have hfinS : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj A₀)).Finite :=
    finite_irreducibleComponents_of_isOpenEmbedding (schemePointsHomeomorph B S hS A₀).symm
      (schemePointsHomeomorph B S hS A₀).symm.isOpenEmbedding hfin₀
  -- A quasi-compact open of the representing scheme through all of its generic points.
  obtain ⟨W, hWcomp, hWgen⟩ := exists_opens_isCompact_genericPoints_subset _ hfinS
  obtain ⟨A, i, hiOI, hirange, -⟩ := exists_restrict_bigFppfOver A₀ W
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map i) := hiOI
  -- The restricted chart is quasi-compact.
  have hAcomp : CompactSpace ((BigFppfOver.toScheme B S hS).obj A) := by
    rw [← isCompact_univ_iff]
    have hemb : Topology.IsEmbedding ⇑((BigFppfOver.toScheme B S hS).map i) :=
      ((BigFppfOver.toScheme B S hS).map i).isOpenEmbedding.isEmbedding
    rw [hemb.isCompact_iff, Set.image_univ, hirange]
    exact hWcomp
  refine ⟨A, yoneda.map i ≫ u₀, hAcomp, ?_, ?_⟩
  · exact isOpenImmersion_comp B S hS _ _
      (presheaf_yoneda_map_of_inverseImage B S hS inferInstance i hiOI) hu₀
  · -- The restricted chart is still dense.
    have hDeq : Set.range (pointsMap B S hS (yoneda.obj A) (yoneda.map i)) =
        pointsToScheme B S hS A₀ ⁻¹' (W : Set _) := by
      refine Set.image_injective.2 (injective_pointsToScheme B S hS A₀) ?_
      rw [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS A₀), ← hirange]
      have hfun : pointsToScheme B S hS A₀ ∘ pointsMap B S hS (yoneda.obj A) (yoneda.map i) =
          ⇑((BigFppfOver.toScheme B S hS).map i) ∘ pointsToScheme B S hS A :=
        funext fun w => pointsToScheme_pointsMap_yoneda B S hS i w
      rw [← Set.range_comp, hfun, (surjective_pointsToScheme B S hS A).range_comp]
    have hWdense : Dense (W : Set ((BigFppfOver.toScheme B S hS).obj A₀)) :=
      dense_iff_closure_eq.2 (Set.univ_subset_iff.1
        ((genericPoints.closure (α := (BigFppfOver.toScheme B S hS).obj A₀)) ▸ closure_mono hWgen))
    have hopen : IsOpenMap (pointsToScheme B S hS A₀) :=
      (schemePointsHomeomorph B S hS A₀).isOpenMap
    have hDdense : Dense (pointsToScheme B S hS A₀ ⁻¹' (W : Set _)) :=
      hWdense.preimage hopen
    rw [DenseRange, pointsMap_comp, Set.range_comp, hDeq]
    exact hu₀dense.dense_image (continuous_pointsMap B S hS u₀) hDdense

/-- **A decent algebraic space with finitely many irreducible components has a quasi-compact
dense open subscheme**, with quasi-compactness read as Stacks 03E3 for the represented
algebraic space.  This is
`AlgebraicGeometry.Space.exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace`
with its compactness assertion transported along
`AlgebraicGeometry.Space.isQuasiCompact_yoneda_of_compact`. -/
theorem exists_isQuasiCompactSpace_isOpenImmersion_denseRange_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hfin : (irreducibleComponents (points B S hS X)).Finite) :
    ∃ (A : BigFppfOver B S hS) (u : yoneda.obj A ⟶ X),
      IsQuasiCompactSpace B S hS (yoneda.obj A) ∧
      IsOpenImmersion B S hS u ∧
      DenseRange (pointsMap B S hS (yoneda.obj A) u) := by
  obtain ⟨A, u, hAcomp, hu, hudense⟩ :=
    exists_compactSpace_isOpenImmersion_denseRange_of_isDecentSpace B S hS hX hdec hfin
  exact ⟨A, u, isQuasiCompact_yoneda_of_compact B S hS A hAcomp, hu, hudense⟩

end Space

end AlgebraicGeometry

end
