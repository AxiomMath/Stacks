module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.SingularLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFiniteSingularities
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Nodal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# At-worst-nodal families of curves lie in `Curves^{lci+}`

A family of curves whose structure morphism is at-worst-nodal of relative dimension one has a
local complete intersection structure morphism, and the reduced closed subspace of its total
space supported on the non-smooth locus is finite over the base. These are the two defining
conditions of `Curves^{lci}` (Tag 0DZV) and of `Curves^{+}` (Tag 0DZW), so this is the inclusion
`Curves^{nodal} ⊂ Curves^{lci+}` that the proof of Tag 0E00 starts from, read on families.

## Main results

* `AlgebraicGeometry.Space.isSmoothAt_pointsMap_of_smoothAt`: a point of an étale chart at which
  the chart morphism is smooth maps to a point at which the morphism of algebraic spaces is
  smooth.
* `AlgebraicGeometry.CurveFamily.isLciFamily_of_isAtWorstNodal`: an at-worst-nodal family of
  relative dimension one has a local complete intersection structure morphism.
* `AlgebraicGeometry.CurveFamily.isFiniteNonSmoothLocus_of_isAtWorstNodal`: its reduced
  non-smooth locus is finite over the base.

## Implementation notes

The finiteness is Tag 0A4X: the reduced non-smooth locus `Z` is proper over the base, being a
closed subspace of a proper family, and it is locally quasi-finite over the base. The second
point is read on one surjective étale chart of `Z`, the presentation of the reduced induced
closed subscheme `Z_U` of an étale chart `U` of the total space. On `U` the family is
at-worst-nodal, so its relative singular subscheme `Sing(U)`, cut out by the first Fitting ideal
of the relative differentials, is unramified over the base, and by Tag 0C3K it contains every
point at which `U` is not smooth. Every point of `Z_U` is such a point, so the reduced subscheme
`Z_U` is a closed subscheme of `Sing(U)`, and `Z_U` is locally quasi-finite over the base.

## References

* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0DZV](https://stacks.math.columbia.edu/tag/0DZV)
* [Stacks Project, Tag 0DZW](https://stacks.math.columbia.edu/tag/0DZW)
* [Stacks Project, Tag 0C3K](https://stacks.math.columbia.edu/tag/0C3K)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `φ : U ⟶ X` be an étale chart of an algebraic space, let `f : X ⟶ W` be a morphism to a
scheme of the site and `g : U ⟶ W` the morphism of schemes with `φ ≫ f = g`. If `g` is smooth at
a point `x` of `U`, then `f` is smooth at the image of `x` in `|X|`. -/
theorem isSmoothAt_pointsMap_of_smoothAt {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U W : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (f : X ⟶ yoneda.obj W) (g : U ⟶ W) (hg : φ ≫ f = yoneda.map g)
    (x : (BigFppfOver.toScheme B S hS).obj U)
    (hx : InfinitesimalLifting.SmoothAt ((BigFppfOver.toScheme B S hS).map g) x) :
    IsSmoothAt B S hS f
      (pointsMap B S hS (yoneda.obj U) φ ((pointsEquivScheme B S hS U).symm x)) := by
  classical
  set p := (pointsEquivScheme B S hS U).symm x with hp
  let r : FieldValuedPoint B S hS (yoneda.obj U) := Quot.out p
  have hr : r.class B S hS (yoneda.obj U) = p := Quot.out_eq p
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (MorphismOfGerms.HasRepresentativeWithProperty
        (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})) :=
    MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      Smooth.isEtaleLocalOnSourceAndTarget
  let c : EtaleChartAtPoint B S hS f (pointsMap B S hS (yoneda.obj U) φ p) :=
    { U := U
      V := W
      a := φ
      b := yoneda.map (𝟙 W)
      h := g
      a_etale := hφ
      b_etale := presheaf_yoneda_map_id_etale B S hS W
      comm := by rw [CategoryTheory.Functor.map_id, Category.comp_id, hg]
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by rw [hr] }
  have hsrc : c.sourcePoint B S hS = x := by
    change pointsToScheme B S hS U (r.class B S hS (yoneda.obj U)) = x
    rw [hr, hp]
    exact pointsToScheme_pointsEquivScheme_symm B S hS U x
  have hY : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  exact (isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY f _).mpr
    ((holdsOnEveryEtaleChartAtPoint_iff_some B S hS _ hQ hX hY f _).mpr
      ⟨c, (smoothAt_iff_hasRepresentativeWithProperty _ _).mp (by rwa [hsrc])⟩)

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

/-- A family of curves whose structure morphism is at-worst-nodal of relative dimension one has
a local complete intersection structure morphism: an at-worst-nodal morphism of relative
dimension one is syntomic on every étale chart. -/
theorem isLciFamily_of_isAtWorstNodal (F : CurveFamily B hZ)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :
    IsLciFamily B hZ F :=
  (isLciFamily_iff_isSyntomicFamily B hZ F).mpr
    (Space.holdsOnEveryEtaleChart_mono B integerBase hZ (fun _ hg => hg.1.1) hF)

attribute [local instance] Space.pointTopology

/-- A family of curves whose structure morphism is at-worst-nodal of relative dimension one has
finite reduced non-smooth locus: the reduced closed subspace of the total space supported on the
points at which the family is not smooth is finite over the base. -/
theorem isFiniteNonSmoothLocus_of_isAtWorstNodal (F : CurveFamily B hZ)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :
    IsFiniteNonSmoothLocus B hZ F := by
  classical
  let Tsch := BigFppfOver.toScheme B integerBase hZ
  let X := F.total.1
  have hX : IsAlgebraicSpace B integerBase hZ X := F.total.2
  let f : X ⟶ yoneda.obj F.base := F.toBase.hom
  let T : Set (Space.points B integerBase hZ X) := {x | ¬ Space.IsSmoothAt B integerBase hZ f x}
  have hT : IsClosed T := (Space.isOpen_setOf_isSmoothAt B integerBase hZ hX f).isClosed_compl
  let Z := Space.reducedClosedSubspace B integerBase hZ X hX T hT
  have hZcl : Space.IsClosedSubspace B integerBase hZ Z :=
    Space.isClosedSubspace_reducedClosedSubspace B integerBase hZ X hX T hT
  refine ⟨Z, hZcl, Space.range_pointsMap_ι_reducedClosedSubspace B integerBase hZ X hX T hT,
    Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B integerBase hZ X hX T hT, ?_⟩
  have hZa : IsAlgebraicSpace B integerBase hZ Z.toFunctor := hZcl.1
  have hY : IsAlgebraicSpace B integerBase hZ (yoneda.obj F.base) :=
    isAlgebraicSpace_yoneda B integerBase hZ F.base
  refine Space.isFinite_of_isProper_of_isLocallyQuasiFinite B integerBase hZ hZa hY _
    (Space.isProper_comp B integerBase hZ hZa hX hY Z.ι f
      (Space.isProper_ι_reducedClosedSubspace B integerBase hZ X hX T hT) F.proper) ?_
  -- the atlas from which the reduced closed subspace is built
  let U := Classical.choose hX.exists_atlas
  let φ : yoneda.obj U ⟶ X := Classical.choose (Classical.choose_spec hX.exists_atlas)
  have hs := (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
  have he := (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2
  -- a surjective étale chart of `Z`: the presentation of the reduced subscheme of the atlas
  have him := Space.isImmersion_arrow_atlasReducedSubscheme B integerBase hZ φ T hT
  have hci := Space.isClosedImmersion_arrow_atlasReducedSubscheme B integerBase hZ φ T hT
  obtain ⟨V, i, e, hei⟩ := Space.exists_presentation B integerBase hZ _ him
  obtain ⟨k, hk⟩ := Space.exists_isPullback_yoneda_presentation B integerBase hZ hs _
    (Space.isInvariantSubscheme_atlasReducedSubscheme B integerBase hZ hs he T hT) i e hei
  have hstabs := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Tsch)
  have hstabe := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsch)
  have hks := MorphismProperty.of_isPullback hk.flip hs
  have hke := MorphismProperty.of_isPullback hk.flip he
  -- the chart morphism of the family
  let g : U ⟶ F.base := yoneda.preimage (φ ≫ f)
  have hg : φ ≫ f = yoneda.map g := (yoneda.map_preimage (φ ≫ f)).symm
  have hnod : IsAtWorstNodalOfRelativeDimensionOne (Tsch.map g) :=
    hF U F.base φ (yoneda.map (𝟙 F.base)) g he
      (Space.presheaf_yoneda_map_id_etale B integerBase hZ F.base)
      (by rw [CategoryTheory.Functor.map_id]; exact (Category.comp_id _).trans hg.symm)
  obtain ⟨hflat, hlfp, hrd, -⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_fibres _).mp hnod
  have : Flat (Tsch.map g) := hflat
  have : LocallyOfFinitePresentation (Tsch.map g) := hlfp
  -- every point of the chart over the non-smooth locus is in the relative singular subscheme
  let I := relativeSingularIdeal (Tsch.map g)
  let J := Space.atlasVanishingIdeal B integerBase hZ φ T hT
  have hsupp : Space.atlasPointSet B integerBase hZ φ T ⊆ (I.support : Set (Tsch.obj U)) := by
    intro y hy
    have hmem : y ∈ Set.range I.subschemeι := by
      refine (mem_fittingIdeal_relativeDifferentials_iff_not_smoothAt (Tsch.map g) 1 hrd y).mpr
        fun hsm => hy ?_
      exact Space.isSmoothAt_pointsMap_of_smoothAt B integerBase hZ hX φ he f g hg y hsm
    rwa [Scheme.IdealSheafData.range_subschemeι] at hmem
  have hIJ : I ≤ J :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hsupp
  -- the chart of `Z` factors through the relative singular subscheme
  have : IsClosedImmersion (Space.atlasReducedSubscheme B integerBase hZ φ T hT).arrow := hci
  have hTi : IsClosedImmersion (Tsch.map i) := by
    rw [← hei]
    infer_instance
  let e' : Tsch.obj V ≅ Subobject.underlying.obj (Subobject.mk J.subschemeι) := e
  have hei' : e'.hom ≫ (Subobject.mk J.subschemeι).arrow = Tsch.map i := hei
  let m : Tsch.obj V ⟶ I.subscheme :=
    e'.hom ≫ (Subobject.underlyingIso J.subschemeι).hom ≫ Scheme.IdealSheafData.inclusion hIJ
  have hm : m ≫ I.subschemeι = Tsch.map i := by
    rw [← hei', Category.assoc, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
      Subobject.underlyingIso_hom_comp_eq_mk]
  have : LocallyOfFiniteType (m ≫ I.subschemeι) := by rw [hm]; infer_instance
  have : LocallyQuasiFinite (m ≫ I.subschemeι) := by rw [hm]; infer_instance
  have : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m I.subschemeι
  have : LocallyQuasiFinite m := LocallyQuasiFinite.of_comp m I.subschemeι
  have : Unramified (I.subschemeι ≫ Tsch.map g) := hnod.2
  have hP : ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) (Tsch.map (i ≫ g)) := by
    rw [Functor.map_comp, ← hm, Category.assoc]
    exact ⟨inferInstance, inferInstance⟩
  refine Space.holdsOnEveryEtaleChart_of_surjectiveChart B integerBase hZ _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    ⟨V, F.base, k, yoneda.map (𝟙 F.base), i ≫ g, hke,
      Space.presheaf_yoneda_map_id_etale B integerBase hZ F.base, hks, ?_, hP⟩
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, ← hg,
    ← Category.assoc, ← hk.w, Category.assoc]
  rfl

end CurveFamily

end AlgebraicGeometry

end
