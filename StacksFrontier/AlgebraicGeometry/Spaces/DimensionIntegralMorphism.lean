module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Dimension under an integral morphism of algebraic spaces

An integral morphism of algebraic spaces over a scheme `S` does not increase the dimension, and
preserves it when it is surjective. Dimensions are taken in `WithBot ℕ∞`, as for
`AlgebraicGeometry.Space.dimension`.

## Main results

* `AlgebraicGeometry.Space.dimension_le_of_isIntegralHom` and
  `AlgebraicGeometry.Space.dimension_eq_of_isIntegralHom_of_isSurjective` are the two
  assertions of **Stacks 0EDB**.

## References

* [Stacks Project, Tag 0EDB](https://stacks.math.columbia.edu/tag/0EDB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The dimension of a represented algebraic space is the Krull dimension of the representing
scheme. -/
private theorem dimension_yoneda_eq_krullDim (T : BigFppfOver B S hS) :
    dimension B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj T) := by
  classical
  let X := (BigFppfOver.toScheme B S hS).obj T
  have hdim : topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt X x := by
    simpa only [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] using
      TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim X
  have hId := AlgebraicGeometry.Space.presheaf_etale_id B S hS T
  rw [dimension, hdim]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    rw [dimensionAtPoint_eq_of_etale_chart B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) (p.class B S hS (yoneda.obj T)) T
      (𝟙 (yoneda.obj T)) hId p rfl]
    exact le_iSup (fun z : X ↦ topologicalKrullDimAt X z) (schemePoint B S hS T p)
  · refine iSup_le fun x => ?_
    let p := schemePointRepresentative B S hS T x
    rw [← schemePointRepresentative_point B S hS T x,
      ← dimensionAtPoint_eq_of_etale_chart B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) (p.class B S hS (yoneda.obj T)) T
        (𝟙 (yoneda.obj T)) hId p rfl]
    exact le_iSup (fun y : points B S hS (yoneda.obj T) ↦
      dimensionAtPoint B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) y)
      (p.class B S hS (yoneda.obj T))

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An integral morphism of algebraic spaces over `S` becomes an integral morphism of schemes
over a surjective étale chart of its target, and both dimensions are the Krull dimensions of
the two schemes in that chart. -/
private theorem exists_integral_chart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsIntegralHom B S hS f) :
    ∃ (V W : BigFppfOver B S hS) (p : W ⟶ V) (a : yoneda.obj W ⟶ X)
      (g : yoneda.obj V ⟶ Y),
      IsPullback a (yoneda.map p) f g ∧
        _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p) ∧
        dimension B S hS X hX =
          topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj W) ∧
        dimension B S hS Y hY =
          topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj V) := by
  obtain ⟨V, g, hgSurj, hgEt⟩ := hY.exists_atlas
  obtain ⟨hrep, hprop⟩ := (isIntegralHom_iff_representable B S hS f hX hY).mp hf
  have hbc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    have := inverseImage_isStableUnderBaseChange B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
    MorphismProperty.relative_isStableUnderBaseChange _
  have hgEtale : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).mpr hgEt
  have hgSurjPts : IsSurjective B S hS g :=
    (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hgSurj
  have haEt : IsEtale B S hS (hrep.fst g) :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).mpr
      (hbc.of_isPullback (hrep.isPullback g).flip hgEt)
  have haSurj : IsSurjective B S hS (hrep.fst g) :=
    surjective_pointsMap_of_isPullback B S hS (hrep.isPullback g).flip hgSurjPts
  refine ⟨V, hrep.pullback g, hrep.snd g, hrep.fst g, g, hrep.isPullback g,
    hprop.property g (hrep.fst g) (hrep.snd g) (hrep.isPullback g), ?_, ?_⟩
  · rw [← dimension_eq_of_isEtale_of_isSurjective B S hS
      (isAlgebraicSpace_yoneda B S hS (hrep.pullback g)) hX (hrep.fst g) haEt haSurj,
      dimension_yoneda_eq_krullDim]
  · rw [← dimension_eq_of_isEtale_of_isSurjective B S hS
      (isAlgebraicSpace_yoneda B S hS V) hY g hgEtale hgSurjPts,
      dimension_yoneda_eq_krullDim]

/-- An integral morphism of algebraic spaces over `S` does not increase the dimension. -/
@[stacks 0EDB "dimension inequality"]
theorem dimension_le_of_isIntegralHom (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsIntegralHom B S hS f) :
    dimension B S hS X hX ≤ dimension B S hS Y hY := by
  obtain ⟨V, W, p, a, g, sq, hpInt, hdimW, hdimV⟩ := exists_integral_chart B S hS hX hY f hf
  rw [hdimW, hdimV]
  exact AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom
    ((BigFppfOver.toScheme B S hS).map p)

/-- A surjective integral morphism of algebraic spaces over `S` preserves the dimension. -/
@[stacks 0EDB "surjective case"]
theorem dimension_eq_of_isIntegralHom_of_isSurjective (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsIntegralHom B S hS f)
    (hsurj : IsSurjective B S hS f) :
    dimension B S hS X hX = dimension B S hS Y hY := by
  obtain ⟨V, W, p, a, g, sq, hpInt, hdimW, hdimV⟩ := exists_integral_chart B S hS hX hY f hf
  have : Surjective ((BigFppfOver.toScheme B S hS).map p) :=
    (AlgebraicGeometry.surjective_iff _).mpr
      ((surjective_pointsMap_yoneda_iff B S hS p).mp
        (surjective_pointsMap_of_isPullback B S hS sq hsurj))
  rw [hdimW, hdimV]
  exact AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective
    ((BigFppfOver.toScheme B S hS).map p)

end AlgebraicGeometry.Space

end
