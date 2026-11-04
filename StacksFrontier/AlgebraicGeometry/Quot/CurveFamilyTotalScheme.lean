module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SpacesImmersions

/-!
# The total space of a family of curves over a field is a scheme
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- The points of the total space of a family of curves over the spectrum of a field have local
rings of dimension at most one. -/
theorem localRingDimension_le_one_of_base_eq (x : CurveFamily B hZ) {K : Type u} [Field K]
    (hK : (BigFppfOver.toScheme B integerBase hZ).obj x.base = Spec (.of K))
    (y : Space.points B integerBase hZ x.total.obj) :
    Space.localRingDimension B integerBase hZ y ≤ 1 := by
  obtain ⟨base, total, toBase, hflat, hproper, hfp, hdim⟩ := x
  obtain ⟨⟨T₀, hT₀⟩, ⟨⟨⟩⟩, t⟩ := base
  change T₀ = Spec (.of K) at hK
  subst hK
  let p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj (Over.mk t)) :=
    { carrier := K
      contained := hT₀
      toBase := t.hom
      value := 𝟙 _ }
  have hbound : ∀ z : Space.points B integerBase hZ total.obj,
      Space.dimensionAtPoint B integerBase hZ total.obj total.property z ≤ 1 := by
    intro z
    obtain ⟨e, he, hrel⟩ := hdim z
    have h := (Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B integerBase hZ
      total.property p toBase.hom z (e : ℕ∞)).mp hrel
    rw [h]
    exact_mod_cast he
  have hsup := Space.iSup_dimensionAtPoint_eq_iSup_localRingDimension B integerBase hZ
    total.obj total.property
  have hle : (Space.localRingDimension B integerBase hZ y : WithBot ℕ∞) ≤ 1 :=
    (le_iSup (fun z : Space.points B integerBase hZ total.obj =>
      (Space.localRingDimension B integerBase hZ z : WithBot ℕ∞)) y).trans
      (hsup ▸ iSup_le hbound)
  exact_mod_cast hle

/-- **The total space of a family of curves over the spectrum of a field is a scheme.** It is
separated and locally Noetherian, being proper over a field, and its local rings have dimension at
most one; so every point lies in a representable open subspace (Stacks 0ADD), and an algebraic
space covered by representable open subspaces is representable (Stacks 03JH). -/
theorem isRepresentable_total_of_base_eq (x : CurveFamily B hZ) {K : Type u} [Field K]
    (hK : (BigFppfOver.toScheme B integerBase hZ).obj x.base = Spec (.of K)) :
    x.total.obj.IsRepresentable := by
  have hX := x.total.property
  have haff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj x.base) := by
    rw [hK]; infer_instance
  have hnoethBase : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj x.base) := by
    rw [hK]; infer_instance
  have hsep := Space.isAbsolutelySeparated_of_isSeparated_to_affine B integerBase hZ
    B.contains_terminal x.base haff x.toBase.hom x.proper.1
  have hnoeth := Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B
    integerBase hZ hX (isAlgebraicSpace_yoneda B integerBase hZ x.base) x.toBase.hom
    x.proper.2.1.1
    (Space.hasEtaleLocalProperty_of_representable B integerBase hZ _ _ x.base (Iso.refl _)
      hnoethBase)
  refine Space.isRepresentable_of_surjective_pointsMap_schematicLocus B integerBase hZ hX
    fun y => (Space.mem_range_pointsMap_schematicLocus_iff B integerBase hZ _ y).2 ?_
  exact Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one B integerBase hZ
    hX hsep hnoeth y (x.localRingDimension_le_one_of_base_eq hK y)

/-- **A thickening of a scheme is a scheme** (Stacks 05ZR), for algebraic spaces over the
big fppf site of the integers: the closed-immersion case of Stacks 07VS supplies the affine case
of the reduction to it. -/
theorem _root_.AlgebraicGeometry.Space.isRepresentable_target_of_isThickeningHom
    {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (hi : Space.IsThickeningHom B S hS i) (hX : X.1.IsRepresentable) :
    X'.1.IsRepresentable :=
  Space.isRepresentable_of_isThickeningHom_of_affineCase B S hS i hi hX
    fun j hP hW hj hsurj haff =>
      Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace B S hS j hP hW hj
        hsurj haff

/-- **The total space of a family of curves is a scheme as soon as it contains a scheme along a
thickening of the bases.** If `φ : x ⟶ y` is a morphism of families of curves whose morphism of
base schemes is a thickening and the total space of `x` is a scheme, then so is the total space
of `y`: the morphism of total spaces is the base change of the thickening of bases, hence a
thickening (Stacks 05ZK), and Stacks 05ZR applies. -/
theorem isRepresentable_total_of_hom {x y : CurveFamily B hZ} (φ : x ⟶ y)
    (hφ : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap))
    (hx : x.total.obj.IsRepresentable) : y.total.obj.IsRepresentable := by
  have hi : Space.IsThickeningHom B integerBase hZ (schemeSpaceMap φ.baseMap) :=
    FormalSpace.isThickeningHom_yonedaSpace_map B integerBase hZ φ.baseMap hφ
  exact Space.isRepresentable_target_of_isThickeningHom φ.totalMap
    (Space.IsThickeningHom.of_isPullback B integerBase hZ φ.cartesian.flip hi) hx

end CurveFamily

end AlgebraicGeometry
