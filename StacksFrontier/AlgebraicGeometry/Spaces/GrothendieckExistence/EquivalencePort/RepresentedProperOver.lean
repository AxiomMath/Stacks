module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedAffineLiftStep
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Closed subsets proper over the base, for a represented algebraic space

For a morphism `q : U ⟶ V` of the big fppf site, a closed subset `Z` of the scheme of `U` is
proper over the scheme of `V` (Stacks 0CYM) exactly when the corresponding closed set of points
of the algebraic space `h_U` is proper over `h_V` (Stacks 0CZD)
(`AlgebraicGeometry.Space.C1573.isProperOver_yoneda_map_iff`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An immersion into the scheme of an object of the site, as an object of the site. -/
def C1573.immersionSiteObject {U : BigFppfOver B S hS} {W : Scheme.{u}}
    (i : W ⟶ (BigFppfOver.toScheme B S hS).obj U) [_root_.AlgebraicGeometry.IsImmersion i] :
    BigFppfOver B S hS :=
  Over.mk (⟨i ≫ U.hom.hom⟩ : B.obj (contains_of_isImmersion B U.left.2 i) ⟶ B.obj hS)

/-- An immersion into the scheme of an object of the site, as a morphism of the site. -/
def C1573.immersionSiteHom {U : BigFppfOver B S hS} {W : Scheme.{u}}
    (i : W ⟶ (BigFppfOver.toScheme B S hS).obj U) [_root_.AlgebraicGeometry.IsImmersion i] :
    immersionSiteObject B S hS i ⟶ U :=
  Over.homMk ⟨i⟩ rfl

/-- The scheme morphism underlying `C1573.immersionSiteHom B S hS i` is the immersion `i`. -/
theorem C1573.toScheme_map_immersionSiteHom {U : BigFppfOver B S hS} {W : Scheme.{u}}
    (i : W ⟶ (BigFppfOver.toScheme B S hS).obj U) [_root_.AlgebraicGeometry.IsImmersion i] :
    (BigFppfOver.toScheme B S hS).map (immersionSiteHom B S hS i) = i := rfl

/-- The points of `h_U` lying in the range of the image of an immersion of schemes are those
whose scheme point lies in its range. -/
theorem C1573.range_pointsMap_yoneda_map_eq_preimage_pointsEquivScheme {U R : BigFppfOver B S hS}
    (j : R ⟶ U) :
    Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)) =
      pointsEquivScheme B S hS U ⁻¹' Set.range ((BigFppfOver.toScheme B S hS).map j) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨pointsEquivScheme B S hS R y, (pointsEquivScheme_pointsMap_yoneda_map B S hS j y).symm⟩
  · rintro ⟨w, hw⟩
    refine ⟨(pointsEquivScheme B S hS R).symm w, (pointsEquivScheme B S hS U).injective ?_⟩
    rwa [pointsEquivScheme_pointsMap_yoneda_map, Equiv.apply_symm_apply]

/-- The points of the range subfunctor of a monomorphism are the image of its points. -/
theorem C1573.range_pointsMap_range_ι {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) [Mono p] :
    Set.range (pointsMap B S hS (Subfunctor.range p).toFunctor (Subfunctor.range p).ι) =
      Set.range (pointsMap B S hS F p) := by
  have e : pointsMap B S hS F p = pointsMap B S hS _ (Subfunctor.range p).ι ∘
      pointsMap B S hS F (Subfunctor.toRange p) := by
    rw [← pointsMap_comp, Subfunctor.toRange_ι]
  have h2 : pointsMap B S hS F (Subfunctor.toRange p) ∘
      pointsMap B S hS _ (inv (Subfunctor.toRange p)) = id := by
    rw [← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id]
  rw [e]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨pointsMap B S hS _ (inv (Subfunctor.toRange p)) y,
      congrArg (pointsMap B S hS _ (Subfunctor.range p).ι) (congrFun h2 y)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨pointsMap B S hS F (Subfunctor.toRange p) y, rfl⟩

/-- **A closed subset of the scheme of `U` is proper over `V` exactly when the corresponding
closed set of points of `h_U` is proper over `h_V`.** -/
theorem C1573.isProperOver_yoneda_map_iff {U V : BigFppfOver B S hS} (q : U ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q)]
    (hq : IsLocallyOfFiniteType B S hS (yoneda.map q))
    (Z : Closeds ((BigFppfOver.toScheme B S hS).obj U))
    (hcl : IsClosed (pointsEquivScheme B S hS U ⁻¹' (Z : Set _))) :
    IsProperOver B S hS (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
        (yoneda.map q) hq (pointsEquivScheme B S hS U ⁻¹' (Z : Set _)) hcl ↔
      _root_.AlgebraicGeometry.IsProperOver ((BigFppfOver.toScheme B S hS).map q) Z := by
  let g := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  let j := immersionSiteHom B S hS g
  have hZf := isClosedSubspace_range_yoneda_map B S hS j
    (inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion g))
  have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map (inferInstanceAs (Mono g))
  have hrange : Set.range (pointsMap B S hS (Subfunctor.range (yoneda.map j)).toFunctor
      (Subfunctor.range (yoneda.map j)).ι) = pointsEquivScheme B S hS U ⁻¹' (Z : Set _) := by
    rw [range_pointsMap_range_ι, range_pointsMap_yoneda_map_eq_preimage_pointsEquivScheme]
    congr 1
    exact (Scheme.IdealSheafData.range_subschemeι _).trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  have hprop : IsProper B S hS ((Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map q) ↔
      _root_.AlgebraicGeometry.IsProper (g ≫ (BigFppfOver.toScheme B S hS).map q) := by
    have hfac : Subfunctor.toRange (yoneda.map j) ≫
        ((Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map q) = yoneda.map (j ≫ q) := by
      rw [← Category.assoc, Subfunctor.toRange_ι, Functor.map_comp]
    have hfac' : (Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map q =
        inv (Subfunctor.toRange (yoneda.map j)) ≫ yoneda.map (j ≫ q) := by
      rw [← hfac, IsIso.inv_hom_id_assoc]
    have hsch : (BigFppfOver.toScheme B S hS).map (j ≫ q) =
        g ≫ (BigFppfOver.toScheme B S hS).map q := Functor.map_comp _ _ _
    constructor
    · intro h
      have h' := isProper_comp' B S hS _ _ hZf.1 (isAlgebraicSpace_yoneda B S hS V)
        (isProper_of_isIso B S hS (Subfunctor.toRange (yoneda.map j))) h
      rw [hfac] at h'
      exact hsch ▸ isProper_toScheme_map_of_isProper_yoneda_map B S hS (j ≫ q) h'
    · intro h
      rw [hfac']
      exact isProper_comp' B S hS _ _ (isAlgebraicSpace_yoneda B S hS _)
        (isAlgebraicSpace_yoneda B S hS V)
        (isProper_of_isIso B S hS (inv (Subfunctor.toRange (yoneda.map j))))
        (isProper_yoneda_map B S hS (j ≫ q) (hsch ▸ h))
  rw [isProper_reducedClosedSubspace_iff_exists]
  exact ⟨fun h => hprop.1 ((exists_isProper_closedSubspace_iff_forall B S hS
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V) (yoneda.map q) hq _
      hcl).1 h _ hZf hrange), fun h => ⟨_, hZf, hrange, hprop.2 h⟩⟩

end AlgebraicGeometry.Space

end
