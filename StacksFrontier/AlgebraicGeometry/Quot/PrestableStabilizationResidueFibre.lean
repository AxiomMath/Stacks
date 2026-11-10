module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionEtaleLocal

/-!
# The fibre of a contraction at a point, read over the residue field of the point

Let `c : X ⟶ Y` be a morphism over `S` of families of curves, and let `ū : P ⟶ S` be a morphism
from the spectrum `P` of a field whose point `x` maps to `u ∈ S` with `κ(u) ≅ κ(x)`. If the fibre
of `c` over `ū`, presented by schemes `V` and `G` of the site, satisfies `𝒪 = a_*𝒪` and
`R¹a_*𝒪 = 0`, then so does the base change of `c` along the point `Spec κ(u) ⟶ S` of the site:
the two fibres differ by the isomorphism `P ≅ Spec κ(u)`. This identifies the fibre produced by
Stacks 0E7C over an elementary étale neighbourhood with the fibre appearing in Stacks 0E88.

## Main results

* `AlgebraicGeometry.CurveFamily.isStructureContraction_residueFieldMap_of_fibre`: the transport.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The fibre of a contraction over the residue field of a point.** Let `c : X ⟶ Y` be a
morphism over `S` of families of curves, `ū : P ⟶ S` a morphism of the site whose source is the
spectrum of a field (`Spec κ(x) ≅ P`), inducing an isomorphism of residue fields at `x`, with image
`u`. If `V` and `G` present the fibres of `X` and `Y` over `ū` and the fibre `a : V ⟶ G` of `c`
satisfies `𝒪 = a_*𝒪` and `R¹a_*𝒪 = 0`, then so does the base change of `c` along the point
`Spec κ(u) ⟶ S`. -/
theorem isStructureContraction_residueFieldMap_of_fibre (X Y : CurveFamily B hZ)
    (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    {P : BigFppfOver B integerBase hZ} (ū : P ⟶ X.base) (x : P.left.1) (s : X.base.left.1)
    (hxs : ū.left.1 x = s) (hx : IsIso (P.left.1.fromSpecResidueField x))
    (hres : IsIso (ū.left.1.residueFieldMap x)) {V G : BigFppfOver B integerBase hZ} (v : V ⟶ P)
    (tG : G ⟶ P) (qV : schemeSpace V ⟶ X.total) (qG : schemeSpace G ⟶ Y.total)
    (sqV : IsPullback qV (schemeSpaceMap v) X.toBase (schemeSpaceMap ū))
    (sqG : IsPullback qG (schemeSpaceMap tG) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb))
      (schemeSpaceMap ū))
    (a : V ⟶ G) (ha₁ : schemeSpaceMap a ≫ qG = qV ≫ c) (ha₂ : a ≫ tG = v)
    (hA : Space.IsStructureContraction B integerBase hZ (schemeSpaceMap a)) :
    Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base s
          (B.residueField_spec_contains X.base.left.property s)))) := by
  subst hxs
  have := hx
  have := hres
  set gY := Y.toBase ≫ eqToHom (congrArg schemeSpace hb)
  -- `P ≅ Spec κ(u)` over `S`
  let ρ := Space.residueFieldMap B integerBase hZ X.base (ū.left.1 x)
    (B.residueField_spec_contains X.base.left.property (ū.left.1 x))
  let ι₀ := Space.residueFieldObjectMap B integerBase hZ P X.base ū x
  let rP := Space.residueFieldMap B integerBase hZ P x
    (B.residueField_spec_contains P.left.property x)
  have : IsIso ι₀ := Space.isIso_residueFieldObjectMap B integerBase hZ P X.base ū x
  have : IsIso rP := by
    have : IsIso (B.inclusion.map ((Over.forget (B.obj hZ)).map rP)) := by
      change IsIso (P.left.1.fromSpecResidueField x)
      infer_instance
    have : IsIso ((Over.forget (B.obj hZ)).map rP) :=
      isIso_of_reflects_iso _ B.inclusion
    exact isIso_of_reflects_iso _ (Over.forget _)
  let ι : P ⟶ _ := inv rP ≫ ι₀
  have hι : ι ≫ ρ = ū := by
    simp only [ι, Category.assoc]
    rw [Space.residueFieldObjectMap_comp, IsIso.inv_hom_id_assoc]
  have : IsIso (schemeSpaceMap ι) := Functor.map_isIso (schemeSpaceFunctor B integerBase hZ) ι
  have hι' : schemeSpaceMap ι ≫ schemeSpaceMap ρ = schemeSpaceMap ū := by
    rw [← schemeSpaceMap_comp, hι]
  -- the fibres over `Spec κ(u)`
  have sqX := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap ρ)
  have sqY := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ gY (schemeSpaceMap ρ)
  let iX := sqX.lift qV (schemeSpaceMap v ≫ schemeSpaceMap ι) (by rw [sqV.w, Category.assoc, hι'])
  let iY := sqY.lift qG (schemeSpaceMap tG ≫ schemeSpaceMap ι) (by rw [sqG.w, Category.assoc, hι'])
  have : IsIso iX := (IsPullback.of_right (by rw [sqX.lift_fst, hι']; exact sqV)
    (sqX.lift_snd _ _ _) sqX).isIso_fst_of_isIso inferInstance
  have : IsIso iY := (IsPullback.of_right (by rw [sqY.lift_fst, hι']; exact sqG)
    (sqY.lift_snd _ _ _) sqY).isIso_fst_of_isIso inferInstance
  have hsq : IsPullback iX (schemeSpaceMap a)
      (Space.structureContractionBaseChange B integerBase hZ c hc (schemeSpaceMap ρ)) iY := by
    refine IsPullback.of_horiz_isIso ⟨sqY.hom_ext ?_ ?_⟩
    · rw [Category.assoc, Space.structureContractionBaseChange_fst, ← Category.assoc,
        sqX.lift_fst, Category.assoc, sqY.lift_fst, ha₁]
    · rw [Category.assoc, Space.structureContractionBaseChange_snd, sqX.lift_snd,
        Category.assoc, sqY.lift_snd, ← Category.assoc, ← ha₂, schemeSpaceMap_comp]
  exact (Space.isStructureContraction_iff_of_isPullback_of_isIso hsq).2 hA

end CurveFamily

end AlgebraicGeometry

end
