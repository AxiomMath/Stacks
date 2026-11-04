module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationComplement
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.ConeEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Class
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisorUnit
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.GlobalParameter

/-!
# The class at infinity of the deformation to the normal cone

Let `(S, δ)` be as in chapter 42 of the Stacks Project, let `X` be locally of finite type over `S`
and let `i : Z ⟶ X` be a closed immersion. Let `π : D ⟶ X` be the deformation space
`D = Spec_X(𝒪_X[t⁻¹, ℐt])` of `Z ⊆ X`. The section `t⁻¹` of `𝒪_D` cuts out the normal cone
`C_ZX` (`Stacks.Deformation.ker_normalConeToDeformation`), its complement `D(t⁻¹)` is flat of
relative dimension one over `X` (`Stacks.Deformation.relativeDimension_complementOpen`), and
`𝒪_D` restricts trivially to `C_ZX`. So the general construction of Stacks 0F9J
(`Stacks.Chow.GysinAtInfinity.infinityClass`) gives a bivariant class

  `σ ∈ A⁰(C_ZX ⟶ X)`,  `σ ∩ α = i_∞^* β` for any `β ∈ A_{*+1}(D)` restricting to `α × 𝐆_m`.

The deformation space is the open subscheme `W ∖ X'` of the blowup `W` of `𝐏¹_X` in `∞(Z)` of
Stacks 0FBG, and its special fibre is the open `C_ZX = W_∞ ∖ X'` of `W_∞` of Stacks 0FBH; so `σ`
is the class `j^* ∘ C` of the construction preceding Stacks 0FBK, computed on the open where it
lives.

This file also identifies the zero scheme of `t⁻¹` with the normal cone and composes with the
closed immersion `C_ZX ⟶ N` of a virtual normal bundle
(`Stacks.Chow.VirtualNormalBundle.coneEmbedding`).

## Main definitions

* `Stacks.Deformation.deformationProjection` — `π : D ⟶ X`.
* `Stacks.Deformation.specialFibreIsoNormalCone` — `Z(t⁻¹) ≅ C_ZX`.
* `Stacks.Deformation.normalConeClass` — **the class `σ ∈ A⁰(Z(t⁻¹) ⟶ X)`.**
* `Stacks.Chow.VirtualNormalBundle.specialFibreEmbedding` — the closed immersion
  `Z(t⁻¹) ≅ C_ZX ⟶ N`.

## Main results

* `Stacks.Deformation.range_zeroScheme_paramGlobal` — `Z(t⁻¹)` is the complement of `D(t⁻¹)`.
* `Stacks.Chow.VirtualNormalBundle.specialFibreEmbedding_comp` — `Z(t⁻¹) ⟶ N ⟶ Z ⟶ X` is
  `Z(t⁻¹) ⟶ D ⟶ X`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.Conormal (coborderIdeal)

universe u

namespace Stacks.Deformation

section Support

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The zero scheme of `t⁻¹` is the complement of `D(t⁻¹)`.** -/
theorem range_zeroScheme_paramGlobal :
    Set.range (Stacks.Divisors.zeroScheme (deformationSpace I)
        (Scheme.unitModule (deformationSpace I)) (paramGlobal I)).subschemeι.base =
      (Set.range (complementOpen I).ι.base)ᶜ := by
  ext x
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Opens.range_ι]
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show deformationSpaceToBase I x ∈ (⊤ : X.Opens) from trivial)
  have hW' : IsAffineOpen (deformationSpaceToBase I ⁻¹ᵁ W) :=
    Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) ⟨W, hW⟩
  have h1 := Stacks.Divisors.basicOpen_eq_inf_compl_support_of_ideal_eq_span
    (Stacks.Divisors.zeroScheme (deformationSpace I) (Scheme.unitModule (deformationSpace I))
      (paramGlobal I)) ⟨_, hW'⟩ (paramChartOf I W) (zeroScheme_paramGlobal_ideal I ⟨W, hW⟩)
  have h2 := complementOpen_inf_preimage I W
  have hx : x ∈ deformationSpaceToBase I ⁻¹ᵁ W := hxW
  change x ∈ (Stacks.Divisors.zeroScheme _ _ _).support ↔ x ∉ (complementOpen I : Set _)
  refine ⟨fun hs hc => ?_, fun hc => ?_⟩
  · have : x ∈ complementOpen I ⊓ deformationSpaceToBase I ⁻¹ᵁ W := ⟨hc, hx⟩
    rw [h2, h1] at this
    exact this.2 hs
  · by_contra hs
    have : x ∈ (deformationSpace I).basicOpen (paramChartOf I W) := by
      rw [h1]
      exact ⟨hx, hs⟩
    rw [← h2] at this
    exact hc this.1

end Support

section Immersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The deformation space of `Z ⊆ X` over `X`: the deformation space of the ideal of `Z` in the
coborder neighbourhood of `i`, followed by the inclusion of that open. -/
abbrev deformationProjection : deformationSpace (coborderIdeal i) ⟶ X :=
  deformationSpaceToBase (coborderIdeal i) ≫ i.coborderRange.ι

/-- The zero scheme `Z(t⁻¹)` of the parameter on the deformation space. -/
abbrev specialFibre : (deformationSpace (coborderIdeal i)).IdealSheafData :=
  Stacks.Divisors.zeroScheme (deformationSpace (coborderIdeal i))
    (Scheme.unitModule (deformationSpace (coborderIdeal i))) (paramGlobal (coborderIdeal i))

/-- **The special fibre `Z(t⁻¹)` of the deformation space is the normal cone**: the closed
immersion `C_ZX ⟶ D` has the ideal of `Z(t⁻¹)`. -/
def specialFibreIsoNormalCone : (specialFibre i).subscheme ≅ Stacks.Conormal.normalCone i :=
  haveI := IsClosedImmersion.isIso_lift (normalConeToDeformation i) (specialFibre i).subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_normalConeToDeformation])
  asIso (IsClosedImmersion.lift (normalConeToDeformation i) (specialFibre i).subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_normalConeToDeformation]))

/-- The isomorphism `Z(t⁻¹) ≅ C_ZX` followed by `C_ZX ⟶ D` is the inclusion of `Z(t⁻¹)` in `D`. -/
@[reassoc (attr := simp)]
theorem specialFibreIsoNormalCone_hom_comp :
    (specialFibreIsoNormalCone i).hom ≫ normalConeToDeformation i =
      (specialFibre i).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- The special fibre lies over `Z`: `Z(t⁻¹) ⟶ D ⟶ X` is `Z(t⁻¹) ≅ C_ZX ⟶ Z ⟶ X`. -/
theorem specialFibre_ι_comp_deformationProjection :
    (specialFibre i).subschemeι ≫ deformationProjection i =
      (specialFibreIsoNormalCone i).hom ≫ Stacks.Conormal.normalConeToBase i ≫ i := by
  rw [← specialFibreIsoNormalCone_hom_comp, Category.assoc, deformationProjection,
    ← Category.assoc (normalConeToDeformation i), normalConeToDeformation_toBase, Category.assoc,
    Scheme.Hom.liftCoborder_ι]

/-- `D(t⁻¹) ⟶ X` is flat. -/
instance flat_complementOpen_deformationProjection :
    Flat ((complementOpen (coborderIdeal i)).ι ≫ deformationProjection i) := by
  rw [deformationProjection, ← Category.assoc]
  infer_instance

/-- `D(t⁻¹) ⟶ X` is locally of finite type. -/
instance locallyOfFiniteType_complementOpen_deformationProjection :
    LocallyOfFiniteType ((complementOpen (coborderIdeal i)).ι ≫ deformationProjection i) := by
  rw [deformationProjection, ← Category.assoc]
  infer_instance

/-- `D(t⁻¹) ⟶ X` has relative dimension one. -/
theorem relativeDimension_complementOpen_deformationProjection :
    AlgebraicGeometry.RelativeDimension
      ((complementOpen (coborderIdeal i)).ι ≫ deformationProjection i) 1 := by
  have h0 : AlgebraicGeometry.RelativeDimension i.coborderRange.ι 0 :=
    (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance
  exact AlgebraicGeometry.RelativeDimension.congr (Category.assoc _ _ _)
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ _
      (relativeDimension_complementOpen (coborderIdeal i)) h0)

/-- Over a locally Noetherian base the deformation space is locally of finite type. -/
instance locallyOfFiniteType_deformationProjection [IsLocallyNoetherian X] :
    LocallyOfFiniteType (deformationProjection i) := by
  have := locallyOfFiniteType_deformationSpaceToBase_of_isLocallyNoetherian (coborderIdeal i)
  infer_instance

end Immersion

section Class

variable (C : Stacks.Chow.ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i]

/-- **The class at infinity of the deformation to the normal cone**, `σ ∈ A⁰(Z(t⁻¹) ⟶ X)`: the
class of Stacks 0F9J for the divisor `Z(t⁻¹)` of the deformation space, whose complement `D(t⁻¹)`
is flat of relative dimension one over `X`. -/
def normalConeClass :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    Stacks.Chow.BivariantClass C (Stacks.Chow.gysinSystemOfInvertible C)
      ((specialFibre i).subschemeι ≫ (deformationProjection i ≫ sX)) sX
      ((specialFibre i).subschemeι ≫ deformationProjection i) (Category.assoc _ _ _) 0 :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  Stacks.Chow.GysinAtInfinity.infinityClass C sX (deformationProjection i)
    (complementOpen (coborderIdeal i)).ι
    (relativeDimension_complementOpen_deformationProjection i)
    (Scheme.unitModule (deformationSpace (coborderIdeal i))) (paramGlobal (coborderIdeal i))
    (range_zeroScheme_paramGlobal (coborderIdeal i))
    (Stacks.Chow.isTrivial_pullback_unitModule _)

end Class

end Stacks.Deformation

namespace Stacks.Chow.VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i)

/-- **The closed immersion `Z(t⁻¹) ≅ C_ZX ⟶ N`** of the special fibre of the deformation space into
the vector bundle of the virtual normal bundle. -/
def specialFibreEmbedding :
    (Stacks.Deformation.specialFibre i).subscheme ⟶
      Scheme.Modules.vectorBundle Z (dualSheaf 𝒩.bundle) :=
  (Stacks.Deformation.specialFibreIsoNormalCone i).hom ≫ 𝒩.coneEmbedding

/-- `Z(t⁻¹) ⟶ N` is a closed immersion. -/
instance isClosedImmersion_specialFibreEmbedding : IsClosedImmersion 𝒩.specialFibreEmbedding := by
  unfold specialFibreEmbedding
  infer_instance

/-- `Z(t⁻¹) ⟶ N ⟶ Z ⟶ X` is `Z(t⁻¹) ⟶ D ⟶ X`. -/
theorem specialFibreEmbedding_comp :
    𝒩.specialFibreEmbedding ≫ (Scheme.Modules.vectorBundleToBase Z (dualSheaf 𝒩.bundle) ≫ i) =
      (Stacks.Deformation.specialFibre i).subschemeι ≫
        Stacks.Deformation.deformationProjection i := by
  rw [Stacks.Deformation.specialFibre_ι_comp_deformationProjection, specialFibreEmbedding,
    Category.assoc, ← Category.assoc 𝒩.coneEmbedding, coneEmbedding_toBase]

end Stacks.Chow.VirtualNormalBundle

end
