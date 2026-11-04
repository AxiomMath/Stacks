module

public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NormalIntegralElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.RingTheory.ValuationRing.UnitFractionLocalHom

/-!
# `𝒪_{U, u}` is a discrete valuation ring, and unit-ness descends to it from `𝒪^h_{X, ξ}`

Let `X` be a normal, locally Noetherian, integral, decent algebraic space over a scheme `S`, let
`Z ⊂ X` be a prime divisor with generic point `ξ`, and let `(U, u)` be the chosen affine
elementary étale neighbourhood of `ξ`. The local ring `𝒪_{U, u}` —
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkRing` — is a *discrete valuation ring*, and the
coefficient `t / s_ξ` of Stacks 0EPR of a meromorphic section of an invertible `𝒪_X`-module is the
image of a **unit of `𝒪_{U, u}`** as soon as its image in `Q(𝒪^h_{X, ξ})` is the image of a unit of
`𝒪^h_{X, ξ}`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isNormal_genericChart`: the chart at the generic point of
  a prime divisor of a normal algebraic space is a normal scheme.
* `AlgebraicGeometry.Space.PrimeDivisor.coheight_genericChart_point`: its distinguished point has
  coheight one.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_isDiscreteValuationRing_genericStalkRing`:
  `𝒪_{U, u}` is a discrete valuation ring.
* `AlgebraicGeometry.Space.PrimeDivisor.isLocalHom_genericStalkSectionsToHenselian`: the
  henselization `𝒪_{U, u} → 𝒪^h_{X, ξ}` is a local homomorphism.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_genericStalkCoefficient_of_isUnit`: the
  coefficient of Stacks 0EPR is the image of a unit of `𝒪_{U, u}` as soon as the canonical ratio
  is the image of a unit of `𝒪^h_{X, ξ}`.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### `𝒪_{U, u}` is a discrete valuation ring -/

/-- The map from the chart at the generic point of a prime divisor to the space is étale, in the
sense of the presheaf-level property. -/
private theorem PrimeDivisor.etale_presheaf_genericChart_toSpace :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Z.genericChart B S hS hX hdec).toSpace :=
  (isEtale_iff_presheaf_of_yoneda B S hS (Z.genericChart B S hS hX hdec).toSpace).1
    (Z.genericChart B S hS hX hdec).etale_toSpace

/-- The chart at the generic point of a prime divisor of a normal algebraic space is a normal
scheme. -/
theorem PrimeDivisor.isNormal_genericChart (hNormal : IsNormal B S hS X) :
    AlgebraicGeometry.IsNormal
      ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme) :=
  (isNormal_iff_forall_etale B S hS X hX).mp hNormal
    (Z.genericChart B S hS hX hdec).scheme (Z.genericChart B S hS hX hdec).toSpace
    (Z.etale_presheaf_genericChart_toSpace B S hS hX hdec)

/-- The distinguished point of the chart at the generic point of a prime divisor has coheight
one. -/
theorem PrimeDivisor.coheight_genericChart_point :
    Order.coheight (Z.genericChart B S hS hX hdec).point = 1 := by
  refine coheight_eq_one_of_chartPoint_genericPoint B S hS hX hdec Z
    (Z.genericChart B S hS hX hdec).scheme (Z.genericChart B S hS hX hdec).toSpace
    (Z.etale_presheaf_genericChart_toSpace B S hS hX hdec)
    (Z.genericChart B S hS hX hdec).point ?_
  have hchart := chartPoint_pointsToScheme B S hS (Z.genericChart B S hS hX hdec).scheme
    (Z.genericChart B S hS hX hdec).toSpace
    (presheafPoint B S hS (Z.genericChart B S hS hX hdec).scheme
      (Z.genericChart B S hS hX hdec).point
      (Z.genericChart B S hS hX hdec).residueField_contained)
  rwa [pointsToScheme_presheafPoint B S hS (Z.genericChart B S hS hX hdec).scheme
    (Z.genericChart B S hS hX hdec).point
    (Z.genericChart B S hS hX hdec).residueField_contained,
    (Z.genericChart B S hS hX hdec).map_point] at hchart

/-- On a normal, locally Noetherian, decent algebraic space the local ring of the chosen chart at
the generic point of a prime divisor, at its distinguished point, is a discrete valuation ring. -/
theorem PrimeDivisor.exists_isDiscreteValuationRing_genericStalkRing
    (hNormal : IsNormal B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :
    ∃ _ : IsDomain ↥(Z.genericStalkRing B S hS hX hdec),
      IsDiscreteValuationRing ↥(Z.genericStalkRing B S hS hX hdec) := by
  have : AlgebraicGeometry.IsNormal
      ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme) :=
    Z.isNormal_genericChart B S hS hX hdec hNormal
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme) :=
    Z.isLocallyNoetherian_chart B S hS hX hN (Z.genericChart B S hS hX hdec)
  exact ⟨inferInstance, isDiscreteValuationRing_stalk_of_coheight_eq_one
    (Z.coheight_genericChart_point B S hS hX hdec)⟩

/-! ### The henselization out of `𝒪_{U, u}` is local -/

/-- The henselization `𝒪_{U, u} → 𝒪^h_{X, ξ}` at the generic point of a prime divisor is a local
homomorphism. -/
theorem PrimeDivisor.isLocalHom_genericStalkSectionsToHenselian :
    IsLocalHom (Z.genericStalkSectionsToHenselian B S hS hX hdec) := by
  have hloc : IsLocalHom (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      (Z.genericChart B S hS hX hdec)) :=
    isLocalHom_stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      (Z.genericChart B S hS hX hdec)
  set e : ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec))) ≃+* ↥(Z.genericStalkRing B S hS hX hdec) :=
    (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).commRingCatIsoToRingEquiv
  refine ⟨fun a h ↦ ?_⟩
  obtain ⟨u, hu⟩ : IsUnit (e a) := hloc.map_nonunit _ h
  refine IsUnit.of_mul_eq_one (e.symm ((u⁻¹ : _) : _)) (e.injective ?_)
  rw [map_mul, map_one, e.apply_symm_apply, ← hu]
  exact u.mul_inv

/-! ### Unit-ness descends from `𝒪^h_{X, ξ}` to `𝒪_{U, u}` -/

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-- The coefficient of Stacks 0EPR is the image of a unit of `𝒪_{U, u}` as soon as the canonical
ratio is the image of a unit of `𝒪^h_{X, ξ}`. -/
theorem PrimeDivisor.exists_isUnit_genericStalkCoefficient_of_isUnit
    (hNormal : IsNormal B S hS X) (t : MeromorphicSection.{u, u} B S hS X hX L)
    (v : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) (hv : IsUnit v)
    (hveq : Z.canonicalGenericRatio B S hS hX hdec L hL hInt hN t =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec) v) :
    ∃ a : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)), IsUnit a ∧
      Z.genericStalkCoefficient B S hS hX hdec L hL t =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) a := by
  obtain ⟨hdom, hdvr⟩ :=
    Z.exists_isDiscreteValuationRing_genericStalkRing B S hS hX hdec hNormal hN
  let : IsDomain ↥(Z.genericStalkRing B S hS hX hdec) := hdom
  let : IsDiscreteValuationRing ↥(Z.genericStalkRing B S hS hX hdec) := hdvr
  let e := (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).commRingCatIsoToRingEquiv
  let : IsDomain ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))) :=
    MulEquiv.isDomain ↥(Z.genericStalkRing B S hS hX hdec) e.toMulEquiv
  let e' : ↥(Z.genericStalkRing B S hS hX hdec) ≃+*
      ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec))) := e.symm
  let : IsDiscreteValuationRing ((structurePresheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e'
  let : IsFractionRing ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec)))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec))) :=
    Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN
  let : Field ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec))) :=
    IsFractionRing.toField ((structurePresheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1).obj (op (Z.genericStalkChart B S hS hX hdec)))
  let : Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  let : IsLocalHom (Z.genericStalkSectionsToHenselian B S hS hX hdec) :=
    Z.isLocalHom_genericStalkSectionsToHenselian B S hS hX hdec
  obtain ⟨a, ha, haeq⟩ := Stacks.ValuationRing.exists_isUnit_algebraMap_eq_of_isUnit_map
    (Z.genericStalkSectionsToHenselian B S hS hX hdec)
    (Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN)
    (Z.genericStalkMeromorphicToGeneric_algebraMap B S hS hX hdec hInt hN) hv hveq
  exact ⟨a, ha, haeq.symm⟩

end AlgebraicGeometry.Space

end
