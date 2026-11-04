module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.RingTheory.Henselian.ReducedDimensionOneNoetherianOfHenselization

/-!
# The henselian local ring at the generic point of a prime divisor

Let `X` be a decent, locally Noetherian, integral algebraic space and let `Z` be a prime
divisor of `X` with generic point `ξ`. The henselian local ring `𝒪^h_{X, ξ}` is a reduced,
Noetherian local ring of Krull dimension one (part of Stacks 0ENK).

## Main results

* `PrimeDivisor.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing`:
  the henselian local ring at the generic point of a prime divisor of a decent, locally
  Noetherian, integral algebraic space is reduced, of Krull dimension one, and Noetherian.
* `PrimeDivisor.isReduced_genericHenselianLocalRing`,
  `PrimeDivisor.ringKrullDim_genericHenselianLocalRing_eq_one`,
  `PrimeDivisor.isNoetherianRing_genericHenselianLocalRing`: the three properties separately.
* `PrimeDivisor.nontrivial_genericHenselianLocalRing`,
  `PrimeDivisor.krullDimLE_genericHenselianLocalRing`: the same local ring is nontrivial and of
  Krull dimension at most one.

## References

* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The henselian local ring at the generic point of a prime divisor of a decent, locally
Noetherian, integral algebraic space is reduced, of Krull dimension one, and Noetherian. -/
@[stacks 0ENK "the henselian local ring at the generic point of a prime divisor is a reduced
  1-dimensional Noetherian local ring; the canonical injection of the function field into its
  total ring of fractions is
  `AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing`"]
theorem
  PrimeDivisor.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
    _root_.IsReduced ↥(Z.genericHenselianLocalRing B S hS hX hdec) ∧
      ringKrullDim ↥(Z.genericHenselianLocalRing B S hS hX hdec) = 1 ∧
      IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) := by
  set ξ := Z.genericPoint B S hS X
  obtain ⟨E, -, -, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec ξ
  have hEetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf E.toSpace :=
    (isEtale_iff_presheaf_of_yoneda B S hS E.toSpace).1 E.etale_toSpace
  have hENoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj E.scheme) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) hX).mp hN E.scheme E.toSpace hEetale
  have hERed : IsReduced ((BigFppfOver.toScheme B S hS).obj E.scheme) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun T : Scheme.{u} => IsReduced T) hX).mp hInt.hasEtaleLocalProperty_isReduced
      E.scheme E.toSpace hEetale
  let : IsLocallyNoetherian E.scheme.left.1 := hENoeth
  let : IsReduced E.scheme.left.1 := hERed
  set R := E.scheme.left.1.presheaf.stalk E.point
  let : _root_.IsReduced R := isReduced_stalk_of_isReduced E.scheme.left.1 E.point
  let : IsNoetherianRing R := inferInstance
  let p : FieldValuedPoint B S hS (yoneda.obj E.scheme) :=
    ⟨E.scheme.left.1.residueField E.point, E.residueField_contained,
      E.scheme.left.1.fromSpecResidueField E.point ≫ E.scheme.hom.1,
      residueFieldMap B S hS E.scheme E.point E.residueField_contained⟩
  have hp : schemePoint B S hS E.scheme p = E.point :=
    E.scheme.left.1.fromSpecResidueField_apply E.point _
  have hChart : ChartPoint B S hS E.scheme E.toSpace E.point ξ := ⟨p, hp, E.map_point⟩
  have hdimChart : (localRingDimension B S hS ξ : WithBot ℕ∞) = ringKrullDim R :=
    localRingDimension_eq_of_chartPoint B S hS hX E.scheme E.toSpace hEetale E.point ξ hChart
  have hξgen : IsGenericPoint ξ (IrreducibleCloseds.closureSingleton ξ : Set (points B S hS X)) :=
    (IrreducibleCloseds.coe_closureSingleton ξ).symm
  have hcodim : codimension (IrreducibleCloseds.closureSingleton ξ) =
      localRingDimension B S hS ξ :=
    codimension_eq_localRingDimension B S hS hX hdec
      (IrreducibleCloseds.closureSingleton ξ) ξ hξgen
  have hdimR : ringKrullDim R = 1 := by
    rw [← hdimChart, ← hcodim, Z.codimension_genericPoint B S hS X]
    norm_cast
  let : IsLocalRing (henselianLocalRing B S hS X hX ξ hdec : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX ξ hdec
  let := stalkAlgebra B S hS X hX ξ hdec E
  let := henselianLocalRing_isHenselization B S hS X hX ξ hdec E
  exact StacksDraft.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization
    (R := R) (H := (henselianLocalRing B S hS X hX ξ hdec : Type (u + 1))) hdimR

/-- **Part of Stacks 0ENK.** The henselian local ring at the generic point of a prime divisor
of a decent, locally Noetherian, integral algebraic space is reduced. -/
theorem PrimeDivisor.isReduced_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
    _root_.IsReduced ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  (PrimeDivisor.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing
    B S hS hX hdec hInt hN Z).1

/-- **Part of Stacks 0ENK.** The henselian local ring at the generic point of a prime divisor
of a decent, locally Noetherian, integral algebraic space has Krull dimension one. -/
theorem PrimeDivisor.ringKrullDim_genericHenselianLocalRing_eq_one
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
    ringKrullDim ↥(Z.genericHenselianLocalRing B S hS hX hdec) = 1 :=
  (PrimeDivisor.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing
    B S hS hX hdec hInt hN Z).2.1

/-- **Part of Stacks 0ENK.** The henselian local ring at the generic point of a prime divisor
of a decent, locally Noetherian, integral algebraic space is Noetherian. -/
theorem PrimeDivisor.isNoetherianRing_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
    IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  (PrimeDivisor.isReduced_and_ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing
    B S hS hX hdec hInt hN Z).2.2

/-- The henselian local ring at the generic point of a prime divisor of a decent, locally
Noetherian, integral algebraic space is nontrivial. -/
theorem PrimeDivisor.nontrivial_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
    Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec) := by
  rw [← zero_le_ringKrullDim_iff_nontrivial,
    PrimeDivisor.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN Z]
  norm_num

/-- **Part of Stacks 0ENK.** The henselian local ring at the generic point of a prime divisor of
a decent, locally Noetherian, integral algebraic space has Krull dimension at most one. -/
theorem PrimeDivisor.krullDimLE_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
    Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec) := by
  rw [Ring.krullDimLE_iff,
    PrimeDivisor.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN Z]
  norm_num

end AlgebraicGeometry.Space

end
