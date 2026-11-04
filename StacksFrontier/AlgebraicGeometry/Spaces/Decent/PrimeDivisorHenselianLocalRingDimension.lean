module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianLocalRing
public import StacksFrontier.RingTheory.Henselian.DimensionOneNoetherianOfHenselization

/-!
# The henselian local ring at the generic point of a prime divisor of a space that is not integral

Let `X` be a decent, locally Noetherian algebraic space — *not* assumed integral — and let `Z`
be a prime divisor of `X` with generic point `ξ`. Then `𝒪^h_{X, ξ}` is a Noetherian local ring
of Krull dimension one.

## Main results

* `PrimeDivisor.ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing`: for a decent,
  locally Noetherian algebraic space, the henselian local ring at the generic point of a prime
  divisor is Noetherian of Krull dimension one.

## References

* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)
* [Stacks Project, Tag 06LK](https://stacks.math.columbia.edu/tag/06LK)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The henselian local ring at the generic point of a prime divisor of a decent, locally
Noetherian algebraic space is Noetherian of Krull dimension one.** No integrality is assumed of
the ambient space, so the ring need not be reduced. -/
theorem PrimeDivisor.ringKrullDim_eq_one_and_isNoetherianRing_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X) :
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
  let : IsLocallyNoetherian E.scheme.left.1 := hENoeth
  set R := E.scheme.left.1.presheaf.stalk E.point
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
  have hdimR : ringKrullDim R = 1 := by
    rw [← hdimChart, ← codimension_eq_localRingDimension B S hS hX hdec
      (IrreducibleCloseds.closureSingleton ξ) ξ hξgen, Z.codimension_genericPoint B S hS X]
    norm_cast
  let : IsLocalRing (henselianLocalRing B S hS X hX ξ hdec : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX ξ hdec
  let := stalkAlgebra B S hS X hX ξ hdec E
  let := henselianLocalRing_isHenselization B S hS X hX ξ hdec E
  exact StacksDraft.ringKrullDim_eq_one_and_isNoetherianRing_of_isHenselization
    (R := R) (H := (henselianLocalRing B S hS X hX ξ hdec : Type (u + 1))) hdimR

end AlgebraicGeometry.Space

end
