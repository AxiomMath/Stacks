module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Henselian.NormalDomainOfHenselization

/-!
# The henselian local ring at the generic point of a prime divisor of a normal space

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S` which is
moreover **normal**, and let `Z` be a prime divisor of `X` with generic point `ξ`. Then
`𝒪^h_{X, ξ}` is a discrete valuation ring.

## Main results

* `PrimeDivisor.isDomain_and_isIntegrallyClosed_genericHenselianLocalRing`: on a normal decent
  algebraic space the henselian local ring at the generic point of a prime divisor is a normal
  domain.
* `PrimeDivisor.exists_isDiscreteValuationRing_genericHenselianLocalRing`: on a normal, decent,
  locally Noetherian, integral algebraic space it is a discrete valuation ring.

## References

* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **The henselian local ring at the generic point of a prime divisor of a normal space is a
normal domain.** -/
theorem PrimeDivisor.isDomain_and_isIntegrallyClosed_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hNormal : IsNormal B S hS X)
    (Z : PrimeDivisor B S hS X) :
    IsDomain ↥(Z.genericHenselianLocalRing B S hS hX hdec) ∧
      IsIntegrallyClosed ↥(Z.genericHenselianLocalRing B S hS hX hdec) := by
  set ξ := Z.genericPoint B S hS X
  obtain ⟨E, -, -, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec ξ
  have hEetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf E.toSpace :=
    (isEtale_iff_presheaf_of_yoneda B S hS E.toSpace).1 E.etale_toSpace
  have hENormal : _root_.AlgebraicGeometry.IsNormal
      ((BigFppfOver.toScheme B S hS).obj E.scheme) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsNormal T) hX).mp hNormal
      E.scheme E.toSpace hEetale
  let : _root_.AlgebraicGeometry.IsNormal E.scheme.left.1 := hENormal
  let : IsDomain (E.scheme.left.1.presheaf.stalk E.point) :=
    _root_.AlgebraicGeometry.IsNormal.stalk_isDomain E.point
  let : IsIntegrallyClosed (E.scheme.left.1.presheaf.stalk E.point) :=
    _root_.AlgebraicGeometry.IsNormal.stalk_normal E.point
  let : IsLocalRing (henselianLocalRing B S hS X hX ξ hdec : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX ξ hdec
  let := stalkAlgebra B S hS X hX ξ hdec E
  let := henselianLocalRing_isHenselization B S hS X hX ξ hdec E
  exact StacksDraft.isDomain_and_isIntegrallyClosed_of_isHenselization
    (R := E.scheme.left.1.presheaf.stalk E.point)
    (H := (henselianLocalRing B S hS X hX ξ hdec : Type (u + 1)))

/-- **The henselian local ring at the generic point of a prime divisor of a normal space is a
discrete valuation ring.** -/
theorem PrimeDivisor.exists_isDiscreteValuationRing_genericHenselianLocalRing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hNormal : IsNormal B S hS X) (Z : PrimeDivisor B S hS X) :
    ∃ _ : IsDomain ↥(Z.genericHenselianLocalRing B S hS hX hdec),
      IsDiscreteValuationRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) := by
  obtain ⟨hdom, hic⟩ :=
    Z.isDomain_and_isIntegrallyClosed_genericHenselianLocalRing B S hS hX hdec hNormal
  let : IsDomain ↥(Z.genericHenselianLocalRing B S hS hX hdec) := hdom
  let : IsIntegrallyClosed ↥(Z.genericHenselianLocalRing B S hS hX hdec) := hic
  let : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let : IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  refine ((isDiscreteValuationRing_tfae _).out 5 1).mp ?_
  exact ⟨inferInstance, inferInstance, hdom, hic,
    Z.ringKrullDim_genericHenselianLocalRing_eq_one B S hS hX hdec hInt hN⟩

end AlgebraicGeometry.Space

end
