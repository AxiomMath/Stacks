module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericHenselianSpaceCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent

/-!
# `𝒦(Spec(𝒪^h_{X, ξ})) = Q(𝒪^h_{X, ξ})`

Let `X` be a decent, locally Noetherian, integral algebraic space over `S` and let `Z ⊆ X` be a
prime divisor with generic point `ξ`.  Let `R` be a henselization of the Zariski local ring of
`AlgebraicGeometry.Space.PrimeDivisor.genericChart`, assumed reduced and Noetherian.  The
meromorphic functions of the algebraic space `Spec(R)` over its identity étale chart form a total
ring of fractions of `R`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericMeromorphicFunctions`: the
  meromorphic functions of `Spec(𝒪^h_{X, ξ})` over the identity étale chart are a total ring of
  fractions of `𝒪^h_{X, ξ}`, the algebra structure being the one
  `AlgebraicGeometry.Space.PrimeDivisor.genericToMeromorphicFunctions` gives.

* `AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericMeromorphicChartRing`: the same,
  over `AlgebraicGeometry.Space.meromorphicChartRing`.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  (hR : B.Contains (Spec (.of R)))

include hX hdec Z in
/-- The ring of meromorphic functions of `Spec(𝒪^h_{X, ξ})` over the identity étale chart is a
total ring of fractions of `𝒪^h_{X, ξ}`, for a reduced Noetherian henselization `𝒪^h_{X, ξ}` at
the generic point `ξ` of a prime divisor. -/
theorem PrimeDivisor.isFractionRing_genericMeromorphicFunctions
    (hred : _root_.IsReduced R) (hnoeth : IsNoetherianRing R) :
    letI : Algebra R ((meromorphicFunctionSheaf B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property).obj.obj
        (op (Z.genericHenselianChart B S hS hX hdec R hR))) :=
      (((toMeromorphicFunctionSheaf B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
            (Z.genericHenselianSpace B S hS hX hdec R hR).property).hom.app
          (op (Z.genericHenselianChart B S hS hX hdec R hR))).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
    IsFractionRing R ((meromorphicFunctionSheaf B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property).obj.obj
      (op (Z.genericHenselianChart B S hS hX hdec R hR))) := by
  let : Algebra R ((meromorphicFunctionSheaf B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property).obj.obj
      (op (Z.genericHenselianChart B S hS hX hdec R hR))) :=
    (((toMeromorphicFunctionSheaf B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianSpace B S hS hX hdec R hR).property).hom.app
        (op (Z.genericHenselianChart B S hS hX hdec R hR))).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
  let : Algebra (Γ(Spec (CommRingCat.of R), ⊤))
      ((meromorphicFunctionSheaf B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property).obj.obj
        (op (Z.genericHenselianChart B S hS hX hdec R hR))) :=
    ((toMeromorphicFunctionSheaf B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property).hom.app
      (op (Z.genericHenselianChart B S hS hX hdec R hR))).hom.toAlgebra
  have : IsFractionRing (Γ(Spec (CommRingCat.of R), ⊤))
      ((meromorphicFunctionSheaf B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property).obj.obj
        (op (Z.genericHenselianChart B S hS hX hdec R hR))) :=
    isFractionRing_meromorphicFunctionSheaf_obj B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR)
      (Z.forall_localRingDimension_genericHenselianSpace_eq_zero B S hS hX hdec R hR hred)
      (Z.hasLocallyFiniteIrreducibleComponents_genericHenselianSpace B S hS hX hdec R hR hnoeth)
      (Z.genericHenselianChart B S hS hX hdec R hR)
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of R))))
  exact IsFractionRing.of_ringEquiv_left
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv fun _ => rfl

include hX hdec Z in
/-- `AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericMeromorphicFunctions` over
`AlgebraicGeometry.Space.meromorphicChartRing`, with the algebra structure given by
`AlgebraicGeometry.Space.PrimeDivisor.genericToMeromorphicFunctions`. -/
theorem PrimeDivisor.isFractionRing_genericMeromorphicChartRing
    (hred : _root_.IsReduced R) (hnoeth : IsNoetherianRing R) :
    letI : Algebra R (meromorphicChartRing B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianChart B S hS hX hdec R hR)) :=
      (Z.genericToMeromorphicFunctions B S hS hX hdec R hR).toAlgebra
    IsFractionRing R (meromorphicChartRing B S hS
      (Z.genericHenselianSpace B S hS hX hdec R hR).obj
      (Z.genericHenselianSpace B S hS hX hdec R hR).property
      (Z.genericHenselianChart B S hS hX hdec R hR)) :=
  Z.isFractionRing_genericMeromorphicFunctions B S hS hX hdec R hR hred hnoeth

end Generic

end AlgebraicGeometry.Space

end
