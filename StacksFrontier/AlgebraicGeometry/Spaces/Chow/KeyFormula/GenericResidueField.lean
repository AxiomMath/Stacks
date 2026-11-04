module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints

/-!
# The residue field at the generic point of a prime divisor is its function field

Let `X` be a decent algebraic space over a scheme `S`, let `Z ⊂ X` be a prime divisor with
generic point `ξ`, and let `(U, u)` be the chosen affine elementary étale neighbourhood of `ξ`,
`AlgebraicGeometry.Space.PrimeDivisor.genericChart`.  Section 0EQU of the Stacks project
identifies the residue field `κ(ξ)` with the function field `R(Z)` of `Z`, and the residue field
of `𝒪^h_{X, ξ}` with `κ(ξ)` (Stacks 0EN0).  This file makes both identifications canonical, at
the residue field `κ(u)` of the local ring `𝒪_{U, u}` of the chart.

The construction is the source's.  The closed point of `Spec 𝒪_{U, u}` gives the morphism
`ρ_Z : Spec κ(u) → U → X`, which is a monomorphism because `(U, u)` is elementary.  Its image
is `ξ ∈ |Z|` and `Spec κ(u)` is reduced, so it factors through the closed subspace `Z` by
Stacks 03JJ at the reduced closed subspace on `|Z|` (`Z` is integral, hence reduced, so it *is*
that subspace by Stacks 03IQ).  The factorization is a monomorphic field-valued representative
of the generic point of the integral space `Z`, so evaluation of rational functions of `Z` at it
is a ring isomorphism `R(Z) ≅ κ(u)` by Stacks 0END; its inverse is `θ_Z`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericResidueField` is `κ(u)`, the residue field of
  `AlgebraicGeometry.Space.PrimeDivisor.genericStalkRing`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldPoint` is `ρ_Z`, as a field-valued point of
  the integral space `Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.functionFieldToGenericResidueField` is evaluation
  `R(Z) → κ(u)` at `ρ_Z`, and
  `AlgebraicGeometry.Space.PrimeDivisor.genericResidueFieldEquivFunctionField` is the resulting
  isomorphism `θ_Z : κ(u) ≃+* R(Z)`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericResidueFieldEquivHenselian` is the canonical
  isomorphism `κ(u) ≃+* κ(𝒪^h_{X, ξ})` induced by the henselization map, and
  `AlgebraicGeometry.Space.PrimeDivisor.henselianResidueFieldEquivFunctionField` the composite
  `κ(𝒪^h_{X, ξ}) ≃+* R(Z)`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.fieldMorphism_genericFieldPoint_comp_ι`: `ρ_Z` followed
  by the inclusion of `Z` is the residue-field morphism of the chart.
* `AlgebraicGeometry.Space.PrimeDivisor.class_genericFieldPoint`: `ρ_Z` represents the generic
  point of `Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericResidueFieldEquivFunctionField_symm_toRationalMap`
  and `…_symm_eq_appTop`: the characterization of `θ_Z⁻¹` on a dense-open representative, by
  *any* factorization of `ρ_Z` through its domain, and through any representable chart of the
  domain receiving `ρ_Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericResidueFieldEquivHenselian_residue`: the
  isomorphism with the residue field of `𝒪^h_{X, ξ}` is induced by `𝒪_{U, u} → 𝒪^h_{X, ξ}`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EN0](https://stacks.math.columbia.edu/tag/0EN0)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### The prime divisor as the reduced closed subspace on its points -/

include hX in
/-- The point set of a prime divisor is closed. -/
theorem PrimeDivisor.isClosed_support : IsClosed (Z.support B S hS X) :=
  isClosed_range_pointsMap_integralClosedSubspace B S hS hX (Z.toIntegralClosedSubspace B S hS)

/-- **A prime divisor is the reduced closed subspace on its points**, by the uniqueness of
Stacks 03IQ: it is a closed subspace which is reduced, being integral. -/
theorem PrimeDivisor.subspace_eq_reducedClosedSubspace :
    Z.subspace = reducedClosedSubspace B S hS X hX (Z.support B S hS X)
      (Z.isClosed_support B S hS hX) :=
  eq_reducedClosedSubspace B S hS X hX _ _ Z.subspace Z.closed rfl Z.integral.1

include hX in
/-- The generic point of a prime divisor is the image of the generic point of the integral
space it is. -/
theorem PrimeDivisor.genericPoint_eq_pointsMap_ι :
    Z.genericPoint B S hS X = pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι
      (Space.genericPoint B S hS Z.closed.1 Z.integral) :=
  eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX (Z.toIntegralClosedSubspace B S hS) _
    (Z.isGenericPoint_genericPoint B S hS)

/-! ### The field-valued point `ρ_Z` -/

/-- **The residue field `κ(u)`** of the local ring `𝒪_{U, u}` of the chosen affine elementary
étale neighbourhood of the generic point of a prime divisor. -/
abbrev PrimeDivisor.genericResidueField : Type u :=
  IsLocalRing.ResidueField ↥(Z.genericStalkRing B S hS hX hdec)

/-- The residue-field point of the chart lies in the subfunctor of the prime divisor: it
represents the generic point, which lies in the prime divisor, and the prime divisor is the
reduced closed subspace on its points. -/
theorem PrimeDivisor.value_neighborhoodFieldPoint_mem :
    (neighborhoodFieldPoint B S hS X hX (Z.genericPoint B S hS X)
        (Z.genericChart B S hS hX hdec)).value ∈
      Z.subspace.obj (op ((neighborhoodFieldPoint B S hS X hX (Z.genericPoint B S hS X)
        (Z.genericChart B S hS hX hdec)).siteObject B S hS X)) := by
  rw [Z.subspace_eq_reducedClosedSubspace B S hS hX,
    FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem,
    neighborhoodFieldPoint_class]
  exact (Z.isGenericPoint_genericPoint B S hS).mem

/-- **The field-valued point `ρ_Z : Spec κ(u) → Z`**: the residue-field point of the chart at
the generic point of a prime divisor, which lands in the prime divisor. -/
def PrimeDivisor.genericFieldPoint : FieldValuedPoint B S hS Z.subspace.toFunctor where
  carrier := Z.genericResidueField B S hS hX hdec
  contained := (Z.genericChart B S hS hX hdec).residueField_contained
  toBase := (neighborhoodFieldPoint B S hS X hX (Z.genericPoint B S hS X)
    (Z.genericChart B S hS hX hdec)).toBase
  value := ⟨_, Z.value_neighborhoodFieldPoint_mem B S hS hX hdec⟩

/-- The site object of `ρ_Z` is that of the residue-field point of the chart. -/
theorem PrimeDivisor.siteObject_genericFieldPoint :
    (Z.genericFieldPoint B S hS hX hdec).siteObject B S hS Z.subspace.toFunctor =
      (neighborhoodFieldPoint B S hS X hX (Z.genericPoint B S hS X)
        (Z.genericChart B S hS hX hdec)).siteObject B S hS X :=
  rfl

/-- **`ρ_Z` followed by the inclusion of the prime divisor is the residue-field morphism of the
chart** `Spec κ(u) → U → X`. -/
theorem PrimeDivisor.fieldMorphism_genericFieldPoint_comp_ι :
    fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec) ≫
        Z.subspace.ι =
      fieldMorphism B S hS X (neighborhoodFieldPoint B S hS X hX (Z.genericPoint B S hS X)
        (Z.genericChart B S hS hX hdec)) := by
  simp only [fieldMorphism, yonedaEquiv_symm_naturality_right]
  rfl

/-- `ρ_Z` is a monomorphism: followed by the inclusion of the prime divisor it is the
residue-field morphism of an elementary étale neighbourhood, which is a monomorphism. -/
theorem PrimeDivisor.mono_fieldMorphism_genericFieldPoint :
    Mono (fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec)) := by
  have : Mono (fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec) ≫
      Z.subspace.ι) := by
    rw [Z.fieldMorphism_genericFieldPoint_comp_ι B S hS hX hdec]
    exact ElementaryEtaleNeighborhood.mono_neighborhoodFieldPoint B S hS X hX _ _
  exact mono_of_mono _ Z.subspace.ι

/-- **`ρ_Z` represents the generic point of the integral space `Z`.** Its image in `X` is the
generic point `ξ` of the prime divisor, which is the image of the generic point of `Z`, and the
inclusion of `Z` is injective on points. -/
theorem PrimeDivisor.class_genericFieldPoint :
    (Z.genericFieldPoint B S hS hX hdec).class B S hS Z.subspace.toFunctor =
      Space.genericPoint B S hS Z.closed.1 Z.integral := by
  apply pointsMap_injective_of_mono B S hS Z.subspace.ι
  rw [← Z.genericPoint_eq_pointsMap_ι B S hS hX, pointsMap_class]
  exact neighborhoodFieldPoint_class B S hS X hX _ _

/-! ### The isomorphism `θ_Z : κ(u) ≃+* R(Z)` -/

/-- **`θ_Z⁻¹ : R(Z) → κ(u)`**, evaluation of the rational functions of the prime divisor at the
field-valued point `ρ_Z`. -/
def PrimeDivisor.functionFieldToGenericResidueField :
    rationalFunctions B S hS Z.closed.1 →+* Z.genericResidueField B S hS hX hdec :=
  evalRingHom B S hS Z.closed.1 Z.integral (Z.genericFieldPoint B S hS hX hdec)
    (Z.class_genericFieldPoint B S hS hX hdec)

/-- Evaluation at `ρ_Z` is bijective, by Stacks 0END: `ρ_Z` is a monomorphic field-valued
representative of the generic point of the integral space `Z`. -/
theorem PrimeDivisor.bijective_functionFieldToGenericResidueField :
    Function.Bijective (Z.functionFieldToGenericResidueField B S hS hX hdec) :=
  evalRingHom_bijective B S hS Z.closed.1 Z.integral _ _
    (Z.mono_fieldMorphism_genericFieldPoint B S hS hX hdec)

/-- **The canonical isomorphism `θ_Z : κ(u) ≃+* R(Z)`** of Section 0EQU between the residue
field of the local ring of the chart at the generic point of a prime divisor and the function
field of the prime divisor.  Its inverse is evaluation at `ρ_Z`. -/
@[stacks 0EQU "the identification κ(ξ) = R(Z) of the residue field at the generic point of a \
  prime divisor with its function field, at the residue field of the chosen chart"]
def PrimeDivisor.genericResidueFieldEquivFunctionField :
    Z.genericResidueField B S hS hX hdec ≃+* rationalFunctions B S hS Z.closed.1 :=
  (RingEquiv.ofBijective _ (Z.bijective_functionFieldToGenericResidueField B S hS hX hdec)).symm

/-- `θ_Z⁻¹` is evaluation at `ρ_Z`. -/
theorem PrimeDivisor.genericResidueFieldEquivFunctionField_symm_apply
    (f : rationalFunctions B S hS Z.closed.1) :
    (Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm f =
      Z.functionFieldToGenericResidueField B S hS hX hdec f :=
  rfl

/-- **The characterization of `θ_Z⁻¹` on a representative.** On a rational function of `Z`
represented on a dense open subspace `W`, `θ_Z⁻¹` is the coordinate of the representative
pulled back along *any* factorization of `ρ_Z` through `W`. -/
theorem PrimeDivisor.genericResidueFieldEquivFunctionField_symm_toRationalMap
    (f : PartialMap B S hS Z.closed.1 (affineLineFunctor B S hS))
    (j : yoneda.obj ((Z.genericFieldPoint B S hS hX hdec).siteObject B S hS
      Z.subspace.toFunctor) ⟶ f.domain.toFunctor)
    (hj : j ≫ f.domain.ι =
      fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec)) :
    (Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm (f.toRationalMap B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).hom.hom
        (affineLineCoordinate B S hS (op ((Z.genericFieldPoint B S hS hX hdec).siteObject
          B S hS Z.subspace.toFunctor)) (yonedaEquiv (j ≫ f.hom))) :=
  evalPartial_eq B S hS Z.closed.1 Z.integral _ (Z.class_genericFieldPoint B S hS hX hdec) f j hj

/-- **The characterization of `θ_Z⁻¹` on a chart.** On a rational function of `Z` represented on
a dense open subspace `W`, and for a representable chart `C → W` through which `ρ_Z` factors by
a morphism of schemes `g : Spec κ(u) → C`, `θ_Z⁻¹` is the pullback along `g` of the coordinate
of the representative on `C`. -/
theorem PrimeDivisor.genericResidueFieldEquivFunctionField_symm_eq_appTop
    (f : PartialMap B S hS Z.closed.1 (affineLineFunctor B S hS)) (C : BigFppfOver B S hS)
    (γ : yoneda.obj C ⟶ f.domain.toFunctor)
    (g : (Z.genericFieldPoint B S hS hX hdec).siteObject B S hS Z.subspace.toFunctor ⟶ C)
    (hg : yoneda.map g ≫ γ ≫ f.domain.ι =
      fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec)) :
    (Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm (f.toRationalMap B S hS) =
      (Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).hom.hom
        (((BigFppfOver.toScheme B S hS).map g).appTop
          (affineLineCoordinate B S hS (op C) (yonedaEquiv (γ ≫ f.hom)))) :=
  evalRingHom_eq_appTop B S hS Z.closed.1 Z.integral _ (Z.class_genericFieldPoint B S hS hX hdec)
    f C γ g hg

/-! ### The residue field of the henselian local ring -/

/-- The map `𝒪_{U, u} → 𝒪^h_{X, ξ}` of Stacks 0EMY at the chart of a prime divisor is a local
homomorphism. -/
theorem PrimeDivisor.isLocalHom_stalkToGenericHenselianLocalRing :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    IsLocalHom (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      (Z.genericChart B S hS hX hdec)) :=
  isLocalHom_stalkToHenselianLocalRing B S hS X hX _ hdec _

/-- The homomorphism `κ(u) → κ(𝒪^h_{X, ξ})` of residue fields induced by the henselization map
`𝒪_{U, u} → 𝒪^h_{X, ξ}`. -/
def PrimeDivisor.genericResidueFieldToHenselian :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.genericResidueField B S hS hX hdec →+*
      IsLocalRing.ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  haveI := Z.isLocalHom_stalkToGenericHenselianLocalRing B S hS hX hdec
  IsLocalRing.ResidueField.map (stalkToHenselianLocalRing B S hS X hX
    (Z.genericPoint B S hS X) hdec (Z.genericChart B S hS hX hdec))

/-- The map on residue fields sends the residue of an element of `𝒪_{U, u}` to the residue of its
image in `𝒪^h_{X, ξ}`. -/
theorem PrimeDivisor.genericResidueFieldToHenselian_residue
    (r : ↥(Z.genericStalkRing B S hS hX hdec)) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.genericResidueFieldToHenselian B S hS hX hdec (IsLocalRing.residue _ r) =
      IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX
        (Z.genericPoint B S hS X) hdec (Z.genericChart B S hS hX hdec) r) :=
  let _ := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have := Z.isLocalHom_stalkToGenericHenselianLocalRing B S hS hX hdec
  IsLocalRing.ResidueField.map_residue _ r

/-- **Stacks 0EN0 at the chart.** The henselization map induces a bijection of residue fields
`κ(u) → κ(𝒪^h_{X, ξ})`: it agrees on residues with the isomorphism of
`AlgebraicGeometry.Space.exists_residueFieldEquiv_henselianLocalRing`, and residues are all of
`κ(u)`. -/
theorem PrimeDivisor.bijective_genericResidueFieldToHenselian :
    Function.Bijective (Z.genericResidueFieldToHenselian B S hS hX hdec) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  obtain ⟨e, he⟩ := exists_residueFieldEquiv_henselianLocalRing B S hS X hX
    (Z.genericPoint B S hS X) hdec (Z.genericChart B S hS hX hdec)
  have heq : ⇑(Z.genericResidueFieldToHenselian B S hS hX hdec) = ⇑e := by
    funext c
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    exact (Z.genericResidueFieldToHenselian_residue B S hS hX hdec r).trans (he r).symm
  rw [heq]
  exact e.bijective

/-- **The canonical isomorphism `κ(u) ≃+* κ(𝒪^h_{X, ξ})`** induced by the henselization map
`𝒪_{U, u} → 𝒪^h_{X, ξ}`. -/
@[stacks 0EN0 "the residue field of the henselian local ring at the generic point of a prime \
  divisor is the residue field of the chosen chart, canonically through the henselization map"]
def PrimeDivisor.genericResidueFieldEquivHenselian :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.genericResidueField B S hS hX hdec ≃+*
      IsLocalRing.ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  RingEquiv.ofBijective _ (Z.bijective_genericResidueFieldToHenselian B S hS hX hdec)

/-- The isomorphism `κ(u) ≃+* κ(𝒪^h_{X, ξ})` is induced by the henselization map. -/
theorem PrimeDivisor.genericResidueFieldEquivHenselian_residue
    (r : ↥(Z.genericStalkRing B S hS hX hdec)) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.genericResidueFieldEquivHenselian B S hS hX hdec (IsLocalRing.residue _ r) =
      IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX
        (Z.genericPoint B S hS X) hdec (Z.genericChart B S hS hX hdec) r) :=
  Z.genericResidueFieldToHenselian_residue B S hS hX hdec r

/-- **The composite `κ(𝒪^h_{X, ξ}) ≃+* R(Z)`**: the residue field of the henselian local ring at
the generic point of a prime divisor is the function field of the prime divisor, through the
residue field `κ(u)` of the chosen chart.  A unit `v` of `𝒪^h_{X, ξ}` thus has a residue
`θ(v̄) ∈ R(Z)`, which is how the key formula of Section 0EQU reads a change of generator on
`Z`. -/
@[stacks 0EQU "the residue field of the henselian local ring at the generic point of a prime \
  divisor is its function field"]
def PrimeDivisor.henselianResidueFieldEquivFunctionField :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    IsLocalRing.ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec) ≃+*
      rationalFunctions B S hS Z.closed.1 :=
  (Z.genericResidueFieldEquivHenselian B S hS hX hdec).symm.trans
    (Z.genericResidueFieldEquivFunctionField B S hS hX hdec)

/-- On the residue of an element `r` of `𝒪_{U, u}`, the composite `κ(𝒪^h_{X, ξ}) ≃+* R(Z)` is
`θ_Z` of the residue of `r`. -/
theorem PrimeDivisor.henselianResidueFieldEquivFunctionField_residue
    (r : ↥(Z.genericStalkRing B S hS hX hdec)) :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    Z.henselianResidueFieldEquivFunctionField B S hS hX hdec
        (IsLocalRing.residue _ (stalkToHenselianLocalRing B S hS X hX
          (Z.genericPoint B S hS X) hdec (Z.genericChart B S hS hX hdec) r)) =
      Z.genericResidueFieldEquivFunctionField B S hS hX hdec (IsLocalRing.residue _ r) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  rw [henselianResidueFieldEquivFunctionField, RingEquiv.trans_apply,
    ← Z.genericResidueFieldEquivHenselian_residue B S hS hX hdec r, RingEquiv.symm_apply_apply]

end AlgebraicGeometry.Space

end
