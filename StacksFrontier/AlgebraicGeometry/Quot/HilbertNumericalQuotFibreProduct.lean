module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorNumericalSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotNumericalFibreProduct

/-!
# `Hilb^P_{X/B}` is the fibre product `Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation, with the data
of Situation 0DNC: a set `I`, perfect objects `E_i ∈ D(𝒪_X)` and `P : I → ℤ`.  Stacks 0DP6
*defines* `Quot^P_{F/X/B}` by the 2-fibre product square

```
Quot^P_{F/X/B} ⟶ Coh^P_{X/B}
      ↓               ↓
Quot_{F/X/B}   ⟶ Coh_{X/B}
```

(`AlgebraicGeometry.Space.QuotSituation.numericalQuot`), and Stacks 0DPG defines
`Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B}` through `Hilb_{X/B} = Quot_{𝒪_X/X/B}` (Stacks 0D00).  On the
other hand `AlgebraicGeometry.Space.numericalHilbertCondition` is a subfunctor of the Hilbert
presheaf.  This file shows that the two agree: a family `Z ⊆ X_T` lies in the subfunctor exactly
when its quotient `𝒪_{X_T} ⟶ 𝒪_Z`, a section of `Quot_{𝒪_X/X/B}` over `T`, lifts to the
2-fibre product of Stacks 0DP6.  Since the left vertical arrow of the square is fully faithful
(`AlgebraicGeometry.Space.QuotSituation.full_numericalQuotToQuot`,
`AlgebraicGeometry.Space.QuotSituation.faithful_numericalQuotToQuot`), this identifies the
category fibred in sets `Quot^P_{𝒪_X/X/B}` with the subfunctor.

## Main definitions

* `AlgebraicGeometry.Space.QuotFamilyOver.toQuotObjects`: a section of the Quot presheaf over a
  scheme of the site, as an object of the category fibred in sets attached to `Quot_{F/X/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.exists_numericalQuot_x_eq_toQuotObjects_iff`: a section
  of `Quot_{F/X/B}` lifts to `Quot^P_{F/X/B}` exactly when its object of `Coh_{X/B}` lies in
  `Coh^P_{X/B}`.
* `AlgebraicGeometry.Space.mem_numericalHilbertCondition_iff_exists_numericalQuot`: a family lies
  in the subfunctor `Hilb^P_{X/B}` exactly when its quotient lifts to `Quot^P_{𝒪_X/X/B}`.

## References

* [Stacks Project, Tag 0DPG](https://stacks.math.columbia.edu/tag/0DPG)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotFamilyOver

variable {D : QuotSituation B S hS}

/-- A section `F_T ⟶ 𝒬` of the Quot presheaf over a scheme `T` of the site, as an object of the
category fibred in sets attached to `Quot_{F/X/B}`: the element of the Quot functor at the test
scheme `T ⟶ B` it lies over. -/
def toQuotObjects {T : BigFppfOver B S hS} (x : QuotFamilyOver D T) : D.QuotObjects :=
  ULiftHom.objUp
    (op (D.quotFunctor.elementsMk (op (CostructuredArrow.mk x.toBase)) ⟨x.subobject, x.mem⟩))

/-- The object of `Coh_{X/B}` of a section is the object of `Coh_{X/B}` of the corresponding
element of the Quot functor. -/
theorem cohObject_toQuotObjects {T : BigFppfOver B S hS} (x : QuotFamilyOver D T) :
    D.cohObject x.toQuotObjects.T x.toQuotObjects.K x.toQuotObjects.mem = x.cohObject :=
  rfl

end QuotFamilyOver

namespace QuotSituation

variable (D : QuotSituation B S hS) (N : NumericalSituation.{u, v, u} B S hS D.toCoherentSituation)

/-- **A section of `Quot_{F/X/B}` lifts to `Quot^P_{F/X/B}` exactly when its object of
`Coh_{X/B}` lies in `Coh^P_{X/B}`**, as soon as the condition cutting out `Coh^P_{X/B}` is
inherited along the morphisms of `Coh_{X/B}`. -/
theorem exists_numericalQuot_x_eq_toQuotObjects_iff
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A →
      N.HasNumericalInvariants A → N.HasNumericalInvariants A')
    {T : BigFppfOver B S hS} (x : QuotFamilyOver D T) :
    (∃ P : D.NumericalQuotObjects N, P.x = x.toQuotObjects) ↔
      N.HasNumericalInvariants x.cohObject :=
  D.exists_numericalQuot_x_eq_iff N hQ x.toQuotObjects

end QuotSituation

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  {N : NumericalSituation.{u, v, u} B S hS (structureSheafQuotSituation f hf).toCoherentSituation}

/-- **`Hilb^P_{X/B} = Quot^P_{𝒪_X/X/B}`.**  A family `Z ⊆ X_T` lies in the subfunctor
`Hilb^P_{X/B}` of the Hilbert presheaf exactly when its quotient `𝒪_{X_T} ⟶ 𝒪_Z`, the section of
`Quot_{𝒪_X/X/B}` over `T` it corresponds to under Stacks 0D00, lifts to the 2-fibre product
`Quot^P_{𝒪_X/X/B} = Quot_{𝒪_X/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}` of Stacks 0DP6. -/
theorem mem_numericalHilbertCondition_iff_exists_numericalQuot
    (hbc : ∀ {A' A : CoherentObject (structureSheafQuotSituation f hf).toCoherentSituation}
      (φ : CoherentHom A' A) (i : N.I) (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : (hilbertPresheaf f).obj T) :
    x ∈ (numericalHilbertCondition f hf hbc).obj T ↔
      ∃ P : (structureSheafQuotSituation f hf).NumericalQuotObjects N,
        P.x = ((hilbertPresheafIsoQuotSitePresheaf f hf).hom.app T x).toQuotObjects :=
  ((structureSheafQuotSituation f hf).exists_numericalQuot_x_eq_toQuotObjects_iff N
    (CoherentSituation.numerical_points_of_hom (χ := N.numericalEuler) N.P hbc) _).symm

end AlgebraicGeometry.Space

end
