module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomPhiTransport
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaCochainCommShift

/-!
# Step 2 of Tag 09LK: `R Hom(K, -) : D(A) ⥤ D(E)` is exact

Let `A` be an abelian category, `K` a cochain complex in `A`, `C = Comp^dg(A)` the differential
graded category of complexes and `E = C(K, K)` the endomorphism complex of `K`. The functor
step 2 of the replacement proof of [Stacks, Tag 09LK] produces is

`R̃ = DGCategory.phiReflector A K L hΦ : D(A) ⥤ D(E)`,

the `R̃` of `DGCategory.derivedHomPhi` at the localization
`DGCategory.phiComparisonLocalization` and the generator family `DGCategory.phiGen`. This file
records that it **commutes with the translations and is exact**, which is what step 2 owes.

## Nothing new is assumed

Both facts are already consequences of the instances
`DGCategory.derivedHomReflector`'s file registers, for the `phiReflector` is an abbreviation for
`DGCategory.derivedHomReflector` and that functor is by construction a composite of two exact
functors: the descent `J = DGCategory.derivedReflectorDescent` of step 1 through the localization
`q`, and evaluation at `K` on the derived categories, `DGCategory.derivedEvaluation`. The
declarations below are therefore `inferInstance`, with no hypothesis beyond the binders
`DGCategory.phiReflector` already carries:

* `[L.CommShift ℤ]` and `[L.IsTriangulated]`, the exactness of the reflector of step 1, which
  the caller supplies;
* `[((yonedaDGFunctor (Comp^dg A)).onK).CommShift ℤ]` and `.IsTriangulated`, the exactness of
  the differential graded Yoneda functor, which is where steps 1 and 2 leave it and which
  `CochainComplex.yonedaOnK_commShift` and `CochainComplex.yonedaOnK_isTriangulated` discharge
  for an abelian `A` with a zero object and binary biproducts;
* `hΦ`, the hypothesis that `L` annihilates the representables of the acyclic complexes.

The binder `[HasDerivedCategory (ModuleCat ℤ)]` that `DGCategory.derivedHomPhiQh` needs is
*not* among them: `DGCategory.phiReflector` lands in `D(E)` and never mentions the derived
category of `ModuleCat ℤ`, so step 2 costs nothing there either.

In particular **no K-injective resolutions, no smallness, no universe inequality and no
derivability of `CochainComplex.homToDerivedCategory` is used** — the localization hypothesis
that the transport would otherwise carry is discharged inside
`DGCategory.phiComparisonLocalization` by
`DGCategory.RightModule.comparisonInverse_comp_isLocalization_yonedaInverseImage`.

## Main results

* `DGCategory.phiReflectorCommShift`: `R̃` commutes with the translations. Stated as a
  definition rather than an instance: global instance search already produces this term, and a
  `CategoryTheory.Functor.CommShift` is data, so a second registration would be a diamond.
* `DGCategory.phiReflector_isTriangulated`: `R̃` is an exact functor of triangulated
  categories.
* `DGCategory.phiReflector_map_distinguished`: the content of exactness spelled out — `R̃`
  carries distinguished triangles of `D(A)` to distinguished triangles of `D(E)`.

## What this does *not* give

The forgetful functor `U = DGCategory.endDerivedForget` out of `D(E)`, through which
`DGCategory.derivedHomPhiQh` reads the values of `R̃`, carries no `Functor.CommShift ℤ`
instance in this development, so `DGCategory.phiReflectorForget` is *not* known to be exact
here. That is a statement about `U`, not about `R̃`, and it is not part of step 2.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DGCategory

universe v

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ)
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (L : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
    (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
    IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X))

/-- **`R̃ : D(A) ⥤ D(E)` commutes with the translations.** The comparison isomorphisms are
those of the composite `J ⋙ ev_K`: on the first factor they come from
`CategoryTheory.Functor.commShiftOfLocalization` at the localization
`DGCategory.phiComparisonLocalization`, on the second from the derived evaluation functor.

This names the term global instance search already produces for this goal; it is deliberately
not itself registered as an instance, since `CategoryTheory.Functor.CommShift` is data and a
second registration would be a diamond. -/
@[instance_reducible, stacks 09LK "half of exactness as a functor of TRIANGULATED categories: \
the translation compatibility of R Hom(K, -) : D(A) ⥤ D(E, d), relative to which the exactness \
below is stated"]
def phiReflectorCommShift : (phiReflector A K L hΦ).CommShift ℤ := inferInstance

/-- **`R̃ : D(A) ⥤ D(E)` is exact.** It is the composite of the descent `J` of step 1 through
the localization `q` of `K(Comp^dg(A))` at the complexes `Φ⁻¹ N`, which is exact by
`DGCategory.isTriangulated_derivedReflectorDescent`, with evaluation at `K` on the derived
categories; both factors are exact, hence so is `R̃`. -/
@[stacks 09LK "the other half: R Hom(K, -) : D(A) ⥤ D(E, d) is EXACT -- it carries distinguished \
triangles to distinguished triangles, for the translation compatibility above"]
instance phiReflector_isTriangulated : (phiReflector A K L hΦ).IsTriangulated := inferInstance

/-- **Exactness of `R̃`, spelled out.** For every distinguished triangle `T` of `D(A)` the
triangle `R̃ T` is distinguished in `D(E) = D(C(K, K))`, the translation of `R̃` being the one
of `DGCategory.phiReflectorCommShift`. -/
theorem phiReflector_map_distinguished
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) :
    (phiReflector A K L hΦ).mapTriangle.obj T ∈
      distTriang (RightModule.derivedCategory (endDGCategory (CochainComplex.dgCategory A) K)) :=
  (phiReflector A K L hΦ).map_distinguished T hT

end DGCategory

end
