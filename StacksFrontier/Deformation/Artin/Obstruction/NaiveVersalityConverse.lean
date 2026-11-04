module

public import StacksFrontier.Deformation.Artin.Obstruction.CanonicalDerivedTensorProduct
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDegreeNegOne
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDegreeZero
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenness

/-!
# Stacks 07YM, the direction `(1) ⇒ (2)`, at the derived fibre

The two halves of the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] are proved separately and
in the presentation of the derived fibre that [Stacks, Tag 07YL] uses: a chosen derived tensor
product `T` on `D(A)`, at which `H^n(ξ ⊗ᴸ_A κ(u₀))` is the map
`H^n(T(−, κ(u₀)))` of `A`-modules. The cohomological conditions of the tag are stated
downstream — in `Deformation.Artin.NaiveVersalityCriterion`, which [Stacks, Tag 07YN]
consumes — through `Deformation.Artin.derivedFibreHomologyMap`, the derived fibre read as the
total derived extension of scalars along `A ⟶ κ(u₀)`, whose value is a map of
`κ(u₀)`-modules.

This file composes the two halves with the comparison of the two presentations and states the
direction once, in the second presentation.

## Main results

* `Deformation.Artin.derivedFibreHomologyMap_conditions_of_isVersalAt` — **the direction
  `(1) ⇒ (2)` of [Stacks, Tag 07YM]**: at a closed point `u₀` at which `x` is versal, `ξ` is
  surjective on `H^{-1}` and injective on `H^0` of the derived fibre.

## Implementation notes

The comparison of the two presentations is
`Deformation.Artin.surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars` and
its injective counterpart, which hold for an arbitrary morphism of `D(A)`, an arbitrary degree
and an arbitrary `A`-algebra `k` in the same universe; no boundedness or finiteness enters
there. They are `iff`s for *every* chosen derived tensor product, so the conclusion does not depend
on which one the halves are run with, and the one used is
`Deformation.Artin.canonicalDerivedTensorProduct`, which exists for every commutative ring.

Closedness of `u₀` is used only by the degree `-1` half, exactly as in the source: the
degree `0` half, `Deformation.Artin.injective_derivedTensorFibre_zero_of_isVersalAt`, holds at
any point.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

universe u v w

section Converse

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
  [IsNoetherianRing Λ] [IsNoetherianRing A] [Algebra.FiniteType Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A)))
  (baseMap : Spec (CommRingCat.of Λ) ⟶ S) [Mono baseMap]
  (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
variable (E : DerivedCategory (ModuleCat.{u} A))
  (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        hbase).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)
variable (u₀ : Spec (CommRingCat.of A))

include hbase hp hRS hΩ hE tangentEquiv_natural tangentEquiv_canonical in
/-- **Stacks 07YM, the direction `(1) ⇒ (2)`.** Let `x` be a family over `Spec A` whose
deformation theory is controlled by `ξ : E ⟶ NL_{A/Λ}` as in hypotheses (i) and (ii) of the
tag. If `x` is versal at a *closed* point `u₀` of `Spec A`, then `ξ` induces a surjection
`H^{-1}(E ⊗ᴸ_A κ(u₀)) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A κ(u₀))` and an injection
`H^0(E ⊗ᴸ_A κ(u₀)) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A κ(u₀))`.

The two conclusions are
`Deformation.Artin.surjective_derivedTensorFibre_neg_one_of_isVersalAt` and
`Deformation.Artin.injective_derivedTensorFibre_zero_of_isVersalAt`, read through the
comparison of the two presentations of the derived fibre. Only the first uses that `u₀` is
closed. -/
public theorem derivedFibreHomologyMap_conditions_of_isVersalAt
    (hclosed : IsClosed ({u₀} : Set (Spec (CommRingCat.of A))))
    (hLifts : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A] (D : SquareZeroThickening A B S hS toS hA A'),
      D.q = algebraMap A' A →
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap = B.inclusion.map D.toS' →
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0 →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))))
    (hversal : IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x
      (by change (Over.post B.inclusion).obj (p.obj x) = _; rw [hx]; rfl)) :
    Function.Surjective (derivedFibreHomologyMap ξ u₀ (-1)) ∧
      Function.Injective (derivedFibreHomologyMap ξ u₀ 0) := by
  have : u₀.asIdeal.IsPrime := u₀.isPrime
  let T : DerivedTensorProduct A := canonicalDerivedTensorProduct A
  constructor
  · refine (surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars
      (k := u₀.asIdeal.ResidueField) T ξ (-1)).mp ?_
    exact surjective_derivedTensorFibre_neg_one_of_isVersalAt Λ A B S hS toS hA baseMap hbase
      p x hx hp E hE ξ u₀ T hclosed hLifts hversal
  · refine (injective_derivedTensorFibre_iff_injective_derivedExtensionScalars
      (k := u₀.asIdeal.ResidueField) T ξ 0).mp ?_
    exact injective_derivedTensorFibre_zero_of_isVersalAt Λ A B S hS toS hA p x hx hp hRS hΩ
      baseMap hbase E hE ξ tangentEquiv tangentEquiv_natural tangentEquiv_canonical u₀ T hversal

end Converse

end Deformation.Artin

end
