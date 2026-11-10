module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationQuotientAlgebraic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplicative group is smooth, and of dimension one over a field

The multiplicative group scheme `𝐆_m = Spec ℤ[T, T⁻¹]` is smooth over `Spec ℤ`, hence so is its
base change `𝐆_{m,S}` over any scheme `S`, and so is the multiplicative group algebraic space
`𝐆_{m,B} = B ×_S 𝐆_{m,S}` over an algebraic space `B` over `S` (Stacks 043J). Over a field `k`
the scheme `𝐆_{m,k}` is the spectrum of `k[T, T⁻¹]`, a Dedekind domain which is not a field, so
it has Krull dimension one; the multiplicative group algebraic space over the final algebraic
space of the big fppf site of `Spec k` therefore has dimension one in the sense of Stacks 04N5.

## Main results

* `LaurentPolynomial.smooth`: `R[T, T⁻¹]` is a smooth `R`-algebra.
* `AlgebraicGeometry.smooth_multiplicativeGroupBaseChange`: `𝐆_{m,S} ⟶ S` is smooth.
* `AlgebraicGeometry.Space.isSmooth_multiplicativeGroupSpace`: `𝐆_{m,B} ⟶ B` is smooth.
* `LaurentPolynomial.ringKrullDim_eq_one`: `k[T, T⁻¹]` has Krull dimension one.
* `AlgebraicGeometry.Space.dimension_multiplicativeGroupSpace_terminalSpace`: the multiplicative
  group algebraic space over a field `k` has dimension one.

## References

* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
* [Stacks Project, Tag 043J](https://stacks.math.columbia.edu/tag/043J)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace LaurentPolynomial

/-- The `R`-algebra structures on `R[T, T⁻¹]` directly and through `R[X]` agree. -/
theorem isScalarTower_polynomial (R : Type*) [CommRing R] :
    IsScalarTower R R[X] (LaurentPolynomial R) :=
  IsScalarTower.of_algebraMap_eq fun r => (Polynomial.toLaurent_C r).symm

/-- **`R[T, T⁻¹]` is a smooth `R`-algebra**: it is the localization of the smooth `R`-algebra
`R[X]` away from `X`. -/
theorem smooth (R : Type u) [CommRing R] : Algebra.Smooth R (LaurentPolynomial R) := by
  have : Algebra.Smooth R (MvPolynomial PUnit.{u + 1} R) :=
    AlgebraicGeometry.smooth_mvPolynomial R PUnit.{u + 1}
  have : Algebra.Smooth R R[X] :=
    Algebra.Smooth.of_equiv (MvPolynomial.uniqueAlgEquiv.{u, u} R PUnit.{u + 1})
  have : Algebra.Smooth R[X] (LaurentPolynomial R) := Algebra.Smooth.of_isLocalization_Away X
  have := isScalarTower_polynomial R
  exact Algebra.Smooth.comp R R[X] (LaurentPolynomial R)

/-- `k[T, T⁻¹]` is not a field: evaluation at `1` is a surjection onto `k` which kills the nonzero
element `T - 1`. -/
theorem not_isField (k : Type*) [Field k] : ¬ IsField (LaurentPolynomial k) := by
  intro hF
  let ev : LaurentPolynomial k →+* k := eval₂ (RingHom.id k) 1
  have hT : ev (T 1 - 1) = 0 := by simp [ev]
  have hne : (T 1 - 1 : LaurentPolynomial k) ≠ 0 := by
    intro h
    have h1 : Polynomial.toLaurent (X : k[X]) = Polynomial.toLaurent 1 := by
      rw [Polynomial.toLaurent_X, map_one]
      exact sub_eq_zero.mp h
    have h2 := congrArg Polynomial.natDegree (Polynomial.toLaurent_injective h1)
    simp at h2
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
  have := congrArg ev hy
  rw [map_mul, hT, zero_mul, map_one] at this
  exact zero_ne_one this

/-- **`k[T, T⁻¹]` has Krull dimension one**: it is a localization of the principal ideal domain
`k[X]` away from the nonzero element `X`, hence a Dedekind domain, and it is not a field. -/
theorem ringKrullDim_eq_one (k : Type*) [Field k] : ringKrullDim (LaurentPolynomial k) = 1 := by
  have : IsDomain (LaurentPolynomial k) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (X : k[X])) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
  have : IsDedekindDomain (LaurentPolynomial k) :=
    IsLocalization.isDedekindDomain k[X]
      (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero) (LaurentPolynomial k)
  have hle : ringKrullDim (LaurentPolynomial k) ≤ 1 := by
    rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  refine le_antisymm hle (not_lt.mp fun h => not_isField k ?_)
  have h0 : ringKrullDim (LaurentPolynomial k) ≤ 0 := Order.le_of_lt_succ h
  rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h0
  exact Ring.KrullDimLE.isField_of_isDomain

end LaurentPolynomial

namespace AlgebraicGeometry

/-- **The multiplicative group is smooth over the integers.** -/
@[sga "3 I 4.4.4" "special case"]
theorem smooth_multiplicativeGroupULift :
    Smooth (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  have := LaurentPolynomial.smooth (ULift.{u} ℤ)
  exact smooth_Spec_map_algebraMap (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))

/-- **The multiplicative group over a scheme `S` is smooth over `S`**, being a base change of the
multiplicative group over the integers. -/
@[sga "3 I 4.4.4" "G_m,S is smooth over S", sga "3 VIII 2.1" "special case"]
theorem smooth_multiplicativeGroupBaseChange (S : Scheme.{u}) :
    Smooth (Scheme.asOver (multiplicativeGroupBaseChange S) S).hom :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth.{u})
    (IsPullback.of_hasPullback (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S)) smooth_multiplicativeGroupULift

/-- The Krull dimension of the multiplicative group over a field is one. -/
theorem topologicalKrullDim_multiplicativeGroupBaseChange (k : Type u) [Field k] :
    topologicalKrullDim (multiplicativeGroupBaseChange (Spec (.of k))) = 1 := by
  let : Algebra (ULift.{u} ℤ) k :=
    ((Int.castRingHom k).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  let : Module (ULift.{u} ℤ) k := Algebra.toModule
  have hfrom : specULiftZIsTerminal.from (Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) k)) :=
    specULiftZIsTerminal.hom_ext _ _
  have hstr : (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)))) :=
    rfl
  let e : multiplicativeGroupBaseChange (Spec (.of k)) ≅
      Spec (.of (TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) k)) :=
    pullback.congrHom hstr hfrom ≪≫ pullbackSpecIso _ _ _
  let e' : TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) k ≃+*
      LaurentPolynomial k :=
    (Algebra.TensorProduct.comm (ULift.{u} ℤ) _ _).toRingEquiv.trans
      (AddMonoidAlgebra.scalarTensorEquiv (ULift.{u} ℤ) (M := ℤ) k).toRingEquiv
  calc topologicalKrullDim (multiplicativeGroupBaseChange (Spec (.of k)))
      = topologicalKrullDim
          (PrimeSpectrum (TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) k)) :=
        e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = ringKrullDim (TensorProduct (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) k) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = ringKrullDim (LaurentPolynomial k) := ringKrullDim_eq_of_ringEquiv e'
    _ = 1 := LaurentPolynomial.ringKrullDim_eq_one k

namespace Space

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The structure morphism of `𝐆_{m,S}`, read through the object of the site it defines, is
smooth. -/
@[sga "3 VIII 2.1" "special case"]
theorem smooth_toScheme_map_multiplicativeGroupSiteObject :
    Smooth ((BigFppfOver.toScheme 𝒞 S hS).map
      (Over.mkIdTerminal.from (multiplicativeGroupSiteObject 𝒞 S hS))) := by
  have h : Over.mkIdTerminal.from (multiplicativeGroupSiteObject 𝒞 S hS) =
      Over.homMk (multiplicativeGroupSiteObject 𝒞 S hS).hom :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h]
  exact smooth_multiplicativeGroupBaseChange S

/-- **The multiplicative group algebraic space `𝐆_{m,B}` is smooth over `B`.** -/
theorem isSmooth_multiplicativeGroupSpace {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    IsSmooth 𝒞 S hS (multiplicativeGroupSpace 𝒞 S hS B hB).obj.X.hom := by
  let a := multiplicativeGroupSiteObject 𝒞 S hS
  let P := multiplicativeGroupPointsOnSite 𝒞 S hS ⋙ forget GrpCat
  let r := pointsOnSiteRepresentableBy 𝒞 S hS a (multiplicativeGroupSiteObjectGrpObj 𝒞 S hS)
  have hprod : IsAlgebraicSpace 𝒞 S hS (B ⨯ yoneda.obj a) :=
    isAlgebraicSpace_of_iso 𝒞 S hS (prod.braiding B (yoneda.obj a)).symm
      (isAlgebraicSpace_prod_yoneda_obj a hB)
  let e : (B ⨯ P) ≅ (B ⨯ yoneda.obj a) := prod.mapIso (Iso.refl B) r.toIso.symm
  have hsrc : IsAlgebraicSpace 𝒞 S hS (B ⨯ P) := isAlgebraicSpace_of_iso 𝒞 S hS e.symm hprod
  have hcomp : e.hom ≫ (prod.fst : B ⨯ yoneda.obj a ⟶ B) = (prod.fst : B ⨯ P ⟶ B) := by
    simp [e]
  rw [multiplicativeGroupSpace_obj_X]
  change IsSmooth 𝒞 S hS (prod.fst : B ⨯ P ⟶ B)
  rw [← hcomp]
  exact isSmooth_comp 𝒞 S hS hsrc hprod hB _ _ (isSmooth_of_isIso 𝒞 S hS hsrc hprod _)
    (isSmooth_prod_fst_yoneda_obj a hB (smooth_toScheme_map_multiplicativeGroupSiteObject 𝒞 S hS))

/-- **The multiplicative group algebraic space over a field has dimension one.** Over the final
algebraic space of the big fppf site of `Spec k`, the algebraic space underlying `𝐆_m` is
isomorphic to the one represented by the scheme `𝐆_{m,k}`, whose Krull dimension is one. -/
theorem dimension_multiplicativeGroupSpace_terminalSpace {k : Type u} [Field k]
    (hk : 𝒞.Contains (Spec (.of k))) :
    dimension 𝒞 (Spec (.of k)) hk
        (multiplicativeGroupSpace 𝒞 (Spec (.of k)) hk (terminalSpace 𝒞 (Spec (.of k)) hk).obj
          (terminalSpace 𝒞 (Spec (.of k)) hk).property).obj.X.left
        (multiplicativeGroupSpace 𝒞 (Spec (.of k)) hk (terminalSpace 𝒞 (Spec (.of k)) hk).obj
          (terminalSpace 𝒞 (Spec (.of k)) hk).property).property = 1 := by
  let a := multiplicativeGroupSiteObject 𝒞 (Spec (.of k)) hk
  let r := pointsOnSiteRepresentableBy 𝒞 (Spec (.of k)) hk a
    (multiplicativeGroupSiteObjectGrpObj 𝒞 (Spec (.of k)) hk)
  let e : (multiplicativeGroupSpace 𝒞 (Spec (.of k)) hk (terminalSpace 𝒞 (Spec (.of k)) hk).obj
        (terminalSpace 𝒞 (Spec (.of k)) hk).property).obj.X.left ≅ yoneda.obj a :=
    terminalSpaceProdIso 𝒞 (Spec (.of k)) hk _ ≪≫ r.toIso.symm
  rw [dimension_eq_of_iso 𝒞 (Spec (.of k)) hk _ (isAlgebraicSpace_yoneda 𝒞 (Spec (.of k)) hk a) e,
    dimension_yoneda_eq_topologicalKrullDim]
  exact_mod_cast topologicalKrullDim_multiplicativeGroupBaseChange k

end Space

end AlgebraicGeometry

end
