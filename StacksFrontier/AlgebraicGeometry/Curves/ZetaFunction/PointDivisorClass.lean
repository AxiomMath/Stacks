module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.TwistedFrobeniusFixedPoints
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardDegree

/-!
# The Picard classes of the closed points of a curve

Let `C` be a smooth proper curve over an algebraically closed field `Ω`. A closed point `x` is an
effective Cartier divisor (its local ring is a discrete valuation ring), whose class `[x]` in
`Pic(C)` has degree `1`: the reduced subscheme on `x` is `Spec κ(x) = Spec Ω`. The class of a
divisor `D = ∑ n_x x` on the closed points is `∑ n_x [x]`, of degree `∑ n_x`.

Pullback along an automorphism `Ψ` of `C` moves point classes: `Ψ^* [x] = [Ψ⁻¹ x]`. Indeed
`Ψ^* ℐ_x ≅ ℐ_{Ψ^{-1} x}` (`Stacks.Divisors.pullbackIdealSheafComapIso`), `[𝒪(x)] = -[ℐ_x]`, and
the scheme-theoretic inverse image of the reduced point `x` is the reduced point `Ψ⁻¹ x`. Hence
`Ψ^* [D] = [D ∘ Ψ]` for every divisor `D`.

## Main definitions

* `Stacks.Zeta.pointIdeal`: the ideal sheaf of a closed point.
* `Stacks.Zeta.pointClass`: its class `[x]` in `Pic(C)`.
* `Stacks.Zeta.divisorClass`: the class `∑ n_x [x]` of a divisor on the closed points.

## Main results

* `Stacks.Zeta.picardDegree_pointClass`, `Stacks.Zeta.picardDegree_divisorClass`: degrees.
* `Stacks.Zeta.schemePullbackClass_picardClass_comap`: `f^* [𝒪(D)] = [𝒪(f^{-1} D)]` when the
  pullback of `D` is defined.
* `Stacks.Zeta.schemePullbackClass_pointClass`, `Stacks.Zeta.schemePullbackClass_divisorClass`:
  pullback along an automorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Zeta

/-! ### Pullback of the class of a divisor -/

section Pullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : Stacks.Divisors.IsPullbackDefined h D)

/-- The isomorphism `h^* ℐ_D ≅ ℐ_{h^{-1} D}` of negative twists, when the pullback of `D` along `h`
is defined. -/
def pullbackNegativeTwistIso :
    (Stacks.RingedSpace.pullbackFunctor h.toLRSHom.toShHom).obj
      (Stacks.Divisors.negativeTwist' D) ≅ Stacks.Divisors.negativeTwist' (D.comap h) :=
  Stacks.Divisors.pullbackIdealSheafComapIso h D hD

/-- The pullback along `h` of the class of `ℐ_D` is the class of the pullback module `h^* ℐ_D`. -/
theorem schemePullbackClass_negativeTwistPicardClass_eq :
    Stacks.Picard.schemePullbackClass h (Stacks.Divisors.negativeTwistPicardClass D) =
    Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor h.toLRSHom.toShHom).obj
        (Stacks.Divisors.negativeTwist' D))
      (Stacks.RingedSpace.modulePullback_isInvertible_of h.toLRSHom.toShHom _
        (Stacks.Divisors.isInvertible_negativeTwist_picard D)) :=
  Stacks.Picard.pullbackClass_classOf h.toLRSHom.toShHom (Stacks.Divisors.negativeTwist' D)
    (Stacks.Divisors.isInvertible_negativeTwist_picard D)

/-- The class of `h^* ℐ_D` is the class of `ℐ_{h^{-1} D}`, when the pullback of `D` along `h` is
defined. -/
theorem picardClass_pullback_negativeTwist_eq :
    Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
      ((Stacks.RingedSpace.pullbackFunctor h.toLRSHom.toShHom).obj
        (Stacks.Divisors.negativeTwist' D))
      (Stacks.RingedSpace.modulePullback_isInvertible_of h.toLRSHom.toShHom _
        (Stacks.Divisors.isInvertible_negativeTwist_picard D)) =
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
    Stacks.Divisors.negativeTwistPicardClass (D.comap h) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨pullbackNegativeTwistIso h D hD⟩

/-- **Pullback of the class of an effective Cartier divisor.** If the pullback of `D` along `h` is
defined, then `h^* [𝒪(D)] = [𝒪(h^{-1} D)]`. -/
theorem schemePullbackClass_picardClass_comap :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
    Stacks.Picard.schemePullbackClass h (Stacks.Divisors.picardClass D) =
      Stacks.Divisors.picardClass (D.comap h) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap h) := hD
  have hneg := (schemePullbackClass_negativeTwistPicardClass_eq h D).trans
    (picardClass_pullback_negativeTwist_eq h D hD)
  rw [Stacks.Divisors.negativeTwistPicardClass_eq_neg,
    Stacks.Divisors.negativeTwistPicardClass_eq_neg] at hneg
  have hmap : Stacks.Picard.schemePullbackClass h (-Stacks.Divisors.picardClass D) =
      -Stacks.Picard.schemePullbackClass h (Stacks.Divisors.picardClass D) :=
    map_neg (Stacks.Picard.schemePullbackClassHom h) _
  rw [hmap] at hneg
  exact neg_injective hneg

end Pullback

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g]

/-! ### Point classes -/

/-- The closed points of a scheme. -/
abbrev ClosedPoint (C : Scheme.{u}) : Type u := {x : C // IsClosed ({x} : Set C)}

/-- The ideal sheaf of the reduced closed subscheme on a closed point. -/
def pointIdeal (x : ClosedPoint C) : C.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (⟨{x.1}, x.2⟩ : Closeds C)

omit [IsAlgClosed Ω] [IsProper g] in
include g in
/-- The ideal sheaf of a closed point of `C` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_pointIdeal (x : ClosedPoint C) :
    Stacks.Divisors.IsEffectiveCartierDivisor (pointIdeal x) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian g
  have := IsCurve.isDiscreteValuationRing_stalk_of_isClosed Ω g x.2
  exact isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing x.2

/-- The class `[x]` in `Pic(C)` of a closed point. -/
def pointClass (x : ClosedPoint C) : Stacks.Picard.ofScheme C :=
  haveI := isEffectiveCartierDivisor_pointIdeal g x
  Stacks.Divisors.picardClass (pointIdeal x)

/-- The class `∑ n_x [x]` of a divisor on the closed points. -/
def divisorClass : (ClosedPoint C →₀ ℤ) →+ Stacks.Picard.ofScheme C :=
  Finsupp.liftAddHom fun x => zmultiplesHom _ (pointClass g x)

omit [IsAlgClosed Ω] [IsProper g] in
/-- The class of the divisor `n x` is `n [x]`. -/
theorem divisorClass_single (x : ClosedPoint C) (n : ℤ) :
    divisorClass g (Finsupp.single x n) = n • pointClass g x := by
  rw [divisorClass, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

omit [IsAlgClosed Ω] [IsProper g] in
/-- The class of `D = ∑ n_x x` is `∑ n_x [x]`. -/
theorem divisorClass_apply (D : ClosedPoint C →₀ ℤ) :
    divisorClass g D = D.sum fun x n => n • pointClass g x := by
  simp only [divisorClass, Finsupp.liftAddHom_apply]
  rfl

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
include g in
/-- The curve `C` has topological Krull dimension at most one. -/
theorem topologicalKrullDim_le_one : topologicalKrullDim C ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := Ω) (f := g)).le

/-- **A closed point has degree one.** -/
theorem picardDegree_pointClass (x : ClosedPoint C) :
    Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) (pointClass g x) = 1 := by
  have := isEffectiveCartierDivisor_pointIdeal g x
  set D := pointIdeal x
  have hdeg := Stacks.Picard.picardDegree_divisorPicardClass g (topologicalKrullDim_le_one g) D
  let : Algebra Ω Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (D.subschemeι ≫ g).appTop).hom.toAlgebra
  have : IsFinite (D.subschemeι ≫ g) :=
    isFinite_divisorSubscheme Ω g (topologicalKrullDim_le_one g) D
  have hfin : Module.Finite Ω Γ(D.subscheme, ⊤) := by
    have hiso : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).hom :=
      (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv)).surjective
    have h : ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (D.subschemeι ≫ g).appTop).hom.Finite := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Finite.comp (Scheme.Hom.finite_appTop (D.subschemeι ≫ g))
        (RingHom.Finite.of_surjective _ hiso)
    exact h
  have : IsIntegral D.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ isIrreducible_singleton
  have hbij : Function.Bijective (algebraMap Ω Γ(D.subscheme, ⊤)) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral _
      (Algebra.IsIntegral.isIntegral (R := Ω) (A := Γ(D.subscheme, ⊤)) ·)
  have h1 : Module.finrank Ω Γ(D.subscheme, ⊤) = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap Ω Γ(D.subscheme, ⊤)) hbij).finrank_eq,
      Module.finrank_self]
  show Stacks.Picard.picardDegree g _ (Stacks.Divisors.picardClass D) = 1
  rw [hdeg, h1, Nat.cast_one]

/-- **The degree of a divisor class is the degree of the divisor.** -/
theorem picardDegree_divisorClass (D : ClosedPoint C →₀ ℤ) :
    Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) (divisorClass g D) =
      D.sum fun _ n => n := by
  rw [divisorClass_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_zsmul, picardDegree_pointClass, smul_eq_mul, mul_one]

/-! ### Pullback along an automorphism -/

/-- An automorphism of `C` permutes the closed points. -/
def closedPointPerm (Ψ : C ≅ C) : Equiv.Perm (ClosedPoint C) where
  toFun x := ⟨Ψ.hom.base x.1, by
    have := Ψ.hom.homeomorph.isClosedMap _ x.2
    simpa [Set.image_singleton] using this⟩
  invFun x := ⟨Ψ.inv.base x.1, by
    have := Ψ.inv.homeomorph.isClosedMap _ x.2
    simpa [Set.image_singleton] using this⟩
  left_inv x := Subtype.ext (by
    change (Ψ.hom ≫ Ψ.inv).base x.1 = x.1
    rw [Ψ.hom_inv_id]; rfl)
  right_inv x := Subtype.ext (by
    change (Ψ.inv ≫ Ψ.hom).base x.1 = x.1
    rw [Ψ.inv_hom_id]; rfl)

/-- The permutation `closedPointPerm Ψ` sends a closed point `x` to `Ψ x`. -/
@[simp]
theorem closedPointPerm_apply_val (Ψ : C ≅ C) (x : ClosedPoint C) :
    (closedPointPerm Ψ x).1 = Ψ.hom.base x.1 := rfl

/-- The inverse of `closedPointPerm Ψ` sends a closed point `x` to `Ψ⁻¹ x`. -/
@[simp]
theorem closedPointPerm_symm_apply_val (Ψ : C ≅ C) (x : ClosedPoint C) :
    ((closedPointPerm Ψ).symm x).1 = Ψ.inv.base x.1 := rfl

/-- The scheme-theoretic inverse image of a reduced closed point along an automorphism is the
reduced closed point `Ψ⁻¹ x`. -/
theorem pointIdeal_comap (Ψ : C ≅ C) (x : ClosedPoint C) :
    (pointIdeal x).comap Ψ.hom = pointIdeal ((closedPointPerm Ψ).symm x) := by
  have key := Stacks.Chow.comap_vanishingIdeal_closure_singleton_of_isIso Ψ.hom (Ψ.inv.base x.1)
  have hx : Ψ.hom.base (Ψ.inv.base x.1) = x.1 := by
    show (Ψ.inv ≫ Ψ.hom).base x.1 = x.1
    rw [Ψ.inv_hom_id]; rfl
  have hcl (y : ClosedPoint C) : Closeds.closure ({y.1} : Set C) = ⟨{y.1}, y.2⟩ :=
    Closeds.ext y.2.closure_eq
  rw [hx, hcl x] at key
  exact key.trans (congrArg _ (hcl ((closedPointPerm Ψ).symm x)))

omit [IsAlgClosed Ω] [IsProper g] in
/-- **Pullback of a point class**: `Ψ^* [x] = [Ψ⁻¹ x]`. -/
theorem schemePullbackClass_pointClass (Ψ : C ≅ C) (x : ClosedPoint C) :
    Stacks.Picard.schemePullbackClass Ψ.hom (pointClass g x) =
      pointClass g ((closedPointPerm Ψ).symm x) := by
  have := isEffectiveCartierDivisor_pointIdeal g x
  have := isEffectiveCartierDivisor_pointIdeal g ((closedPointPerm Ψ).symm x)
  have hD : Stacks.Divisors.IsPullbackDefined Ψ.hom (pointIdeal x) :=
    Stacks.Divisors.isPullbackDefined_of_flat Ψ.hom _ inferInstance
  have := schemePullbackClass_picardClass_comap Ψ.hom (pointIdeal x) hD
  refine this.trans ?_
  exact Stacks.Divisors.picardClass_congr (pointIdeal_comap Ψ x)

omit [IsAlgClosed Ω] [IsProper g] in
/-- **Pullback of a divisor class**: `Ψ^* [D] = [Ψ⁻¹ D]`, the divisor `Ψ⁻¹ D` being `D`
transported along `Ψ⁻¹` (its coefficient at `y` is the coefficient of `D` at `Ψ y`). -/
theorem schemePullbackClass_divisorClass (Ψ : C ≅ C) (D : ClosedPoint C →₀ ℤ) :
    Stacks.Picard.schemePullbackClassHom Ψ.hom (divisorClass g D) =
      divisorClass g (D.mapDomain (closedPointPerm Ψ).symm) := by
  rw [divisorClass_apply, divisorClass_apply, map_finsuppSum,
    Finsupp.sum_mapDomain_index (h := fun x n => n • pointClass g x) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [map_zsmul]
  exact congrArg _ (schemePullbackClass_pointClass g Ψ x)

end Stacks.Zeta

end
