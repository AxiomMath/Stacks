module

public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackBase
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFibre
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.LocalFlatTensorConverse

/-!
# Weakly associated points of a flat tensor product with a pullback: Stacks 05IH

Let `S` be a scheme, `f : X ⟶ S` locally of finite type, `x ∈ X` with image `s`, `F` a
quasi-coherent `𝒪_X`-module of finite type and `G` a quasi-coherent `𝒪_S`-module. If `F` is flat
at `x` over `S`, then

`x ∈ WeakAss_X(F ⊗_{𝒪_X} f^*G) ↔ s ∈ WeakAss_S(G) and x ∈ Ass_{X_s}(F_s)`.

This file assembles the three clauses:

* the base clause `x ∈ WeakAss(F ⊗ f^*G) → s ∈ WeakAss(G)` is
  `Stacks.Divisors.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType`;
* the fibre clause `x ∈ WeakAss(F ⊗ f^*G) → x ∈ Ass_{X_s}(F_s)` is
  `Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType`;
* the converse is proved here on stalks, by
  `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_closedFibre`:
  at a point the fibre prime is the maximal ideal of `𝒪_{X, x}`, which is maximal among the
  associated primes of the closed fibre, so no projectivity is needed.

The condition `x ∈ Ass_{X_s}(F_s)` is written as membership in the relative assassin
`Stacks.Divisors.relativeAssassin f F` of tag 05AT, which at `x` says exactly that the point `x`
determines on its fibre is associated to the restriction of `F` to that fibre
(`Stacks.Divisors.mem_relativeAssassin_iff_isAssociatedPoint_asFiber`).

## Main results

* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin_of_finiteType`
* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType`: **Stacks 05IH**.

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct IsLocalRing
open Stacks.WeaklyAssociatedPrimes

universe u

namespace Stacks.Divisors

/-- **The converse implication of Stacks 05IH.** Let `f : X ⟶ S` be locally of finite
type, let `F` be an `𝒪_X`-module which is flat over `S` at `x`, and let `G` be an `𝒪_S`-module.
If `f x` is weakly associated to `G` and `x` lies in the relative assassin `Ass_{X/S}(F)`, then
`x` is weakly associated to `F ⊗_{𝒪_X} f^*G`. -/
theorem isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules) (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hG : IsWeaklyAssociatedPoint G (f x))
    (hx : x ∈ relativeAssassin f F) :
    IsWeaklyAssociatedPoint
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
                  ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G)))) x := by
  classical
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have : IsNoetherianRing
      (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R)) := by
    have : IsLocallyNoetherian (f.fiber (f x)) := by
      have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
        change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
        infer_instance
      exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
    rw [RingHom.algebraMap_toAlgebra]
    exact isNoetherianRing_of_ringEquiv _ (quotientStalkEquivFiberStalk f x).symm
  rw [mem_relativeAssassin_iff_isAssociatedPoint_asFiber,
    isAssociatedPoint_pullback_fiberι_iff] at hx
  have hq : IsAssociatedPrimeStacks B
      (N ⧸ Ideal.map (algebraMap R B) (maximalIdeal R) • (⊤ : Submodule B N))
      (maximalIdeal B) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hx
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] M) (maximalIdeal B) :=
    isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_closedFibre hG hq
  let P := (Scheme.Modules.pullback f).obj G
  let tens := (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
          ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (P))
  obtain ⟨eTensor⟩ := exists_tensorStalkLinearEquiv F P x
  let ePull : TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x ≃ₗ[B]
      TensorProduct R B M := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G x)
  let : Module B (TopCat.Presheaf.stalk (C := Ab.{u}) tens.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) tens.val x
  exact (LinearEquiv.isWeaklyAssociatedPrime_iff (eTensor.trans ((ePull.lTensor N).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N M))) _).mpr hT

/-- Let `S` be a scheme, let `f : X ⟶ S` be locally of finite type, let `x ∈ X`, let `F` be a
quasi-coherent `𝒪_X`-module of finite type and let `G` be a quasi-coherent `𝒪_S`-module. If `F` is
flat at `x` over `S`, then `x` is weakly associated to `F ⊗_{𝒪_X} f^*G` if and only if `f x` is
weakly associated to `G` and `x` is an associated point of the restriction of `F` to the fibre
`X_{f x}`, that is, `x` lies in the relative assassin `Ass_{X/S}(F)`. -/
@[stacks 05IH]
theorem isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (x : X) (hF : IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsWeaklyAssociatedPoint
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
                    ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
              (((Scheme.Modules.pullback f).obj G)))) x ↔
      (IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F) :=
  ⟨fun hx => ⟨isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType
      f F G x hF hx,
    mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType f F G x hF hx⟩,
   fun h => isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin_of_finiteType
      f F G x hF h.1 h.2⟩

end Stacks.Divisors

end
