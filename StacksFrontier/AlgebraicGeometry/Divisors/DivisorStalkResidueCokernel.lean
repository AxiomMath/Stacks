module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProductFactorizationEquiv
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantNonzero
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.ExactStalkCokernel
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtStalk

/-!
# The cokernel of a stalk map carried by a finite locally free module on a divisor

Let `S` be a short exact complex of `𝒪_X`-modules whose last term is the direct image of a
finite locally free module of rank `s` on the integral closed subscheme cut out by an ideal
sheaf `D`.  At the image `ξ` of the generic point of that subscheme the cokernel of the stalk
map of `S.f` is `κ(ξ) ^ s`, where `κ(ξ)` is the residue field of `𝒪_{X, ξ}`.

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal`: the stalk
  of the ideal sheaf at `ξ` is the maximal ideal of `𝒪_{X, ξ}`.
* `AlgebraicGeometry.linearEquiv_quotient_range_stalkHom_fin`: **the cokernel of the stalk map
  of `S.f` at `ξ` is `κ(ξ) ^ s`.**

## Implementation notes

The chain runs through four already available identifications: the cokernel of the stalk map
is the stalk of `S.X₃` (`Stacks.SheafOfModules.quotientRangeStalkHomEquiv`), that stalk is the
stalk of `G` at the generic point of the subscheme
(`Stacks.Algebraization.stalkPushforwardModuleLinearEquiv`), which is free of rank `s`
(`AlgebraicGeometry.SheafOfModules.nonempty_stalkLinearEquiv_fin`) over the local ring of the
subscheme, and that local ring is `𝒪_{X, ξ}` modulo the stalk of the ideal sheaf
(`AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv`), which is the maximal ideal
because the quotient is the function field of the integral subscheme.

Three of the four speak different base rings, so the middle steps are restrictions of scalars
along the stalk map of the closed immersion; `Stacks.Discriminant.linearEquivCompHom` does
those, and `AlgebraicGeometry.piRingEquivLinearEquiv` is the one transport that had to be
written out.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

/-! ### A restriction of scalars -/

/-- A ring isomorphism `ψ : A ≃+* κ` carrying the `R`-algebra structure of `A` to that of `κ`
turns `ι → A`, an `R`-module through `φ`, into `ι → κ`. -/
def piRingEquivLinearEquiv {R A κ : Type*} [CommRing R] [CommRing A] [CommRing κ]
    [Module R κ] (φ : R →+* A) (ψ : A ≃+* κ)
    (hsmul : ∀ (r : R) (q : κ), r • q = ψ (φ r) * q) (ι : Type*) :
    letI : Module R (ι → A) := Module.compHom _ φ
    (ι → A) ≃ₗ[R] (ι → κ) :=
  letI : Module R (ι → A) := Module.compHom _ φ
  { toFun := fun v i => ψ (v i)
    map_add' := fun v w => funext fun i => map_add ψ (v i) (w i)
    map_smul' := fun r v => funext fun i => by
      change ψ ((φ r • v) i) = r • ψ (v i)
      rw [hsmul, Pi.smul_apply, smul_eq_mul, map_mul]
    invFun := fun w i => ψ.symm (w i)
    left_inv := fun v => funext fun i => ψ.symm_apply_apply (v i)
    right_inv := fun w => funext fun i => ψ.apply_symm_apply (w i) }

/-! ### The local ring of an integral subscheme at its generic point -/

variable {X : Scheme.{u}}

/-- **The stalk of an ideal sheaf with integral subscheme, at the image of the generic point of
that subscheme, is the maximal ideal**: the quotient by it is the function field. -/
theorem IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal (D : X.IdealSheafData)
    [IsIntegral D.subscheme] :
    IdealSheafData.stalk D (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))
      = IsLocalRing.maximalIdeal
          (X.presheaf.stalk (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))) :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _ isField_quotient_stalk_subschemeι_genericPoint)

/-- **The local ring of an integral closed subscheme at its generic point is the residue field
of the ambient local ring there.** -/
def IdealSheafData.subschemeStalkGenericPointResidueFieldEquiv (D : X.IdealSheafData)
    [IsIntegral D.subscheme] :
    D.subscheme.presheaf.stalk (_root_.genericPoint (D.subscheme : Type u)) ≃+*
      IsLocalRing.ResidueField
        (X.presheaf.stalk (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))) :=
  (IdealSheafData.subschemeStalkQuotEquiv D
      (_root_.genericPoint (D.subscheme : Type u))).symm.trans
    (Ideal.quotEquivOfEq (IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal D))

/-- The identification of the previous declaration takes the stalk map of the closed immersion
to the residue map. -/
theorem IdealSheafData.subschemeStalkGenericPointResidueFieldEquiv_stalkMap
    (D : X.IdealSheafData) [IsIntegral D.subscheme]
    (r : X.presheaf.stalk (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))) :
    IdealSheafData.subschemeStalkGenericPointResidueFieldEquiv D
        (D.subschemeι.stalkMap (_root_.genericPoint (D.subscheme : Type u)) r)
      = IsLocalRing.residue _ r := by
  change Ideal.quotEquivOfEq
      (IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal D)
      ((IdealSheafData.subschemeStalkQuotEquiv D
          (_root_.genericPoint (D.subscheme : Type u))).symm
        (D.subschemeι.stalkMap (_root_.genericPoint (D.subscheme : Type u)) r))
    = IsLocalRing.residue _ r
  rw [← IdealSheafData.subschemeStalkQuotEquiv_mk D _ r, RingEquiv.symm_apply_apply,
    Ideal.quotEquivOfEq_mk]
  rfl

/-! ### The cokernel at the generic point of the divisor -/

/-- **The cokernel of the stalk map of `S.f` at the image `ξ` of the generic point of the
integral subscheme cut out by `D` is `κ(ξ) ^ s`**, when `S` is exact with `S.g` an
epimorphism and `S.X₃` is the direct image of a module `G` on that subscheme which is finite
locally free of rank `s`. -/
theorem linearEquiv_quotient_range_stalkHom_fin {S : ShortComplex X.Modules} (hS : S.Exact)
    [Epi S.g] {D : X.IdealSheafData} [IsIntegral D.subscheme] {G : D.subscheme.Modules} (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s]
    (hquot : S.X₃ ≅ (Scheme.Modules.pushforward D.subschemeι).obj G) :
    Nonempty ((modStalk S.X₂ (D.subschemeι (_root_.genericPoint (D.subscheme : Type u))) ⧸
        LinearMap.range
          (stalkHom S.f (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))))
      ≃ₗ[ringStalk X.sheaf (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))]
        (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf
          (D.subschemeι (_root_.genericPoint (D.subscheme : Type u)))))) := by
  set z : (D.subscheme : Type u) := _root_.genericPoint (D.subscheme : Type u)
  let φ : ringStalk X.sheaf (D.subschemeι z) →+* D.subscheme.presheaf.stalk z :=
    (D.subschemeι.stalkMap z).hom
  let : Module (ringStalk X.sheaf (D.subschemeι z)) (G.presheaf.stalk z) :=
    Module.compHom _ φ
  obtain ⟨e⟩ : Nonempty (G.presheaf.stalk z ≃ₗ[D.subscheme.presheaf.stalk z]
      (Fin s →₀ D.subscheme.presheaf.stalk z)) :=
    SheafOfModules.nonempty_stalkLinearEquiv_fin G s z
  let ψ : D.subscheme.presheaf.stalk z ≃+*
      IsLocalRing.ResidueField (ringStalk X.sheaf (D.subschemeι z)) :=
    IdealSheafData.subschemeStalkGenericPointResidueFieldEquiv D
  have hsmul : ∀ (r : ringStalk X.sheaf (D.subschemeι z))
      (q : IsLocalRing.ResidueField (ringStalk X.sheaf (D.subschemeι z))),
      r • q = ψ (φ r) * q := fun r q => by
    rw [show ψ (φ r) = IsLocalRing.residue _ r from
      IdealSheafData.subschemeStalkGenericPointResidueFieldEquiv_stalkMap D r]
    exact Algebra.smul_def r q
  let E₁ := Stacks.SheafOfModules.quotientRangeStalkHomEquiv hS (D.subschemeι z)
  let E₂ := Stacks.SheafOfModules.modStalkEquivOfIso X.sheaf hquot (D.subschemeι z)
  let E₃ : modStalk ((Scheme.Modules.pushforward D.subschemeι).obj G) (D.subschemeι z)
      ≃ₗ[ringStalk X.sheaf (D.subschemeι z)] G.presheaf.stalk z :=
    Stacks.Algebraization.stalkPushforwardModuleLinearEquiv D.subschemeι G z
      (IsClosedImmersion.isClosedEmbedding D.subschemeι).isInducing
  let E₄ := Stacks.Discriminant.linearEquivCompHom φ e
  let E₅ := Stacks.Discriminant.linearEquivCompHom φ (Finsupp.linearEquivFunOnFinite
    (D.subscheme.presheaf.stalk z) (D.subscheme.presheaf.stalk z) (Fin s))
  let E₆ := piRingEquivLinearEquiv φ ψ hsmul (Fin s)
  exact ⟨E₁.trans (E₂.trans (E₃.trans (E₄.trans (E₅.trans E₆))))⟩

end AlgebraicGeometry

end
