module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.BaseChange
public import StacksFrontier.RingTheory.Flat.QuotientInf

/-!
# Flattening over an Artinian ring

Over an Artinian ring every module has a smallest ideal `I` such that the quotient becomes flat
over the quotient ring, and that ideal has a universal property with respect to base change.

## Main results

* `exists_least_flat_quotient_ideal`: existence of the smallest flattening ideal.
* `flat_tensorProduct_iff_map_least_flat_quotient_ideal_eq_bot`: the base change of the module
  along a ring map is flat if and only if the smallest flattening ideal maps to zero.

## References

* [Stacks Project, Tag 05LJ](https://stacks.math.columbia.edu/tag/05LJ)
-/

@[expose] public section

section

/-- Over an Artinian ring `R`, there is a smallest ideal `I` such that `M ⧸ I • M` is flat over
`R ⧸ I`. -/
@[stacks 0524, ega "IV 11.4.4" "flat clause, Artinian"]
theorem exists_least_flat_quotient_ideal {R M : Type*} [CommRing R]
    [IsArtinianRing R] [AddCommGroup M] [Module R M] :
    ∃ I : Ideal R,
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        ∀ J : Ideal R,
          Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) → I ≤ J := by
  obtain ⟨I, hI, hImin⟩ := exists_minimal_of_wellFoundedLT
    (fun I : Ideal R ↦ Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    ⟨⊤, Module.Flat.iff_rTensor_injective'.2 fun _ ↦ Function.injective_of_subsingleton _⟩
  exact ⟨I, hI, fun J hJ ↦
    (hImin (Module.Flat.quotient_inf I J hI hJ) inf_le_left).trans inf_le_right⟩

end

section
open TensorProduct
open scoped TensorProduct

private noncomputable def quotientBaseChangeEquiv
    {R M S : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [CommRing S] [Algebra R S] [Algebra (R ⧸ I) S]
    [IsScalarTower R (R ⧸ I) S] :
    S ⊗[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[S] S ⊗[R] M := by
  let e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[R] M :=
    { (TensorProduct.quotTensorEquivQuotSMul M I).symm with
      map_smul' := by
        rintro ⟨r⟩ ⟨m⟩
        change (TensorProduct.quotTensorEquivQuotSMul M I).symm
            (Submodule.Quotient.mk (r • m)) =
          (Ideal.Quotient.mk I r) •
            (TensorProduct.quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk m)
        rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk,
          TensorProduct.quotTensorEquivQuotSMul_symm_mk, TensorProduct.smul_tmul',
          TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul (R ⧸ I) r (1 ⊗ₜ[R] m)]
        rfl }
  exact e.baseChange (R ⧸ I) S _ _ ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) S S M

/-- The least ideal making the corresponding quotient of a module flat maps
to zero under precisely those ring maps along which the module becomes flat. -/
@[stacks 0525]
theorem flat_tensorProduct_iff_map_least_flat_quotient_ideal_eq_bot
    {R M : Type*} [CommRing R] [IsArtinianRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hI : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hmin : ∀ J : Ideal R,
      Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) → I ≤ J) :
    ∀ {S : Type*} [CommRing S] (φ : R →+* S),
      let _ := φ.toAlgebra;
      Module.Flat S (S ⊗[R] M) ↔ I.map φ = ⊥ := by
  intro S _ φ _
  refine ⟨fun hflat ↦ ?_, fun hmap ↦ ?_⟩
  · let J := RingHom.ker φ
    let _ := (RingHom.kerLift φ).toAlgebra
    have : IsScalarTower R (R ⧸ J) S :=
      IsScalarTower.of_algebraMap_eq fun x => (RingHom.kerLift_mk φ x).symm
    have : Module.Flat S (S ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) :=
      Module.Flat.of_linearEquiv (quotientBaseChangeEquiv J)
    exact (Ideal.map_eq_bot_iff_le_ker φ).2 <| hmin J <| .of_flat_baseChange_of_injective S _
      (TensorProduct.isBaseChange (R ⧸ J) _ S) (RingHom.kerLift_injective φ)
  · have hle : I ≤ RingHom.ker φ := (Ideal.map_eq_bot_iff_le_ker φ).1 hmap
    let _ := (Ideal.Quotient.lift I φ fun _ hx => hle hx).toAlgebra
    have : IsScalarTower R (R ⧸ I) S :=
      IsScalarTower.of_algebraMap_eq fun x => (Ideal.Quotient.lift_mk I φ fun _ hx => hle hx).symm
    exact Module.Flat.of_linearEquiv (quotientBaseChangeEquiv I).symm

end
