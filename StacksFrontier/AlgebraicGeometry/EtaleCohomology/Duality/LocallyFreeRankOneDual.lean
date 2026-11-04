module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyFreeDual
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineTopLisse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallyConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChangeFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllDictionary

/-!
# An étale-locally free sheaf of rank one is invertible

Let `Λ` be a commutative ring, `Y` a scheme and `N` a sheaf of `Λ`-modules on `Y_étale` which is
étale-locally constant with value a module isomorphic to `Λ`. Then the dual `N^∨ = Hom(N, Λ)`
(`Stacks.EtaleCohomology.etaleModuleDual`) is étale-locally free of finite rank and the evaluation
`N^∨ ⊗ N ⟶ Λ` is an isomorphism; with the braiding, also `N ⊗ N^∨ ≅ Λ`.

The evaluation is checked on the conservative family of residue geometric points: at a point `Φ`
the fibre `N_Φ` is `Λ` (the constant value at a trivializing neighbourhood), the fibre pairing
`(N^∨)_Φ ⟶ Hom(N_Φ, Λ)` is bijective
(`Stacks.EtaleCohomology.bijective_fiberPairing_etaleModuleDualEvaluation`), and for `L ≅ Λ` the
contraction `Hom(L, Λ) ⊗ L ⟶ Λ` is bijective. The dual is locally constant of finite type (Tag 093T
(3), `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_moduleSheafHom`) with free fibres, hence
locally free.

## Main results

* `Stacks.EtaleCohomology.exists_linearEquiv_sheafFiber_of_isLocallyConstantWith`.
* `Stacks.EtaleCohomology.isIso_etaleModuleDualEvaluation_of_rankOne`.
* `Stacks.EtaleCohomology.isLocallyFreeEtaleModule_etaleModuleDual`.
* `Stacks.EtaleCohomology.exists_invertible_of_rankOne`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Algebra

variable {Λ : Type*} [CommRing Λ] {A L : Type*} [AddCommGroup A] [Module Λ A] [AddCommGroup L]
  [Module Λ L]

/-- **The contraction against a module isomorphic to `Λ` is bijective**: if `p : A ⟶ Hom(L, Λ)` is
bijective and `L ≅ Λ`, then `A ⊗ L ⟶ Λ, a ⊗ x ↦ p a x` is bijective. -/
theorem bijective_lift_of_bijective_of_linearEquiv (p : A →ₗ[Λ] L →ₗ[Λ] Λ)
    (hp : Function.Bijective p) (lL : L ≃ₗ[Λ] Λ) : Function.Bijective (TensorProduct.lift p) := by
  let g : L := lL.symm 1
  have hx : ∀ x : L, x = lL x • g := fun x => by
    apply lL.injective
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  let ev : (L →ₗ[Λ] Λ) →ₗ[Λ] Λ := LinearMap.applyₗ g
  have hev : Function.Bijective ev := by
    refine ⟨fun f₁ f₂ h => LinearMap.ext fun x => ?_, fun c => ⟨c • lL.toLinearMap, ?_⟩⟩
    · rw [hx x, map_smul, map_smul]
      exact congrArg (lL x • ·) h
    · show c * lL (lL.symm 1) = c
      rw [LinearEquiv.apply_symm_apply, mul_one]
  have heq : TensorProduct.lift p = (ev ∘ₗ p) ∘ₗ (TensorProduct.rid Λ A).toLinearMap ∘ₗ
      TensorProduct.map LinearMap.id lL.toLinearMap := by
    refine TensorProduct.ext' fun a x => ?_
    simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe,
      TensorProduct.rid_tmul, map_smul, ev, LinearMap.applyₗ_apply_apply]
    conv_lhs => rw [hx x]
    rw [map_smul]
  rw [heq]
  exact ((hev.comp hp).comp (TensorProduct.rid Λ A).bijective).comp
    (TensorProduct.congr (LinearEquiv.refl Λ A) lL).bijective

end Algebra

attribute [local instance] Sheaf.monoidalCategory moduleCat_hasLimitsOfSize
  etaleModules_AB5OfSize etaleModules_preservesFilteredColimits_forget
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

open Stacks.SheafDuality Functor.LaxMonoidal

variable {Λ : Type} [CommRing Λ] {Y : Scheme.{u}}

attribute [local instance] isMonoidal_W_etaleModules

/-- **The fibre of an étale-locally constant sheaf is one of its constant values**: at every point
of `Y_étale`, `N_Φ ≅ E` for a value `E` of `N` on a trivializing neighbourhood. -/
theorem exists_linearEquiv_sheafFiber_of_isLocallyConstantWith (Q : ModuleCat.{u + 1} Λ → Prop)
    (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology Q N)
    (Φ : Y.smallEtaleTopology.Point.{u + 1}) :
    ∃ E : ModuleCat.{u + 1} Λ, Q E ∧
      Nonempty ((SheafDuality.moduleFiber Λ Φ).obj N ≃ₗ[Λ] E) := by
  have : ∀ V : Y.Etale, (Y.smallEtaleTopology.over V).WEqualsLocallyBijective
      (ModuleCat.{u + 1} Λ) := fun _ =>
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ Λ
  obtain ⟨⟨X, x⟩⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨I, V, f, hcov, htriv⟩ := hN X
  obtain ⟨Y₀, g, ⟨Z, p, q, ⟨i⟩, rfl⟩, y₀, -⟩ := Φ.jointly_surjective _ hcov x
  obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
  exact ⟨E, hE, ⟨(Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Φ (Φ.fiber.map p y₀) N E
    e).toLinearEquiv⟩⟩

/-- **A sheaf étale-locally isomorphic to `Λ` is étale-locally free of finite rank.** -/
private theorem isLocallyFreeEtaleModule_of_rankOne (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Nonempty (E ≃ₗ[Λ] Λ)) N) :
    IsLocallyFreeEtaleModule Λ N :=
  isLocallyConstantWith_of_imp Λ (fun _ ⟨l⟩ => ⟨Module.Free.of_equiv l.symm,
    Module.Finite.equiv l.symm⟩) hN

/-- **The evaluation `N^∨ ⊗ N ⟶ Λ` of a sheaf étale-locally isomorphic to `Λ` is an
isomorphism.** -/
theorem isIso_etaleModuleDualEvaluation_of_rankOne (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Nonempty (E ≃ₗ[Λ] Λ)) N) :
    IsIso (etaleModuleDualEvaluation N) := by
  have : ∀ Φ : (residueGeometricPoints.{u, 0} Y).FullSubcategory,
      IsIso ((Φ.obj.sheafFiber (A := ModuleCat.{u + 1} Λ)).map (etaleModuleDualEvaluation N)) :=
    fun Φ => by
      obtain ⟨E, ⟨lE⟩, ⟨lN⟩⟩ := exists_linearEquiv_sheafFiber_of_isLocallyConstantWith _ N hN Φ.obj
      have hψ := bijective_lift_of_bijective_of_linearEquiv _
        (bijective_fiberPairing_etaleModuleDualEvaluation N
          (isLocallyFreeEtaleModule_of_rankOne N hN) Φ.obj).1 (lN.trans lE)
      let μ₀ := μ (SheafDuality.moduleFiber Λ Φ.obj) (etaleModuleDual N) N
      have hcomp : Function.Bijective (μ₀ ≫ (SheafDuality.moduleFiber Λ Φ.obj).map
          (etaleModuleDualEvaluation N)).hom := by
        have h : TensorProduct.lift (fiberPairing (etaleModuleDualEvaluation N) Φ.obj) =
            (unitEquiv (SheafDuality.moduleFiber Λ Φ.obj)).toLinearMap ∘ₗ
              (μ₀ ≫ (SheafDuality.moduleFiber Λ Φ.obj).map (etaleModuleDualEvaluation N)).hom :=
          TensorProduct.ext' fun _ _ => rfl
        rw [h, LinearMap.coe_comp] at hψ
        exact (Function.Bijective.of_comp_iff'
          (unitEquiv (SheafDuality.moduleFiber Λ Φ.obj)).bijective _).1 hψ
      have : IsIso (μ₀ ≫ (SheafDuality.moduleFiber Λ Φ.obj).map (etaleModuleDualEvaluation N)) :=
        (ConcreteCategory.isIso_iff_bijective _).2 hcomp
      exact IsIso.of_isIso_comp_left μ₀ _
  exact ((isConservativeFamilyOfPoints_residueGeometricPoints.{u, 0} Y).jointlyReflectIsomorphisms
    (ModuleCat.{u + 1} Λ)).isIso _

/-- **The dual of an étale-locally free sheaf of finite rank is étale-locally free of finite
rank.** -/
theorem isLocallyFreeEtaleModule_etaleModuleDual (N : EtaleModules.{u, 0} Λ Y)
    (hN : IsLocallyFreeEtaleModule Λ N) : IsLocallyFreeEtaleModule Λ (etaleModuleDual N) := by
  have hF : Stacks.ConstantSheaf.IsFreeFiniteLocallyConstantModuleSheaf.{u + 1, u, 0, 0}
      Y.smallEtaleTopology Λ N :=
    fun U => by
      obtain ⟨I, V, f, hcov, htriv⟩ := hN U
      exact ⟨I, V, f, hcov, fun i => by
        obtain ⟨E, ⟨hfree, hfin⟩, he⟩ := htriv i
        exact ⟨E, hfree, hfin, he⟩⟩
  have hdual : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology
      (etaleModuleDual N) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_moduleSheafHom.{u + 1, u, 0, 0}
      Y.smallEtaleTopology Λ N _ hF
      (isFiniteTypeLocallyConstant_of_isLocallyConstantWith _
        (isLocallyFreeEtaleModule_tensorUnit Λ Y))
  refine isLocallyFreeEtaleModule_of_forall_sheafFiber Λ _ hdual fun s => ?_
  let Φ := (Scheme.pointSmallEtale s.hom).ulift.{u + 1}
  obtain ⟨hp, hfree, hfin⟩ := bijective_fiberPairing_etaleModuleDualEvaluation N hN Φ
  let l : (SheafDuality.moduleFiber Λ Φ).obj (etaleModuleDual N) ≃ₗ[Λ]
      Module.Dual Λ ((SheafDuality.moduleFiber Λ Φ).obj N) :=
    LinearEquiv.ofBijective _ hp
  let eu := ((Scheme.pointSmallEtale s.hom).sheafFiberUliftNatIso.{u, u + 1}
    (ModuleCat.{u + 1} Λ)).app (etaleModuleDual N)
  let l' := eu.toLinearEquiv.symm.trans l
  exact ⟨Module.Free.of_equiv l'.symm, Module.Finite.equiv l'.symm⟩

attribute [local instance] Sheaf.braidedCategory

/-- **A sheaf étale-locally isomorphic to `Λ` is invertible**: it is étale-locally free, and so is
its dual `T'`, with `N ⊗ T' ≅ Λ` and `T' ⊗ N ≅ Λ`. -/
theorem exists_invertible_of_rankOne (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Nonempty (E ≃ₗ[Λ] Λ)) N) :
    IsLocallyFreeEtaleModule Λ N ∧ ∃ T' : EtaleModules.{u, 0} Λ Y, IsLocallyFreeEtaleModule Λ T' ∧
      Nonempty (N ⊗ T' ≅ 𝟙_ (EtaleModules.{u, 0} Λ Y)) ∧
      Nonempty (T' ⊗ N ≅ 𝟙_ (EtaleModules.{u, 0} Λ Y)) := by
  have hN' := isLocallyFreeEtaleModule_of_rankOne N hN
  have := isIso_etaleModuleDualEvaluation_of_rankOne N hN
  exact ⟨hN', etaleModuleDual N, isLocallyFreeEtaleModule_etaleModuleDual N hN',
    ⟨β_ N (etaleModuleDual N) ≪≫ asIso (etaleModuleDualEvaluation N)⟩,
    ⟨asIso (etaleModuleDualEvaluation N)⟩⟩

end Stacks.EtaleCohomology

end
