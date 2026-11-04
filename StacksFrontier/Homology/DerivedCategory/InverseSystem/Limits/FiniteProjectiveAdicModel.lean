module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.AdicCompletionModel
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect

/-!
# A bounded finite projective model over the adic completion

Let `I` be an ideal of a commutative ring `Λ` and `N` a complex of `Λ`-modules whose reductions
`Λ/Iⁿ⁺¹ ⊗ N` are K-flat, the first of them perfect. [Stacks, Tag 0CQF] gives a bounded above
complex `F` of finite free modules over the `I`-adic completion `Λ^∧` with
`Λ/Iⁿ⁺¹ ⊗_{Λ^∧} F ≅ Λ/Iⁿ⁺¹ ⊗ N` for every `n`
(`StacksDraft.DerivedInverseLimit.exists_isBoundedAboveFiniteFree_adicCompletion_iso`). This file
shows that `F` is perfect, so that it may be replaced by a bounded complex of finite projective
modules.

## Main results

* `StacksDraft.DerivedInverseLimit.exists_finiteProjective_adicCompletion_iso`: a complex of
  `Λ`-modules with K-flat reductions, the first one perfect, has a bounded finite projective model
  over the `I`-adic completion `Λ^∧`.

## Implementation notes

Perfectness of `F` is deduced from that of its first reduction by
`StacksDraft.DerivedInverseLimit.isPerfect_of_surjective_baseChange`, whose unit-detection
hypothesis for `Λ^∧ → Λ/I` is the private lemma `isUnit_of_isUnit_limit_projection_zero` of
`StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect`, used here by `import all`.

## References

* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace StacksDraft.DerivedInverseLimit

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### A finite projective adic model -/

section AdicModel

/-- The comparison map of a derived extension of scalars is invertible at a bounded above complex
of modules which are projective over the base ring. -/
private theorem isIso_comparison_app_of_module_projective {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S}
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u} f)
    (G : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [G.IsStrictlyLE b]
    [∀ i, Module.Projective R (G.X i)] : IsIso (D.comparison.app G) :=
  have : ∀ i, Projective (G.X i) := fun _ => inferInstance
  D.comparison_isIso_of_projective G b

/-- **A bounded finite projective adic model.** Let `I` be an ideal of a commutative ring `Λ` and
`N` a complex of `Λ`-modules whose reductions `Λ/Iⁿ⁺¹ ⊗ N` are K-flat, the first of them
`Λ/I ⊗ N` being perfect. Then there is a bounded complex `M` of finite projective modules over
the `I`-adic completion `Λ^∧` such that `Λ/Iⁿ⁺¹ ⊗_{Λ^∧} M ≅ Λ/Iⁿ⁺¹ ⊗ N` in `D(Λ/Iⁿ⁺¹)` for every
`n`.

Stacks 0CQF (`exists_isBoundedAboveFiniteFree_adicCompletion_iso`) gives such an `F` which is
bounded above and finite free; it is perfect because `Λ^∧ → Λ/I` is surjective, detects units
(its kernel is locally nilpotent along the tower) and `Λ/I ⊗_{Λ^∧} F ≅ Λ/I ⊗ N` is perfect
(`isPerfect_of_surjective_baseChange`); a bounded complex of finite projective modules
representing `F` is the model, derived base change being computed termwise on bounded above
complexes of projectives. -/
public theorem exists_finiteProjective_adicCompletion_iso {Λ : Type u} [CommRing Λ]
    (I : Ideal Λ) (N : CochainComplex (ModuleCat.{u} Λ) ℤ)
    (hN : ∀ n : ℕ, CochainComplex.KFlat.{u, u} (((ModuleCat.extendScalars
      (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    (hN₀ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj (((ModuleCat.extendScalars
      (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) :
    ∃ (M : CochainComplex (ModuleCat.{u} (AdicCompletion I Λ)) ℤ) (a b : ℤ),
      M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ k : ℤ, Module.Finite (AdicCompletion I Λ) (M.X k) ∧
        Module.Projective (AdicCompletion I Λ) (M.X k)) ∧ ∀ n : ℕ,
        Nonempty (DerivedCategory.Q.obj (((ModuleCat.extendScalars
            (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) ≅
          DerivedCategory.Q.obj (((ModuleCat.extendScalars
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj N)) := by
  obtain ⟨F, hF, hFN⟩ := exists_isBoundedAboveFiniteFree_adicCompletion_iso I N hN
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.mp hN₀).1
  obtain ⟨b₀, hb₀⟩ := hF.upperBound
  have hFp : ∀ i, Module.Projective (AdicCompletion I Λ) (F.X i) := fun i => by
    have := (hF.finiteFree i).2
    infer_instance
  have hs : ∀ n : ℕ, Function.Surjective
      ((quotientPowerDiagram I).map (homOfLE (Nat.le_succ n)).op).hom := fun n ↦
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hNil (n : ℕ) : IsNilpotent (RingHom.ker
      ((quotientPowerDiagram I).map (homOfLE (Nat.le_succ n)).op).hom) :=
    ⟨2, ker_factor_pow_eq_bot (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega))⟩
  let f := ((adicCompletionPowerCone I).π.app (op 0)).hom
  let D₀ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  have := isIso_comparison_app_of_module_projective D₀ F b₀
  have hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj F) :=
    isPerfect_of_surjective_baseChange.{u, u} f
      (Concrete.surjective_π_app_zero_of_surjective_map (adicCompletionPowerConeIsLimit I) hs)
      (isUnit_of_isUnit_limit_projection_zero _ _ (adicCompletionPowerConeIsLimit I) hs
        (fun n ↦ isLocallyNilpotent_of_isNilpotent _ (hNil n)))
      _ ⟨F, hF, ⟨Iso.refl _⟩⟩
      (StacksDraft.Perfect.isPerfect_of_iso (asIso (D₀.comparison.app F) ≪≫ (hFN 0).some)
        hN₀)
  obtain ⟨M, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hperf
  refine ⟨M, a, b, hGE, hLE, fun k => ⟨hfin k, hproj k⟩, fun n => ⟨?_⟩⟩
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom
  have := isIso_comparison_app_of_module_projective D M b
  have := isIso_comparison_app_of_module_projective D F b₀
  exact (asIso (D.comparison.app M)).symm ≪≫ D.functor.mapIso e.symm ≪≫
    asIso (D.comparison.app F) ≪≫ (hFN n).some

end AdicModel

end StacksDraft.DerivedInverseLimit

end
