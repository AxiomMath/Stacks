module

public import StacksFrontier.RingTheory.Koszul.SheafSectionBimoduleSystem
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFlipTower
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestrictionTranspose
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionQuasiCoherent

/-!
# For a quasi-coherent module the Koszul tower `n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t` is constant

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_n` be the Koszul differential
graded algebra on `f₁^n, …, f_r^n`, let `ℬ = Koszul.liftedPowSheafAlgebra f` be the sheaf of
differential graded algebras `(K_{n+1})_n` on the chaotic site `Stacks.LiftedNat`, and let `𝓜` be
a right differential graded `ℬ`-module. For `t ≥ 1` the sections of `𝓜` form an inverse system
`(M_n)` of differential graded `K_{t+n}`-modules (`Koszul.liftedPowSectionBimoduleSystem`), and
[Stacks, Tag 0GZJ] compares the derived limits of the towers `n ↦ M_n ⊗^𝐋_R K_t` and
`n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t`. If `𝓜` satisfies the quasi-coherence condition, the transition maps
`M_n ⊗^𝐋_{K_{t+n}} K_t ⟶ M_0 ⊗^𝐋_{K_t} K_t` of the second tower are isomorphisms, so that tower is
constant with value `M_0 = 𝓜(t - 1)`.

## Main definitions

* `Koszul.liftedPowSectionTower`: the tower `n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t` attached to `𝓜`.

## Main results

* `DifferentialGradedAlgebra.Hom.bijective_cohomologyMap_of_leftInverse`: a homomorphism of
  differential graded algebras with a two-sided inverse is bijective on cohomology.
* `Koszul.bijective_cohomologyMap_liftedPowSectionAlgebraHom`: the identification of `K_{t+n}`
  with the section algebra of `ℬ` over the stage `t - 1 + n` is bijective on cohomology.
* `Koszul.isIso_derivedTranspose_liftedPowSectionTrans`: for `𝓜` quasi-coherent, the derived
  transpose `M_m ⊗^𝐋_{K_{t+m}} K_{t+n} ⟶ M_n` of the restriction map is an isomorphism.
* `Koszul.isIso_liftedPowSectionTower_map_zero`: for `𝓜` quasi-coherent, the transition maps into
  the zeroth term of the tower `n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t` are isomorphisms.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) and
  [Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- A homomorphism of differential graded algebras with a two-sided inverse is bijective on
cohomology. -/
theorem Hom.bijective_cohomologyMap_of_leftInverse (ψ : A.Hom B) (ψ' : B.Hom A)
    (h₁ : ∀ a, ψ'.toAlgebraHom (ψ.toAlgebraHom a) = a)
    (h₂ : ∀ b, ψ.toAlgebraHom (ψ'.toAlgebraHom b) = b) (k : ℤ) :
    Function.Bijective (ψ.cohomologyMap k) := by
  refine Function.bijective_iff_has_inverse.2 ⟨ψ'.cohomologyMap k, ?_, ?_⟩
  · intro x
    induction x using Quotient.inductionOn with
    | h a =>
      show Quotient.mk _ (ψ'.cocycleMap k (ψ.cocycleMap k a)) = Quotient.mk _ a
      exact congrArg _ (Subtype.ext (Subtype.ext (h₁ _)))
  · intro x
    induction x using Quotient.inductionOn with
    | h b =>
      show Quotient.mk _ (ψ.cocycleMap k (ψ'.cocycleMap k b)) = Quotient.mk _ b
      exact congrArg _ (Subtype.ext (Subtype.ext (h₂ _)))

end DifferentialGradedAlgebra

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open Stacks Stacks.ChaoticSite

/-- The transition homomorphism back from the algebra at the stage `t - 1 + n` to `K_{t+n}`; its
underlying map is the identity. -/
def liftedPowStageAlgebraInv (n : ℕ) :
    (powAlgebra f (t - 1 + n + 1)).Hom (powAlgebra f (t + n)) :=
  powTransition f (ht.trans (Nat.le_add_right t n)) (by omega)

/-- The inverse of `Koszul.liftedPowSectionAlgebraHom`. -/
def liftedPowSectionAlgebraInv (n : ℕ) :
    ((liftedPowSheafAlgebra f).sectionAlgebra (liftedPowStage.{u} t n)).Hom
      ((powAlgebra f (t + n)).restrictBase (ULift.{u} ℤ)) :=
  ((liftedPowStageAlgebraInv f ht n).restrictBase (ULift.{u} ℤ)).comp
    (sectionAlgebraHom (liftedPowDiagram f) (liftedPowStage t n))

/-- Two transition homomorphisms of the Koszul algebras whose composite has the same source and
target act as the identity. -/
theorem powTransition_apply_apply_self {n m : ℕ} (h₁ : 1 ≤ n) (h₂ : n ≤ m) (h₃ : 1 ≤ m)
    (h₄ : m ≤ n) (x : ExteriorAlgebra R (Fin r → R)) :
    (powTransition f h₁ h₂).toAlgebraHom ((powTransition f h₃ h₄).toAlgebraHom x) = x := by
  rw [powTransition_comp_apply f h₁ h₂ h₄]
  exact AlgHom.congr_fun (powTransition_self_toAlgebraHom f h₁) x

/-- The identification of `K_{t+n}` with the section algebra of `ℬ` over the stage carrying it is
bijective on cohomology. -/
theorem bijective_cohomologyMap_liftedPowSectionAlgebraHom (n : ℕ) (k : ℤ) :
    Function.Bijective ((liftedPowSectionAlgebraHom f ht n).cohomologyMap k) := by
  refine Hom.bijective_cohomologyMap_of_leftInverse _ (liftedPowSectionAlgebraInv f ht n)
    (fun a => ?_) (fun b => ?_) k
  · show (liftedPowStageAlgebraInv f ht n).toAlgebraHom
      (sectionRingEquiv (liftedPowDiagram f) (liftedPowStage t n)
        ((sectionRingEquiv (liftedPowDiagram f) (liftedPowStage t n)).symm
          ((liftedPowStageAlgebraHom f ht n).toAlgebraHom a))) = a
    rw [RingEquiv.apply_symm_apply]
    exact powTransition_apply_apply_self f _ _ _ _ a
  · show (sectionRingEquiv (liftedPowDiagram f) (liftedPowStage t n)).symm
      ((liftedPowStageAlgebraHom f ht n).toAlgebraHom
        ((liftedPowStageAlgebraInv f ht n).toAlgebraHom
        (sectionRingEquiv (liftedPowDiagram f) (liftedPowStage t n) b))) = b
    exact (congrArg (sectionRingEquiv (liftedPowDiagram f) (liftedPowStage t n)).symm
      (powTransition_apply_apply_self f _ _ _ _ _)).trans
      ((sectionRingEquiv (liftedPowDiagram f) (liftedPowStage t n)).symm_apply_apply b)

variable {f ht}

/-- If `𝓜` satisfies the quasi-coherence condition, the derived transpose
`M_m ⊗^𝐋_{K_{t+m}} K_{t+n} ⟶ M_n` of the restriction map is an isomorphism. -/
theorem isIso_derivedTranspose_liftedPowSectionTrans
    {𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f)}
    (h𝓜 : SheafOfModules.DifferentialGradedModule.Chaotic.IsQCModule 𝓜) {n m : ℕ}
    (h : n ≤ m) :
    IsIso (((derivedTensorFunctor_adj_derivedRestriction (powShiftTransition f ht h)).homEquiv
        _ _).symm (derivedTrans (powShiftTransition f ht h) (liftedPowSectionTrans f ht 𝓜 h))) := by
  have hQC := h𝓜 (liftedPowStageMap t h)
  have hm : IsIso (((derivedTensorFunctor_adj_derivedRestriction
      ((liftedPowSheafAlgebra f).sectionRestriction (liftedPowStageMap t h))).homEquiv _ _).symm
      ((quasiIsomorphisms' _).Q.map ((toHomotopyCategory _).map
        (𝓜.sectionModuleRestriction (liftedPowStageMap t h))) ≫
        (restrictScalarsClassIso ((liftedPowSheafAlgebra f).sectionRestriction
          (liftedPowStageMap t h)) (𝓜.sectionModule (liftedPowStage t n))).hom)) := by
    have e := map_id_comp_aux (quasiIsomorphisms' _).Q
      ((restrictScalarsHomotopyFunctorIso ((liftedPowSheafAlgebra f).sectionRestriction
        (liftedPowStageMap t h))).inv.app (𝓜.sectionModule (liftedPowStage t n))) rfl
      ((derivedRestrictionFactorization ((liftedPowSheafAlgebra f).sectionRestriction
        (liftedPowStageMap t h))).inv.app
          ((toHomotopyCategory _).obj (𝓜.sectionModule (liftedPowStage t n))))
    exact (congrArg (fun z => IsIso (((derivedTensorFunctor_adj_derivedRestriction
      ((liftedPowSheafAlgebra f).sectionRestriction (liftedPowStageMap t h))).homEquiv _ _).symm
      ((quasiIsomorphisms' _).Q.map ((toHomotopyCategory _).map
        (𝓜.sectionModuleRestriction (liftedPowStageMap t h))) ≫ z))) e).mp hQC
  exact isIso_derivedTranspose_of_square (ULift.{u} ℤ) (powShiftTransition f ht h)
    ((liftedPowSheafAlgebra f).sectionRestriction (liftedPowStageMap t h))
    (liftedPowSectionAlgebraHom f ht m) (liftedPowSectionAlgebraHom f ht n)
    (fun x => sectionRestriction_liftedPowSectionAlgebraHom f ht h x)
    (𝓜.sectionModuleRestriction (liftedPowStageMap t h)) (liftedPowSectionTrans f ht 𝓜 h)
    (fun _ => rfl) (bijective_cohomologyMap_liftedPowSectionAlgebraHom f ht m)
    (bijective_cohomologyMap_liftedPowSectionAlgebraHom f ht n) hm

variable (f ht) in
/-- The tower `n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t` of [Stacks, Tag 0GZJ] attached to a right differential
graded `ℬ`-module `𝓜`. -/
abbrev liftedPowSectionTower
    (𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f)) :
    ℕᵒᵖ ⥤ derivedCategory' (degreeZero R R) :=
  (liftedPowSectionBimoduleSystem f ht 𝓜).toBimoduleSystem.tower (powRestrictedModuleSystem f ht)

/-- If `𝓜` satisfies the quasi-coherence condition, the transition maps into the zeroth term of
the tower `n ↦ M_n ⊗^𝐋_{K_{t+n}} K_t` are isomorphisms: the tower is constant with value
`M_0 ⊗^𝐋_{K_t} K_t`. -/
theorem isIso_liftedPowSectionTower_map_zero
    {𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f)}
    (h𝓜 : SheafOfModules.DifferentialGradedModule.Chaotic.IsQCModule 𝓜) (n : ℕ) :
    IsIso ((liftedPowSectionTower f ht 𝓜).map (homOfLE (Nat.zero_le n)).op) := by
  rcases n with _ | n
  · simp only [homOfLE_refl, op_id]
    infer_instance
  · have h0 : 0 < n + 1 := Nat.zero_lt_succ n
    show IsIso (InverseSequence.tr (liftedPowSectionTower f ht 𝓜) h0.le)
    rw [BimoduleSystem.tr_tower _ _ h0]
    exact isIso_flipTowerMap_of_isIso_derivedTranspose (powShiftTransition f ht h0.le)
      (powTransition f ht (Nat.le_add_right t (n + 1)) :
        (powAlgebra f (t + (n + 1))).Hom (powAlgebra f (t + 0)))
      (powTransition f ht (Nat.le_add_right t 0) :
        (powAlgebra f (t + 0)).Hom (powAlgebra f (t + 0)))
      (fun _ => rfl) (fun c => AlgHom.congr_fun (powTransition_self_toAlgebraHom f ht) c)
      (liftedPowSectionTrans f ht 𝓜 h0.le)
      (flipSemilinear (powShiftTransition f ht h0.le) (liftedPowSectionTrans f ht 𝓜 h0.le))
      (fun _ => rfl) (powRestrictedSystemTrans f ht h0.le) (fun _ => rfl) _ rfl
      (isIso_derivedTranspose_liftedPowSectionTrans h𝓜 h0.le)

end Koszul

end
