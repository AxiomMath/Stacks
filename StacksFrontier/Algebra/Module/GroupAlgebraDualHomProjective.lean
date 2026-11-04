module

public import StacksFrontier.Algebra.Module.GroupAlgebraDualHom
public import StacksFrontier.Algebra.Category.ModuleCat.BimoduleHomFunctor
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace

/-!
# `Hom_{A[H]}(M^*, -)` preserves finite projective modules

Let `H` be a finite group, `A = ℤ/n`, and `M` a finite `ℤ/n`-module with an action `ρ` of `H`
commuting with a ring `Λ`, which is finite projective over `Λ`. For every finite projective
`A[H]`-module `P`, the `Λ`-module `Hom_{A[H]}(M^*, P)` is finite projective: `P` is a direct
summand of `A[H]^k`, and `Hom_{A[H]}(M^*, A[H]^k) ≅ M^k`
(`Stacks.GroupAlgebraDual.ofM_bijective`). This is the hypothesis on the change of coefficients
`Hom_{A[H]}(M^*, -)` under which traces of perfect complexes are carried along it, in Step 7 of
the proof of [Stacks, Tag 03UG].

## Main results

* `Stacks.GroupAlgebraDual.preservesFiniteProjective_bimoduleHom`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 7.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidAlgebra CategoryTheory.FilteredDerived

universe u

namespace Stacks.GroupAlgebraDual

variable (n : ℕ) [NeZero n] {H : Type} [Group H] [Fintype H] {Λ : Type} [Ring Λ]
  {M : Type (u + 1)} [AddCommGroup M] [Module Λ M] [Module (ZMod n) M] [Finite M]
  (ρ : H →* Module.End Λ M)

/-- **The change of coefficients `Hom_{A[H]}(M^*, -)`**, from `A[H]`-modules to `Λ`-modules. -/
abbrev dualHomFunctor :
    ModuleCat.{u + 1} (MonoidAlgebra (ZMod n) H) ⥤ ModuleCat.{u + 1} Λ :=
  ModuleCat.BimoduleHom.functor (MonoidAlgebra (ZMod n) H) Λ (Dual n ρ)

/-- The bijection `M ≃ Hom_{A[H]}(M^*, A[H])`. -/
def ofMEquiv : M ≃ (Dual n ρ →ₗ[MonoidAlgebra (ZMod n) H] MonoidAlgebra (ZMod n) H) :=
  Equiv.ofBijective _ ofM_bijective

variable {n ρ}

/-- The inverse of `ofMEquiv` is `Λ`-linear: precomposing `ψ : Hom_{A[H]}(M^*, A[H])` with the
action of `l : Λ` on `M^*` corresponds to multiplying by `l` in `M`. -/
lemma ofMEquiv_symm_comp_smul (l : Λ)
    (ψ : Dual n ρ →ₗ[MonoidAlgebra (ZMod n) H] MonoidAlgebra (ZMod n) H) :
    (ofMEquiv n ρ).symm (ψ ∘ₗ DistribSMul.toLinearMap (MonoidAlgebra (ZMod n) H) (Dual n ρ)
      (MulOpposite.op l)) = l • (ofMEquiv n ρ).symm ψ := by
  apply (ofMEquiv n ρ).injective
  rw [Equiv.apply_symm_apply]
  refine LinearMap.ext fun φ => ?_
  show _ = ofM (l • (ofMEquiv n ρ).symm ψ) φ
  rw [ofM_smul]
  show ψ _ = ofMEquiv n ρ ((ofMEquiv n ρ).symm ψ) _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The inverse of `ofMEquiv` is additive. -/
private lemma ofMEquiv_symm_add (ψ χ :
    Dual n ρ →ₗ[MonoidAlgebra (ZMod n) H] MonoidAlgebra (ZMod n) H) :
    (ofMEquiv n ρ).symm (ψ + χ) = (ofMEquiv n ρ).symm ψ + (ofMEquiv n ρ).symm χ := by
  apply (ofMEquiv n ρ).injective
  refine LinearMap.ext fun φ => ?_
  change _ = ofM _ φ
  rw [ofM_add]
  change _ = ofMEquiv n ρ _ φ + ofMEquiv n ρ _ φ
  simp only [Equiv.apply_symm_apply, LinearMap.add_apply]

variable [Module.Finite Λ M] [Module.Projective Λ M]

variable (n ρ) in
/-- **`Hom_{A[H]}(M^*, -)` preserves finite projective modules**, when `M` is finite projective
over `Λ`. -/
theorem preservesFiniteProjective_bimoduleHom :
    PreservesFiniteProjective.{0, u + 1}
      (ModuleCat.BimoduleHom.functor (MonoidAlgebra (ZMod n) H) Λ (Dual n ρ)) := by
  intro P _ _
  let R := MonoidAlgebra (ZMod n) H
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' R P
  obtain ⟨i, hi⟩ := Module.projective_lifting_property s LinearMap.id hs
  let T := ModuleCat.BimoduleHom.Obj R (Dual n ρ) P
  let toL : T ≃+ (Dual n ρ →ₗ[R] P) := ModuleCat.BimoduleHom.toLinearMap _
  let a : T →ₗ[Λ] (Fin k → M) :=
    { toFun := fun f j => (ofMEquiv n ρ).symm (LinearMap.proj j ∘ₗ i ∘ₗ toL f)
      map_add' := fun f g => funext fun j => by
        show (ofMEquiv n ρ).symm (LinearMap.proj j ∘ₗ i ∘ₗ (toL f + toL g)) = _
        rw [LinearMap.comp_add, LinearMap.comp_add, ofMEquiv_symm_add]
        rfl
      map_smul' := fun l f => funext fun j => by
        show (ofMEquiv n ρ).symm (LinearMap.proj j ∘ₗ i ∘ₗ (toL f ∘ₗ
          DistribSMul.toLinearMap R (Dual n ρ) (MulOpposite.op l))) = _
        rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ofMEquiv_symm_comp_smul]
        rfl }
  let b : (Fin k → M) →ₗ[Λ] T :=
    { toFun := fun v => toL.symm (s ∘ₗ LinearMap.pi fun j => ofMEquiv n ρ (v j))
      map_add' := fun v w => toL.injective (by
        show s ∘ₗ LinearMap.pi (fun j => ofM (v j + w j)) =
          s ∘ₗ LinearMap.pi (fun j => ofM (v j)) + s ∘ₗ LinearMap.pi (fun j => ofM (w j))
        rw [← LinearMap.comp_add]
        congr 1
        refine LinearMap.ext fun φ => funext fun j => ?_
        simp only [LinearMap.pi_apply, LinearMap.add_apply, Pi.add_apply, ofM_add])
      map_smul' := fun l v => toL.injective (by
        refine LinearMap.ext fun φ => ?_
        show s (fun j => ofM (l • v j) φ) = s (fun j => ofM (v j) (MulOpposite.op l • φ))
        simp only [ofM_smul]) }
  have hba : b.comp a = LinearMap.id := by
    refine LinearMap.ext fun f => toL.injective (LinearMap.ext fun φ => ?_)
    show s (fun j => ofMEquiv n ρ ((ofMEquiv n ρ).symm (LinearMap.proj j ∘ₗ i ∘ₗ toL f)) φ) =
      toL f φ
    simp only [Equiv.apply_symm_apply]
    exact LinearMap.congr_fun hi (toL f φ)
  have : Module.Projective Λ (Fin k → M) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := Λ) (M := fun _ : Fin k => M))
  refine ⟨Module.Finite.of_surjective b fun f => ⟨a f, LinearMap.congr_fun hba f⟩,
    Module.Projective.of_split a b hba⟩

end Stacks.GroupAlgebraDual

end
