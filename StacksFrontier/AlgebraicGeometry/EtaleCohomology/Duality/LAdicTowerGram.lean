module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicTowerLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicGramMatrix

/-!
# A Gram matrix from compatible pairings on the levels of a tower

Let `H : ℕᵒᵖ ⥤ ModuleCat ℤ_ℓ` be a tower of finite modules looking free
(`Stacks.EtaleCohomology.TowerLimit`), `M = lim H(n)`, and `φ` an endomorphism of `M` lying over
maps `ψₙ` of the levels. If every level `H(n)` carries a left nondegenerate pairing with values in
`ℤ/ℓⁿ⁺¹` with `e(ψₙ a, ψₙ b) = c e(a, b)`, then for every basis of `V = M ⊗ ℚ_ℓ` the matrix `A` of
`φ ⊗ ℚ_ℓ` satisfies `Aᵀ J A = c J` for a matrix `J` with unit determinant
(`Stacks.EtaleCohomology.TowerLimit.exists_isUnit_det_transpose_mul_mul_eq_smul`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Matrix

universe v

namespace Stacks.EtaleCohomology.TowerLimit

variable {p : ℕ} [Fact p.Prime] {F : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[p]} [HasLimit F]
  (hkill : ∀ n (x : F.obj (op n)), (p : ℤ_[p]) ^ (n + 1) • x = 0)
  (hsurj : ∀ n, Function.Surjective (tr F (Nat.le_succ n)))
  (hker : ∀ n (x : F.obj (op (n + 1))), tr F (Nat.le_succ n) x = 0 →
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y)
  (htors : ∀ n k (x : F.obj (op (n + k + 1))), (p : ℤ_[p]) ^ (k + 1) • x = 0 →
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y)
  (hfin : ∀ n, Finite (F.obj (op n)))

include hkill hsurj hker htors hfin in
/-- **The Gram matrix of a tower of equivariant pairings.** For a tower of finite `ℤ_ℓ`-modules
looking free, an endomorphism `φ` of the limit lying over maps `ψₙ` of the levels, and left
nondegenerate pairings `eₙ` on the levels with values in `ℤ/ℓⁿ⁺¹` and
`eₙ(ψₙ a, ψₙ b) = c eₙ(a, b)`, every basis of `lim H(n) ⊗ ℚ_ℓ` gives a matrix `J` with unit
determinant and `Aᵀ J A = c J`, `A` the matrix of `φ ⊗ ℚ_ℓ`. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_smul (φ : limit F ⟶ limit F)
    (ψ : ∀ n, F.obj (op n) → F.obj (op n))
    (hφ : ∀ n x, (limit.π F (op n)).hom (φ.hom x) = ψ n ((limit.π F (op n)).hom x)) (c : ℕ)
    (hpair : ∀ n, ∃ e : F.obj (op n) →+ F.obj (op n) →+ ZMod (p ^ (n + 1)),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧ ∀ a b, e (ψ n a) (ψ n b) = (c : ZMod (p ^ (n + 1))) * e a b)
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (bV : Module.Basis ι' ℚ_[p]
      ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj (limit F))) :
    ∃ J : Matrix ι' ι' ℚ_[p], IsUnit J.det ∧
      (LinearMap.toMatrix bV bV
          ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom)ᵀ *
          J * LinearMap.toMatrix bV bV
            ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map φ).hom =
        (c : ℚ_[p]) • J := by
  have := finite hkill hsurj hker htors hfin
  have := free hkill hsurj hker htors hfin
  refine exists_isUnit_det_transpose_mul_mul_eq_smul_extendScalars
    (Module.Free.chooseBasis ℤ_[p] ↑(limit F)) φ c (fun n => ?_) bV
  rcases n with _ | m
  · exact ⟨0, fun a _ => ⟨a, by rw [pow_zero, one_smul]⟩, fun a b => by
      simp only [AddMonoidHom.zero_apply, mul_zero]⟩
  obtain ⟨e, he0, he⟩ := hpair m
  let π := (limit.π F (op m)).hom.toAddMonoidHom
  refine ⟨(e.comp π).compl₂ π, fun a ha => ?_, fun a b => ?_⟩
  · have h0 : (limit.π F (op m)).hom a = 0 := by
      refine he0 _ fun b => ?_
      obtain ⟨b', rfl⟩ := surjective_π hsurj hfin m b
      exact ha b'
    exact exists_eq_smul_of_π_eq_zero hkill hsurj hker htors m a h0
  · change e ((limit.π F (op m)).hom (φ.hom a)) ((limit.π F (op m)).hom (φ.hom b)) =
      _ * e ((limit.π F (op m)).hom a) ((limit.π F (op m)).hom b)
    rw [hφ, hφ, he]

end Stacks.EtaleCohomology.TowerLimit

end
