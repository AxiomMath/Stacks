module

public import StacksFrontier.Algebra.QuadraticMap.CubeRelation
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullbackFormula
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion

/-!
# Intersection numbers of pullbacks along integral combinations of morphisms

Let `A` be an abelian variety over a field `k`, `L` an invertible `𝒪_A`-module, `B` a proper
scheme over `k` and `a_1, …, a_r : B ⟶ A` morphisms over `k`. The morphisms `B ⟶ A` form a
commutative group, and for integers `c_1, …, c_r` write `∑ c_j a_j` for the corresponding
integral combination (`∏ a_j ^ c_j` in the multiplicative notation of group objects). This file
proves that for every closed subscheme `Z ⊆ B` of dimension at most `d` the intersection number

`((∑ c_j a_j)^* L)^d · Z)`

is a polynomial function of `c` of total degree at most `2 d`.

## Main results

* `Stacks.Groupoids.exists_mvPolynomial_picardIntersection_pullbackPicardClass_prod_zpow` — the
  intersection numbers are a polynomial of total degree at most `2 d` in `c`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- **The intersection numbers of the pullbacks of `L` along `∑ c_j a_j` are a polynomial of
total degree at most `2 d` in `c`.** For an abelian variety `A` over `k`, an invertible module `L`
on `A`, morphisms `a : σ → (B ⟶ A)` over `k` from a proper `k`-scheme `B`, and a closed
subscheme `i : Z ⟶ B.left` of dimension at most `d`, there is `P ∈ ℚ[c_j : j ∈ σ]` of total degree
at most `2 d` with `((∏ a_j ^ c_j)^* L)^d · Z) = P(c)` for all `c : σ → ℤ`. -/
theorem exists_mvPolynomial_picardIntersection_pullbackPicardClass_prod_zpow
    (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)
    {B : Over (Spec (.of k))} [IsProper B.hom] {Z : Scheme.{u}} (i : Z ⟶ B.left)
    [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))
    {σ : Type*} [LinearOrder σ] [Fintype σ] (a : σ → (B ⟶ A)) :
    ∃ P : MvPolynomial σ ℚ, P.totalDegree ≤ 2 * d ∧ ∀ c : σ → ℤ,
      ((picardIntersection k B.hom i d hd (fun _ =>
          Stacks.SheafOfModules.pullbackPicardClass (∏ j, a j ^ c j).left L hL) : ℤ) : ℚ) =
        MvPolynomial.eval (fun j => (c j : ℚ)) P := by
  let Q : Additive (B ⟶ A) →
      Stacks.SheafOfModules.PicardGroup B.left.presheaf B.left.ringCatIsSheaf :=
    fun x => Stacks.SheafOfModules.pullbackPicardClass (Additive.toMul x).left L hL
  have hQ : ∀ x y z : Additive (B ⟶ A),
      Q (x + y + z) + Q x + Q y + Q z = Q (x + y) + Q (x + z) + Q (y + z) := fun x y z =>
    pullbackPicardClass_cubeRelation A (hasTheoremOfTheCube k A) L hL
      (Additive.toMul x) (Additive.toMul y) (Additive.toMul z)
  obtain ⟨P, hP, hPc⟩ := Stacks.QuadraticMap.exists_mvPolynomial_multilinear_eq hQ d
    (picardIntersection k B.hom i d hd) (fun j => Additive.ofMul (a j))
  refine ⟨P, hP, fun c => ?_⟩
  rw [← hPc c]
  congr 3

end Stacks.Groupoids
