module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.OverField

/-!
# Affine space over a field as an open of projective space

The open immersion `Spec k[X_0, …, X_{n-1}] ⟶ ℙ^n_k` over `k` onto the standard chart `D₊(T₀)`,
in the spelling `Spec (MvPolynomial (Fin n) k)` of affine space used by Noether normalization
(`AlgebraicGeometry.exists_dense_isOpenImmersion_fiber_le_one`). It is the compactification of
`𝔸^n_k` used in the fibration step of the trace formula in any dimension
([Stacks, Tag 03UI] (1)).

## Main definitions

* `AlgebraicGeometry.mvPolynomialChart`: the open immersion `𝔸^n_k ⟶ ℙ^n_k` onto `D₊(T₀)`.

## Main results

* `AlgebraicGeometry.mvPolynomialChart_over`: `mvPolynomialChart` is a morphism over `Spec k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (n : ℕ)

/-- **`𝔸^n_k ⊆ ℙ^n_k`**: the open immersion `Spec k[X_0, …, X_{n-1}] ⟶ ℙ^n_k` onto the standard
chart `D₊(T₀)`. -/
def mvPolynomialChart : Spec (.of (MvPolynomial (Fin n) k)) ⟶ projectiveSpaceOverRing n (.of k) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv k Equiv.ulift).toRingEquiv.toRingHom) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).inv ≫
    projectiveSpaceOver.affineChart n 0 (Equiv.ulift.trans (finSuccAboveEquiv 0)) (Spec (.of k))

/-- The chart `𝔸^n_k ⟶ ℙ^n_k` is an open immersion. -/
instance : IsOpenImmersion (mvPolynomialChart k n) := by
  unfold mvPolynomialChart
  haveI : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv k (Equiv.ulift.{u, 0} (α := Fin n))).toRingEquiv.toRingHom) :=
    (MvPolynomial.renameEquiv k Equiv.ulift).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

/-- `𝔸^n_k ⊆ ℙ^n_k` lies over `k`. -/
theorem mvPolynomialChart_over :
    mvPolynomialChart k n ≫ (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) := by
  unfold mvPolynomialChart
  rw [Category.assoc, Category.assoc, projectiveSpaceOver.affineChart_over,
    AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  congr 1
  ext x
  simp [MvPolynomial.algebraMap_eq]

/-- The structure morphism `ℙ^n_k ⟶ Spec k` is proper. -/
instance : IsProper (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) :=
  isProper_projectiveSpaceOver n _

end AlgebraicGeometry

end
