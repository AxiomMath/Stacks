module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowRetraction
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialTotalRowZero

/-!
# Transporting the quasi-isomorphy of the coprojections along row identifications

Let `K` be a cochain complex of cosimplicial abelian groups and `W` a cosimplicial pair with
completed de Rham complexes `M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`
(`Crystalline.CosimplicialCompletedPair.degreeDeRhamComplex`).  If every row `b` of `K` is
identified with the universe lift of the de Rham complex of the degree `b` of `W`, compatibly with
the coprojections `⦋0⦌ ⟶ ⦋b⦌, 0 ↦ 0` on both sides, then the coprojections of the rows of `K` are
quasi-isomorphisms as soon as those of `W` are (`quasiIso_cosimplicialRowCoprojection_of_rowIso`).

Nothing here constructs such identifications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Crystalline

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}

/-- **The coprojections of the rows of `K` are quasi-isomorphisms** when the rows are identified,
compatibly with the coprojections, with the universe lifts of the completed de Rham complexes of a
cosimplicial pair whose coprojections are quasi-isomorphisms. -/
theorem quasiIso_cosimplicialRowCoprojection_of_rowIso
    (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u + 1}) ℕ)
    (W : CosimplicialCompletedPair.{u, u, u} E p)
    (φ : ∀ b, cosimplicialRowComplex K b ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).obj
        (W.degreeDeRhamComplex b))
    (hφ : ∀ b, cosimplicialRowCoprojection K b ≫ (φ b).hom =
      (φ 0).hom ≫ (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
        (W.rowFromZeroHom b))
    (hW : ∀ b, QuasiIso (W.rowFromZeroHom b)) (b : ℕ) :
    QuasiIso (cosimplicialRowCoprojection K b) := by
  have : QuasiIso ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
      (W.rowFromZeroHom b)) := by
    have := hW b
    infer_instance
  have h : QuasiIso (cosimplicialRowCoprojection K b ≫ (φ b).hom) := by
    rw [hφ b]
    infer_instance
  exact (quasiIso_iff_comp_right _ (φ b).hom).mp h

end Crystalline

end
