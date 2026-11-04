module

public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.LocalModel
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraChartComparison

/-!
# The coordinates of the local model of a vector bundle

Over an affine étale chart `V` of an algebraic space `W` on which `ℰ` is free, the identification
`E ×_W V ≅ 𝐀^n_V` of a ring isomorphism `ψ : Γ(V, 𝒪)[T_i] ≅ Γ(V, Sym(ℰ))` pulls the `i`-th
coordinate back to `ψ(T_i)`; for the identification of a trivialization, `ψ(T_i)` is the
degree-one section of `Sym(ℰ)` given by the `i`-th basis section of `ℰ(V)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  (V : SmallEtale B S hS W.1) [IsAffine (chartScheme V)]

/-- **The coordinates of `E ×_W V ≅ 𝐀^n_V`**: the `i`-th coordinate pulls back to `ψ(T_i)`. -/
theorem vectorBundleChartIsoOfRingEquiv_hom_appTop_coord {n : Type u}
    (ψ : MvPolynomial n Γ(chartScheme V, ⊤) ≃+*
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) (i : n) :
    (vectorBundleChartIsoOfRingEquiv B S hS W F V ψ).hom.appTop
        (AffineSpace.coord (chartScheme V) i) =
      (Scheme.ΓSpecIso ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V))).inv
        (ψ (MvPolynomial.X i)) := by
  simp only [vectorBundleChartIsoOfRingEquiv, Iso.trans_hom, Iso.symm_hom, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [AffineSpace.isoOfIsAffine_inv_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

variable {ι : Type u} [DecidableEq ι] [Finite ι]
  (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)

omit [SheafOfModules.IsFiniteLocallyFree F] in
/-- **The variables of the local model**: `T_i` is the degree-one section of `Sym(ℰ)` given by
the `i`-th basis section of `ℰ(V)`. -/
theorem polynomialChartRingEquiv_X (i : ι) :
    polynomialChartRingEquiv B S hS W F V e (MvPolynomial.X i) =
      (symmetricAlgebra B S hS W F).ungradedIncl 1
        ((symmetricAlgebraGen B S hS W F).val.app (op V)
          (SymAlgSections.sectionsBasis B S hS W F V e i)) :=
  (congrArg (SymAlgSections.symSectionsRingEquiv B S hS W F V e ‹_›)
    (SymmetricAlgebra.equivMvPolynomial_symm_X _ i)).trans
    (SymAlgSections.symSectionsRingHom_ι B S hS W F V _)

end AlgebraicGeometry.Space

end
