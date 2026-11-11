module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowRetraction

/-!
# The row zero and the column zero of the double complex of a cosimplicial pair, in `D(Ab)`

Let `W` be a cosimplicial module over the completed cosimplicial rings `D̂(*)` with a completed
connection in each cosimplicial degree (`Crystalline.CosimplicialCompletedPair`), and let
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` be its double complex.  The proof of
[Stacks, Proposition 60.21.3, Tag 07LG] identifies the row `K^{*,0} = M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}`
with the column `K^{0,*} = M(•)` through the total complex, by two quasi-isomorphisms:

* the columns `a > 0` are acyclic ([Stacks, Lemma 60.19.1, Tag 07LA]), so the projection of the
  total complex onto the column `0` is a quasi-isomorphism;
* every coprojection `K^{*,0} ⟶ K^{*,b}` is a quasi-isomorphism
  ([Stacks, Lemma 60.21.2, Tag 07LD]), so the comparison of `K` with the constant double complex
  on its row zero is a quasi-isomorphism on every row, hence on the total complexes, and the
  row zero of the constant double complex is quasi-isomorphic to its total complex.

`Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroHomologyIsoOfQuasiIso` reads this zigzag
on cohomology, degree by degree.  This module reads it in the derived category: the zigzag is a
string of morphisms of complexes, each a quasi-isomorphism or an isomorphism, so it defines an
isomorphism of the two complexes in `D`.  It is stated after an arbitrary additive functor `F`
out of abelian groups preserving homology, applied degreewise, so that it can be read in the
derived category of abelian groups of a larger universe (`F` a universe lift).

## Main definitions

* `Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroDerivedIso` — **`M(0) ⊗^∧_{D(0)}
  Ω^*_{D(0)} ≅ M(•)` in `D`**, after `F`, both complexes extended by zero from `ℕ` to `ℤ`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

universe u v w uC vC wC

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open StacksDraft.TotalComplexQuasiIso StacksDraft.TotalDegeneration StacksDraft.TotalRowComparison

namespace Crystalline

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (F : AddCommGrpCat.{max v w} ⥤ C) [F.Additive] [F.PreservesHomology]

/-- **The comparison of [Stacks, Proposition 60.21.3, Tag 07LG] in the derived category**: given
the acyclicity of the columns `a > 0` of the double complex `K` and the quasi-isomorphy of every
coprojection `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`, the row zero
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` and the Moore complex of the column zero `M(•)` are isomorphic in
`D(C)` after `F`, both extended by zero to `ℤ`.

The isomorphism is the zigzag of the proof:
`K^{*,0} ⟶ Const(K^{*,0})^{*,0} ⟶ Tot(Const(K^{*,0})) ≅ Tot(Const(K^{*,0})^t) ⟵ Tot(K^t) ≅ Tot(K)
⟶ Tot(K^{0,*}[0]) ≅ K^{0,*}`, where `K^t` is the flip, the first arrow is the codiagonal
comparison on the row zero, the second the inclusion of the row zero of a double complex whose
columns resolve their degree-zero terms, the arrow pointing backwards the comparison on total
complexes (a quasi-isomorphism because it is one on every row), and the last arrow the projection
onto the column `0` (a quasi-isomorphism because the other columns are acyclic). -/
def rowZeroColumnZeroDerivedIso
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hq : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b)) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((W.degreeDeRhamComplex 0).extend ComplexShape.embeddingUpNat)) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj (W.doubleComplex.X 0)).extend
          ComplexShape.embeddingUpNat)) :=
  have hrow := W.quasiIso_flipMap_rowZeroComparison_of_quasiIso hq
  haveI : QuasiIso ((flipMap (cosimplicialDoubleComplexFunctor.map W.rowZeroComparison)).f 0) :=
    hrow 0
  haveI : QuasiIso (rowZeroTotalMap (cosimplicialDoubleComplexFunctor.obj
      (constantCosimplicialCochainComplex.obj (W.degreeDeRhamComplex 0)))
      (diagonalFinite_constCosimplicialDoubleComplex (W.degreeDeRhamComplex 0))
      (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg _ p hq)
      (fun a _q hq => exactAt_constCosimplicialDoubleComplex_X (W.degreeDeRhamComplex 0) a hq)
      (constCosimplicialDoubleComplex_X_d_zero_one (W.degreeDeRhamComplex 0))) :=
    quasiIso_rowZeroTotalMap _ _ _ _ _
  haveI : QuasiIso (HomologicalComplex₂.total.map
      (flipMap (cosimplicialDoubleComplexFunctor.map W.rowZeroComparison)) (ComplexShape.up ℤ)) :=
    quasiIso_total_map_flip _
      (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg W.doubleComplex p hq)
      (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg W.doubleComplex hp)
      (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg _ p hq)
      (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg _ hp) hrow
  haveI := hasTotal_singleColumn
    ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).X 0) 0
  haveI : QuasiIso (HomologicalComplex₂.total.map
      (bottomProj (cosimplicialDoubleComplexFunctor.obj W.doubleComplex) 0
        (isZero_X_neg_one _ fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg _ hp))
      (ComplexShape.up ℤ)) :=
    quasiIso_total_bottomProj_zero _
      (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg W.doubleComplex p hq)
      (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg W.doubleComplex hp)
      (acyclic_cosimplicialDoubleComplex_X_of_ne_zero W.doubleComplex hcol)
  haveI := isIso_totalSingleColumnUnit
    ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).X 0) 0
  DerivedCategory.Q.mapIso
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (W.flipRowDeRhamIso 0).symm) ≪≫
    asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((flipMap (cosimplicialDoubleComplexFunctor.map W.rowZeroComparison)).f 0))) ≪≫
    asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (rowZeroTotalMap (cosimplicialDoubleComplexFunctor.obj
        (constantCosimplicialCochainComplex.obj (W.degreeDeRhamComplex 0)))
        (diagonalFinite_constCosimplicialDoubleComplex (W.degreeDeRhamComplex 0))
        (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg _ p hq)
        (fun a _q hq => exactAt_constCosimplicialDoubleComplex_X (W.degreeDeRhamComplex 0) a hq)
        (constCosimplicialDoubleComplex_X_d_zero_one (W.degreeDeRhamComplex 0))))) ≪≫
    DerivedCategory.Q.mapIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((cosimplicialDoubleComplexFunctor.obj
        (constantCosimplicialCochainComplex.obj (W.degreeDeRhamComplex 0))).totalFlipIso
          (ComplexShape.up ℤ)).symm) ≪≫
    (asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex₂.total.map
        (flipMap (cosimplicialDoubleComplexFunctor.map W.rowZeroComparison))
        (ComplexShape.up ℤ))))).symm ≪≫
    DerivedCategory.Q.mapIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).totalFlipIso
        (ComplexShape.up ℤ))) ≪≫
    asIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex₂.total.map
        (bottomProj (cosimplicialDoubleComplexFunctor.obj W.doubleComplex) 0
          (isZero_X_neg_one _ fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg _ hp))
        (ComplexShape.up ℤ)))) ≪≫
    DerivedCategory.Q.mapIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((asIso (totalSingleColumnUnit
        ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).X 0) 0)).symm ≪≫
      (shiftFunctorZero (CochainComplex AddCommGrpCat.{max v w} ℤ) ℤ).app
        ((cosimplicialDoubleComplexFunctor.obj W.doubleComplex).X 0) ≪≫
      cosimplicialDoubleComplexColumnIso W.doubleComplex 0))

end CosimplicialCompletedPair

end Crystalline

end
