module

public import StacksFrontier.Algebra.Homology.InternalHomComplexSingleCollapse
public import StacksFrontier.CategoryTheory.Monoidal.MateAsInternalHomPre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom complex into the unit is a signed mate dual

Let `A` be a braided monoidal closed preadditive category with the coproducts and products that
make `CochainComplex A ℤ` monoidal and monoidal closed, and let `K` be a cochain complex in `A`
each of whose terms carries a left dual.  Then the complex `Hom•(K, 𝟙)` — the internal hom into
the unit, which is the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` of [Stacks, Tag 0FP9] — satisfies
`CochainComplex.IsSignedMateDual` for the degreewise pairings obtained by transporting the given
duals onto its terms.

This is the obligation `CochainComplex.exactPairingOfSignedMateDual` was left binding: that file
proves a complex whose differential is the signed transpose is a left dual *in the monoidal
category of complexes*, with the signed-transpose property a hypothesis; here that hypothesis is
discharged for the tag's own dual complex, so nothing about the differential is assumed any
more.

## Main results

* `CochainComplex.internalHomComplex_single_d`: the differential of `Hom•(K, L)` for `L`
  concentrated in degree zero, read through the collapse isomorphisms
  `CochainComplex.internalHomXSingleIso`, is `(-1)^n` times `MonoidalClosed.pre (d_K)`.
* `CochainComplex.isSignedMateDual_internalHomComplex`: **`Hom•(K, 𝟙)` is a signed mate dual of
  `K`.**  Feeding this to `CochainComplex.exactPairingOfSignedMateDual` exhibits it as a left
  dual of `K` in `CochainComplex A ℤ`.

## Implementation notes

**Two steps, and only the second is about duality.**  The differential of `Hom•(K, L)` is
`f ↦ d_L ∘ f ± f ∘ d_K` (`CochainComplex.internalHomComplex_d_π`).  Against a `L` concentrated
in degree zero the `d_L` half vanishes and the `d_K` half is `MonoidalClosed.pre (d_K)` up to the
reindexing isomorphism of the surviving factor; that is `internalHomComplex_single_d`, and it
mentions no pairing.  Identifying `pre` with the mate of the pairings is
`CategoryTheory.ExactPairing.mate_eq_pre_app`, and it mentions no complexes.  The sign survives
both steps unchanged: `(-1)^{-n} = (-1)^n`.

**A retyped collapse isomorphism.**  `CochainComplex.internalHomComplexSingleIso` is
`CochainComplex.internalHomXSingleIso` with its source written as a degree of the complex rather
than as the bare product.  The two are definitionally equal but not interchangeable for `rw`,
which works at the `implicit` transparency level and will not unfold `internalHomComplex`; this
is the same reason `CochainComplex.internalHomComplexπ` exists.  It is also the spelling the
sheaf-theoretic consumer `Stacks.SheafOfModules.Strict.ihomUnitXIso` already uses.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category Limits MonoidalCategory MonoidalClosed GradedObject

universe v u

namespace CochainComplex

noncomputable section

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [MonoidalClosed A] [Preadditive A]
  [MonoidalPreadditive A] [HasProductsOfShape ℤ A] [HasZeroObject A]

/-- The collapse isomorphism of `CochainComplex.internalHomXSingleIso`, with its source retyped
as a degree of the complex `Hom•(K, L)`. -/
def internalHomComplexSingleIso (K : CochainComplex A ℤ) (X : A) (n : ℤ) :
    (internalHomComplex K ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)).X (-n) ≅
      (ihom (K.X n)).obj X :=
  internalHomXSingleIso K X n

/-- The collapse isomorphism, unfolded. -/
lemma internalHomComplexSingleIso_hom (K : CochainComplex A ℤ) (X : A) (n : ℤ) :
    (internalHomComplexSingleIso K X n).hom =
      internalHomComplexπ K ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X) (-n) n ≫
        (ihom (K.X n)).map
          (((((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).XIsoOfEq
              (show n + -n = 0 by omega)).trans
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X)).hom) :=
  rfl

/-- **The differential of the internal Hom complex into a complex concentrated in degree zero.**
Read through the collapse isomorphisms it is the `negOnePow`-signed precomposition with the
differential of `K`. -/
@[sga "4 XVII 1.1.10" "(ii)"]
lemma internalHomComplex_single_d (K : CochainComplex A ℤ) (X : A) (n : ℤ) :
    (internalHomComplex K ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)).d
        (-(n + 1)) (-n) =
      (n.negOnePow : ℤˣ) • ((internalHomComplexSingleIso K X (n + 1)).hom ≫
        (pre (K.d n (n + 1))).app X ≫ (internalHomComplexSingleIso K X n).inv) := by
  refine (cancel_mono (internalHomComplexSingleIso K X n).hom).1 ?_
  rw [Linear.units_smul_comp, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    internalHomComplexSingleIso_hom, internalHomComplexSingleIso_hom,
    internalHomComplex_d_π_assoc K _ (-(n + 1)) (-n) (by omega) n,
    show ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).d (n + -(n + 1)) (n + -n) = 0
      from HomologicalComplex.single_obj_d .., Functor.map_zero, Limits.comp_zero, zero_add,
    Linear.units_smul_comp, Int.negOnePow_neg, Category.assoc, Category.assoc, Category.assoc,
    ((pre (K.d n (n + 1))).naturality _).symm,
    ← Functor.map_comp_assoc]
  congr 3
  simp

variable [BraidedCategory A]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

omit [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- **The internal Hom complex into the unit is a signed mate dual of `K`.**  Let every term of
`K` carry a left dual `D n`.  Transport those duals onto the terms of `Hom•(K, 𝟙)` — along
`CategoryTheory.rightDualIsoIhomUnit` and then along the collapse isomorphism — and the
differential of `Hom•(K, 𝟙)` is the `negOnePow`-signed mate of the differential of `K` for the
transported pairings.

So `CochainComplex.exactPairingOfSignedMateDual` applies to this complex with no hypothesis on
its differential: `Hom•(K, 𝟙)` is a left dual of `K` in the monoidal category of complexes as
soon as `K` is bounded.  The sign is not an artefact of the transport — it is the Koszul sign of
the Hom-complex differential, and `Stacks.SignedMateDual.two_torsion_of_signed_and_unsigned`
shows it cannot be dropped. -/
theorem isSignedMateDual_internalHomComplex (K : CochainComplex A ℤ) (D : ℤ → A)
    (pd : ∀ n : ℤ, ExactPairing (K.X n) (D n)) :
    IsSignedMateDual K
      (internalHomComplex K ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (𝟙_ A)))
      (fun n => @exactPairingCongrRight A _ _ (K.X n) _ _
        (@exactPairingCongrRight A _ _ (K.X n) _ _ (pd n)
          (rightDualIsoIhomUnit (K.X n) (D n)).symm)
        (internalHomComplexSingleIso K (𝟙_ A) n)) := by
  intro n
  rw [ExactPairing.mate_exactPairingCongrRight, ExactPairing.mate_eq_pre_app _ _
    (@ExactPairing.evaluation_exactPairingRightDualIhomUnit A _ _ _ _ (K.X n) (D n) (pd n))
    (@ExactPairing.evaluation_exactPairingRightDualIhomUnit A _ _ _ _ (K.X (n + 1)) (D (n + 1))
      (pd (n + 1)))]
  exact internalHomComplex_single_d K (𝟙_ A) n

end

end CochainComplex

end
