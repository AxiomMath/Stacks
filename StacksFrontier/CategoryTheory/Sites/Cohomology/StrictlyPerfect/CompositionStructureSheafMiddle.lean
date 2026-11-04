module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalUnitality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect

/-!
# The composition morphism at intermediate object the structure sheaf

Let `X` be a ringed site, write `O[0]` for the structure sheaf placed in degree zero, and let
`E` and `I` be complexes of `O`-modules. The composition morphism of Stacks 0A91 at intermediate
object `O[0]`,

`Tot(SheafHom(O[0], I) ⊗_O SheafHom(E, O[0])) ⟶ SheafHom(E, I)`,

is, up to two isomorphisms, the interchange morphism of Stacks 0BYR

`Tot(I ⊗_O SheafHom(E, O[0])) ⟶ SheafHom(E, Tot(I ⊗_O O[0]))`.

Both the left tensor factor and the target of the composition morphism are internal Homs out of
`O[0]`; replacing each by the complex it is evaluation-at-`1`-isomorphic to turns one morphism
into the other. The identification on the source is `structureSheafHomEvaluation`
(`AlgebraicGeometry.RingedSite.structureSheafHomIso`), the one on the target is
`SheafHom(E, -)` applied to `diagonalTensorUnit`, and what makes the square commute is that the
diagonal of Stacks 0A93 at the structure sheaf *is* `diagonalTensorUnit` read back through
evaluation at `1` (`structureSheafHomEvaluation_comp_diagonalMap`).

The consequence is the one the dual-tensor map of Stacks 08JD needs: the composition morphism at
intermediate object the structure sheaf is a **quasi-isomorphism at a strictly perfect source**,
because the interchange morphism is
(`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`). Nothing
is assumed of `I`.

## Main results

* `AlgebraicGeometry.RingedSite.structureSheafHomEvaluation_comp_diagonalMap`: evaluation at the
  unit section followed by the diagonal of Stacks 0A93 at the structure sheaf is
  `SheafHom(O[0], -)` applied to `diagonalTensorUnit`.
* `AlgebraicGeometry.RingedSite.compositionMap_structureSheafMiddle_comp_homMap`: **the square**
  identifying the composition morphism at intermediate object `O[0]` with the interchange
  morphism.
* `RingedSite.compositionMap_structureSheafMiddle_quasiIso_of_isFiniteFreeSummand`: **the
  strictly perfect case.** For `E` with only finitely many nonzero terms, each a direct summand of
  a finite free `O`-module, and arbitrary `I`, the composition morphism
  `Tot(SheafHom(O[0], I) ⊗_O SheafHom(E, O[0])) ⟶ SheafHom(E, I)` is a quasi-isomorphism.

## Implementation notes

The square is stated with the two identifications on opposite sides — the source one
precomposed with the interchange morphism, the target one postcomposed with the composition
morphism — rather than as a conjugation, because that is the form in which the two cancellation
lemmas `quasiIso_of_comp_right` and `quasiIso_of_comp_left` consume it, and both flanking
morphisms are invertible so the conjugated form follows.

No Koszul sign enters: the composition morphism of Stacks 0A91 carries none on homogeneous local
pure tensors, and `DiagonalUnitality` records that the same is true of the diagonal at the
structure sheaf.

The invertibility of `homMap X (𝟙 E) (diagonalTensorUnit X)` is established inline rather than
through a named lemma: the named form is `AlgebraicGeometry.RingedSite.isIso_homMap` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationLocality`, which this file does
not import.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})
  (E I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Evaluation at the unit section followed by the diagonal at the structure sheaf is the
internal Hom of `diagonalTensorUnit`.** Both are morphisms
`SheafHom(O[0], I) ⟶ SheafHom(O[0], Tot(I ⊗_O O[0]))`, and they agree because
`AlgebraicGeometry.RingedSite.diagonalTensorUnit` is by definition the diagonal of Stacks 0A93
at the structure sheaf followed by evaluation at the unit section: postcomposing both sides with
that evaluation turns the right-hand side into the left by naturality of evaluation, and
evaluation at the unit section is an isomorphism, hence a monomorphism. -/
theorem structureSheafHomEvaluation_comp_diagonalMap :
    structureSheafHomEvaluation X I ≫ diagonalMap X I (structureSheafComplex X) =
      homMap X (𝟙 (structureSheafComplex X)) (diagonalTensorUnit X (A := I)) := by
  refine (cancel_mono (structureSheafHomEvaluation X
    (tensorTotal X I (structureSheafComplex X)))).1 ?_
  rw [Category.assoc, structureSheafHomEvaluation_naturality]
  rfl

/-- **The composition morphism of Stacks 0A91 at intermediate object the structure sheaf is the
interchange morphism of Stacks 0BYR.** Reading the left tensor factor `SheafHom(O[0], I)` of the
composition morphism as `I` by evaluation at the unit section and following with the interchange
morphism is the same as applying the composition morphism and then reading its target
`SheafHom(E, I)` as `SheafHom(E, Tot(I ⊗_O O[0]))`.

This is the covariant naturality of the composition morphism in its target applied to
`diagonalTensorUnit`, together with the unfolding of the interchange morphism as
`tensorTotalMap (diagonalMap) (𝟙) ≫ compositionMap` and the identification
`structureSheafHomEvaluation_comp_diagonalMap` of its left tensor factor. -/
theorem compositionMap_structureSheafMiddle_comp_homMap :
    tensorTotalMap X (structureSheafHomEvaluation X I)
          (𝟙 (sheafHomComplex X E (structureSheafComplex X)).obj) ≫
        tensorHomInterchange X I (structureSheafComplex X) E =
      compositionMap X E (structureSheafComplex X) I ≫
        homMap X (𝟙 E) (diagonalTensorUnit X (A := I)) := by
  rw [← compositionMap_natural_target X E (structureSheafComplex X)
      (diagonalTensorUnit X (A := I)),
    tensorHomInterchange, ← Category.assoc, tensorTotalMap_comp, Category.comp_id,
    structureSheafHomEvaluation_comp_diagonalMap]

/-- **The strictly perfect case for the composition morphism of Stacks 0A91 at intermediate
object the structure sheaf.** If `E` has only finitely many nonzero terms and each of them is a
direct summand of a finite free `O`-module, then

`Tot(SheafHom(O[0], I) ⊗_O SheafHom(E, O[0])) ⟶ SheafHom(E, I)`

is a quasi-isomorphism, for an arbitrary complex `I`.

This is the base case of the third assertion of Stacks 08DQ, the one the source calls clear: the
morphism is, by `compositionMap_structureSheafMiddle_comp_homMap`, the interchange morphism of
Stacks 0BYR flanked by two isomorphisms, and the interchange morphism at a strictly perfect
source of the internal Hom is a quasi-isomorphism by
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`. -/
theorem compositionMap_structureSheafMiddle_quasiIso_of_isFiniteFreeSummand
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (compositionMap X E (structureSheafComplex X) I) := by
  have hdu : IsIso (homMap X (𝟙 E) (diagonalTensorUnit X (A := I))) :=
    ⟨homMap X (𝟙 E) (inv (diagonalTensorUnit X (A := I))), by
      rw [homMap_comp, Category.comp_id, IsIso.hom_inv_id, homMap_id], by
      rw [homMap_comp, Category.comp_id, IsIso.inv_hom_id, homMap_id]⟩
  have hsrc : IsIso (tensorTotalMap X (structureSheafHomEvaluation X I)
      (𝟙 (sheafHomComplex X E (structureSheafComplex X)).obj)) :=
    isIso_tensorTotalMap X _ _
  have hint : QuasiIso (tensorHomInterchange X I (structureSheafComplex X) E) :=
    tensorHomInterchange_quasiIso_of_isFiniteFreeSummand X I (structureSheafComplex X) E hbdd
      hterm
  have hcomp : QuasiIso (compositionMap X E (structureSheafComplex X) I ≫
      homMap X (𝟙 E) (diagonalTensorUnit X (A := I))) := by
    rw [← compositionMap_structureSheafMiddle_comp_homMap]
    infer_instance
  exact quasiIso_of_comp_right _ (homMap X (𝟙 E) (diagonalTensorUnit X (A := I)))

end AlgebraicGeometry.RingedSite

end
