module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalReindexSections

/-!
# The interchange morphism at a trivialised single-degree source

Let `X` be a ringed site, let `A`, `I` be complexes of `O`-modules and let `E` be a complex
concentrated in a single degree `k` whose term there is isomorphic to the structure sheaf. This
file proves that the interchange morphism of Stacks 0BYR

`Tot(A ⊗_O SheafHom(E, I)) ⟶ SheafHom(E, Tot(A ⊗_O I))`

is an **isomorphism** — not merely a quasi-isomorphism. This is the base case of the induction
by which Stacks 0ATN reduces the invertibility of the interchange to a strictly perfect source,
and it is the counterpart of `AlgebraicGeometry.RingedSite.homMap_quasiIso_of_unit`, the base
case of the corresponding induction for the induced map of internal Hom complexes.

The proof is a square. Both complexes of the interchange are identified with ones built out of
`I` alone: the source by `AlgebraicGeometry.RingedSite.homUnitReindexIso` inside the tensor
product, the target by the same isomorphism outside it, leaving
`Tot(A ⊗_O reindexBy I k) ⟶ reindexBy (Tot(A ⊗_O I)) k`. That morphism is
`AlgebraicGeometry.RingedSite.tensorTotalReindexIso₂`, and the square says so. Since the two
identifications are isomorphisms, the interchange is one.

The square is checked on the local pure tensors, where both sides evaluate a Hom-section at the
unit section of the source: on the one side the interchange is applied first and its output
evaluated, on the other the factor is evaluated first and the pure tensor formed. That these
agree is exactly `AlgebraicGeometry.RingedSite.tensorHomInterchange_applyHomSection`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorHomInterchange_comp_homUnitReindexIso`: the square.
* `AlgebraicGeometry.RingedSite.isIso_tensorHomInterchange_of_unit` and
  `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_unit`: the interchange is an
  isomorphism, hence a quasi-isomorphism.

## What this file does not contain

**The single-degree finite free case.** The source here is trivialised — its one nonzero term is
isomorphic to `O` itself — whereas the case needed next has that term a power `O^{⊕r}`. The model
file `StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso`
passes from one to the other by induction on `r` along the degreewise split short complex
`O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O` of `AlgebraicGeometry.RingedSite.unitPowerShortComplex`, using its
two-out-of-three lemma for a degreewise split short complex of sources. The corresponding
two-out-of-three lemma for the interchange is not yet available: it needs the degreewise
splitting of the row `Tot(A ⊗_O SheafHom(-, I))`, which, the degree `n` of a total complex being
a coproduct over `p + q = n`, has to be assembled from the summands as
`StacksDraft.TotalComplexQuasiIso.totalBottomSplitting` does for its own case, and is the one
step of this argument with no counterpart in the model file.

## References

* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive

variable (X : RingedSite.{u, u, u})

variable {E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Evaluation at the unit section, in the vocabulary of `applyHomSection`.** The isomorphism
`AlgebraicGeometry.RingedSite.homUnitEvaluation` of a trivialised single-degree source is the
evaluation of a Hom-section at the unit section of that source. The two sides are the same term;
the statement is needed because the identifications of complexes are phrased in the first
vocabulary and the characterisation of the interchange morphism in the second. -/
lemma homUnitEvaluation_val_app (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : ((sheafHomComplex X E F).obj.X n).val.obj (op U)) :
    (homUnitEvaluation X (F := F) k n e).val.app (op U) s =
      applyHomSection X (sheafHomComplex X E F) U n k (k + n) rfl s
        (e.inv.val.app (op U) (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) :=
  rfl

/-- The degreewise components of `AlgebraicGeometry.RingedSite.homUnitReindexIso` are the
evaluations at the unit section, by construction. -/
lemma homUnitReindexIso_hom_f (k n : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (homUnitReindexIso X (F := F) k e hE).hom.f n = homUnitEvaluation X (F := F) k n e :=
  rfl

/-- **The square identifying the interchange morphism at a trivialised single-degree source.**
Transported along the identifications of its source and target with complexes built out of `I`
alone, the interchange morphism is the sign-free reindexing comparison
`AlgebraicGeometry.RingedSite.tensorTotalReindexIso₂`.

Both sides are checked on a local pure tensor of a degree-`t` section `a` of `A` and a degree-`r`
section `φ` of `SheafHom(E, I)`, where both come to the same thing: the pure tensor of `a` with
the value of `φ` at the unit section of `E`. -/
theorem tensorHomInterchange_comp_homUnitReindexIso
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    tensorHomInterchange X A I E ≫ (homUnitReindexIso X k e hE).hom =
      (tensorTotalMapIso₂ X A (homUnitReindexIso X (F := I) k e hE)).hom ≫
        (tensorTotalReindexIso₂ X A I k).hom := by
  refine tensorTotal_hom_ext X fun U t r a φ ↦ ?_
  rw [HomologicalComplex.comp_f, comp_val_app_apply', homUnitReindexIso_hom_f,
    homUnitEvaluation_val_app,
    tensorHomInterchange_applyHomSection X A I E U t r k (k + r) (k + (t + r)) rfl (by omega)
      a φ _, ← homUnitEvaluation_val_app]
  rw [HomologicalComplex.comp_f, comp_val_app_apply', tensorTotalMapIso₂_hom,
    tensorTotalMap_tensorTotalSection, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, tensorTotalReindexIso₂_tensorTotalSection,
    homUnitReindexIso_hom_f]
  rfl

/-- **The interchange morphism at a trivialised single-degree source is an isomorphism.** By the
square above it is a composite of three isomorphisms. -/
theorem isIso_tensorHomInterchange_of_unit
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    IsIso (tensorHomInterchange X A I E) := by
  have h : tensorHomInterchange X A I E =
      (tensorTotalMapIso₂ X A (homUnitReindexIso X (F := I) k e hE)).hom ≫
        (tensorTotalReindexIso₂ X A I k).hom ≫ (homUnitReindexIso X k e hE).inv := by
    rw [← Category.assoc, ← tensorHomInterchange_comp_homUnitReindexIso, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **The base case of the induction**: the interchange morphism at a trivialised single-degree
source is a quasi-isomorphism, being an isomorphism. -/
theorem tensorHomInterchange_quasiIso_of_unit
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    QuasiIso (tensorHomInterchange X A I E) := by
  have := isIso_tensorHomInterchange_of_unit X A I k e hE
  infer_instance

end AlgebraicGeometry.RingedSite

end
