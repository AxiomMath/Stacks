module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeUnitTensorFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso

/-!
# The interchange morphism of Stacks 0BYR in the tensor factor

Let `X` be a ringed site. This file collects the steps of the dévissage of Stacks 0ATN part (2)
which concern the tensor factor of the interchange morphism of Stacks 0BYR

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

and which do not need the rows of the dévissage: the vanishing case, and the passage to retracts.
Each is the companion, in the tensor factor, of a step already present for the source of the
internal Hom, where part (1)'s dévissage runs:
`tensorHomInterchange_quasiIso_of_isZero` and `tensorHomInterchange_quasiIso_of_retract`.

Two vanishing statements are needed along the way and are of independent use. A zero tensor
factor gives a zero total tensor complex, the left-hand companion of
`tensorTotal_isZero_of_isZero_right`; and a zero target gives a zero internal Hom complex, the
companion of `sheafHomComplex_isZero_of_isZero`, which is the statement for a zero source. The
second is proved on sections, because the terms of an internal Hom complex are produced by
`Classical.choice` and are therefore opaque.

The vanishing case is an isomorphism, not merely a quasi-isomorphism, as is the single-degree case
`tensorHomInterchange_isIso_of_unitTensorFactor`.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **A zero tensor factor gives a zero total tensor complex.** This is the left-hand companion
of `tensorTotal_isZero_of_isZero_right`: in each total degree the complex is a coproduct of the
`A^p ⊗_O Y^q`, and every one of them vanishes because `A^p` does. -/
theorem tensorTotal_isZero_of_isZero_left
    (A Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsZero A) :
    IsZero (tensorTotal X A Y) := by
  refine complex_isZero_of_terms _ fun n => ?_
  refine IsZero.of_iso ?_
    ((HomologicalComplex.eval _ _ n).mapIso (tensorTotalIsoTensorComplex X A Y))
  refine StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
    ((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O A Y).toGradedObject.isColimitCofanMapObj
      _ n) ?_
  rintro ⟨⟨p, q⟩, hpq⟩
  exact ((sheafTensor.{u, u, u, u, u} X.O).flip.obj (Y.X q)).map_isZero
    ((HomologicalComplex.eval _ _ p).map_isZero hA)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **A zero target gives a zero internal Hom complex.** This is the companion of
`sheafHomComplex_isZero_of_isZero`, which is the statement for a zero source. The terms of the
internal Hom complex are opaque, so the argument is on sections: a section is determined by its
evaluations, and every evaluation lands in a term of the zero target. -/
theorem sheafHomComplex_isZero_of_isZero_target
    (N B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : IsZero B) :
    IsZero (sheafHomComplex X N B).obj := by
  refine complex_isZero_of_terms _ fun n => (IsZero.iff_id_eq_zero _).2 ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext
    (LinearMap.ext fun x => ?_))
  refine homSection_ext X (sheafHomComplex X N B) U.unop n (fun p q hpq V i y => ?_)
  have hz : IsZero ((B.X q).val.obj (op V)) :=
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
        (op V)).map_isZero
        ((HomologicalComplex.eval _ _ q).map_isZero hB)
  have hzero : ∀ z : ((B.X q).val.obj (op V)), z = 0 := fun z => by
    simpa using congrArg (fun φ => ModuleCat.Hom.hom φ z) ((IsZero.iff_id_eq_zero _).1 hz)
  exact (hzero _).trans (hzero _).symm

/-- **A zero tensor factor makes the interchange morphism of Stacks 0BYR an isomorphism**, for
trivial reasons: both of its complexes vanish. This is the base of the induction on the number of
nonzero terms of the tensor factor. -/
theorem tensorHomInterchange_isIso_of_isZero_tensorFactor
    (A I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsZero A) :
    IsIso (tensorHomInterchange X A I N) :=
  StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero
    (tensorHomInterchange X A I N)
    (tensorTotal_isZero_of_isZero_left X A (sheafHomComplex X N I).obj hA)
    (sheafHomComplex_isZero_of_isZero_target X N (tensorTotal X A I)
      (tensorTotal_isZero_of_isZero_left X A I hA))

/-- **The interchange morphism of Stacks 0BYR as a functor to the arrow category, in the tensor
factor.** The functoriality is the covariance of Stacks 0BYT in that variable; this is the
companion of `interchangeArrowFunctor`, which is the same construction in the source of the
internal Hom, where Stacks 0BYT is contravariant. -/
def interchangeTensorArrowFunctor
    (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      Arrow
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  obj A := Arrow.mk (tensorHomInterchange X A I N)
  map f := Arrow.homMk
    (tensorTotalMap X f (𝟙 (sheafHomComplex X N I).obj))
    (homMap X (𝟙 N) (tensorTotalMap X f (𝟙 I)))
    (tensorHomInterchange_natural_tensor X f I N).symm
  map_id A := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.id_left, Arrow.id_right,
        tensorTotalMap_id, homMap_id] <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · simp only [Arrow.homMk_left, Arrow.comp_left, tensorTotalMap_comp, Category.comp_id]
    · simp only [Arrow.homMk_right, Arrow.comp_right, homMap_comp, Category.comp_id,
        tensorTotalMap_comp]

omit [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- **The interchange morphism of Stacks 0BYR passes to retracts of the tensor factor.** This is
what reduces a term of the tensor factor which is a direct summand of a finite free module to a
finite free one. -/
theorem tensorHomInterchange_quasiIso_of_retract_tensorFactor
    (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {A A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ρ : Retract A A')
    [QuasiIso (tensorHomInterchange X A' I N)] :
    QuasiIso (tensorHomInterchange X A I N) :=
  quasiIso_of_retractArrow (ρ.map (interchangeTensorArrowFunctor X I N))

end AlgebraicGeometry.RingedSite

end
