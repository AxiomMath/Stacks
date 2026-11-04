module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect

/-!
# The dévissage of the evaluation morphism of Stacks 0A92 in its source

Let `X` be a ringed site and let `I`, `I'` be complexes of `O`-modules. The evaluation morphism
of Stacks 0A92

`Tot(SheafHom(I, I') ⊗_O P) ⟶ SheafHom(SheafHom(P, I), I')`

is covariant in `P`: the variable occupies two slots at once, a tensor factor on the source side
and the source of the *inner* internal Hom on the target side, and the two contravariances of the
latter cancel. This file proves the structural properties of quasi-isomorphy of that morphism in
the variable `P`:

* a zero `P` makes both complexes vanish;
* quasi-isomorphy passes to retracts of `P`;
* a degreewise split short complex of sources gives two out of three.

## Main definitions

* `AlgebraicGeometry.RingedSite.evaluationArrowFunctor`: the evaluation morphism of Stacks 0A92
  as a covariant functor from the complexes — the source of the inner internal Hom — to the arrow
  category.

## Main results

* `AlgebraicGeometry.RingedSite.evaluationMap_quasiIso_of_retract`: quasi-isomorphy passes to
  retracts of the source.
* `AlgebraicGeometry.RingedSite.evaluationMap_quasiIso_of_isZero`: a zero source gives a
  quasi-isomorphism, both complexes vanishing.
* `AlgebraicGeometry.RingedSite.evaluationMap_quasiIso_of_degreewiseSplit`: two out of three for a
  degreewise split short complex of sources.
* `AlgebraicGeometry.RingedSite.evaluationMap_single_quasiIso_of_isFiniteFreeSummand`: the
  single-degree finite-free-summand case follows from the single-degree finite free case.

## References

* [Stacks Project, Lemma 20.49.6 (Tag 0A92)](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Definition 20.47.1 (Tag 08FL)](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Lemma 36.10.12 (Tag 08JJ)](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u})
  (I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The evaluation morphism of Stacks 0A92 as a functor to the arrow category**, in the source
of the inner internal Hom, with the two outer complexes held fixed. It is covariant. -/
def evaluationArrowFunctor :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      Arrow
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) where
  obj P := Arrow.mk (evaluationMap X P I I')
  map {P P'} g := Arrow.homMk
    (tensorTotalMap X (𝟙 (sheafHomComplex X I I').obj) g)
    (homMap X (homMap X g (𝟙 I)) (𝟙 I'))
    (by
      have h := evaluationMap_natural X g (𝟙 I) (𝟙 I')
      rw [homMap_id] at h
      exact h)
  map_id P := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.id_left, Arrow.id_right,
        homMap_id, tensorTotalMap_id] <;> rfl
  map_comp g h := by
    apply Arrow.hom_ext <;>
      simp only [Arrow.homMk_left, Arrow.homMk_right, Arrow.comp_left, Arrow.comp_right,
        tensorTotalMap_comp, homMap_comp, Category.comp_id]

/-- **The evaluation morphism of Stacks 0A92 passes to retracts of the source of the inner
internal Hom.** -/
theorem evaluationMap_quasiIso_of_retract
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ρ : Retract P P')
    [QuasiIso (evaluationMap X P' I I')] :
    QuasiIso (evaluationMap X P I I') :=
  quasiIso_of_retractArrow (ρ.map (evaluationArrowFunctor X I I'))

/-- **A zero source makes the evaluation morphism a quasi-isomorphism**: both of its complexes
vanish. -/
theorem evaluationMap_quasiIso_of_isZero
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsZero P) :
    QuasiIso (evaluationMap X P I I') := by
  have h := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero
    (evaluationMap X P I I')
    (tensorTotal_isZero_of_isZero_right X (sheafHomComplex X I I').obj hP)
    (sheafHomComplex_isZero_of_isZero X (sheafHomComplex_isZero_of_isZero X hP I) I')
  infer_instance

/-- **Two out of three for a degreewise split short complex of sources.** If `S` is a short
complex of complexes which is split in each degree, and the evaluation morphism is a
quasi-isomorphism at `S.X₁` and at `S.X₃`, then it is a quasi-isomorphism at `S.X₂`. -/
theorem evaluationMap_quasiIso_of_degreewiseSplit
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ q : ℤ, (S.map (HomologicalComplex.eval _ _ q)).Splitting)
    [QuasiIso (evaluationMap X S.X₁ I I')] [QuasiIso (evaluationMap X S.X₃ I I')] :
    QuasiIso (evaluationMap X S.X₂ I I') := by
  let φ : tensorTotalShortComplex X (sheafHomComplex X I I').obj S ⟶
      internalHomShortComplex X (internalHomShortComplex X S I) I' :=
    { τ₁ := evaluationMap X S.X₁ I I'
      τ₂ := evaluationMap X S.X₂ I I'
      τ₃ := evaluationMap X S.X₃ I I'
      comm₁₂ := (Arrow.w ((evaluationArrowFunctor X I I').map S.f)).symm
      comm₂₃ := (Arrow.w ((evaluationArrowFunctor X I I').map S.g)).symm }
  have : QuasiIso φ.τ₁ := ‹QuasiIso (evaluationMap X S.X₁ I I')›
  have : QuasiIso φ.τ₃ := ‹QuasiIso (evaluationMap X S.X₃ I I')›
  exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ φ
    (tensorTotalShortComplex_shortExact X (sheafHomComplex X I I').obj S σ)
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplitting X (internalHomShortComplex X S I) I'
        (fun q => internalHomTermwiseSplitting X S I σ q) n).shortExact))

/-- **The single-degree case for a direct summand of a finite free module follows from the
single-degree finite free case.** -/
theorem evaluationMap_single_quasiIso_of_isFiniteFreeSummand (k : ℤ)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M)
    (h : ∀ r : ℕ, QuasiIso (evaluationMap X
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        (unitPower X r)) I I')) :
    QuasiIso (evaluationMap X
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        M) I I') := by
  obtain ⟨r, ⟨ρ⟩⟩ := exists_retract_single_of_isFiniteFreeSummand X k hM
  have := h r
  exact evaluationMap_quasiIso_of_retract X I I' ρ

end AlgebraicGeometry.RingedSite

end
