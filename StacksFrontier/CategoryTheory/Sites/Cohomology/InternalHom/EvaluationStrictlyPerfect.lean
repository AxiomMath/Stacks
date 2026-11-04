module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationUnitSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree

/-!
# The evaluation morphism of Stacks 0A92 at a strictly perfect source

Let `X` be a ringed site and let `I`, `I'` be complexes of `O`-modules. This file completes the
proof that the evaluation morphism of Stacks 0A92

`Tot(SheafHom(I, I') ⊗_O P) ⟶ SheafHom(SheafHom(P, I), I')`

is a quasi-isomorphism whenever `P` is **strictly perfect**: bounded, with every term a direct
summand of a finite free `O`-module.

## Main results

* `AlgebraicGeometry.RingedSite.evaluationMap_single_quasiIso_of_unitPower` and
  `AlgebraicGeometry.RingedSite.evaluationMap_single_quasiIso_of_finiteFreeSummand`: the
  single-degree cases.
* `AlgebraicGeometry.RingedSite.evaluationMap_quasiIso_of_bounded` and
  `AlgebraicGeometry.RingedSite.evaluationMap_quasiIso_of_isFiniteFreeSummand`: the bounded and
  the strictly perfect cases, the latter phrased with boundedness and the termwise condition
  separately.
* `AlgebraicGeometry.RingedSite.quasiIso_evaluationMap_of_isStrictlyPerfect`: the strictly
  perfect case phrased with the predicate `IsStrictlyPerfect` of Stacks 08FL.

## References

* [Stacks Project, Lemma 20.49.6 (Tag 0A92)](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Definition 20.47.1 (Tag 08FL)](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Lemma 36.10.12 (Tag 08JJ)](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive hasFiniteBiproducts_sheafOfModules
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ)]
  (I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The evaluation morphism is a quasi-isomorphism at the complex concentrated in degree `k` with
term `O^{⊕r}`. -/
theorem evaluationMap_single_quasiIso_of_unitPower (k : ℤ) (r : ℕ) :
    QuasiIso (evaluationMap X
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        (unitPower X r)) I I') := by
  let Sg := HomologicalComplex.single (SheafOfModules.{u} (ringSheaf X.O)) (ComplexShape.up ℤ) k
  have hone : QuasiIso (evaluationMap X (Sg.obj (SheafOfModules.unit (ringSheaf X.O))) I I') := by
    have := isIso_evaluationMap_of_unitSource X k
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k
        (SheafOfModules.unit (ringSheaf X.O)))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k
        (SheafOfModules.unit (ringSheaf X.O))) I I'
    infer_instance
  induction r with
  | zero =>
    rw [unitPower_zero]
    exact evaluationMap_quasiIso_of_isZero X I I' (Sg.map_isZero (isZero_zero _))
  | succ r ih =>
    rw [unitPower_succ]
    let T := (unitPowerShortComplex X r).map Sg
    have : QuasiIso (evaluationMap X T.X₁ I I') := ih
    have : QuasiIso (evaluationMap X T.X₃ I I') := hone
    exact evaluationMap_quasiIso_of_degreewiseSplit X I I' T fun _ =>
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (ringSheaf X.O))).map Sg).map _

/-- The evaluation morphism is a quasi-isomorphism at the complex concentrated in degree `k` with
term a direct summand `M` of a finite free `O`-module. -/
theorem evaluationMap_single_quasiIso_of_finiteFreeSummand (k : ℤ)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    QuasiIso (evaluationMap X
      ((HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k).obj
        M) I I') :=
  evaluationMap_single_quasiIso_of_isFiniteFreeSummand X I I' k hM
    (fun r => evaluationMap_single_quasiIso_of_unitPower X I I' k r)

/-- **The bounded case.** If `P` vanishes outside the window `[a, a + r)` and each of its terms is
a direct summand of a finite free `O`-module, then the evaluation morphism at `P` is a
quasi-isomorphism. -/
theorem evaluationMap_quasiIso_of_bounded (r : ℕ) (a : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (P.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (P.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (P.X i)) :
    QuasiIso (evaluationMap X P I I') := by
  induction r generalizing a P with
  | zero =>
    refine evaluationMap_quasiIso_of_isZero X I I' (complex_isZero_of_terms P fun i => ?_)
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (P.X (a - 1)) := hlo (a - 1) (by omega)
    set q := bottomProjection P a ha with hq
    set K := kernel q with hK
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self P a ha
    have hKiso (i : ℤ) (hi : i ≠ a) : K.X i ≅ P.X i :=
      have := isIso_kernel_ι_bottomProjection_f P a ha i hi
      asIso ((kernel.ι q).f i)
    have hKterm (i : ℤ) : IsFiniteFreeSummand X (K.X i) := by
      by_cases hi : i = a
      · subst i
        exact IsFiniteFreeSummand.of_isZero X hz
      · exact IsFiniteFreeSummand.of_iso X (hKiso i hi) (hterm i)
    have hKlo (i : ℤ) (hi : i < a + 1) : IsZero (K.X i) := by
      by_cases hia : i = a
      · subst i
        exact hz
      · exact IsZero.of_iso (hlo i (by omega)) (hKiso i hia)
    have hKhi (i : ℤ) (hi : a + 1 + r ≤ i) : IsZero (K.X i) :=
      IsZero.of_iso (hhi i (by push_cast; omega)) (hKiso i (by omega))
    have hKq : QuasiIso (evaluationMap X K I I') := ih (a + 1) K hKlo hKhi hKterm
    have hAq : QuasiIso (evaluationMap X
        ((HomologicalComplex.single (SheafOfModules.{u} (ringSheaf X.O))
          (ComplexShape.up ℤ) a).obj (P.X a)) I I') :=
      evaluationMap_single_quasiIso_of_finiteFreeSummand X I I' a (hterm a)
    let T := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    refine evaluationMap_quasiIso_of_degreewiseSplit X I I' T (fun i => ?_)
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self P a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (isIso_kernel_ι_bottomProjection_f P a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (P.X a) i hi)

/-- **The strictly perfect case, with boundedness and the termwise condition given separately.**
If `P` has only finitely many nonzero terms and each of them is a direct summand of a finite free
`O`-module, then

`Tot(SheafHom(I, I') ⊗_O P) ⟶ SheafHom(SheafHom(P, I), I')`

is a quasi-isomorphism, for arbitrary `I` and `I'`. -/
theorem evaluationMap_quasiIso_of_isFiniteFreeSummand
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (P.X i)) :
    QuasiIso (evaluationMap X P I I') := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine evaluationMap_quasiIso_of_bounded X I I' (b - a + 1).toNat a P ?_ ?_ hterm
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

/-- **The evaluation morphism of Stacks 0A92 is a quasi-isomorphism at a strictly perfect
source.** If `P` is strictly perfect in the sense of Stacks 08FL — finitely many nonzero terms,
each a direct summand of a finite free `O`-module — then

`Tot(SheafHom(I, I') ⊗_O P) ⟶ SheafHom(SheafHom(P, I), I')`

is a quasi-isomorphism, for arbitrary `I` and `I'`. -/
theorem quasiIso_evaluationMap_of_isStrictlyPerfect
    (P I I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    [I.IsKInjective] [I'.IsKInjective] :
    QuasiIso (evaluationMap X P I I') :=
  evaluationMap_quasiIso_of_isFiniteFreeSummand X I I' P hP.bounded
    (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand X (hP.termDirectSummand i))

end AlgebraicGeometry.RingedSite

end
