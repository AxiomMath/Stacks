module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.KInjectiveClosure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeTensorFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalShortComplexLeft
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorUnitFactor

/-!
# K-injectivity of the total tensor complex at a strictly perfect tensor factor

Let `X` be a ringed site, let `E` be a strictly perfect complex of `O`-modules — finitely many
nonzero terms, each a direct summand of a finite free `O`-module — and let `I` be a K-injective
complex of `O`-modules. Then `Tot(E ⊗_O I)` is K-injective. That is
`AlgebraicGeometry.RingedSite.isKInjective_tensorTotal_of_isFiniteFreeSummand`.

This is the side condition of
`isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange`, and with it that criterion
turns the invertibility of the diagonal of Stacks 0BYS into quasi-isomorphy of the interchange
morphism of Stacks 0BYR alone, with nothing induced by a resolution left over. It is therefore
one of the two inputs to the globally strictly perfect case of Stacks 0ATN part (2).

The dévissage is the same one the interchange morphism is proved by, and it runs on the closure
properties of K-injectivity: the vanishing case, retracts, and two out of three along a
degreewise split short complex, the splittings of the row of total tensor complexes being
`tensorTotalShortComplexLeftSplitting`.

The one case that is not formal is the trivialised single-degree tensor factor, and it is where
the **chain-level** unit collapse is needed rather than the degreewise one: K-injectivity is a
property of a complex. `Tot(E ⊗_O I)` is carried by the Koszul symmetry to `Tot(I ⊗_O E)`, which
`tensorTotalUnitFactorRightIso` identifies with `I` reindexed, and a reindexing of a K-injective
complex is K-injective.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Remark 20.49.12 (Tag 0BYS)](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Definition 20.47.1 (Tag 08FL)](https://stacks.math.columbia.edu/tag/08FL)
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

variable (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  [I.IsKInjective]

omit [I.IsKInjective] in
/-- A zero tensor factor gives a K-injective total tensor complex, the complex being zero. -/
theorem isKInjective_tensorTotal_of_isZero
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : IsZero E) :
    (tensorTotal X E I).IsKInjective :=
  CochainComplex.isKInjective_of_isZero (tensorTotal_isZero_of_isZero_left X E I hE)

/-- **The total tensor complex with a trivialised single-degree tensor factor is K-injective.**
`Tot(E ⊗_O I)` is carried by the Koszul symmetry to `Tot(I ⊗_O E)`, which the chain-level unit
collapse identifies with `I` reindexed by `-k`; a reindexing of a K-injective complex is
K-injective.

This is where the chain-level collapse is needed rather than the degreewise one, K-injectivity
being a property of the complex. -/
theorem isKInjective_tensorTotal_of_unit
    {E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (k : ℤ)
    (e : E.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (tensorTotal X E I).IsKInjective := by
  have := CochainComplex.isKInjective_reindexBy I (-k)
  exact CochainComplex.isKInjective_of_iso
    (tensorTotalUnitFactorRightIso X k e hE ≪≫ (tensorTotalIsoTensorComplex X I E).symm ≪≫
      tensorTotalFlipIso X I E)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [I.IsKInjective] in
/-- **K-injectivity of the total tensor complex passes to retracts of the tensor factor**, the
retract being carried by the functoriality of `Tot(− ⊗_O I)`. -/
theorem isKInjective_tensorTotal_of_retract
    {E E' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (ρ : Retract E E')
    (h : (tensorTotal X E' I).IsKInjective) :
    (tensorTotal X E I).IsKInjective :=
  CochainComplex.isKInjective_of_retract
    { i := tensorTotalMap X ρ.i (𝟙 I)
      r := tensorTotalMap X ρ.r (𝟙 I)
      retract := by rw [tensorTotalMap_comp, Category.comp_id, ρ.retract, tensorTotalMap_id] }

omit [I.IsKInjective] in
/-- **Two out of three for K-injectivity along a degreewise split short complex of tensor
factors.** The row of total tensor complexes is split in every degree by
`tensorTotalShortComplexLeftSplitting`, so the two-out-of-three closure of K-injectivity
applies. -/
theorem isKInjective_tensorTotal_of_degreewiseSplit
    (T : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ q : ℤ, (T.map (HomologicalComplex.eval _ _ q)).Splitting)
    (h₁ : (tensorTotal X T.X₁ I).IsKInjective) (h₃ : (tensorTotal X T.X₃ I).IsKInjective) :
    (tensorTotal X T.X₂ I).IsKInjective := by
  have h₁' : (tensorTotalShortComplexLeft X T I).X₁.IsKInjective := h₁
  have h₃' : (tensorTotalShortComplexLeft X T I).X₃.IsKInjective := h₃
  exact CochainComplex.isKInjective_X₂_of_degreewiseSplit
    (tensorTotalShortComplexLeft X T I) (tensorTotalShortComplexLeftSplitting X T σ I)

/-- **The single-degree finite free case**, by induction on the rank along the degreewise split
short complex `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`, with the vanishing case as base and the trivialised
case as third term. -/
theorem isKInjective_tensorTotal_single_of_unitPower (k : ℤ) (r : ℕ) :
    (tensorTotal X ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) k).obj (unitPower X r)) I).IsKInjective := by
  let Sg := HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k
  induction r with
  | zero =>
    rw [unitPower_zero]
    exact isKInjective_tensorTotal_of_isZero X I _ (Sg.map_isZero (isZero_zero _))
  | succ r ih =>
    rw [unitPower_succ]
    have hone :
        (tensorTotal X (Sg.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          I).IsKInjective :=
      isKInjective_tensorTotal_of_unit X I k (HomologicalComplex.singleObjXSelf _ k _)
        (HomologicalComplex.isZero_single_obj_X _ _ _)
    let T := (unitPowerShortComplex X r).map Sg
    have hT (p : ℤ) : (T.map (HomologicalComplex.eval _ _ p)).Splitting :=
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map Sg).map _
    exact isKInjective_tensorTotal_of_degreewiseSplit X I T hT ih hone

/-- **The single-degree case for a direct summand of a finite free module**, by the retract
lemma from the single-degree finite free case. -/
theorem isKInjective_tensorTotal_single_of_isFiniteFreeSummand (k : ℤ)
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    (tensorTotal X ((HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) k).obj M) I).IsKInjective := by
  obtain ⟨r, ⟨ρ⟩⟩ := exists_retract_single_of_isFiniteFreeSummand X k hM
  exact isKInjective_tensorTotal_of_retract X I ρ
    (isKInjective_tensorTotal_single_of_unitPower X I k r)

/-- **The bounded case.** If the tensor factor vanishes outside a window of width `r` and each
of its terms is a direct summand of a finite free `O`-module, the total tensor complex is
K-injective. The induction is on the width, splitting off the bottom term. -/
theorem isKInjective_tensorTotal_of_bounded (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    (tensorTotal X E I).IsKInjective := by
  induction r generalizing a E with
  | zero =>
    refine isKInjective_tensorTotal_of_isZero X I E (complex_isZero_of_terms E fun i => ?_)
    by_cases hi : i < a
    · exact hlo i hi
    · exact hhi i (by push_cast; omega)
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have hKiso (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      have := isIso_kernel_ι_bottomProjection_f E a ha i hi
      asIso ((kernel.ι p).f i)
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
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine isKInjective_tensorTotal_of_degreewiseSplit X I T (fun i => ?_)
      (ih (a + 1) K hKlo hKhi hKterm)
      (isKInjective_tensorTotal_single_of_isFiniteFreeSummand X I a (hterm a))
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The total tensor complex of a strictly perfect complex with a K-injective complex is
K-injective.** If `E` has finitely many nonzero terms, each a direct summand of a finite free
`O`-module, and `I` is K-injective, then `Tot(E ⊗_O I)` is K-injective.

This is the side condition of
`isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange`, and so one of the two inputs
to the globally strictly perfect case of Stacks 0ATN part (2) — the other being that the
interchange morphism is a quasi-isomorphism at a strictly perfect tensor factor. -/
theorem isKInjective_tensorTotal_of_isFiniteFreeSummand
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    (tensorTotal X E I).IsKInjective := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine isKInjective_tensorTotal_of_bounded X I (b - a + 1).toNat a E ?_ ?_ hterm
  · intro i hi
    by_contra hz
    have := ha hz
    omega
  · intro i hi
    by_contra hz
    have := hb hz
    omega

end AlgebraicGeometry.RingedSite

end
