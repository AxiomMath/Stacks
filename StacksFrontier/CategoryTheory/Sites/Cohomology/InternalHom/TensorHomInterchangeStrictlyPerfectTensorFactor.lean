module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeTensorFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalShortComplexLeft
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplitTarget

/-!
# The interchange morphism of Stacks 0BYR at a strictly perfect tensor factor

Let `X` be a ringed site and let `E`, `I`, `N` be cochain complexes of `O`-modules with `E`
strictly perfect — finitely many nonzero terms, each a direct summand of a finite free
`O`-module. Then the interchange morphism of Stacks 0BYR

`Tot(E ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(E ⊗_O I))`

is a quasi-isomorphism, for arbitrary `I` and `N`. That is
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand_tensorFactor`,
and it is the dévissage of Stacks 0ATN part (2) on the tensor factor.

The companion for the **source of the internal Hom** is
`tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`, which is what part (1) needs, and the
shape of the argument is the same: two out of three along a degreewise split short complex,
reducing a bounded complex of direct summands of finite free modules to a single degree by
splitting off the bottom term, a single degree to a finite free one by a retract, and a finite
free one to the trivialised case by induction on the rank. The two base cases — the vanishing
complex and the trivialised single-degree complex — are isomorphisms rather than merely
quasi-isomorphisms.

What differs is the two rows. Both of them preserve the direction of the arrows here, the total
tensor complex and the internal Hom both being covariant in the variable at issue, where for the
source of the internal Hom both reverse them. The rows come from
`tensorTotalShortComplexLeft_shortExact`, obtained from its second-variable companion by the
Koszul symmetry, and from `internalHomTermwiseSplittingTarget`.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.11 (Tag 0BYT)](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Definition 20.47.1 (Tag 08FL)](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u} X.O) (ComplexShape.up ℤ)]

variable (I N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Two out of three for a degreewise split short complex of tensor factors.** The interchange
morphism is a morphism of short complexes from the row of its sources, short exact by
`tensorTotalShortComplexLeft_shortExact`, to the row of its targets, short exact by
`internalHomTermwiseSplittingTarget`; two out of three in the middle is
`StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂`.

Both rows preserve the direction of the arrows, the total tensor complex and the internal Hom
both being covariant in the variable at issue here. In
`tensorHomInterchange_quasiIso_of_degreewiseSplit`, which is the same step for the source of the
internal Hom, the rows reverse them. -/
theorem tensorHomInterchange_quasiIso_of_degreewiseSplit_tensorFactor
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σs : ∀ q : ℤ, (S.map (HomologicalComplex.eval _ _ q)).Splitting)
    [QuasiIso (tensorHomInterchange X S.X₁ I N)]
    [QuasiIso (tensorHomInterchange X S.X₃ I N)] :
    QuasiIso (tensorHomInterchange X S.X₂ I N) := by
  let φ : tensorTotalShortComplexLeft X S (sheafHomComplex X N I).obj ⟶
      internalHomShortComplexTarget X (tensorTotalShortComplexLeft X S I) N :=
    { τ₁ := tensorHomInterchange X S.X₁ I N
      τ₂ := tensorHomInterchange X S.X₂ I N
      τ₃ := tensorHomInterchange X S.X₃ I N
      comm₁₂ := tensorHomInterchange_natural_tensor X S.f I N
      comm₂₃ := tensorHomInterchange_natural_tensor X S.g I N }
  have h1 : QuasiIso φ.τ₁ := ‹QuasiIso (tensorHomInterchange X S.X₁ I N)›
  have h3 : QuasiIso φ.τ₃ := ‹QuasiIso (tensorHomInterchange X S.X₃ I N)›
  exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ φ
    (tensorTotalShortComplexLeft_shortExact X S σs (sheafHomComplex X N I).obj)
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n => (internalHomTermwiseSplittingTarget X (tensorTotalShortComplexLeft X S I) N
        (tensorTotalShortComplexLeftSplitting X S σs I) n).shortExact))

/-- **The single-degree finite free case**, by induction on the rank along the degreewise split
short complex `O^{⊕r} ⟶ O^{⊕(r+1)} ⟶ O`. The base of the induction is the vanishing case and the
third term is always the trivialised case, which is an isomorphism. -/
theorem tensorHomInterchange_single_quasiIso_of_unitPower_tensorFactor (k : ℤ) (r : ℕ) :
    QuasiIso (tensorHomInterchange X
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj (unitPower X r)) I N) := by
  let Sg := HomologicalComplex.single
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ) k
  have hone : QuasiIso (tensorHomInterchange X
      (Sg.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) I N) := by
    have := tensorHomInterchange_isIso_of_unitTensorFactor X k
      (HomologicalComplex.singleObjXSelf _ k _)
      (fun p hp => HomologicalComplex.isZero_single_obj_X _ _ _ p hp) I N
    infer_instance
  induction r with
  | zero =>
    rw [unitPower_zero]
    have := tensorHomInterchange_isIso_of_isZero_tensorFactor X _ I N
      (Sg.map_isZero (isZero_zero _))
    infer_instance
  | succ r ih =>
    rw [unitPower_succ]
    let T := (unitPowerShortComplex X r).map Sg
    have hT (p : ℤ) : (T.map (HomologicalComplex.eval _ _ p)).Splitting :=
      ((ShortComplex.Splitting.ofHasBinaryBiproduct (unitPower X r)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map Sg).map _
    have h1 : QuasiIso (tensorHomInterchange X T.X₁ I N) := ih
    have h3 : QuasiIso (tensorHomInterchange X T.X₃ I N) := hone
    exact tensorHomInterchange_quasiIso_of_degreewiseSplit_tensorFactor X I N T hT

/-- **The single-degree case for a direct summand of a finite free module**, by the retract
lemma from the single-degree finite free case. -/
theorem tensorHomInterchange_single_quasiIso_of_isFiniteFreeSummand_tensorFactor
    (k : ℤ) {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsFiniteFreeSummand X M) :
    QuasiIso (tensorHomInterchange X
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj M) I N) := by
  obtain ⟨r, ⟨ρ⟩⟩ := exists_retract_single_of_isFiniteFreeSummand X k hM
  have := tensorHomInterchange_single_quasiIso_of_unitPower_tensorFactor X I N k r
  exact tensorHomInterchange_quasiIso_of_retract_tensorFactor X I N ρ

/-- **The bounded case.** If the tensor factor `E` vanishes outside the window `[a, a + r)` and
each of its terms is a direct summand of a finite free `O`-module, then the interchange morphism
at `E` is a quasi-isomorphism. The induction is on the width of the window, splitting off the
bottom term. -/
theorem tensorHomInterchange_quasiIso_of_bounded_tensorFactor (r : ℕ) (a : ℤ)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hlo : ∀ i, i < a → IsZero (E.X i)) (hhi : ∀ i, a + r ≤ i → IsZero (E.X i))
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (tensorHomInterchange X E I N) := by
  induction r generalizing a E with
  | zero =>
    have := tensorHomInterchange_isIso_of_isZero_tensorFactor X E I N
      (complex_isZero_of_terms E fun i => by
        by_cases hi : i < a
        · exact hlo i hi
        · exact hhi i (by push_cast; omega))
    infer_instance
  | succ r ih =>
    have ha : IsZero (E.X (a - 1)) := hlo (a - 1) (by omega)
    set p := bottomProjection E a ha
    set K := kernel p
    have hz : IsZero (K.X a) := isZero_kernel_bottomProjection_X_self E a ha
    have hKiso (i : ℤ) (hi : i ≠ a) : K.X i ≅ E.X i :=
      haveI := isIso_kernel_ι_bottomProjection_f E a ha i hi
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
    have hKq : QuasiIso (tensorHomInterchange X K I N) := ih (a + 1) K hKlo hKhi hKterm
    have hAq : QuasiIso (tensorHomInterchange X
        ((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) a).obj (E.X a)) I N) :=
      tensorHomInterchange_single_quasiIso_of_isFiniteFreeSummand_tensorFactor X I N a (hterm a)
    let T := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    refine tensorHomInterchange_quasiIso_of_degreewiseSplit_tensorFactor X I N T (fun i => ?_)
    by_cases hi : i = a
    · subst i
      exact ShortComplex.Splitting.ofIsZeroOfIsIso _ hz (isIso_bottomProjection_f_self E a ha)
    · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (isIso_kernel_ι_bottomProjection_f E a ha i hi)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (E.X a) i hi)

/-- **The interchange morphism of Stacks 0BYR is a quasi-isomorphism at a strictly perfect
tensor factor.** If `E` has only finitely many nonzero terms and each of them is a direct summand
of a finite free `O`-module, then

`Tot(E ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(E ⊗_O I))`

is a quasi-isomorphism, for arbitrary `I` and `N`.

This is the companion, in the tensor factor, of
`tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`, which is the same statement for the
source of the internal Hom and is what Stacks 0ATN part (1) needs. Together with the
K-injectivity of `Tot(E ⊗_O I)` it gives the globally strictly perfect case of part (2), by
`isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange`. -/
theorem tensorHomInterchange_quasiIso_of_isFiniteFreeSummand_tensorFactor
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (E.X i)) :
    QuasiIso (tensorHomInterchange X E I N) := by
  obtain ⟨a, ha⟩ := hbdd.bddBelow
  obtain ⟨b, hb⟩ := hbdd.bddAbove
  refine tensorHomInterchange_quasiIso_of_bounded_tensorFactor X I N (b - a + 1).toNat a E ?_ ?_
    hterm <;>
  · intro i hi
    by_contra hz
    have := ha hz
    have := hb hz
    omega

end AlgebraicGeometry.RingedSite

end
