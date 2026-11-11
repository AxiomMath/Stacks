module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteCoproductOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexOfALocallyStrictlyPerfectComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The dual complex of a locally strictly perfect complex is a left dual

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules such that every object
`U` of `C` admits a covering `{U_i → U}` on whose members `ℱ^•|_{U_i}` is strictly perfect.
This file proves that the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)`, together with `η = ∑ ηₙ` and
`ε = ∑ εₙ`, is a **left dual** of `ℱ^•` in the monoidal category of complexes of `𝒪`-modules —
the assertion of [Stacks, Tag 0FPR] under the tag's own hypothesis, with no global bound on the
degrees in which `ℱ^•` is nonzero.

The one thing the local hypothesis does not supply is the *morphism* `η`: it is a sum over all
degrees, and that sum is only locally finite. What makes it exist is that the degree-zero part
of `ℱ^• ⊗ 𝒢^•` is a coproduct `∐_{a+b=0} ℱ^a ⊗ 𝒢^b` whose summands locally all but finitely
many vanish, so that coproduct is also the *product*
(`Stacks.SheafOfModules.CoproductSheafification.isIso_coprodToProd`): a morphism into it may be
prescribed by its components, and is determined by them. Those are the two inputs that
`CochainComplex.exactPairingDualComplexOfComponents` consumes in place of boundedness.

## Main results

* `Stacks.SheafOfModules.Strict.isLocallyFinitelySupported_tensorSummands`: the summands of a
  fixed degree of `ℱ^• ⊗ 𝒢^•` are locally finitely many, for `ℱ^•` locally strictly perfect.
* `Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect`: the left dual
  structure on `𝒢^•`, with
  `coevaluation_comp_πTensorObj_exactPairingDualComplexOfLocallyStrictlyPerfect` and
  `ιTensorObj_comp_evaluation_exactPairingDualComplexOfLocallyStrictlyPerfect` identifying its
  coevaluation and evaluation with `∑ ηₙ` and `∑ εₙ`.
* `Stacks.SheafOfModules.Strict.isLeftDual_dualComplexOfLocallyStrictlyPerfect`: **[Stacks,
  Tag 0FPR]** — `𝒢^•` with `η = ∑ ηₙ` and `ε = ∑ εₙ` is a left dual of `ℱ^•`.

## Implementation notes

**Where the local finiteness comes from.** On a member `W` of the covering, `ℱ^•|_W` is strictly
perfect, hence bounded: `ℱ^a|_W` is zero outside a finite set `S` of degrees depending on `W`
(`isLocallyBounded_of_isLocallyStrictlyPerfect`). A summand `ℱ^a ⊗ 𝒢^b` with `a ∉ S` then
restricts to zero on `W`, because restriction to a slice is monoidal for the tensor product of
[Stacks, Tag 01CA] and a tensor product with a zero factor is zero — which is
`isZero_tensorObj_over`. The pairs `(a, b)` with `a + b = j` and `a ∈ S` are finitely many, so
all but finitely many summands restrict to zero.

**The index type.** The fibres of a `ℤ`-graded tensor product are indexed by
`{p : ℤ × ℤ // p.1 + p.2 = j}`, which is in `Type 0`; that is exactly the index universe the
coproduct-equals-product comparison for sheaves of modules is available in. The index function
is written as the plain lambda `fun x : ℤ × ℤ => x.1 + x.2` rather than Mathlib's match-lambda:
the body of a match stays a metavariable, and the subtype membership then fails to coerce.

**Spelling.** Three spellings of the slice structure sheaf occur and are all equal by `rfl` but
not interchangeable for instance synthesis, so each monoidal and preadditive instance is
ascribed at the spelling its consumer names, with the definitional equality crossing at the
`:=`, exactly as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Duals/LocallyBoundedDualComplex.lean`.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace CochainComplex

section Components

variable {D : Type*} [Category D] [MonoidalCategory D] [Preadditive D]
  [MonoidalPreadditive D] [HasZeroObject D]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  (K : CochainComplex D ℤ) (E : ℤ → D) (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (E j))
  (coev : 𝟙_ D ⟶ GradedObject.Monoidal.tensorObj K.X E 0)
  (hc : GradedObject.Monoidal.IsAssembledCoev K.X E (dualPairing K E q) coev)
  (hsep : IsSeparatedDegOne K (dualComplex K E q))

/-- **The coevaluation of `exactPairingDualComplexOfComponents` has the prescribed components**:
in degree zero, on the summand `K^n ⊗ E^{-n}`, it is the degreewise coevaluation `ηₙ`. -/
theorem coevaluation_comp_πTensorObj_exactPairingDualComplexOfComponents (n : ℤ) :
    (@ExactPairing.coevaluation' _ _ _ K (dualComplex K E q)
        (exactPairingDualComplexOfComponents K E q coev hc hsep)).f 0 ≫
        GradedObject.Monoidal.πTensorObj K.X E n (-n) 0 (add_neg_cancel n) =
      ((HomologicalComplex.tensorUnitIso D (ComplexShape.up ℤ)).inv 0 ≫
        GradedObject.Monoidal.tensorUnit₀.hom) ≫ (dualPairing K E q n).coevaluation' := by
  have h0 : (@ExactPairing.coevaluation' _ _ _ K (dualComplex K E q)
      (exactPairingDualComplexOfComponents K E q coev hc hsep)).f 0 =
        (HomologicalComplex.tensorUnitIso D (ComplexShape.up ℤ)).inv 0 ≫
          GradedObject.Monoidal.tensorUnit₀.hom ≫ coev := by
    change (HomologicalComplex.tensorUnitIso D (ComplexShape.up ℤ)).inv 0 ≫
        GradedObject.Monoidal.gradedCoevOf K.X E coev 0 = _
    exact whisker_eq _ (GradedObject.Monoidal.gradedCoevOf_zero K.X E coev)
  rw [h0]
  exact (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (hc n)))).trans (Category.assoc _ _ _).symm)

/-- **The evaluation of `exactPairingDualComplexOfComponents` is `ε = ∑ εₙ`**: in degree zero,
on the summand `E^{-n} ⊗ K^n`, it is the degreewise evaluation `εₙ`. -/
theorem ιTensorObj_comp_evaluation_exactPairingDualComplexOfComponents (n : ℤ) :
    HomologicalComplex.ιTensorObj (dualComplex K E q) K (-n) n 0 (neg_add_cancel n) ≫
        (@ExactPairing.evaluation' _ _ _ K (dualComplex K E q)
          (exactPairingDualComplexOfComponents K E q coev hc hsep)).f 0 =
      (dualPairing K E q n).evaluation' ≫ GradedObject.Monoidal.tensorUnit₀.inv ≫
        (HomologicalComplex.tensorUnitIso D (ComplexShape.up ℤ)).hom 0 :=
  ι_evaluationHom_f_zero K (dualComplex K E q) (dualPairing K E q) _ n

end Components

end CochainComplex

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- A tensor product one of whose factors is a zero object is a zero object.
`HomologicalComplex.Monoidal.isZero_tensorObj_of_isZero_left` is the same statement under
`(curriedTensor E).Additive`, which is not the instance the slice monoidal structure carries;
the hypothesis here is `MonoidalPreadditive`, which it does. -/
private theorem isZero_tensorObj_left {E : Type*} [Category E] [MonoidalCategory E]
    [Preadditive E] [MonoidalPreadditive E] {X : E} (hX : IsZero X) (Y : E) :
    IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← MonoidalCategory.id_whiskerRight X Y, hX, MonoidalPreadditive.zero_whiskerRight]

omit [HasSheafify J AddCommGrpCat] in
/-- **A tensor product with a factor vanishing on a slice vanishes on that slice.** Restriction
to the site over `W` is monoidal for the tensor product of [Stacks, Tag 01CA], so the
restriction of `A ⊗ B` is the tensor product of the restrictions, and a tensor product one of
whose factors is a zero object is a zero object. -/
theorem isZero_tensorObj_over (A B : Mod R) (W : C) (h : IsZero (A.over W)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    IsZero ((A ⊗ B).over W) := by
  let instSrc : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj
        (isSheaf_ringSheaf R))) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  let instTgt : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf R.obj
        (isSheaf_ringSheaf R) W)) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory ((R.over W)).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((R.over W))).property)
  let instMon : @Functor.Monoidal _ _ instSrc _ _ instTgt
      (Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W) :=
    Stacks.SheafOfModules.SliceRestriction.overFunctorStrictMonoidal R.obj
      (isSheaf_ringSheaf R) W
  let instPre : @MonoidalPreadditive _ _ _ instTgt := monoidalPreadditiveRingSheaf (R.over W)
  refine Limits.IsZero.of_iso ?_
    (@Functor.Monoidal.μIso _ _ instSrc _ _ instTgt
      (Stacks.SheafOfModules.SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W)
      instMon A B).symm
  exact @isZero_tensorObj_left _ _ instTgt _ instPre _ h _

variable (K G : CochainComplex (Mod R) ℤ)

/-- The summands of the degree-`j` part of `ℱ^• ⊗ 𝒢^•`: the pairs of degrees summing to `j`,
with the tensor product of the corresponding terms. The index type is in `Type 0`. -/
abbrev tensorSummands (j : ℤ) :
    ((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j} : Set (ℤ × ℤ)) → Mod R :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  (((mapBifunctor (curriedTensor (Mod R)) ℤ ℤ).obj K.X).obj G.X).mapObjFun
    (fun x : ℤ × ℤ => x.1 + x.2) j

omit [HasSheafify J AddCommGrpCat] in
/-- **The summands of a fixed degree of `ℱ^• ⊗ 𝒢^•` are locally finitely many.** On a member of
the covering of [Stacks, Tag 0FPR] the complex `ℱ^•` is strictly perfect, hence bounded, and a
summand whose `ℱ`-degree lies outside the finite set of surviving degrees restricts to zero. -/
theorem isLocallyFinitelySupported_tensorSummands (hK : IsLocallyStrictlyPerfect R K) (j : ℤ) :
    CoproductSheafification.IsLocallyFinitelySupported (tensorSummands R K G j) := by
  classical
  intro V
  obtain ⟨T, hT, hbd⟩ := isLocallyBounded_of_isLocallyStrictlyPerfect hK V
  refine ⟨T, hT, fun {W} g hg => ?_⟩
  obtain ⟨S, hS⟩ := hbd g hg
  refine ⟨S.image (fun n => (⟨(n, j - n), by simp⟩ :
    ((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j} : Set (ℤ × ℤ)))), fun idx hidx => ?_⟩
  have hsum : (idx : ℤ × ℤ).1 + (idx : ℤ × ℤ).2 = j := idx.2
  have hfst : (idx : ℤ × ℤ).1 ∉ S := fun hmem => hidx (Finset.mem_image.2
    ⟨(idx : ℤ × ℤ).1, hmem, Subtype.ext (Prod.ext_iff.2 ⟨rfl,
      show j - (idx : ℤ × ℤ).1 = (idx : ℤ × ℤ).2 by omega⟩)⟩)
  exact isZero_tensorObj_over R (K.X (idx : ℤ × ℤ).1) (G.X (idx : ℤ × ℤ).2) W
    (hS (idx : ℤ × ℤ).1 hfst)

variable (hF : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n))

/-- **A coevaluation for the dual complex exists.** The degree-zero part of `ℱ^• ⊗ 𝒢^•` is a
coproduct whose summands are locally finitely many, hence also a product, so the morphism
`η = ∑ ηₙ` may be prescribed by its components even though the sum is only locally finite. -/
theorem exists_isAssembledCoev (hK : IsLocallyStrictlyPerfect R K) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    ∃ coev : 𝟙_ (Mod R) ⟶ GradedObject.Monoidal.tensorObj K.X (dualComplexX R K) 0,
      GradedObject.Monoidal.IsAssembledCoev K.X (dualComplexX R K)
        (CochainComplex.dualPairing K (dualComplexX R K) (dualComplexPairing R K hF)) coev := by
  classical
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  obtain ⟨u, hu⟩ := CoproductSheafification.exists_hom_comp_eq
    (Stacks.SheafOfModules.Tensor.ringSheaf R) (tensorSummands R K (dualComplex R K hF) 0)
    (isLocallyFinitelySupported_tensorSummands R K (dualComplex R K hF) hK 0)
    (fun idx => GradedObject.Monoidal.πTensorObj K.X (dualComplexX R K)
      (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 0 idx.2)
    (fun idx => GradedObject.Monoidal.ιTensorObj_πTensorObj_self K.X (dualComplexX R K)
      (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 0 idx.2)
    (fun idx jdx hne => GradedObject.Monoidal.ιTensorObj_πTensorObj_ne K.X (dualComplexX R K)
      (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 (jdx : ℤ × ℤ).1 (jdx : ℤ × ℤ).2 0 jdx.2 idx.2
      (fun hcon => hne (Subtype.ext (show (jdx : ℤ × ℤ) = (idx : ℤ × ℤ) from
        Prod.ext_iff.2 ⟨hcon.1, hcon.2⟩))))
    (fun idx => (dualComplexPairing R K hF (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 (by
      have := idx.2
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
      omega)).coevaluation')
  exact ⟨u, fun n => hu ⟨(n, -n), by simp⟩⟩

/-- **Morphisms into the degree-one part of `ℱ^• ⊗ 𝒢^•` are determined by their components.**
The summands are locally finitely many, so the coproduct is also the product and its
projections are jointly monomorphic. -/
theorem isSeparatedDegOne_dualComplex (hK : IsLocallyStrictlyPerfect R K) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
    CochainComplex.IsSeparatedDegOne K (dualComplex R K hF) := by
  classical
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  intro f g hfg
  exact CoproductSheafification.hom_ext_of_comp_eq
    (Stacks.SheafOfModules.Tensor.ringSheaf R) (tensorSummands R K (dualComplex R K hF) 1)
    (isLocallyFinitelySupported_tensorSummands R K (dualComplex R K hF) hK 1)
    (fun idx => GradedObject.Monoidal.πTensorObj K.X (dualComplexX R K)
      (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 1 idx.2)
    (fun idx => GradedObject.Monoidal.ιTensorObj_πTensorObj_self K.X (dualComplexX R K)
      (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 1 idx.2)
    (fun idx jdx hne => GradedObject.Monoidal.ιTensorObj_πTensorObj_ne K.X (dualComplexX R K)
      (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 (jdx : ℤ × ℤ).1 (jdx : ℤ × ℤ).2 1 jdx.2 idx.2
      (fun hcon => hne (Subtype.ext (show (jdx : ℤ × ℤ) = (idx : ℤ × ℤ) from
        Prod.ext_iff.2 ⟨hcon.1, hcon.2⟩))))
    f g (fun idx => hfg (idx : ℤ × ℤ).1 (idx : ℤ × ℤ).2 idx.2)

variable {R K}

/-- **The left dual structure of [Stacks, Tag 0FPR].** Let `(C, 𝒪)` be a ringed site and let
`ℱ^•` be a complex of `𝒪`-modules such that for every object `U` of `C` there exists a covering
`{U_i → U}` with `ℱ^•|_{U_i}` strictly perfect. Then the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)`,
together with `η = ∑ ηₙ` and `ε = ∑ εₙ` assembled from the coevaluations and evaluations of
[Stacks, Tag 0FNY] at the terms, is a **left dual** of `ℱ^•` in the monoidal category of
complexes of `𝒪`-modules of [Stacks, Tag 0FPQ]: both triangle identities hold.

No global bound on the degrees of `ℱ^•` is assumed, so `η` is a locally finite sum. It exists
because the degree-zero part of `ℱ^• ⊗ 𝒢^•` is a coproduct whose summands locally all but
finitely many vanish, hence is also the product, and a morphism into it is given by — and
determined by — its components. That its coevaluation and evaluation are `∑ ηₙ` and `∑ εₙ` is
`coevaluation_comp_πTensorObj_exactPairingDualComplexOfLocallyStrictlyPerfect` and
`ιTensorObj_comp_evaluation_exactPairingDualComplexOfLocallyStrictlyPerfect`; the tag is
`isLeftDual_dualComplexOfLocallyStrictlyPerfect`. -/
@[instance_reducible]
def exactPairingDualComplexOfLocallyStrictlyPerfect (hK : IsLocallyStrictlyPerfect R K) :
    @ExactPairing _ _ (monoidalCategoryCochainComplex R) K
      (dualComplexOfLocallyStrictlyPerfect R K hK) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  CochainComplex.exactPairingDualComplexOfComponents K (dualComplexX R K)
    (dualComplexPairing R K
      (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK))
    (exists_isAssembledCoev R K
      (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK).choose
    (exists_isAssembledCoev R K
      (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK).choose_spec
    (isSeparatedDegOne_dualComplex R K
      (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK)

/-- **The coevaluation of `exactPairingDualComplexOfLocallyStrictlyPerfect` is `η = ∑ ηₙ`**: its
degree-zero component on the summand `ℱ^n ⊗ 𝒢^{-n}` of `(ℱ^• ⊗ 𝒢^•)^0` is the coevaluation
`ηₙ` of [Stacks, Tag 0FNY] at the term `ℱ^n`, read through the identification of the unit of
complexes in degree zero with `𝒪`. -/
theorem coevaluation_comp_πTensorObj_exactPairingDualComplexOfLocallyStrictlyPerfect
    (hK : IsLocallyStrictlyPerfect R K) (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
    letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
        ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
    letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
        ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
    letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
        GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
    letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
        GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
    letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
        GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
    (@ExactPairing.coevaluation' _ _ inferInstance K
        (dualComplexOfLocallyStrictlyPerfect R K hK)
        (exactPairingDualComplexOfLocallyStrictlyPerfect hK)).f 0 ≫
        GradedObject.Monoidal.πTensorObj K.X (dualComplexX R K) n (-n) 0 (add_neg_cancel n) =
      ((HomologicalComplex.tensorUnitIso (Mod R) (ComplexShape.up ℤ)).inv 0 ≫
        GradedObject.Monoidal.tensorUnit₀.hom) ≫
        (dualComplexPairing R K
          (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) n (-n)
          (add_neg_cancel n)).coevaluation' := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  let : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  have h := CochainComplex.coevaluation_comp_πTensorObj_exactPairingDualComplexOfComponents K
      (dualComplexX R K) (dualComplexPairing R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK))
      (exists_isAssembledCoev R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK).choose
      (exists_isAssembledCoev R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK).choose_spec
      (isSeparatedDegOne_dualComplex R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK) n
  exact h

/-- **The evaluation of `exactPairingDualComplexOfLocallyStrictlyPerfect` is `ε = ∑ εₙ`**: its
degree-zero component on the summand `𝒢^{-n} ⊗ ℱ^n` of `(𝒢^• ⊗ ℱ^•)^0` is the evaluation `εₙ`
of [Stacks, Tag 0FNY] at the term `ℱ^n`, read through the identification of `𝒪` with the unit
of complexes in degree zero. -/
theorem ιTensorObj_comp_evaluation_exactPairingDualComplexOfLocallyStrictlyPerfect
    (hK : IsLocallyStrictlyPerfect R K) (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
    letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
        ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
    letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
        ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
    letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
        GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
    letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
        GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
    letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
        GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
    HomologicalComplex.ιTensorObj (dualComplexOfLocallyStrictlyPerfect R K hK) K (-n) n 0
        (neg_add_cancel n) ≫
        (@ExactPairing.evaluation' _ _ inferInstance K
          (dualComplexOfLocallyStrictlyPerfect R K hK)
          (exactPairingDualComplexOfLocallyStrictlyPerfect hK)).f 0 =
      (dualComplexPairing R K
          (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) n (-n)
          (add_neg_cancel n)).evaluation' ≫ GradedObject.Monoidal.tensorUnit₀.inv ≫
        (HomologicalComplex.tensorUnitIso (Mod R) (ComplexShape.up ℤ)).hom 0 := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  let : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  have h := CochainComplex.ιTensorObj_comp_evaluation_exactPairingDualComplexOfComponents K
      (dualComplexX R K) (dualComplexPairing R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK))
      (exists_isAssembledCoev R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK).choose
      (exists_isAssembledCoev R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK).choose_spec
      (isSeparatedDegOne_dualComplex R K
        (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) hK) n
  exact h


/-- **[Stacks, Tag 0FPR].** Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of
`𝒪`-modules such that for every object `U` of `C` there exists a covering `{U_i → U}` with
`ℱ^•|_{U_i}` strictly perfect. Let `𝒢^• = SheafHom^•(ℱ^•, 𝒪)`, with degree-`j` term
`SheafHom(ℱ^{-j}, 𝒪)`. Then there is a left dual structure `(𝒢^•, η, ε)` on `ℱ^•` in the
monoidal category of complexes of `𝒪`-modules of [Stacks, Tag 0FPQ] — both triangle identities
of [Stacks, Tag 0FFP] hold — whose coevaluation is `η = ∑ ηₙ` and whose evaluation is
`ε = ∑ εₙ`: the degree-zero component of `η` on the summand `ℱ^n ⊗ 𝒢^{-n}` is the coevaluation
`ηₙ`, and the degree-zero component of `ε` on the summand `𝒢^{-n} ⊗ ℱ^n` is the evaluation `εₙ`,
of [Stacks, Tag 0FNY] at the term `ℱ^n`. Both `η` and `ε` are concentrated in degree zero, and
the degree-zero parts of `ℱ^• ⊗ 𝒢^•` and `𝒢^• ⊗ ℱ^•` are the coproducts of these summands, so
these components determine them.

The structure is `exactPairingDualComplexOfLocallyStrictlyPerfect`. -/
@[stacks 0FPR "for a complex `ℱ^•` of 𝒪-modules such that every object of the site has a covering \
sieve on whose members `ℱ^•` is strictly perfect (Tag 08FL), the complex \
`𝒢^• = SheafHom^•(ℱ^•, 𝒪)` with \
η = ∑ ηₙ and ε = ∑ εₙ is a left dual of `ℱ^•` (Tag 0FFP) in the monoidal category of complexes \
of Tag 0FPQ. The left dual is an `ExactPairing`, so both triangle identities hold; η and ε are \
pinned down by their degree-zero components on the summands `ℱ^n ⊗ 𝒢^{-n}` and `𝒢^{-n} ⊗ ℱ^n`, \
which are the coevaluation ηₙ and the evaluation εₙ of Tag 0FNY at `ℱ^n`. The complex is \
`dualComplexOfLocallyStrictlyPerfect`, with terms `SheafHom(ℱ^{-j}, 𝒪)` \
(`dualComplexOfLocallyStrictlyPerfect_X`) and the signed-transpose differential of Tag 0FNK \
(`dualComplex_d`); the pairing itself is `exactPairingDualComplexOfLocallyStrictlyPerfect`. The \
converse is Tag 0FPS"]
theorem isLeftDual_dualComplexOfLocallyStrictlyPerfect (hK : IsLocallyStrictlyPerfect R K) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
    letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
        ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
    letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
        ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
    letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
        GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
    letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
        GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
    letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
        GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
    ∃ P : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K
        (dualComplexOfLocallyStrictlyPerfect R K hK),
      (∀ n : ℤ, (@ExactPairing.coevaluation' _ _ inferInstance K
          (dualComplexOfLocallyStrictlyPerfect R K hK) P).f 0 ≫
          GradedObject.Monoidal.πTensorObj K.X (dualComplexX R K) n (-n) 0 (add_neg_cancel n) =
        ((HomologicalComplex.tensorUnitIso (Mod R) (ComplexShape.up ℤ)).inv 0 ≫
          GradedObject.Monoidal.tensorUnit₀.hom) ≫
          (dualComplexPairing R K
            (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) n (-n)
            (add_neg_cancel n)).coevaluation') ∧
      (∀ n : ℤ, HomologicalComplex.ιTensorObj (dualComplexOfLocallyStrictlyPerfect R K hK) K
          (-n) n 0 (neg_add_cancel n) ≫
          (@ExactPairing.evaluation' _ _ inferInstance K
            (dualComplexOfLocallyStrictlyPerfect R K hK) P).f 0 =
        (dualComplexPairing R K
            (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK) n (-n)
            (add_neg_cancel n)).evaluation' ≫ GradedObject.Monoidal.tensorUnit₀.inv ≫
          (HomologicalComplex.tensorUnitIso (Mod R) (ComplexShape.up ℤ)).hom 0) :=
  ⟨exactPairingDualComplexOfLocallyStrictlyPerfect hK,
    coevaluation_comp_πTensorObj_exactPairingDualComplexOfLocallyStrictlyPerfect hK,
    ιTensorObj_comp_evaluation_exactPairingDualComplexOfLocallyStrictlyPerfect hK⟩

end Stacks.SheafOfModules.Strict

end

end
