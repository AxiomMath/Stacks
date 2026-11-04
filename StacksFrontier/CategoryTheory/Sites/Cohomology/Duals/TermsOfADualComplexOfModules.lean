module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
public import StacksFrontier.Algebra.Homology.DegreewiseLeftDual

/-!
# The terms of a complex of modules with a left dual are locally finite free summands

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules admitting a left dual
`𝒢^•` in the monoidal category of complexes of `𝒪`-modules, the tensor product being the total
complex of the tensor product of [Stacks, Tag 01CA]. Then every term `ℱ^n` has `𝒢^{-n}` as a
left dual in `Mod(𝒪)`, and therefore every object of the site has a covering on whose members
`ℱ^n` restricts to a direct summand of a finite free module. Consequently each term `𝒢^{-n}` of
the dual complex is isomorphic to the dual sheaf `SheafHom(ℱ^n, 𝒪)` of [Stacks, Tag 0FNY],
compatibly with the degreewise coevaluation and evaluation.

The two steps are the degreewise reading of a dual complex and the converse half of the duality
cluster [Stacks, Tag 0FNZ]. The identification of the terms is then uniqueness of duals, both
`𝒢^{-n}` and `SheafHom(ℱ^n, 𝒪)` being left duals of `ℱ^n`.

## Main definitions

* `Stacks.SheafOfModules.Strict.dualSheafIsoX_of_complex`: the identification
  `𝒢^{-n} ≅ SheafHom(ℱ^n, 𝒪)`.

## Main results

* `Stacks.SheafOfModules.Strict.exactPairingX_of_complex`: the dual pair `(ℱ^n, 𝒢^{-n})` of
  `𝒪`-modules.
* `Stacks.SheafOfModules.Strict.isLocallyDirectSummandOfFiniteFree_X`: every term of a complex
  with a left dual is, locally on the site, a direct summand of a finite free module.
* `Stacks.SheafOfModules.Strict.isZero_X_of_coevaluation_eq_zero`: a term in whose degree the
  coevaluation vanishes is a zero object. Together with local finiteness of the coevaluation,
  which is not available here, this is what bounds the complex locally.
* `Stacks.SheafOfModules.Strict.coevaluation_dualSheafIsoX_of_complex` and
  `Stacks.SheafOfModules.Strict.dualSheafIsoX_of_complex_evaluation`: the identification of the
  terms carries the degreewise coevaluation and evaluation of the pairing of the complexes to
  the coevaluation and evaluation of [Stacks, Tag 0FNY].

## Implementation notes

The ambient monoidal structure on complexes in the statements below is
`monoidalCategoryCochainComplex`. Reading the pairing degreewise needs no boundedness and sees
no differential.

## References

* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

section

variable (K L : CochainComplex (Mod R) ℤ)

/-- **The terms of a dual pair of complexes of `𝒪`-modules are a dual pair.** If `L` is a left
dual of `K` in the monoidal category of complexes, then in every degree `n` the term `L^{-n}`
is a left dual of `K^n` in `Mod(𝒪)`, for the tensor product of [Stacks, Tag 01CA]. -/
@[instance_reducible]
def exactPairingX_of_complex (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L)
    (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    ExactPairing (K.X n) (L.X (-n)) :=
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
  letI : ExactPairing K L := p
  CochainComplex.exactPairingXApply K L n

/-- A term of a complex with a left dual is a zero object as soon as the degreewise
coevaluation vanishes in that degree. -/
theorem isZero_X_of_coevaluation_eq_zero
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (n : ℤ)
    (h : letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
          (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
        Stacks.SheafOfModules.Strict.monoidalCategory R.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf R).property
      letI := exactPairingX_of_complex R K L p n
      η_ (K.X n) (L.X (-n)) = 0) :
    IsZero (K.X n) :=
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let := exactPairingX_of_complex R K L p n
  CategoryTheory.GradedObject.Monoidal.isZero_of_coevaluation_eq_zero
    (X := K.X n) (Y := L.X (-n)) h

end

variable [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Every term of a complex of `𝒪`-modules with a left dual is locally a direct summand of a
finite free module.** Every object of the site has a covering on whose members the restriction
of `ℱ^n` is a retract of a free module on a finite index type.

This is one of the three assertions of [Stacks, Tag 0FPA], the other two being local
boundedness and that the left dual is the complex of Example 0FP9. -/
theorem isLocallyDirectSummandOfFiniteFree_X (K L : CochainComplex (Mod R) ℤ)
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (n : ℤ) :
    IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n) := fun U =>
  exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf R.obj (isSheaf_ringSheaf R)
    (K.X n) (L.X (-n)) (exactPairingX_of_complex R K L p n) U

/-- **The terms of a left dual complex are the dual sheaves of the terms.** If `L` is a left dual
of `K` in the monoidal category of complexes of `𝒪`-modules, then in every degree `n` the term
`L^{-n}` is isomorphic to the dual sheaf `SheafHom(K^n, 𝒪)` of [Stacks, Tag 0FNY].

Both sheaves are left duals of `K^n` in `Mod(𝒪)`, so they are isomorphic by uniqueness of
duals, the isomorphism being the right adjoint mate of the identity of `K^n`. -/
def dualSheafIsoX_of_complex (K L : CochainComplex (Mod R) ℤ)
    (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (n : ℤ) :
    L.X (-n) ≅ dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n) :=
  @rightDualIso _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property) (K.X n) _ _
    (exactPairingX_of_complex R K L p n)
    (exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) (K.X n)
      (isLocallyDirectSummandOfFiniteFree_X R K L p n))

section

variable (K L : CochainComplex (Mod R) ℤ)
  (p : @ExactPairing _ _ (monoidalCategoryCochainComplex R) K L) (n : ℤ)

/-- The pairing of [Stacks, Tag 0FNY] exhibiting `SheafHom(K^n, 𝒪)` as a left dual of the term
`K^n`. -/
@[instance_reducible]
def exactPairingDualSheafX :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    ExactPairing (K.X n) (dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n)) :=
  exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) (K.X n)
    (isLocallyDirectSummandOfFiniteFree_X R K L p n)

/-- The identification of `L^{-n}` with `SheafHom(K^n, 𝒪)` carries the degreewise coevaluation
`ηₙ` of the pairing of the complexes to the coevaluation of [Stacks, Tag 0FNY]. -/
theorem coevaluation_dualSheafIsoX_of_complex :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := exactPairingX_of_complex R K L p n
    letI := exactPairingDualSheafX R K L p n
    η_ (K.X n) (L.X (-n)) ≫ K.X n ◁ (dualSheafIsoX_of_complex R K L p n).hom =
      η_ (K.X n) (dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n)) := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let := exactPairingX_of_complex R K L p n
  let := exactPairingDualSheafX R K L p n
  have h := @coevaluation_comp_rightAdjointMate _ _ _ (K.X n) (K.X n)
    ⟨dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n)⟩ ⟨L.X (-n)⟩ (𝟙 (K.X n))
  rwa [MonoidalCategory.id_whiskerRight, Category.comp_id] at h

/-- The identification of `L^{-n}` with `SheafHom(K^n, 𝒪)` carries the evaluation of
[Stacks, Tag 0FNY] to the degreewise evaluation `εₙ` of the pairing of the complexes. -/
theorem dualSheafIsoX_of_complex_evaluation :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := exactPairingX_of_complex R K L p n
    letI := exactPairingDualSheafX R K L p n
    (dualSheafIsoX_of_complex R K L p n).hom ▷ K.X n ≫
        ε_ (K.X n) (dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n)) =
      ε_ (K.X n) (L.X (-n)) := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let := exactPairingX_of_complex R K L p n
  let := exactPairingDualSheafX R K L p n
  have h := @rightAdjointMate_comp_evaluation _ _ _ (K.X n) (K.X n)
    ⟨dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n)⟩ ⟨L.X (-n)⟩ (𝟙 (K.X n))
  rwa [MonoidalCategory.whiskerLeft_id, Category.id_comp] at h

end

end Stacks.SheafOfModules.Strict

end

end
