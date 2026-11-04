module

public import StacksFrontier.Algebra.Homology.SignedMateDualOfTheInternalHomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DegreewisePairingOnTheHomComplex

/-!
# The dual complex of a ringed site is a left dual in the monoidal category of complexes

Let `(C, 𝒪)` be a ringed site and `ℱ^•` a complex of `𝒪`-modules each of whose terms is locally
a direct summand of a finite free `𝒪`-module.  `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` of
[Stacks, Tag 0FP9] is the internal hom into the unit for
`Stacks.SheafOfModules.Strict.monoidalClosedCochainComplex`, and
`Stacks.SheafOfModules.Strict.exactPairingIhomComplexX` makes `𝒢^{-n}` a left dual of `ℱ^n` in
every degree.  The differential of `𝒢^•` is the signed transpose of the differential of `ℱ^•`,
so `CochainComplex.exactPairingOfSignedMateDual` assembles these pairings into a left dual of
`ℱ^•` in the monoidal category of complexes.

## Main results

* `Stacks.SheafOfModules.Strict.isSignedMateDual_ihomUnit`: the complex `𝒢^•` satisfies
  `CochainComplex.IsSignedMateDual` for the pairings `exactPairingIhomComplexX`.
* `Stacks.SheafOfModules.Strict.exactPairingIhomUnitComplex`: **`𝒢^•` is a left dual of `ℱ^•`
  in the monoidal category of complexes of `𝒪`-modules**, at a global `Finset` bound on `ℱ^•`.

## Implementation notes

**General results.**  The differential of `𝒢^•` is a signed `MonoidalClosed.pre (d_ℱ)` because
the unit complex has zero differentials, and `pre` is the mate of the pairings; both facts are
proved in general in
`StacksFrontier/Algebra/Homology/SignedMateDualOfTheInternalHomComplex.lean` and
`StacksFrontier/CategoryTheory/Monoidal/MateAsInternalHomPre.lean`, and are instantiated here.
`Mod(𝒪)` carries several monoidal structures that instance search does not cross between, and
the braiding needed for the internal-hom comparison is the symmetry of the strict structure,
`Stacks.SheafOfModules.Strict.symmetricCategory`, ascribed at
`Stacks.SheafOfModules.Strict.monoidalCategory`.

**Bounded and locally bounded complexes.**  `exactPairingIhomUnitComplex` assumes `ℱ^•`
vanishes outside a finite set of degrees; the locally bounded case, where `η = ∑ ηₙ` is a locally
finite sum, is `Stacks.SheafOfModules.Strict.exactPairingIhomUnitComplexOfLocallyBounded`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- **The differential of `𝒢^•` is the signed transpose of the differential of `ℱ^•`.**  The
complex `𝒢^• = (ihom ℱ^•).obj (𝟙_)` of [Stacks, Tag 0FP9] satisfies
`CochainComplex.IsSignedMateDual` for the degreewise pairings
`Stacks.SheafOfModules.Strict.exactPairingIhomComplexX`: in every degree

`d_𝒢^{-(n+1), -n} = (-1)^n (d_ℱ^{n, n+1})^∨`,

the mate being taken for those pairings.  Against a unit complex with zero differentials the
differential of the internal Hom complex is the `negOnePow`-signed
`MonoidalClosed.pre (d_ℱ)`, and `CategoryTheory.ExactPairing.mate_eq_pre_app` identifies `pre`
with the mate. -/
theorem isSignedMateDual_ihomUnit (K : CochainComplex (Mod R) ℤ)
    (hK : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    CochainComplex.IsSignedMateDual K ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ)))
      (fun n => exactPairingIhomComplexX R K n (hK n)) := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  let : @SymmetricCategory _ _ ((Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)) :=
    Stacks.SheafOfModules.Strict.symmetricCategory R.obj (isSheaf_ringSheaf R)
  let : BraidedCategory (Mod R) :=
    (Stacks.SheafOfModules.Strict.symmetricCategory R.obj
      (isSheaf_ringSheaf R)).toBraidedCategory
  let := strictMonoidalClosed R
  let : ∀ X₁ X₂ : GradedObject ℤ (Mod R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
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
  exact CochainComplex.isSignedMateDual_internalHomComplex K
    (fun n => dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n))
    (fun n => exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) (K.X n) (hK n))

/-- **The dual of a bounded complex in the monoidal category of complexes.**  For a complex
`ℱ^•` of `𝒪`-modules vanishing outside a finite set of degrees and with every term locally a direct
summand of a finite free `𝒪`-module, the complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` — the internal hom
into the unit — is a left dual of `ℱ^•` in `CochainComplex Mod(𝒪) ℤ`, with `η = ∑ ηₙ` and
`ε = ∑ εₙ`. -/
@[instance_reducible]
def exactPairingIhomUnitComplex (K : CochainComplex (Mod R) ℤ) (s : Finset ℤ)
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hK : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    ExactPairing K ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))) := by
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI := strictMonoidalClosed R
  letI : ∀ X₁ X₂ : GradedObject ℤ (Mod R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
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
  exact CochainComplex.exactPairingOfSignedMateDual K _
    (fun n => exactPairingIhomComplexX R K n (hK n)) s hbd
    (isSignedMateDual_ihomUnit R K hK)

end Stacks.SheafOfModules.Strict

end

end
