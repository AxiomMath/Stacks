module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocallyStrictlyPerfectGradedDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyBoundedDualOfTheHomComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a locally bounded complex of finite locally free modules on a ringed space

Let `(X, 𝒪_X)` be a ringed space and `ℱ^•` a locally bounded complex of `𝒪_X`-modules each of
whose terms is locally a direct summand of a finite free `𝒪_X`-module.  Then
`𝒢^• = Hom^•(ℱ^•, 𝒪_X)` is a left dual of `ℱ^•` in the monoidal category of complexes of
`𝒪_X`-modules, with coevaluation `η = ∑ ηₙ` and evaluation `ε = ∑ εₙ`, where
`ηₙ : 𝒪_X ⟶ ℱ^n ⊗ 𝒢^{-n}` and `εₙ : 𝒢^{-n} ⊗ ℱ^n ⟶ 𝒪_X` are the pairings of `ℱ^n` with its
dual.

## Main results

* `Stacks.SheafOfModules.OnSpace.exists_exactPairing_ihomUnit_of_isLocallyBounded`: **[Stacks,
  Tag 0FP9]** — `𝒢^•` is a left dual of `ℱ^•` with `η = ∑ ηₙ` and `ε = ∑ εₙ`.
* `Stacks.SheafOfModules.OnSpace.exactPairingIhomUnitComplexOfIsLocallyBounded`: the left dual
  structure itself.
* `Stacks.SheafOfModules.OnSpace.exactPairingIhomUnitComplexOfIsLocallyStrictlyPerfect`: the same
  under the covering phrasing of the hypothesis.
* `coevaluation_comp_πTensorObj_exactPairingIhomUnitComplexOfIsLocallyBounded` and
  `ιTensorObj_comp_evaluation_exactPairingIhomUnitComplexOfIsLocallyBounded`: the components of
  `η` and `ε` are the `ηₙ` and the `εₙ`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace MonoidalCategory GradedObject

noncomputable section

universe u

namespace Stacks.SheafOfModules.OnSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

variable {X} in
/-- The neighbourhoods of the points of `X` on which a locally bounded complex is bounded cover
`X`. -/
theorem coversTop_of_isLocallyBounded
    {F : CochainComplex (Strict.Mod X.sheaf) ℤ}
    (hb : IsLocallyBounded X F) :
    (Opens.grothendieckTopology X.carrier).CoversTop fun x => (hb x).choose :=
  (Opens.coversTop_iff _ _).mpr (IsOpenCover.mk (top_le_iff.mp fun x _ =>
    Opens.mem_iSup.mpr ⟨x, (hb x).choose_spec.1⟩))

/-- **[Stacks, Tag 0FP9].**  Let `ℱ^•` be a locally bounded complex of `𝒪_X`-modules each of
whose terms is locally a direct summand of a finite free `𝒪_X`-module.  Then
`𝒢^• = Hom^•(ℱ^•, 𝒪_X)`, the internal hom into the unit complex, is a left dual of `ℱ^•` in the
monoidal category of complexes of `𝒪_X`-modules, with coevaluation `η = ∑ ηₙ` and evaluation
`ε = ∑ εₙ`: the sum `η` is locally finite, being on each of a covering family of
neighbourhoods on which `ℱ^•` is bounded the finite sum of the `ηₙ` over the surviving degrees,
and the components of `η` and `ε` are
the `ηₙ` and the `εₙ`
(`coevaluation_comp_πTensorObj_exactPairingIhomUnitComplexOfIsLocallyBounded`,
`ιTensorObj_comp_evaluation_exactPairingIhomUnitComplexOfIsLocallyBounded`). -/
@[instance_reducible]
def exactPairingIhomUnitComplexOfIsLocallyBounded
    (F : CochainComplex (Strict.Mod X.sheaf) ℤ)
    (hb : IsLocallyBounded X F) (hF : ∀ n : ℤ, IsLocallyFiniteFreeSummand X (F.X n)) :
    letI := Strict.monoidalCategoryCochainComplex X.sheaf
    letI := Strict.monoidalClosedCochainComplex X.sheaf
    ExactPairing F ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))) :=
  Strict.exactPairingIhomUnitComplexOfLocallyBounded X.sheaf F (coversTop_of_isLocallyBounded hb)
    (fun x => (hb x).choose_spec.2.choose) (fun x => (hb x).choose_spec.2.choose_spec)
    (fun n => isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n) (hF n))

/-- **The coevaluation of `exactPairingIhomUnitComplexOfIsLocallyBounded` is `η = ∑ ηₙ`**: its
degree-zero component on the summand `ℱ^n ⊗ 𝒢^{-n}` of `(ℱ^• ⊗ 𝒢^•)^0` is `ηₙ`, read through
the identification of the degree zero term of the unit complex with `𝒪_X`. -/
theorem coevaluation_comp_πTensorObj_exactPairingIhomUnitComplexOfIsLocallyBounded
    (F : CochainComplex (Strict.Mod X.sheaf) ℤ)
    (hb : IsLocallyBounded X F) (hF : ∀ n : ℤ, IsLocallyFiniteFreeSummand X (F.X n)) (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property
    letI : ∀ X₁ X₂ : GradedObject ℤ (Strict.Mod X.sheaf), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    letI := Strict.monoidalCategoryCochainComplex X.sheaf
    letI := Strict.monoidalClosedCochainComplex X.sheaf
    letI := exactPairingIhomUnitComplexOfIsLocallyBounded X F hb hF
    (η_ F ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ)))).f 0 ≫
        GradedObject.Monoidal.πTensorObj F.X
          ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))).X n (-n) 0
          (add_neg_cancel n) =
      ((HomologicalComplex.tensorUnitIso (Strict.Mod X.sheaf) (ComplexShape.up ℤ)).inv 0 ≫
          GradedObject.Monoidal.tensorUnit₀.hom) ≫
        (Strict.exactPairingIhomComplexX X.sheaf F n
          (isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n)
            (hF n))).coevaluation' := by
  obtain ⟨h₀, hπ, -⟩ := Strict.coevaluation_exactPairingIhomUnitComplexOfLocallyBounded X.sheaf F
    (coversTop_of_isLocallyBounded hb)
    (fun x => (hb x).choose_spec.2.choose) (fun x => (hb x).choose_spec.2.choose_spec)
    (fun n => isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n) (hF n))
  exact (eq_whisker h₀ _).trans ((Category.assoc _ _ _).trans ((whisker_eq _
    ((Category.assoc _ _ _).trans (whisker_eq _ (hπ n)))).trans (Category.assoc _ _ _).symm))

/-- **The evaluation of `exactPairingIhomUnitComplexOfIsLocallyBounded` is `ε = ∑ εₙ`**: its
degree-zero component on the summand `𝒢^{-n} ⊗ ℱ^n` of `(𝒢^• ⊗ ℱ^•)^0` is `εₙ`, read through
the identification of the degree zero term of the unit complex with `𝒪_X`. -/
theorem ιTensorObj_comp_evaluation_exactPairingIhomUnitComplexOfIsLocallyBounded
    (F : CochainComplex (Strict.Mod X.sheaf) ℤ)
    (hb : IsLocallyBounded X F) (hF : ∀ n : ℤ, IsLocallyFiniteFreeSummand X (F.X n)) (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property
    letI : MonoidalPreadditive (Strict.Mod X.sheaf) :=
      Strict.monoidalPreadditiveRingSheaf X.sheaf
    letI := Strict.monoidalCategoryCochainComplex X.sheaf
    letI := Strict.monoidalClosedCochainComplex X.sheaf
    letI := exactPairingIhomUnitComplexOfIsLocallyBounded X F hb hF
    HomologicalComplex.ιTensorObj ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))) F
        (-n) n 0 (neg_add_cancel n) ≫
        (ε_ F ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ)))).f 0 =
      (Strict.exactPairingIhomComplexX X.sheaf F n
          (isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n)
            (hF n))).evaluation' ≫
        GradedObject.Monoidal.tensorUnit₀.inv ≫
          (HomologicalComplex.tensorUnitIso (Strict.Mod X.sheaf) (ComplexShape.up ℤ)).hom 0 :=
  Strict.evaluation_exactPairingIhomUnitComplexOfLocallyBounded X.sheaf F
    (coversTop_of_isLocallyBounded hb)
    (fun x => (hb x).choose_spec.2.choose) (fun x => (hb x).choose_spec.2.choose_spec)
    (fun n => isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n) (hF n)) n

/-- **[Stacks, Tag 0FP9] under the covering phrasing of its hypothesis**: if `X` has an open
covering on whose members `ℱ^•` is strictly perfect, then `𝒢^• = Hom^•(ℱ^•, 𝒪_X)` is a left
dual of `ℱ^•` in the monoidal category of complexes of `𝒪_X`-modules, with `η = ∑ ηₙ` and
`ε = ∑ εₙ`.  This is `exactPairingIhomUnitComplexOfIsLocallyBounded`, the two phrasings being
equivalent by `isLocallyStrictlyPerfect_iff`. -/
@[instance_reducible]
def exactPairingIhomUnitComplexOfIsLocallyStrictlyPerfect
    (F : CochainComplex (Strict.Mod X.sheaf) ℤ) (hF : IsLocallyStrictlyPerfect X F) :
    letI := Strict.monoidalCategoryCochainComplex X.sheaf
    letI := Strict.monoidalClosedCochainComplex X.sheaf
    ExactPairing F ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))) :=
  exactPairingIhomUnitComplexOfIsLocallyBounded X F
    (isLocallyBounded_of_isLocallyStrictlyPerfect X hF)
    (isLocallyFiniteFreeSummand_of_isLocallyStrictlyPerfect X hF)

/-- **[Stacks, Tag 0FP9].**  Let `(X, 𝒪_X)` be a ringed space and `ℱ^•` a locally bounded
complex of `𝒪_X`-modules each of whose terms `ℱ^n` is locally a direct summand of a finite free
`𝒪_X`-module, and let `𝒢^• = Hom^•(ℱ^•, 𝒪_X)`.  Let `ηₙ : 𝒪_X ⟶ ℱ^n ⊗ 𝒢^{-n}` and
`εₙ : 𝒢^{-n} ⊗ ℱ^n ⟶ 𝒪_X` be the coevaluation and evaluation of the duality between `ℱ^n` and
`𝒢^{-n}`.  Then there is a left dual structure on `𝒢^•` over `ℱ^•` in the monoidal category of
complexes of `𝒪_X`-modules whose coevaluation is `η = ∑ ηₙ` and whose evaluation is
`ε = ∑ εₙ`: in degree zero, read through the identification of the degree zero term of the unit
complex with `𝒪_X`, the component of `η` on the summand `ℱ^n ⊗ 𝒢^{-n}` of
`Tot(ℱ^• ⊗ 𝒢^•)^0` is `ηₙ`, and the component of `ε` on the summand `𝒢^{-n} ⊗ ℱ^n` of
`Tot(𝒢^• ⊗ ℱ^•)^0` is `εₙ`.  The structure is `exactPairingIhomUnitComplexOfIsLocallyBounded`. -/
@[stacks 0FP9]
theorem exists_exactPairing_ihomUnit_of_isLocallyBounded
    (F : CochainComplex (Strict.Mod X.sheaf) ℤ)
    (hb : IsLocallyBounded X F) (hF : ∀ n : ℤ, IsLocallyFiniteFreeSummand X (F.X n)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property
    letI : MonoidalPreadditive (Strict.Mod X.sheaf) :=
      Strict.monoidalPreadditiveRingSheaf X.sheaf
    letI : ∀ X₁ X₂ : GradedObject ℤ (Strict.Mod X.sheaf), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    letI := Strict.monoidalCategoryCochainComplex X.sheaf
    letI := Strict.monoidalClosedCochainComplex X.sheaf
    ∃ P : ExactPairing F ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))),
      (∀ n : ℤ, P.coevaluation'.f 0 ≫
          GradedObject.Monoidal.πTensorObj F.X
            ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))).X n (-n) 0
            (add_neg_cancel n) =
        ((HomologicalComplex.tensorUnitIso (Strict.Mod X.sheaf) (ComplexShape.up ℤ)).inv 0 ≫
            GradedObject.Monoidal.tensorUnit₀.hom) ≫
          (Strict.exactPairingIhomComplexX X.sheaf F n
            (isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n)
              (hF n))).coevaluation') ∧
      ∀ n : ℤ, HomologicalComplex.ιTensorObj
          ((ihom F).obj (𝟙_ (CochainComplex (Strict.Mod X.sheaf) ℤ))) F (-n) n 0
          (neg_add_cancel n) ≫ P.evaluation'.f 0 =
        (Strict.exactPairingIhomComplexX X.sheaf F n
            (isLocallyDirectSummandOfFiniteFree_of_isLocallyFiniteFreeSummand X (F.X n)
              (hF n))).evaluation' ≫
          GradedObject.Monoidal.tensorUnit₀.inv ≫
            (HomologicalComplex.tensorUnitIso (Strict.Mod X.sheaf) (ComplexShape.up ℤ)).hom 0 :=
  ⟨exactPairingIhomUnitComplexOfIsLocallyBounded X F hb hF,
    coevaluation_comp_πTensorObj_exactPairingIhomUnitComplexOfIsLocallyBounded X F hb hF,
    ιTensorObj_comp_evaluation_exactPairingIhomUnitComplexOfIsLocallyBounded X F hb hF⟩

end Stacks.SheafOfModules.OnSpace

end

end
