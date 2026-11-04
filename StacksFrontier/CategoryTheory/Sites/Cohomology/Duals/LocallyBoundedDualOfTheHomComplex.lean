module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.SignedMateDualOfTheHomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyFiniteCoevaluation

/-!
# The dual of a locally bounded complex of modules on a ringed site

Let `(C, 𝒪)` be a ringed site and `ℱ^•` a complex of `𝒪`-modules each of whose terms is locally
a direct summand of a finite free `𝒪`-module, and which is locally bounded: there is a family
`{Yᵢ}` of objects covering the final object such that each restriction `ℱ^•|_{Yᵢ}` has only
finitely many nonzero terms.  Then `𝒢^• = SheafHom^•(ℱ^•, 𝒪)`, the internal hom into the unit
for `Stacks.SheafOfModules.Strict.monoidalClosedCochainComplex`, is a left dual of `ℱ^•` in the
monoidal category of complexes of `𝒪`-modules, with `η = ∑ ηₙ` and `ε = ∑ εₙ`.  The sum `η` is
locally finite: on `Yᵢ` it is the finite sum over the degrees surviving there.

## Main results

* `Stacks.SheafOfModules.Strict.exactPairingIhomUnitComplexOfLocallyBounded`: **`𝒢^•` is a left
  dual of `ℱ^•`** in `CochainComplex Mod(𝒪) ℤ`.
* `Stacks.SheafOfModules.Strict.coevaluation_exactPairingIhomUnitComplexOfLocallyBounded` and
  `Stacks.SheafOfModules.Strict.evaluation_exactPairingIhomUnitComplexOfLocallyBounded`: the
  coevaluation is `∑ ηₙ` — componentwise, and on each `Yᵢ` the finite sum — and the evaluation
  is `∑ εₙ`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
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

/-- The coevaluation `η = ∑ ηₙ : 𝒪 ⟶ (ℱ^• ⊗ 𝒢^•)^0` of a locally bounded complex, glued from
the finite sums over the degrees surviving on the members of the covering. -/
def coevIhomUnitOfLocallyBounded (K : CochainComplex (Mod R) ℤ)
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y) (t : ι → Finset ℤ)
    (ht : ∀ i, ∀ n ∉ t i, IsZero ((restr R (Y i)).obj (K.X n)))
    (hK : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    𝟙_ (Mod R) ⟶ (K ⊗ (ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X 0 :=
  locallyFiniteTotalCoev R K.X _ (fun n => exactPairingIhomComplexX R K n (hK n)) t hY ht

/-- **[Stacks, Tag 0FP9] on a ringed site.**  Let `ℱ^•` be a complex of `𝒪`-modules each of
whose terms is locally a direct summand of a finite free `𝒪`-module, and let `{Yᵢ}` be a family
of objects covering the final object such that on each `Yᵢ` only the terms in the finite set of
degrees `tᵢ` survive.  Then `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` is a left dual of `ℱ^•` in the monoidal
category of complexes of `𝒪`-modules, with coevaluation `η = ∑ ηₙ`
(`coevIhomUnitOfLocallyBounded`, the finite sum `∑_{n ∈ tᵢ} ηₙ` on each `Yᵢ`) and evaluation
`ε = ∑ εₙ`, where `ηₙ` and `εₙ` are the pairings of `ℱ^n` with its dual `𝒢^{-n}`. -/
@[instance_reducible]
def exactPairingIhomUnitComplexOfLocallyBounded (K : CochainComplex (Mod R) ℤ)
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y) (t : ι → Finset ℤ)
    (ht : ∀ i, ∀ n ∉ t i, IsZero ((restr R (Y i)).obj (K.X n)))
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
  letI : ∀ i, MonoidalCategory (ModSlice R (Y i)) :=
    fun i => (Stacks.SheafOfModules.Strict.monoidalCategory ((R.over (Y i))).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((R.over (Y i)))).property)
  letI : ∀ i, MonoidalPreadditive (ModSlice R (Y i)) :=
    fun i => monoidalPreadditiveRingSheaf (R.over (Y i))
  let F : ∀ i, Mod R ⥤ ModSlice R (Y i) := fun i => restr R (Y i)
  letI : ∀ i, (F i).Monoidal :=
    fun i => SliceRestriction.overFunctorStrictMonoidal R.obj (isSheaf_ringSheaf R) (Y i)
  letI : ∀ i, (F i).Additive := fun i => additive_sliceOverFunctor R (Y i)
  exact CochainComplex.exactPairingOfSignedMateDualOfLocallyFinite K _
    (fun n => exactPairingIhomComplexX R K n (hK n)) F
    ⟨fun h => SliceRestriction.overFunctor_map_injective hY _ _ h⟩ t ht
    (coevIhomUnitOfLocallyBounded R K hY t ht hK)
    (fun i => restr_map_locallyFiniteTotalCoev R K.X _ _ t hY ht i)
    (isSignedMateDual_ihomUnit R K hK)

/-- **The coevaluation of `exactPairingIhomUnitComplexOfLocallyBounded` is `η = ∑ ηₙ`.**  In
degree zero it is `coevIhomUnitOfLocallyBounded`, read through the identification of the degree
zero term of the unit complex with `𝒪`; that morphism has component `ηₙ` on the summand
`ℱ^n ⊗ 𝒢^{-n}` of `(ℱ^• ⊗ 𝒢^•)^0` for every `n`, and on each `Yᵢ` it is the finite sum
`∑_{n ∈ tᵢ} ηₙ`. -/
theorem coevaluation_exactPairingIhomUnitComplexOfLocallyBounded (K : CochainComplex (Mod R) ℤ)
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y) (t : ι → Finset ℤ)
    (ht : ∀ i, ∀ n ∉ t i, IsZero ((restr R (Y i)).obj (K.X n)))
    (hK : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    letI := exactPairingIhomUnitComplexOfLocallyBounded R K hY t ht hK
    (η_ K ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ)))).f 0 =
        (HomologicalComplex.tensorUnitIso (Mod R) (ComplexShape.up ℤ)).inv 0 ≫
          GradedObject.Monoidal.tensorUnit₀.hom ≫ coevIhomUnitOfLocallyBounded R K hY t ht hK ∧
      (∀ n : ℤ, coevIhomUnitOfLocallyBounded R K hY t ht hK ≫
          GradedObject.Monoidal.πTensorObj K.X ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X
            n (-n) 0 (add_neg_cancel n) =
        (exactPairingIhomComplexX R K n (hK n)).coevaluation') ∧
      ∀ i, (restr R (Y i)).map (coevIhomUnitOfLocallyBounded R K hY t ht hK) =
        (restr R (Y i)).map (GradedObject.Monoidal.totalCoev K.X
          ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))).X (t i)
          (fun n => exactPairingIhomComplexX R K n (hK n))) := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
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
  let : ∀ i, MonoidalCategory (ModSlice R (Y i)) :=
    fun i => (Stacks.SheafOfModules.Strict.monoidalCategory ((R.over (Y i))).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((R.over (Y i)))).property)
  let : ∀ i, MonoidalPreadditive (ModSlice R (Y i)) :=
    fun i => monoidalPreadditiveRingSheaf (R.over (Y i))
  let F : ∀ i, Mod R ⥤ ModSlice R (Y i) := fun i => restr R (Y i)
  let : ∀ i, (F i).Monoidal :=
    fun i => SliceRestriction.overFunctorStrictMonoidal R.obj (isSheaf_ringSheaf R) (Y i)
  let : ∀ i, (F i).Additive := fun i => additive_sliceOverFunctor R (Y i)
  exact ⟨CochainComplex.coevaluation_exactPairingOfSignedMateDualOfLocallyFinite K _
    (fun n => exactPairingIhomComplexX R K n (hK n)) F
    ⟨fun h => SliceRestriction.overFunctor_map_injective hY _ _ h⟩ t ht
    (coevIhomUnitOfLocallyBounded R K hY t ht hK)
    (fun i => restr_map_locallyFiniteTotalCoev R K.X _ _ t hY ht i)
    (isSignedMateDual_ihomUnit R K hK),
    fun n => GradedObject.Monoidal.comp_πTensorObj_of_locallyFinite K.X _
      (fun n => exactPairingIhomComplexX R K n (hK n)) F
      ⟨fun h => SliceRestriction.overFunctor_map_injective hY _ _ h⟩ t ht
      (coevIhomUnitOfLocallyBounded R K hY t ht hK)
      (fun i => restr_map_locallyFiniteTotalCoev R K.X _ _ t hY ht i) n,
    fun i => restr_map_locallyFiniteTotalCoev R K.X _ _ t hY ht i⟩

/-- **The evaluation of `exactPairingIhomUnitComplexOfLocallyBounded` is `ε = ∑ εₙ`**: its
degree-zero component on the summand `𝒢^{-n} ⊗ ℱ^n` of `(𝒢^• ⊗ ℱ^•)^0` is `εₙ`, read through
the identification of the degree zero term of the unit complex with `𝒪`. -/
theorem evaluation_exactPairingIhomUnitComplexOfLocallyBounded (K : CochainComplex (Mod R) ℤ)
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y) (t : ι → Finset ℤ)
    (ht : ∀ i, ∀ n ∉ t i, IsZero ((restr R (Y i)).obj (K.X n)))
    (hK : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n))
    (n : ℤ) :
    letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property
    letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
    letI := monoidalCategoryCochainComplex R
    letI := monoidalClosedCochainComplex R
    letI := exactPairingIhomUnitComplexOfLocallyBounded R K hY t ht hK
    HomologicalComplex.ιTensorObj ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ))) K (-n) n 0
        (neg_add_cancel n) ≫ (ε_ K ((ihom K).obj (𝟙_ (CochainComplex (Mod R) ℤ)))).f 0 =
      (exactPairingIhomComplexX R K n (hK n)).evaluation' ≫
        GradedObject.Monoidal.tensorUnit₀.inv ≫
          (HomologicalComplex.tensorUnitIso (Mod R) (ComplexShape.up ℤ)).hom 0 := by
  let : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  let : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
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
  let : ∀ i, MonoidalCategory (ModSlice R (Y i)) :=
    fun i => (Stacks.SheafOfModules.Strict.monoidalCategory ((R.over (Y i))).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((R.over (Y i)))).property)
  let : ∀ i, MonoidalPreadditive (ModSlice R (Y i)) :=
    fun i => monoidalPreadditiveRingSheaf (R.over (Y i))
  let F : ∀ i, Mod R ⥤ ModSlice R (Y i) := fun i => restr R (Y i)
  let : ∀ i, (F i).Monoidal :=
    fun i => SliceRestriction.overFunctorStrictMonoidal R.obj (isSheaf_ringSheaf R) (Y i)
  let : ∀ i, (F i).Additive := fun i => additive_sliceOverFunctor R (Y i)
  exact CochainComplex.ιTensorObj_comp_evaluation_exactPairingOfSignedMateDualOfLocallyFinite K _
    (fun n => exactPairingIhomComplexX R K n (hK n)) F
    ⟨fun h => SliceRestriction.overFunctor_map_injective hY _ _ h⟩ t ht
    (coevIhomUnitOfLocallyBounded R K hY t ht hK)
    (fun i => restr_map_locallyFiniteTotalCoev R K.X _ _ t hY ht i)
    (isSignedMateDual_ihomUnit R K hK) n

end Stacks.SheafOfModules.Strict

end

end
