module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.RigidJointlyFaithful

/-!
# Restriction to a slice site, on complexes of modules, is monoidal

Let `(C, 𝒪)` be a ringed site.  Restriction of sheaves of `𝒪`-modules to the slice site over an
object `W` is monoidal for the tensor product of [Stacks, Tag 01CA]
(`Stacks.SheafOfModules.SliceRestriction.overFunctorStrictMonoidal`).  This file carries that up
to complexes: the degreewise restriction functor on `CochainComplex (Mod 𝒪) ℤ` is monoidal for
the total tensor product of [Stacks, Tag 0FPQ], and the family of restrictions to the members of
a covering family is jointly faithful.

Those two facts are exactly the hypotheses of
`CategoryTheory.ExactPairing.ofJointlyFaithful`, which is how a statement about left duals of
complexes is reduced to the same statement on the members of a covering.  Before this file
`ofJointlyFaithful` could only be fed the module-level restriction
(`Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective` is the module-level joint
faithfulness), so it was unusable for complexes.

## Main definitions

* `Stacks.SheafOfModules.Strict.restrictComplexFunctor`: `ℱ^• ↦ ℱ^•|_W`, degreewise.
* `Stacks.SheafOfModules.Strict.restrictComplexMonoidal`: **it is monoidal.**

## Main results

* `Stacks.SheafOfModules.Strict.jointlyFaithful_restrictComplexFunctor`: the restrictions to the
  members of a family covering the final object are jointly faithful on complexes.

## Implementation notes

**Three spellings of one category.**  `Mod 𝒪` is `SheafOfModules (Tensor.ringSheaf 𝒪)`, with
`Tensor.ringSheaf` a *reducible* abbreviation, while the restriction functor is stated at
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, a plain definition, and its target
at `Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf`.  All three are definitionally
equal and none of the crossings is reducible, so instance search does not pass between them.
`ModSS` and `ModSlice` name the two spellings the restriction functor uses, and every instance
the monoidal structure on complexes needs is ascribed at those spellings, the definitional
equality crossing at each `:=`.  The two `Functor.Additive` instances of the curried tensor are
pinned as local hypotheses rather than left to synthesis: they resolve where they are stated and
not at the end of the `letI` block.

**What supplies the colimit hypothesis.**  `CategoryTheory.Functor.mapHomologicalComplexMonoidal`
asks that the functor preserve the antidiagonal coproducts of the total complex, which for
`ComplexShape.up ℤ` are indexed by an infinite set, so the finite-coproduct preservation of
`Stacks.SheafOfModules.SliceFinite.preservesColimitsOfShape_discrete_overFunctor` does not
suffice; what does is `Stacks.SheafOfModules.overFunctor_preservesColimits`, shrunk to the
needed universe.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
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

/-- Restriction of `𝒪`-modules to the slice site over `W` is additive. -/
instance additive_sliceOverFunctor (W : C) :
    (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W).Additive where
  map_add := by intros; rfl

/-- Restriction of `𝒪`-modules to the slice site over `W` preserves all colimits of size
`max u v`. -/
instance preservesColimitsOfSize_sliceOverFunctor (W : C) :
    PreservesColimitsOfSize.{max u v, max u v}
      (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W) :=
  Stacks.SheafOfModules.overFunctor_preservesColimits
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj (isSheaf_ringSheaf R)) W

/-- **Restriction of a complex of `𝒪`-modules to the slice site over `W`**, degreewise. -/
def restrictComplexFunctor (W : C) :
    CochainComplex (Mod R) ℤ ⥤ CochainComplex (Mod (R.over W)) ℤ :=
  (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The antidiagonal coproducts of the total tensor complex are preserved by restriction. -/
instance preservesColimitsOfShape_antidiagonal (W : C) (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W) := by
  have : PreservesColimitsOfSize.{0, 0}
      (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W) :=
    preservesColimitsOfSize_shrink _
  infer_instance

/-- Abbreviation for the source category at the spelling the restriction functor names it. -/
abbrev ModSS := SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj (isSheaf_ringSheaf R))

/-- Abbreviation for the slice category at the spelling the restriction functor names it. -/
abbrev ModSlice (W : C) := SheafOfModules.{max u v}
  (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf R.obj (isSheaf_ringSheaf R) W)

/-- **Restriction to a slice site is a monoidal functor on complexes.** -/
@[instance_reducible]
def restrictComplexMonoidal (W : C) :
    letI := monoidalCategoryCochainComplex R
    letI := monoidalCategoryCochainComplex (R.over W)
    (restrictComplexFunctor R W).Monoidal := by
  letI instSrc : MonoidalCategory (ModSS R) :=
    monoidalCategory R.obj (isSheaf_ringSheaf R)
  letI instTgt : MonoidalCategory (ModSlice R W) :=
    monoidalCategory (R.over W).obj (isSheaf_ringSheaf (R.over W))
  letI : @MonoidalPreadditive _ _ _ instSrc := monoidalPreadditiveRingSheaf R
  letI : @MonoidalPreadditive _ _ _ instTgt := monoidalPreadditiveRingSheaf (R.over W)
  letI : (curriedTensor (ModSS R)).Additive := inferInstance
  letI : ∀ X₁ : ModSS R, ((curriedTensor (ModSS R)).obj X₁).Additive := fun _ => inferInstance
  letI : (curriedTensor (ModSlice R W)).Additive := inferInstance
  letI : ∀ X₁ : ModSlice R W, ((curriedTensor (ModSlice R W)).obj X₁).Additive :=
    fun _ => inferInstance
  letI : ∀ X₁ : ModSS R, PreservesColimit (Functor.empty.{0} (ModSS R))
      ((curriedTensor (ModSS R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : ModSS R, PreservesColimit (Functor.empty.{0} (ModSS R))
      ((curriedTensor (ModSS R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (ModSS R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (ModSS R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (ModSS R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  letI : ∀ X₁ : ModSlice R W, PreservesColimit (Functor.empty.{0} (ModSlice R W))
      ((curriedTensor (ModSlice R W)).obj X₁) :=
    fun X₁ => preservesColimit_tensorLeft (R.over W) _ X₁
  letI : ∀ X₂ : ModSlice R W, PreservesColimit (Functor.empty.{0} (ModSlice R W))
      ((curriedTensor (ModSlice R W)).flip.obj X₂) :=
    fun X₂ => preservesColimit_tensorRight (R.over W) _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (ModSlice R W),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor (R.over W)
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (ModSlice R W),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ (R.over W)
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (ModSlice R W),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt (R.over W)
  letI : @Functor.Monoidal _ _ instSrc _ _ instTgt
      (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W) :=
    SliceRestriction.overFunctorStrictMonoidal R.obj (isSheaf_ringSheaf R) W
  exact Functor.mapHomologicalComplexMonoidal
    (C := ModSS R) (D := ModSlice R W) (c := ComplexShape.up ℤ)
    (SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **The restrictions to the members of a covering family are jointly faithful on complexes.**
Two morphisms of complexes agree as soon as they agree in each degree, and in each degree the
module-level statement is `overFunctor_map_injective`. -/
theorem jointlyFaithful_restrictComplexFunctor {ι : Type*} {V : ι → C} (hV : J.CoversTop V) :
    JointlyFaithful (fun i => restrictComplexFunctor R (V i)) where
  map_injective {K L} f g h := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    refine SliceRestriction.overFunctor_map_injective hV (f.f n) (g.f n) (fun i => ?_)
    exact congrArg (fun φ : (restrictComplexFunctor R (V i)).obj K ⟶
      (restrictComplexFunctor R (V i)).obj L => φ.f n) (h i)

end Stacks.SheafOfModules.Strict
end
end
