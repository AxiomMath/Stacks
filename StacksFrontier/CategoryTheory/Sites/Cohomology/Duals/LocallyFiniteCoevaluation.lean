module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceHomGluing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionComplexMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Homology.DualComplexOfSignedMateDuals

/-!
# The coevaluation of a locally bounded complex, summand by summand

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules with a left dual in
every degree.  When `ℱ^•` is only *locally* bounded — the hypothesis of [Stacks, Tag 0FP9] — the
sum `η = ∑ ηₙ` has only finitely many nonzero terms after restriction to a member of a covering,
so it cannot be written as a global finite sum.  It is constructed by gluing: the local finite
sums agree on every common refinement, because a summand restricts to zero wherever its degree
of `ℱ^•` does, and a compatible family of morphisms of `𝒪`-modules glues
(`Stacks.SheafOfModules.Strict.existsUnique_sheafHom_of_isCompatible`).

## Main results

* `Stacks.SheafOfModules.Strict.isZero_overFunctor_obj_of_arrow`: a module that restricts to zero
  on `V` restricts to zero on every object over `V`, by
  `SheafOfModules.overFunctorMap`.
* `Stacks.SheafOfModules.Strict.isZero_restr_obj_tensor`: the restriction of a tensor product one
  factor of which restricts to zero is a zero object — restriction is monoidal for the tensor
  product of [Stacks, Tag 01CA], so the restriction of `ℱ^n ⊗ 𝒢^{-n}` is the tensor product of
  the restrictions.
* `Stacks.SheafOfModules.Strict.coevSummand`: the summand `ηₙ` of `η`, read into degree zero of
  the graded tensor product.
* `Stacks.SheafOfModules.Strict.restr_map_coevSummand_eq_zero`: **it restricts to zero wherever
  `ℱ^n` does.**  This is what makes two local finite sums over different finite sets of degrees
  agree on a common refinement.
* `Stacks.SheafOfModules.Strict.homRestr_restrFun_map`: relocalizing the restriction of a global
  morphism gives its restriction, which is how a family of restrictions of global morphisms is
  recognised as a compatible family.
* `Stacks.SheafOfModules.Strict.restr_map_coevPartialSum_eq`: two local finite sums agree on a
  common refinement — each extends to the union of the two finite sets of degrees without
  changing.
* `Stacks.SheafOfModules.Strict.locallyFiniteTotalCoev`: **the coevaluation `η = ∑ ηₙ` of a
  locally bounded complex**, with `restr_map_locallyFiniteTotalCoev` identifying it with the
  local finite sum on each member of the covering.  No global `Finset` of degrees is assumed.

## Implementation notes

The summands are taken at the **graded** tensor product rather than at the complex, since that
is where `CategoryTheory.GradedObject.Monoidal.totalCoev` forms the sum and so where a
replacement for it has to live.  Everything is ascribed at
`Stacks.SheafOfModules.Strict.ModSS`, the spelling of `Mod 𝒪` that the restriction functor uses;
the two spellings are definitionally equal but the crossing is not reducible, so `rw` and
instance search do not pass between them and each bridge lemma is restated at this spelling.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Category Limits MonoidalCategory GradedObject
noncomputable section
universe v u
namespace Stacks.SheafOfModules.Strict
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Vanishing after restriction propagates to every object over the base.** -/
theorem isZero_overFunctor_obj_of_arrow {M : Mod R} {V : C}
    (hM : IsZero ((SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) V).obj M))
    {Z : C} (f : Z ⟶ V) :
    IsZero ((SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) Z).obj M) :=
  ((Functor.map_isZero (SheafOfModules.overMap
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj
        (isSheaf_ringSheaf R)) f) hM).of_iso
    ((SheafOfModules.overFunctorMap
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj
        (isSheaf_ringSheaf R)) f).app M).symm)

/-- Abbreviation for the restriction functor on modules. -/
abbrev restr (W : C) := SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W

/-- **The image of a tensor product one factor of which restricts to zero is a zero object.** -/
theorem isZero_restr_obj_tensor (W : C) (A B : ModSS R)
    (hA : IsZero ((restr R W).obj A)) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    IsZero ((restr R W).obj (A ⊗ B)) := by
  let instSrc : MonoidalCategory (ModSS R) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  let instTgt : MonoidalCategory (ModSlice R W) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory ((R.over W)).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf ((R.over W))).property)
  let : @MonoidalPreadditive _ _ _ instTgt := monoidalPreadditiveRingSheaf (R.over W)
  let : @Functor.Monoidal _ _ instSrc _ _ instTgt (restr R W) :=
    SliceRestriction.overFunctorStrictMonoidal R.obj (isSheaf_ringSheaf R) W
  exact (CategoryTheory.ExactPairing.isZero_tensor_of_isZero_left
    ((restr R W).obj A) ((restr R W).obj B) hA).of_iso
      (Functor.Monoidal.μIso (restr R W) A B).symm

section Summand

variable (V W' : GradedObject ℤ (ModSS R))
  (p : ∀ n : ℤ,
    @ExactPairing _ _ ((Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)) (V n) (W' (-n)))

/-- The degree-zero summand of `η = ∑ ηₙ` indexed by `n`, as a morphism of `𝒪`-modules. -/
def coevSummand (n : ℤ) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (𝟙_ (ModSS R)) ⟶ GradedObject.Monoidal.tensorObj V W' 0 :=
  letI _instSrc : MonoidalCategory (ModSS R) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  (p n).coevaluation' ≫ GradedObject.Monoidal.ιTensorObj V W' n (-n) 0 (add_neg_cancel n)

/-- **In a degree where `V` restricts to zero, the summand restricts to zero.** -/
theorem restr_map_coevSummand_eq_zero (W : C) (n : ℤ)
    (hV : IsZero ((restr R W).obj (V n))) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (restr R W).map (coevSummand R V W' p n) = 0 := by
  change (restr R W).map ((p n).coevaluation' ≫ _) = 0
  refine Eq.trans ((restr R W).map_comp _ _) ?_
  rw [(isZero_restr_obj_tensor R W (V n) (W' (-n)) hV).eq_of_tgt
    ((restr R W).map (p n).coevaluation') 0, zero_comp]

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Relocalizing the restriction of a global morphism is its restriction. -/
theorem homRestr_restrFun_map {A B : Mod R} (φ : A.val ⟶ B.val) {Z V : C} (f : Z ⟶ V) :
    homRestr R.obj A.val B.val f ((restrFun R.obj V).map φ) = (restrFun R.obj Z).map φ := rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- `homRestr_restrFun_map` at the spelling the restriction functor uses.  The two spellings of
`Mod 𝒪` are definitionally equal and the crossing is not reducible, so unification inside `rw`
does not pass between them. -/
theorem homRestr_restrFun_map_ss {A B : ModSS R} (φ : A.val ⟶ B.val) {Z V : C} (f : Z ⟶ V) :
    homRestr R.obj A.val B.val f ((restrFun R.obj V).map φ) = (restrFun R.obj Z).map φ := rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- `restrFun_map_val` at the spelling the restriction functor uses. -/
theorem restrFun_map_val_ss (W : C) {A B : ModSS R} (f : A ⟶ B) :
    (restrFun R.obj W).map f.val = ((restr R W).map f).val := rfl

section Glue

variable {ι : Type*} {Y : ι → C} (s : ι → Finset ℤ)

/-- The local finite sum of summands over the degrees surviving on `Y i`, as a *global*
morphism.  Only its restriction to `Y i` is used. -/
def coevPartialSum (i : ι) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (𝟙_ (ModSS R)) ⟶ GradedObject.Monoidal.tensorObj V W' 0 :=
  letI _instSrc : MonoidalCategory (ModSS R) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  ∑ n ∈ s i, coevSummand R V W' p n

/-- **Two local finite sums agree on a common refinement.**  Each sum extends to the union of
the two finite sets of degrees without changing, because the added summands restrict to zero. -/
theorem restr_map_coevPartialSum_eq (hbd : ∀ i : ι, ∀ n ∉ s i,
      IsZero ((restr R (Y i)).obj (V n)))
    (Z : C) (i j : ι) (f : Z ⟶ Y i) (g : Z ⟶ Y j) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (restr R Z).map (coevPartialSum R V W' p s i) =
      (restr R Z).map (coevPartialSum R V W' p s j) := by
  have key : ∀ (k : ι) (h : Z ⟶ Y k) (t : Finset ℤ), s k ⊆ t →
      (restr R Z).map (coevPartialSum R V W' p s k) =
        ∑ n ∈ t, (restr R Z).map (coevSummand R V W' p n) := by
    intro k h t hsub
    refine Eq.trans (Functor.map_sum (restr R Z) _ _) ?_
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    exact restr_map_coevSummand_eq_zero R V W' p Z x
      (isZero_overFunctor_obj_of_arrow R (hbd k x hx) h)
  exact (key i f _ Finset.subset_union_left).trans
    (key j g _ Finset.subset_union_right).symm

/-- The local finite sums, as a family of elements of the internal hom. -/
def coevFamily :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    Presheaf.FamilyOfElementsOnObjects
      ((internalHom R.obj (𝟙_ (ModSS R)).val
        (GradedObject.Monoidal.tensorObj V W' 0).val).presheaf ⋙ CategoryTheory.forget _) Y :=
  letI _instSrc : MonoidalCategory (ModSS R) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  fun i => (restrFun R.obj (Y i)).map (coevPartialSum R V W' p s i).val

/-- **The family of local finite sums is compatible.** -/
theorem isCompatible_coevFamily (hbd : ∀ i : ι, ∀ n ∉ s i,
    IsZero ((restr R (Y i)).obj (V n))) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (coevFamily R V W' p (Y := Y) s).IsCompatible := by
  intro Z i j f g
  change homRestr R.obj _ _ f ((restrFun R.obj (Y i)).map _) =
    homRestr R.obj _ _ g ((restrFun R.obj (Y j)).map _)
  rw [homRestr_restrFun_map_ss, homRestr_restrFun_map_ss, restrFun_map_val_ss,
    restrFun_map_val_ss]
  exact congrArg SheafOfModules.Hom.val
    (restr_map_coevPartialSum_eq R V W' p s hbd Z i j f g)

variable (hY : J.CoversTop Y)
  (hbd : ∀ i : ι, ∀ n ∉ s i, IsZero ((restr R (Y i)).obj (V n)))

/-- **The coevaluation of a locally bounded complex.**  `η = ∑ ηₙ` as a morphism of
`𝒪`-modules, glued from the local finite sums.  No global `Finset` of degrees is assumed: the
finite set of surviving degrees may depend on the member of the covering. -/
def locallyFiniteTotalCoev :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (𝟙_ (ModSS R)) ⟶ GradedObject.Monoidal.tensorObj V W' 0 :=
  letI _instSrc : MonoidalCategory (ModSS R) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  (existsUnique_sheafHom_of_isCompatible_ss R (𝟙_ (ModSS R))
    (GradedObject.Monoidal.tensorObj V W' 0) hY
      (isCompatible_coevFamily R V W' p s hbd)).choose

/-- **On each member of the covering the glued coevaluation is the local finite sum.** -/
theorem restr_map_locallyFiniteTotalCoev (i : ι) :
    letI _instSrc : MonoidalCategory (ModSS R) :=
      (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
    letI : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
      fun _ _ => inferInstance
    (restr R (Y i)).map (locallyFiniteTotalCoev R V W' p s hY hbd) =
      (restr R (Y i)).map (coevPartialSum R V W' p s i) := by
  let _instSrc : MonoidalCategory (ModSS R) :=
    (Stacks.SheafOfModules.Strict.monoidalCategory (R).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (R)).property)
  let : ∀ X₁ X₂ : GradedObject ℤ (ModSS R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  refine SheafOfModules.hom_ext ?_
  rw [← restrFun_map_val_ss, ← restrFun_map_val_ss]
  exact (existsUnique_sheafHom_of_isCompatible_ss R (𝟙_ (ModSS R))
    (GradedObject.Monoidal.tensorObj V W' 0) hY
      (isCompatible_coevFamily R V W' p s hbd)).choose_spec.1 i

end Glue

end Summand

end Stacks.SheafOfModules.Strict
end
end
