module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Graded.Category
public import StacksFrontier.CategoryTheory.Graded.DegreeZero

/-!
# The graded category of graded objects

For a preadditive category `B`, the integer-graded objects of `B` form a category graded over
`ℤ`. Its degree-`n` morphisms from `A` to `C` are arbitrary families of maps `A i ⟶ C (i + n)`,
and a total morphism is a finite sum of homogeneous ones; composition is componentwise on
homogeneous morphisms and is extended bilinearly. The degree-zero part of this graded category is
canonically equivalent to Mathlib's ordinary category of graded objects.

## Main definitions

* `CategoryTheory.GradedObject.zeroDifferentialComplex`: a graded object regarded as a cochain
  complex with zero differentials, which is how its homogeneous morphisms are modelled.
* `CategoryTheory.GradedObject.GradedCategoryData`: a category structure on graded objects
  together with its grading, the direct-sum identification of its morphisms, and the identity and
  composition formulas.
* `CategoryTheory.GradedObject.gradedCategoryData`: the construction of that data.
* `CategoryTheory.GradedObject.degreeZeroCategory`: the degree-zero category of that grading.

## Main results

* `CategoryTheory.GradedObject.degreeZeroEquivalence`: the canonical equivalence of the
  degree-zero category with the ordinary category of graded objects, specified on objects and on
  the components of a morphism.

## Implementation notes

Homogeneous morphisms are Mathlib's `CochainComplex.HomComplex.Cochain` on the complexes with
zero differentials; its indexing condition `i + n = j` is the source's `p + q = n` with `i = -q`
and `j = p`, and it is a product over all `i`, with no support restriction inside a homogeneous
component. Only preadditivity of `B` is used; existence of finite biproducts is not.

The category structure is bundled into `GradedCategoryData` rather than registered globally,
because `GradedObject ℤ B` already carries Mathlib's category structure, whose morphisms are only
the degree-zero families. Clients install the `category`, `preadditive` and `graded` projections
locally, as `degreeZeroCategory` does. The exposed construction and `homEquiv` give direct access
to the direct-sum API, while `mem_grade_iff`, `id_homogeneous` and `comp_homogeneous` give the
grading and the operations without unfolding the construction.

`degreeZeroCategory` installs the degree-zero category of the bundled grading, leaving Mathlib's
ordinary category instance on graded objects untouched; the two instances are then compared by
`degreeZeroEquivalence`, whose statement pins down the functor on objects and on the components
of a morphism.

## References

* [Stacks Project, Tag 09MM](https://stacks.math.columbia.edu/tag/09MM)
-/

@[expose] public section

open CochainComplex.HomComplex

namespace CategoryTheory.GradedObject

universe v u

variable (B : Type u) [Category.{v} B]

/-- Regard a graded object as a cochain complex with zero differentials. -/
@[implicit_reducible, simps, ega "0 11.2.1"]
def zeroDifferentialComplex [Limits.HasZeroMorphisms B] (A : GradedObject ℤ B) :
    CochainComplex B ℤ where
  X := A
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

variable [Preadditive B]

/-- The category of graded objects, including the identification of total morphisms with finite
sums of homogeneous component families and the componentwise composition law. -/
structure GradedCategoryData where
  /-- Total morphisms give a category on integer-graded objects. -/
  category : Category.{v} (GradedObject ℤ B)
  /-- Addition of total morphisms is compatible with composition. -/
  preadditive : @Preadditive (GradedObject ℤ B) category
  /-- The grading on the total morphisms. -/
  graded : @GradedCategory ℤ inferInstance (GradedObject ℤ B) category preadditive
  /-- Total morphisms are the direct sum of the products along all diagonals. -/
  homEquiv (A C : GradedObject ℤ B) :
    @Quiver.Hom (GradedObject ℤ B) category.toQuiver A C ≃ₗ[ℤ]
      DirectSum ℤ (fun n ↦ Cochain (zeroDifferentialComplex B A)
        (zeroDifferentialComplex B C) n)
  /-- The degree-`n` submodule is exactly the summand indexed by `n`. -/
  mem_grade_iff (A C : GradedObject ℤ B) (n : ℤ)
      (f : @Quiver.Hom (GradedObject ℤ B) category.toQuiver A C) :
    f ∈ @GradedCategory.grade ℤ _ _ category preadditive graded A C n ↔
      ∃ c, DirectSum.of _ n c = homEquiv A C f
  /-- The identity is the degree-zero family of component identities. -/
  id_homogeneous (A : GradedObject ℤ B) :
    homEquiv A A (@CategoryStruct.id _ category.toCategoryStruct A) =
      DirectSum.of _ 0 (Cochain.ofHom (𝟙 (zeroDifferentialComplex B A)))
  /-- Homogeneous composition is componentwise composition in the underlying category. -/
  comp_homogeneous {A C D : GradedObject ℤ B} (m n : ℤ)
      (g : Cochain (zeroDifferentialComplex B C) (zeroDifferentialComplex B D) m)
      (f : Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n) :
    homEquiv A D
        (@CategoryStruct.comp (GradedObject ℤ B) category.toCategoryStruct A C D
          ((homEquiv A C).symm (DirectSum.of _ n f))
          ((homEquiv C D).symm (DirectSum.of _ m g))) =
      DirectSum.of _ (n + m) (f.comp g rfl)

/-- The direct sum of homogeneous morphisms of all integer degrees. -/
abbrev TotalHom (A C : GradedObject ℤ B) :=
  DirectSum ℤ (fun n ↦ Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n)

/-- Postcomposition of a fixed homogeneous morphism with an arbitrary total morphism. -/
@[implicit_reducible]
def compHomogeneous {A C D : GradedObject ℤ B} (n : ℤ)
    (f : Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n) :
    TotalHom B C D →+ TotalHom B A D :=
  DirectSum.toAddMonoid fun m ↦
    (DirectSum.of _ (n + m)).comp
      { toFun := fun g ↦ f.comp g rfl
        map_zero' := Cochain.comp_zero _ rfl
        map_add' := fun _ _ ↦ Cochain.comp_add _ _ _ rfl }

/-- Bilinear composition of total morphisms, extending homogeneous composition. -/
@[implicit_reducible]
def totalComp {A C D : GradedObject ℤ B} :
    TotalHom B A C →+ TotalHom B C D →+ TotalHom B A D :=
  DirectSum.toAddMonoid fun n ↦
    { toFun := compHomogeneous B n
      map_zero' := by
        ext m
        simp [compHomogeneous]
      map_add' := by
        intro g g'
        ext m
        simp [compHomogeneous] }

/-- The degree-zero componentwise identity. -/
abbrev totalId (A : GradedObject ℤ B) : TotalHom B A A :=
  DirectSum.of _ 0 (Cochain.ofHom (𝟙 (zeroDifferentialComplex B A)))

private lemma cast_cochain_v {A C : GradedObject ℤ B} {n n' : ℤ} (e : n = n')
    (f : Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n)
    (p q : ℤ) (hpq : p + n' = q) :
    (e ▸ f).v p q hpq = f.v p q (by omega) := by subst n'; rfl

private lemma compDS_of_of {A C D : GradedObject ℤ B} (m n : ℤ)
    (g : Cochain (zeroDifferentialComplex B C) (zeroDifferentialComplex B D) m)
    (f : Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n) :
    totalComp B (DirectSum.of _ n f) (DirectSum.of _ m g) =
      DirectSum.of _ (n + m) (f.comp g rfl) := by simp [totalComp, compHomogeneous]

private lemma compDS_zero_left {A C D : GradedObject ℤ B} (g : TotalHom B C D) :
    totalComp B (0 : TotalHom B A C) g = 0 := map_zero (totalComp B) ▸ rfl

private lemma compDS_add_left {A C D : GradedObject ℤ B}
    (f f' : TotalHom B A C) (g : TotalHom B C D) :
    totalComp B (f + f') g = totalComp B f g + totalComp B f' g :=
  DFunLike.congr_fun (map_add (totalComp B) f f') g

private lemma compDS_zero_right {A C D : GradedObject ℤ B} (f : TotalHom B A C) :
    totalComp B f (0 : TotalHom B C D) = 0 := map_zero (totalComp B f)

private lemma compDS_add_right {A C D : GradedObject ℤ B}
    (f : TotalHom B A C) (g g' : TotalHom B C D) :
    totalComp B f (g + g') = totalComp B f g + totalComp B f g' := map_add (totalComp B f) g g'

/-- The category structure with total morphisms on integer-graded objects. -/
@[instance_reducible]
def totalCategory : Category (GradedObject ℤ B) where
  Hom := TotalHom B
  id := totalId B
  comp := fun f g ↦ totalComp B f g
  id_comp := by
    intro A C f
    induction f using DirectSum.induction_on with
    | zero => exact compDS_zero_right B _
    | of n f =>
      rw [totalId, compDS_of_of]
      apply DirectSum.ext
      intro j
      by_cases hj : n = j
      · subst j
        simp only [DirectSum.of_apply, zero_add, dite_eq_left]
        convert Cochain.id_comp f
        ext p q hpq
        rw [cast_cochain_v]
        exact congrArg (fun e : p + n = q ↦
          ((Cochain.ofHom (𝟙 (zeroDifferentialComplex B A))).comp f (zero_add n)).v p q e)
          (Subsingleton.elim (by omega : p + n = q) hpq)
      · simp [DirectSum.of_apply, hj]
    | add f g hf hg => rw [compDS_add_right, hf, hg]
  comp_id := by
    intro A C f
    induction f using DirectSum.induction_on with
    | zero => exact compDS_zero_left B _
    | of n f =>
      rw [totalId, compDS_of_of]
      apply DirectSum.ext
      intro j
      by_cases hj : n = j
      · subst j
        simp only [DirectSum.of_apply, add_zero, dite_eq_left]
        convert Cochain.comp_id f
        ext p q hpq
        rw [cast_cochain_v]
        exact congrArg (fun e : p + n = q ↦
          (f.comp (Cochain.ofHom (𝟙 (zeroDifferentialComplex B C))) (add_zero n)).v p q e)
          (Subsingleton.elim (by omega : p + n = q) hpq)
      · simp [DirectSum.of_apply, hj]
    | add f g hf hg => rw [compDS_add_left, hf, hg]
  assoc := by
    intro A C D E f g h
    induction f using DirectSum.induction_on with
    | zero => simp only [compDS_zero_left]
    | add f f' hf hf' => rw [compDS_add_left, compDS_add_left, compDS_add_left, hf, hf']
    | of n f =>
      induction g using DirectSum.induction_on with
      | zero => simp only [compDS_zero_right, compDS_zero_left]
      | add g g' hg hg' =>
        rw [compDS_add_right, compDS_add_left, compDS_add_left, compDS_add_right, hg, hg']
      | of m g =>
        induction h using DirectSum.induction_on with
        | zero => simp only [compDS_zero_right]
        | add h h' hh hh' =>
          rw [compDS_add_right, compDS_add_right, compDS_add_right, hh, hh']
        | of k h =>
          rw [compDS_of_of, compDS_of_of, compDS_of_of, compDS_of_of]
          apply DirectSum.ext
          intro j
          by_cases hj : n + (m + k) = j
          · subst j
            simp only [DirectSum.of_apply, add_assoc, dite_eq_left]
            convert Cochain.comp_assoc f g h rfl rfl (add_assoc n m k)
            ext p q hpq
            rw [cast_cochain_v]
            exact congrArg (fun e : p + (n + m + k) = q ↦
              ((f.comp g rfl).comp h (by omega)).v p q e)
              (Subsingleton.elim (by omega : p + (n + m + k) = q) (by omega))
          · have hj' : n + m + k ≠ j := by simpa only [add_assoc] using hj
            simp [DirectSum.of_apply, hj, hj']

/-- The preadditive structure on total morphisms. -/
@[instance_reducible]
def totalPreadditive : @Preadditive (GradedObject ℤ B) (totalCategory B) := by
  letI := totalCategory B
  exact
    { homGroup := fun A C ↦ inferInstanceAs (AddCommGroup (TotalHom B A C))
      add_comp := by intros; exact compDS_add_left B _ _ _
      comp_add := by intros; exact compDS_add_right B _ _ _ }

/-- The submodule of total morphisms supported in one degree. -/
abbrev homogeneousSubmodule (A C : GradedObject ℤ B) (n : ℤ) :
    Submodule ℤ (TotalHom B A C) :=
  LinearMap.range (DirectSum.lof ℤ ℤ
    (fun n ↦ Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n) n)

/-- A homogeneous component is linearly equivalent to its image among total morphisms. -/
@[implicit_reducible]
noncomputable def homogeneousEquiv (A C : GradedObject ℤ B) (n : ℤ) :
    Cochain (zeroDifferentialComplex B A) (zeroDifferentialComplex B C) n ≃ₗ[ℤ]
      homogeneousSubmodule B A C n :=
  LinearEquiv.ofInjective (DirectSum.lof ℤ ℤ _ n) fun _ _ h ↦ DirectSum.of_injective n h

/-- The direct-sum decomposition of total morphisms into homogeneous submodules. -/
@[instance_reducible]
noncomputable def homDecomposition (A C : GradedObject ℤ B) :
    DirectSum.Decomposition (homogeneousSubmodule B A C) := by
  let e := DirectSum.congrLinearEquiv (fun n ↦ homogeneousEquiv B A C n)
  have h : DirectSum.coeLinearMap (homogeneousSubmodule B A C) ∘ₗ e.toLinearMap =
      LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, e, DirectSum.congrLinearEquiv_toLinearMap,
      DirectSum.lmap_lof, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
    rfl
  refine DirectSum.Decomposition.ofLinearMap (ℳ := homogeneousSubmodule B A C)
    e.toLinearMap h (LinearMap.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := e.surjective y
  change e (DirectSum.coeLinearMap (homogeneousSubmodule B A C) (e x)) = e x
  exact congrArg e (DFunLike.congr_fun h x)

/-- The integer grading of the category of total morphisms. -/
@[instance_reducible]
noncomputable def totalGrading :
    @GradedCategory ℤ inferInstance (GradedObject ℤ B)
      (totalCategory B) (totalPreadditive B) := by
  letI := totalCategory B
  letI := totalPreadditive B
  letI : Linear ℤ (GradedObject ℤ B) := Linear.preadditiveIntLinear
  exact
    { toLinear := inferInstance
      grade := homogeneousSubmodule B
      decomposition := homDecomposition B
      id_mem := fun A ↦ ⟨Cochain.ofHom (𝟙 (zeroDifferentialComplex B A)), rfl⟩
      comp_mem := by
        intro A C D m n g f hg hf
        rcases hg with ⟨g, rfl⟩
        rcases hf with ⟨f, rfl⟩
        rw [add_comm m n]
        refine ⟨f.comp g rfl, ?_⟩
        exact (compDS_of_of B m n g f).symm }

/-- The graded category of integer-graded objects in a preadditive category. -/
@[implicit_reducible, stacks 09MM "graded_category_of_graded_objects"]
noncomputable def gradedCategoryData : GradedCategoryData B where
  category := totalCategory B
  preadditive := totalPreadditive B
  graded := totalGrading B
  homEquiv A C := LinearEquiv.refl ℤ (TotalHom B A C)
  mem_grade_iff _ _ _ _ := Iff.rfl
  id_homogeneous _ := rfl
  comp_homogeneous := by intros; exact compDS_of_of B _ _ _ _

/-- The degree-zero category of the bundled graded category of graded objects. -/
@[instance_reducible]
noncomputable def degreeZeroCategory :
    Category.{v} (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) := by
  letI : Category.{v} (GradedObject ℤ B) := (gradedCategoryData B).category
  letI : Preadditive (GradedObject ℤ B) := (gradedCategoryData B).preadditive
  letI : GradedCategory ℤ (GradedObject ℤ B) := (gradedCategoryData B).graded
  infer_instance

/-- Degree-zero homogeneous maps of graded objects are precisely the componentwise maps: the
degree-zero category of the graded category of graded objects is canonically equivalent to the
ordinary category of graded objects. -/
@[stacks 09MM]
noncomputable def degreeZeroEquivalence :
    { E : @CategoryTheory.Equivalence
        (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) (GradedObject ℤ B)
        (degreeZeroCategory B) (GradedObject.categoryOfGradedObjects ℤ) //
      let F := @CategoryTheory.Equivalence.functor
        (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) (GradedObject ℤ B)
        (degreeZeroCategory B) (GradedObject.categoryOfGradedObjects ℤ) E
      (∀ X : GradedCategory.DegreeZero ℤ (GradedObject ℤ B),
        @CategoryTheory.Functor.obj _ (degreeZeroCategory B) _
          (GradedObject.categoryOfGradedObjects ℤ) F X = X) ∧
      (∀ (X Y : GradedCategory.DegreeZero ℤ (GradedObject ℤ B))
          (f : @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y) (i : ℤ),
        HEq ((@CategoryTheory.Functor.map _ (degreeZeroCategory B) _
          (GradedObject.categoryOfGradedObjects ℤ) F X Y f) i)
          (((DirectSum.component ℤ ℤ
            (fun n ↦ Cochain
              (zeroDifferentialComplex B X)
              (zeroDifferentialComplex B Y) n) 0)
            ((gradedCategoryData B).homEquiv X Y f.1)).v
              i i (add_zero i))) } := by
  let G := gradedCategoryData B
  letI : Category.{v} (GradedObject ℤ B) := G.category
  letI : Preadditive (GradedObject ℤ B) := G.preadditive
  letI : GradedCategory ℤ (GradedObject ℤ B) := G.graded
  letI : Linear ℤ B := Linear.preadditiveIntLinear
  letI : Category.{v} (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) :=
    degreeZeroCategory B
  letI : Category.{max 0 v} (CochainComplex B ℤ) := inferInstance
  letI : Linear ℤ (CochainComplex B ℤ) := Linear.preadditiveIntLinear
  letI : Limits.HasZeroMorphisms B := inferInstance
  let zeroC (X : GradedObject ℤ B) := zeroDifferentialComplex B X
  let compFamily {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (GradedObject.categoryOfGradedObjects ℤ).toQuiver X Y) :
      Cochain (zeroC X) (zeroC Y) 0 :=
    Cochain.ofHom
      { f := f, comm' := fun _ _ _ ↦ by simp [zeroC, zeroDifferentialComplex] }
  let rep {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y) :
      Cochain (zeroC X) (zeroC Y) 0 :=
    Classical.choose ((G.mem_grade_iff X Y 0 f.1).mp f.2)
  let repSpec {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y) :
      DirectSum.of _ 0 (rep f) = G.homEquiv X Y f.1 :=
    Classical.choose_spec ((G.mem_grade_iff X Y 0 f.1).mp f.2)
  let componentMap {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y) :
      @Quiver.Hom _ (GradedObject.categoryOfGradedObjects ℤ).toQuiver X Y :=
    fun i => ((DirectSum.component ℤ ℤ
      (fun n ↦ Cochain (zeroC X) (zeroC Y) n) 0)
      (G.homEquiv X Y f.1)).v i i (add_zero i)
  let componentMapId : ∀ X : GradedObject ℤ B,
      componentMap (@CategoryStruct.id _
        (degreeZeroCategory B).toCategoryStruct X) =
        @CategoryStruct.id _ (GradedObject.categoryOfGradedObjects ℤ).toCategoryStruct X := by
    intro X
    funext i
    change ((DirectSum.component ℤ ℤ
      (fun n ↦ Cochain (zeroC X) (zeroC X) n) 0)
      (G.homEquiv X X (@CategoryStruct.id _ G.category.toCategoryStruct X))).v i i
      (add_zero i) = 𝟙 (X i)
    rw [G.id_homogeneous, ← DirectSum.lof_eq_of (R := ℤ)]
    simp [zeroC, zeroDifferentialComplex, DirectSum.component.lof_self]
  let componentMapComp : ∀ {X Y Z : GradedObject ℤ B}
      (f : @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y)
      (g : @Quiver.Hom _ (degreeZeroCategory B).toQuiver Y Z),
      componentMap ((degreeZeroCategory B).toCategoryStruct.comp f g) =
        (GradedObject.categoryOfGradedObjects ℤ).toCategoryStruct.comp
          (componentMap f) (componentMap g) := by
    intro X Y Z f g
    funext i
    have hf : (G.homEquiv X Y).symm (DirectSum.of _ 0 (rep f)) = f.1 := by
      simpa using congrArg (G.homEquiv X Y).symm (repSpec f)
    have hg : (G.homEquiv Y Z).symm (DirectSum.of _ 0 (rep g)) = g.1 := by
      simpa using congrArg (G.homEquiv Y Z).symm (repSpec g)
    change ((DirectSum.component ℤ ℤ
      (fun n ↦ Cochain (zeroC X) (zeroC Z) n) 0)
      (G.homEquiv X Z (G.category.toCategoryStruct.comp f.1 g.1))).v i i
      (add_zero i) =
        (((DirectSum.component ℤ ℤ
          (fun n ↦ Cochain (zeroC X) (zeroC Y) n) 0)
          (G.homEquiv X Y f.1)).v i i (add_zero i)) ≫
        (((DirectSum.component ℤ ℤ
          (fun n ↦ Cochain (zeroC Y) (zeroC Z) n) 0)
          (G.homEquiv Y Z g.1)).v i i (add_zero i))
    rw [← hf, ← hg, G.comp_homogeneous 0 0 (rep g) (rep f)]
    simp only [← DirectSum.lof_eq_of (R := ℤ)]
    simp [zeroC, zeroDifferentialComplex]
  let toHom {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (GradedObject.categoryOfGradedObjects ℤ).toQuiver X Y) :
      @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y :=
    ⟨(G.homEquiv X Y).symm (DirectSum.of _ 0 (compFamily f)),
      (G.mem_grade_iff X Y 0 _).mpr ⟨compFamily f, rfl⟩⟩
  let toHomId : ∀ X : GradedObject ℤ B,
      toHom ((GradedObject.categoryOfGradedObjects ℤ).toCategoryStruct.id X) =
        (degreeZeroCategory B).toCategoryStruct.id X := by
    intro X
    apply Subtype.ext
    apply (G.homEquiv X X).injective
    change DirectSum.of _ 0 (compFamily
      ((GradedObject.categoryOfGradedObjects ℤ).toCategoryStruct.id X)) =
      G.homEquiv X X (@CategoryStruct.id _ G.category.toCategoryStruct X)
    rw [G.id_homogeneous]
    congr 1
  let toHomComp : ∀ {X Y Z : GradedObject ℤ B}
      (f : @Quiver.Hom _ (GradedObject.categoryOfGradedObjects ℤ).toQuiver X Y)
      (g : @Quiver.Hom _ (GradedObject.categoryOfGradedObjects ℤ).toQuiver Y Z),
      toHom ((GradedObject.categoryOfGradedObjects ℤ).toCategoryStruct.comp f g) =
        (degreeZeroCategory B).toCategoryStruct.comp (toHom f) (toHom g) := by
    intro X Y Z f g
    apply Subtype.ext
    apply (G.homEquiv X Z).injective
    change DirectSum.of _ 0 (compFamily
        ((GradedObject.categoryOfGradedObjects ℤ).toCategoryStruct.comp f g)) =
      G.homEquiv X Z (G.category.toCategoryStruct.comp
        ((G.homEquiv X Y).symm (DirectSum.of _ 0 (compFamily f)))
        ((G.homEquiv Y Z).symm (DirectSum.of _ 0 (compFamily g))))
    rw [G.comp_homogeneous 0 0 (compFamily g) (compFamily f)]
    congr 1
    ext i
    simp [compFamily, zeroC, zeroDifferentialComplex]
  let componentMapToHom : ∀ {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (GradedObject.categoryOfGradedObjects ℤ).toQuiver X Y),
      componentMap (toHom f) = f := by
    intro X Y f
    funext i
    simp [componentMap, toHom, DirectSum.component.lof_self,
      ← DirectSum.lof_eq_of (R := ℤ), compFamily, zeroC, zeroDifferentialComplex]
  let toHomComponentMap : ∀ {X Y : GradedObject ℤ B}
      (f : @Quiver.Hom _ (degreeZeroCategory B).toQuiver X Y),
      toHom (componentMap f) = f := by
    intro X Y f
    apply Subtype.ext
    apply (G.homEquiv X Y).injective
    change DirectSum.of _ 0 (compFamily (componentMap f)) = G.homEquiv X Y f.1
    rw [← repSpec f]
    congr 1
    ext i
    simp only [compFamily, Cochain.ofHom_v]
    change ((DirectSum.component ℤ ℤ
      (fun n ↦ Cochain (zeroC X) (zeroC Y) n) 0)
      (G.homEquiv X Y f.1)).v i i (add_zero i) = (rep f).v i i (add_zero i)
    rw [← repSpec f]
    simp [← DirectSum.lof_eq_of (R := ℤ)]
  letI : Category.{v} (GradedObject ℤ B) := GradedObject.categoryOfGradedObjects ℤ
  let F : @CategoryTheory.Functor
      (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) (degreeZeroCategory B)
      (GradedObject ℤ B) (GradedObject.categoryOfGradedObjects ℤ) := {
    obj X := X
    map := componentMap
    map_id := componentMapId
    map_comp := componentMapComp }
  let H : @CategoryTheory.Functor
      (GradedObject ℤ B) (GradedObject.categoryOfGradedObjects ℤ)
      (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) (degreeZeroCategory B) := {
    obj X := X
    map := toHom
    map_id := toHomId
    map_comp := toHomComp }
  let η : (@CategoryTheory.Functor.id _ (degreeZeroCategory B)) ≅ (F ⋙ H) :=
    NatIso.ofComponents (fun X => Iso.refl X)
      (by
        intro X Y f
        simpa [F, H] using (toHomComponentMap f).symm)
  let ε : (H ⋙ F) ≅ (@CategoryTheory.Functor.id _ (GradedObject.categoryOfGradedObjects ℤ)) :=
    NatIso.ofComponents (fun X => Iso.refl X)
      (by
        intro X Y f
        simpa [F, H] using componentMapToHom f)
  let E : @CategoryTheory.Equivalence
      (GradedCategory.DegreeZero ℤ (GradedObject ℤ B)) (GradedObject ℤ B)
      (degreeZeroCategory B) (GradedObject.categoryOfGradedObjects ℤ) :=
    { functor := F
      inverse := H
      unitIso := η
      counitIso := ε
      functor_unitIso_comp := by
        intro X
        simp [F, H, η, ε, componentMapId, NatIso.ofComponents_hom_app, Iso.refl_hom] }
  exact ⟨E, fun _ => rfl, fun _ _ _ _ => HEq.rfl⟩

end CategoryTheory.GradedObject
