module

public import StacksFrontier.CategoryTheory.Graded.GradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DirectSumGrading

/-!
# Correspondences as a graded category over the rationals

Smooth projective schemes over a field, with `Corrʳ(X, Y)` as the degree-`r` morphisms from `X`
to `Y` and with composition of correspondences, form a *graded category over* `ℚ` in the sense
of the chapter on differential graded algebra: an `ℚ`-linear category each of whose morphism
modules is the direct sum of its homogeneous pieces, with identities of degree zero and
composition adding degrees.

Given a family `Corr X Y r` of `ℚ`-vector spaces together with a degree-additive composition
which is `ℚ`-bilinear, associative and unital, this file builds the total morphism module
`⨁ᵣ Corrʳ(X, Y)` and the instances `Category`, `Preadditive`, `Linear ℚ` and
`CategoryTheory.GradedCategory ℚ` on it.

## Main definitions

* `Stacks.WeilCohomology.TotalCorrespondence`: the total morphism module `⨁ᵣ Corrʳ(X, Y)`.
* `Stacks.WeilCohomology.GradedCompositionData`: a `ℚ`-bilinear, degree-additive, associative
  and unital composition law on the degreewise pieces.
* `Stacks.WeilCohomology.GradedCompositionData.Obj`: the objects of the resulting category.
* `Stacks.WeilCohomology.GradedCompositionData.compLinear`: the bilinear extension of the
  degreewise composition to the total morphism modules.

## Main results

* `Stacks.WeilCohomology.GradedCompositionData.category`,
  `Stacks.WeilCohomology.GradedCompositionData.preadditive` and
  `Stacks.WeilCohomology.GradedCompositionData.linear`: the correspondences form an `ℚ`-linear
  category.
* `Stacks.WeilCohomology.GradedCompositionData.gradedCategory`: that category is graded over `ℚ`
  in the sense of Definition 09L2, with `Corrʳ(X, Y)` as its degree-`r` piece.
* `Stacks.WeilCohomology.GradedCompositionData.mem_grade_iff`: the homogeneous morphisms of
  degree `r` are exactly the correspondences of degree `r`.
* `Stacks.WeilCohomology.GradedCompositionData.compLinear_of_of`: on homogeneous morphisms the
  categorical composition is the given composition of correspondences, with degrees adding.

## References

* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 09L2](https://stacks.math.columbia.edu/tag/09L2)
* [Stacks Project, Tag 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public section

open CategoryTheory

universe w u

namespace Stacks.WeilCohomology

variable {C : Type u} (Corr : C → C → ℤ → Type w)
  [∀ X Y : C, ∀ r : ℤ, AddCommGroup (Corr X Y r)]
  [∀ X Y : C, ∀ r : ℤ, Module ℚ (Corr X Y r)]

/-- The total module of correspondences from `X` to `Y`: the direct sum `⨁ᵣ Corrʳ(X, Y)` over
all degrees. -/
abbrev TotalCorrespondence (X Y : C) : Type w :=
  DirectSum ℤ fun r ↦ Corr X Y r

/-- A composition of correspondences: a `ℚ`-bilinear law
`Corrʳ(X, Y) × Corrˢ(Y, Z) → Corr^{r+s}(X, Z)` which is associative and has the degree-zero
diagonal classes as two-sided units. The associativity and unit laws are equalities of images
under `DirectSum.of`, as their two sides lie in pieces of equal but not syntactically equal
degree. -/
structure GradedCompositionData where
  /-- Composition of correspondences; degrees add. -/
  comp : ∀ {X Y Z : C} {r s : ℤ}, Corr X Y r →ₗ[ℚ] Corr Y Z s →ₗ[ℚ] Corr X Z (r + s)
  /-- The diagonal class `[Δ] ∈ Corr⁰(X, X)`. -/
  diagonal : ∀ X : C, Corr X X 0
  /-- The diagonal is a left unit: `[Δ] ∘ c = c`. -/
  of_diagonal_comp : ∀ {X Y : C} {r : ℤ} (a : Corr X Y r),
    DirectSum.of (fun k ↦ Corr X Y k) (0 + r) (comp (diagonal X) a) =
      DirectSum.of (fun k ↦ Corr X Y k) r a
  /-- The diagonal is a right unit: `c ∘ [Δ] = c`. -/
  of_comp_diagonal : ∀ {X Y : C} {r : ℤ} (a : Corr X Y r),
    DirectSum.of (fun k ↦ Corr X Y k) (r + 0) (comp a (diagonal Y)) =
      DirectSum.of (fun k ↦ Corr X Y k) r a
  /-- Composition of correspondences is associative. -/
  of_assoc : ∀ {W X Y Z : C} {r s t : ℤ} (a : Corr W X r) (b : Corr X Y s) (c : Corr Y Z t),
    DirectSum.of (fun k ↦ Corr W Z k) (r + s + t) (comp (comp a b) c) =
      DirectSum.of (fun k ↦ Corr W Z k) (r + (s + t)) (comp a (comp b c))

namespace GradedCompositionData

variable {Corr}

/-- An object of the graded category of correspondences: an object of the ambient family. -/
structure Obj (D : GradedCompositionData Corr) where
  /-- The underlying object. -/
  as : C

variable (D : GradedCompositionData Corr)

/-! ### The bilinear extension of composition -/

/-- Composition with a fixed homogeneous correspondence `a` of degree `r`, as a linear map of
total modules. -/
def compAux (X Y Z : C) (r : ℤ) (a : Corr X Y r) :
    TotalCorrespondence Corr Y Z →ₗ[ℚ] TotalCorrespondence Corr X Z :=
  DirectSum.toModule ℚ ℤ _ fun s ↦
    (DirectSum.lof ℚ ℤ (fun k ↦ Corr X Z k) (r + s)).comp (D.comp a)

/-- Composition with `a` of degree `r` sends `b` in degree `s` to `a ∘ b` in degree `r + s`. -/
@[simp]
theorem compAux_lof (X Y Z : C) (r s : ℤ) (a : Corr X Y r) (b : Corr Y Z s) :
    D.compAux X Y Z r a (DirectSum.lof ℚ ℤ (fun k ↦ Corr Y Z k) s b) =
      DirectSum.lof ℚ ℤ (fun k ↦ Corr X Z k) (r + s) (D.comp a b) :=
  DirectSum.toModule_lof ℚ (φ := fun s ↦
    (DirectSum.lof ℚ ℤ (fun k ↦ Corr X Z k) (r + s)).comp (D.comp a)) s b

/-- Composition with a fixed degree, linear in the first argument. -/
def compAuxLinear (X Y Z : C) (r : ℤ) :
    Corr X Y r →ₗ[ℚ] TotalCorrespondence Corr Y Z →ₗ[ℚ] TotalCorrespondence Corr X Z where
  toFun a := D.compAux X Y Z r a
  map_add' a a' := by
    refine DirectSum.linearMap_ext ℚ fun s ↦ LinearMap.ext fun b ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, compAux_lof, map_add]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℚ fun s ↦ LinearMap.ext fun b ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, compAux_lof, map_smul,
      RingHom.id_apply]

/-- The bilinear extension of composition of correspondences to the total morphism modules. -/
def compLinear (X Y Z : C) :
    TotalCorrespondence Corr X Y →ₗ[ℚ] TotalCorrespondence Corr Y Z →ₗ[ℚ]
      TotalCorrespondence Corr X Z :=
  DirectSum.toModule ℚ ℤ _ fun r ↦ D.compAuxLinear X Y Z r

/-- On homogeneous correspondences the bilinear extension is the given composition, with the
degrees adding. -/
@[simp]
theorem compLinear_of_of {X Y Z : C} {r s : ℤ} (a : Corr X Y r) (b : Corr Y Z s) :
    D.compLinear X Y Z (DirectSum.of (fun k ↦ Corr X Y k) r a)
        (DirectSum.of (fun k ↦ Corr Y Z k) s b) =
      DirectSum.of (fun k ↦ Corr X Z k) (r + s) (D.comp a b) := by
  rw [← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ, compLinear,
    DirectSum.toModule_lof]
  exact D.compAux_lof X Y Z r s a b

/-! ### The category of correspondences -/

/-- The diagonal class is a left unit for the bilinear extension of composition. -/
theorem diagonal_compLinear {X Y : C} (f : TotalCorrespondence Corr X Y) :
    D.compLinear X X Y (DirectSum.of (fun k ↦ Corr X X k) 0 (D.diagonal X)) f = f := by
  induction f using DirectSum.induction_on with
  | zero => exact map_zero _
  | of r a => rw [compLinear_of_of]; exact D.of_diagonal_comp a
  | add f g hf hg => rw [map_add, hf, hg]

/-- The diagonal class is a right unit for the bilinear extension of composition. -/
theorem compLinear_diagonal {X Y : C} (f : TotalCorrespondence Corr X Y) :
    D.compLinear X Y Y f (DirectSum.of (fun k ↦ Corr Y Y k) 0 (D.diagonal Y)) = f := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of r a => rw [compLinear_of_of]; exact D.of_comp_diagonal a
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

/-- The bilinear extension of composition of correspondences is associative. -/
theorem compLinear_assoc {W X Y Z : C} (f : TotalCorrespondence Corr W X)
    (g : TotalCorrespondence Corr X Y) (h : TotalCorrespondence Corr Y Z) :
    D.compLinear W Y Z (D.compLinear W X Y f g) h =
      D.compLinear W X Z f (D.compLinear X Y Z g h) := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => simp only [map_add, LinearMap.add_apply, hf₁, hf₂]
  | of r a =>
      induction g using DirectSum.induction_on with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ => simp only [map_add, LinearMap.add_apply, hg₁, hg₂]
      | of s b =>
          induction h using DirectSum.induction_on with
          | zero => simp
          | add h₁ h₂ hh₁ hh₂ => simp only [map_add, hh₁, hh₂]
          | of t c =>
              rw [compLinear_of_of, compLinear_of_of, compLinear_of_of, compLinear_of_of]
              exact D.of_assoc a b c

/-- The category of correspondences: the given objects, with `⨁ᵣ Corrʳ(X, Y)` as morphisms, the
diagonal class as identity, and the bilinear extension of composition of correspondences as
composition. -/
instance category : Category.{w} D.Obj where
  Hom X Y := TotalCorrespondence Corr X.as Y.as
  id X := DirectSum.of (fun k ↦ Corr X.as X.as k) 0 (D.diagonal X.as)
  comp f g := D.compLinear _ _ _ f g
  id_comp f := D.diagonal_compLinear f
  comp_id f := D.compLinear_diagonal f
  assoc f g h := D.compLinear_assoc f g h

/-- Composition in the category of correspondences is the bilinear extension of composition of
correspondences. -/
theorem comp_eq {X Y Z : D.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = D.compLinear X.as Y.as Z.as f g :=
  rfl

/-- The identity of the category of correspondences is the diagonal class. -/
theorem id_eq (X : D.Obj) :
    𝟙 X = DirectSum.of (fun k ↦ Corr X.as X.as k) 0 (D.diagonal X.as) :=
  rfl

/-- Composing two homogeneous morphisms adds their degrees and composes the correspondences. -/
@[simp]
theorem of_comp_of {X Y Z : D.Obj} {r s : ℤ} (a : Corr X.as Y.as r) (b : Corr Y.as Z.as s) :
    CategoryStruct.comp (X := X) (Y := Y) (Z := Z)
        (DirectSum.of (fun k ↦ Corr X.as Y.as k) r a)
        (DirectSum.of (fun k ↦ Corr Y.as Z.as k) s b) =
      DirectSum.of (fun k ↦ Corr X.as Z.as k) (r + s) (D.comp a b) :=
  D.compLinear_of_of a b

/-! ### The additive and `ℚ`-linear structure -/

/-- Correspondences form a preadditive category: the morphism modules are direct sums of abelian
groups and composition is additive in each variable. -/
instance preadditive : Preadditive D.Obj where
  homGroup X Y := inferInstanceAs (AddCommGroup (TotalCorrespondence Corr X.as Y.as))
  add_comp X Y Z f f' g :=
    DFunLike.congr_fun ((D.compLinear X.as Y.as Z.as).map_add f f') g
  comp_add X Y Z f g g' := (D.compLinear X.as Y.as Z.as f).map_add g g'

/-- Correspondences form an `ℚ`-linear category: the morphism modules are `ℚ`-vector spaces and
composition is `ℚ`-bilinear. -/
instance linear : Linear ℚ D.Obj where
  homModule X Y := inferInstanceAs (Module ℚ (TotalCorrespondence Corr X.as Y.as))
  smul_comp X Y Z c f g :=
    DFunLike.congr_fun ((D.compLinear X.as Y.as Z.as).map_smul c f) g
  comp_smul X Y Z f c g := (D.compLinear X.as Y.as Z.as f).map_smul c g

/-! ### The grading -/

/-- Correspondences form a graded category over `ℚ` in the sense of Definition 09L2: the morphism
module `⨁ᵣ Corrʳ(X, Y)` is the direct sum of its homogeneous pieces `Corrʳ(X, Y)`, the
identity — the diagonal class — is homogeneous of degree zero, and composing correspondences of
degrees `r` and `s` gives one of degree `r + s`. -/
@[stacks 0FG2 "correspondences form a graded category over Q"]
instance gradedCategory : GradedCategory ℚ D.Obj where
  grade X Y :=
    DirectSum.lofRange (R := ℚ) fun r ↦ Corr X.as Y.as r
  decomposition X Y :=
    DirectSum.lofRangeDecomposition (R := ℚ) fun r ↦ Corr X.as Y.as r
  id_mem X := ⟨D.diagonal X.as, DirectSum.lof_eq_of ℚ ℤ _ 0 (D.diagonal X.as)⟩
  comp_mem := by
    rintro X Y Z m n _ _ ⟨b, rfl⟩ ⟨a, rfl⟩
    rw [add_comm m n]
    refine ⟨D.comp a b, ?_⟩
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    exact (D.of_comp_of a b).symm

/-- The homogeneous morphisms of degree `r` in the category of correspondences are exactly the
correspondences of degree `r`. -/
theorem mem_grade_iff {X Y : D.Obj} {r : ℤ} {f : X ⟶ Y} :
    f ∈ GradedCategory.grade (R := ℚ) X Y r ↔
      ∃ a : Corr X.as Y.as r, DirectSum.of (fun k ↦ Corr X.as Y.as k) r a = f := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [← DirectSum.lof_eq_of ℚ]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [DirectSum.lof_eq_of]⟩

end GradedCompositionData

end Stacks.WeilCohomology

end
