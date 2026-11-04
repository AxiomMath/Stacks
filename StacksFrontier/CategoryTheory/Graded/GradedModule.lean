module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.GradedModule.ExternalShift
public import StacksFrontier.CategoryTheory.Graded.Category
public import StacksFrontier.CategoryTheory.Graded.DegreeZero
public import StacksFrontier.Algebra.DGA.DirectSumGrading

/-!
# The graded category of graded modules

For an externally `ℤ`-graded algebra `𝒜` over a commutative ring `R`, the graded right
`𝒜`-modules are the objects of a category graded over `R`: a degree-`n` morphism is a right
`𝒜`-linear map of the underlying modules raising degrees by `n`, and a morphism is a finite sum
of homogeneous ones. The degree-zero part of this graded category is the ordinary category of
graded right modules and degree-preserving maps.

## Main definitions

* `ExternallyGraded.RightModuleCat`: the object type of the graded category.
* `ExternallyGraded.RightModuleCat.homogeneousMapSubmodule`: the `R`-module of degree-`n` right
  `𝒜`-linear maps, and `ExternallyGraded.RightModuleCat.HomogeneousMap` its elements.
* `ExternallyGraded.RightModuleCat.GradedHom`: a morphism, i.e. a finite sum of homogeneous maps.

## Main results

* `ExternallyGraded.RightModuleCat.instCategory`, `instPreadditive`, `instLinear` and
  `instGradedCategory`: the category, its additive and `R`-linear structure, and its grading.
* `ExternallyGraded.RightModuleCat.degreeZeroHomEquiv`: the identification of degree-zero
  morphisms with degree-zero homogeneous maps, through their underlying maps on direct sums.
* `ExternallyGraded.RightModuleCat.degreeZeroHomEquiv_id` and
  `ExternallyGraded.RightModuleCat.degreeZeroHomEquiv_comp`: that identification respects
  categorical identities and composition, so it identifies the degree-zero category with the
  ordinary category of graded right modules.

## Implementation notes

The objects are `ExternallyGradedRightModule 𝒜`, whose underlying module is the direct sum of its
pieces; `RightModuleCat` is a type synonym so that it can carry the category structure with all
finite sums of homogeneous maps as morphisms, rather than only the degree-preserving ones. Right
linearity is expressed by commuting with right multiplication by every homogeneous algebra
element, and carries no sign. A morphism is a `DirectSum` of the submodules of homogeneous maps,
which records exactly the finite-support condition of the source. Evaluation by `toLinearMap`
comes with simp lemmas for homogeneous inclusions, identities and composition, so that clients
need never unfold the direct sum. As in the source, the base ring is commutative while the graded
algebra need not be.

## References

* [Stacks Project, Tag 09MN](https://stacks.math.columbia.edu/tag/09MN)
-/

@[expose] public section

open CategoryTheory

namespace ExternallyGraded

universe u v w

variable {R : Type u} [CommRing R] (𝒜 : ExternallyGradedAlgebra.{u, v} R)

/-- The object type of the graded category of graded right modules. This is a type synonym so
that its category structure can have all finite sums of homogeneous maps as morphisms. -/
def RightModuleCat := ExternallyGradedRightModule.{u, v, w} 𝒜

namespace RightModuleCat

variable {𝒜}

/-- Each homogeneous piece of a graded right module is an additive commutative group. -/
instance (M : RightModuleCat 𝒜) (i : ℤ) : AddCommGroup (M.piece i) :=
  ExternallyGradedRightModule.addCommGroup M i

/-- Each homogeneous piece of a graded right module is an `R`-module. -/
instance (M : RightModuleCat 𝒜) (i : ℤ) : Module R (M.piece i) :=
  ExternallyGradedRightModule.module M i

/-- The underlying module of an externally graded module. -/
abbrev Total (M : RightModuleCat 𝒜) := DirectSum ℤ M.piece

/-- The homogeneous piece, viewed inside the underlying module. -/
abbrev grade (M : RightModuleCat 𝒜) (i : ℤ) : Submodule R M.Total :=
  LinearMap.range (DirectSum.lof R ℤ M.piece i)

/-- Right multiplication by a homogeneous algebra element on the underlying module. -/
@[implicit_reducible]
def rightMul (M : RightModuleCat 𝒜) (j : ℤ) (a : 𝒜.piece j) : M.Total →ₗ[R] M.Total :=
  DirectSum.toModule R ℤ _ fun i ↦
    (DirectSum.lof R ℤ M.piece (i + j)).comp ((M.smul i j).flip a)

/-- Right multiplication by `a` of degree `j` sends the image of `x` of degree `i` to the image
of `x * a` in degree `i + j`. -/
@[simp]
theorem rightMul_of (M : RightModuleCat 𝒜) (j : ℤ) (a : 𝒜.piece j) (i : ℤ) (x : M.piece i) :
    rightMul M j a (DirectSum.of _ i x) = DirectSum.of _ (i + j) (M.smul i j x a) :=
  DirectSum.toModule_lof R i x

/-- The degree-`n` right `𝒜`-linear maps between graded right modules. -/
@[stacks 09MN "graded_category_of_graded_modules"]
def homogeneousMapSubmodule (M N : RightModuleCat 𝒜) (n : ℤ) :
    Submodule R (M.Total →ₗ[R] N.Total) where
  carrier := { f | (∀ i x, x ∈ M.grade i → f x ∈ N.grade (i + n)) ∧
    (∀ j (a : 𝒜.piece j) x, f (rightMul M j a x) = rightMul N j a (f x)) }
  zero_mem' := ⟨fun i _ _ ↦ (N.grade (i + n)).zero_mem, fun _ _ _ ↦ by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨fun i x hx ↦ (N.grade (i + n)).add_mem (hf.1 i x hx) (hg.1 i x hx),
      fun j a x ↦ by simp [hf.2 j a x, hg.2 j a x]⟩
  smul_mem' := by
    intro r f hf
    exact ⟨fun i x hx ↦ (N.grade (i + n)).smul_mem r (hf.1 i x hx),
      fun j a x ↦ by simp [hf.2 j a x]⟩

/-- A linear map is homogeneous of degree `n` if and only if it sends each degree-`i` piece into
the degree-`i + n` piece and commutes with right multiplication by homogeneous elements. -/
@[simp]
theorem mem_homogeneousMapSubmodule {M N : RightModuleCat 𝒜} {n : ℤ}
    {f : M.Total →ₗ[R] N.Total} : f ∈ homogeneousMapSubmodule M N n ↔
      ((∀ i x, x ∈ M.grade i → f x ∈ N.grade (i + n)) ∧
        (∀ j (a : 𝒜.piece j) x, f (rightMul M j a x) = rightMul N j a (f x))) := Iff.rfl

/-- A homogeneous right `𝒜`-linear map of degree `n`. -/
abbrev HomogeneousMap (M N : RightModuleCat 𝒜) (n : ℤ) := homogeneousMapSubmodule M N n

/-- Homogeneous maps of degree `n` form an additive commutative group. -/
instance (M N : RightModuleCat 𝒜) (n : ℤ) : AddCommGroup (HomogeneousMap M N n) :=
  (homogeneousMapSubmodule M N n).addCommGroup

/-- A homogeneous map sends the degree-`i` piece into the degree-`i + n` piece. -/
theorem HomogeneousMap.map_grade {M N : RightModuleCat 𝒜} {n i : ℤ}
    (f : HomogeneousMap M N n) {x : M.Total} (hx : x ∈ M.grade i) :
    f.1 x ∈ N.grade (i + n) := f.2.1 i x hx

/-- A homogeneous map is right-linear, without a sign in the action. -/
@[simp]
theorem HomogeneousMap.map_rightMul {M N : RightModuleCat 𝒜} {n : ℤ}
    (f : HomogeneousMap M N n) (j : ℤ) (a : 𝒜.piece j) (x : M.Total) :
    f.1 (rightMul M j a x) = rightMul N j a (f.1 x) := f.2.2 j a x

/-- Morphisms in the graded module category are finite sums of homogeneous maps. -/
@[ega "II 2.1.2" "Hom_S(M"]
abbrev GradedHom (M N : RightModuleCat 𝒜) := DirectSum ℤ (fun n ↦ HomogeneousMap M N n)

/-- Evaluate a finite sum of homogeneous maps as a linear map on underlying modules. -/
@[implicit_reducible]
def toLinearMap (M N : RightModuleCat 𝒜) :
    GradedHom M N →ₗ[R] (M.Total →ₗ[R] N.Total) :=
  DirectSum.toModule R ℤ _ fun n ↦ (homogeneousMapSubmodule M N n).subtype

/-- The single homogeneous summand `f` evaluates to the underlying linear map of `f`. -/
@[simp]
theorem toLinearMap_of {M N : RightModuleCat 𝒜} {n : ℤ} (f : HomogeneousMap M N n) :
    toLinearMap M N (DirectSum.of _ n f) = f.1 :=
  DirectSum.toModule_lof R (φ := fun k ↦ (homogeneousMapSubmodule M N k).subtype) n f

/-- Composition of homogeneous maps; degrees add. -/
@[implicit_reducible]
def HomogeneousMap.comp {M N P : RightModuleCat 𝒜} {m n : ℤ}
    (f : HomogeneousMap M N m) (g : HomogeneousMap N P n) : HomogeneousMap M P (m + n) :=
  ⟨g.1.comp f.1, fun i x hx ↦ by
      simpa only [LinearMap.comp_apply, add_assoc] using g.2.1 (i + m) (f.1 x) (f.2.1 i x hx),
    fun j a x ↦ by rw [LinearMap.comp_apply, LinearMap.comp_apply, f.2.2, g.2.2]⟩

/-- The underlying linear map of a composite of homogeneous maps is the composite of the
underlying linear maps. -/
@[simp]
theorem HomogeneousMap.comp_val {M N P : RightModuleCat 𝒜} {m n : ℤ}
    (f : HomogeneousMap M N m) (g : HomogeneousMap N P n) :
    (HomogeneousMap.comp f g).1 = g.1.comp f.1 := rfl

/-- Two homogeneous maps of the same degree are equal if they agree on every element. -/
@[ext]
theorem HomogeneousMap.ext {M N : RightModuleCat 𝒜} {n : ℤ}
    (f g : HomogeneousMap M N n) (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (LinearMap.ext h)

/-- Identity as a homogeneous map of degree zero. -/
@[implicit_reducible]
def HomogeneousMap.id (M : RightModuleCat 𝒜) : HomogeneousMap M M 0 :=
  ⟨LinearMap.id, fun _ _ hx ↦ by simpa using hx, fun _ _ _ ↦ rfl⟩

/-- The underlying linear map of the identity homogeneous map is the identity. -/
@[simp]
theorem HomogeneousMap.id_val (M : RightModuleCat 𝒜) :
    (HomogeneousMap.id M).1 = LinearMap.id := rfl

/-- Homogeneous composition, bundled as an additive map in both variables. -/
@[implicit_reducible]
def homogeneousCompAddHom (M N P : RightModuleCat 𝒜) (m n : ℤ) :
    HomogeneousMap M N m →+ HomogeneousMap N P n →+ HomogeneousMap M P (m + n) where
  toFun f :=
    { toFun := fun g ↦ HomogeneousMap.comp f g
      map_zero' := HomogeneousMap.ext _ _ fun _ ↦ rfl
      map_add' := fun _ _ ↦ HomogeneousMap.ext _ _ fun _ ↦ rfl }
  map_zero' := AddMonoidHom.ext fun _ ↦ HomogeneousMap.ext _ _ fun _ ↦ by
    simp [HomogeneousMap.comp]
  map_add' := fun _ _ ↦ AddMonoidHom.ext fun _ ↦ HomogeneousMap.ext _ _ fun _ ↦ by
    simp [HomogeneousMap.comp]

/-- Composition of finite sums of homogeneous maps. -/
@[implicit_reducible]
def comp (M N P : RightModuleCat 𝒜) : GradedHom M N →+ GradedHom N P →+ GradedHom M P :=
  DirectSum.toAddMonoid fun m ↦
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun n ↦
        AddMonoidHom.flip <|
          (DirectSum.of (fun k ↦ HomogeneousMap M P k) (m + n)).compHom.comp
            (homogeneousCompAddHom M N P m n)

/-- The composite of homogeneous summands of degrees `m` and `n` is the homogeneous summand of
degree `m + n` given by their composite. -/
@[simp]
theorem comp_of_of {M N P : RightModuleCat 𝒜} {m n : ℤ}
    (f : HomogeneousMap M N m) (g : HomogeneousMap N P n) :
    comp M N P (DirectSum.of _ m f) (DirectSum.of _ n g) =
      DirectSum.of _ (m + n) (HomogeneousMap.comp f g) := by
  simp [comp]
  rfl

/-- Evaluation sends composition of finite sums of homogeneous maps to composition of linear
maps. -/
@[simp]
theorem toLinearMap_comp {M N P : RightModuleCat 𝒜}
    (f : GradedHom M N) (g : GradedHom N P) :
    toLinearMap M P (comp M N P f g) = (toLinearMap N P g).comp (toLinearMap M N f) := by
  induction f using DirectSum.induction_on with
  | of m f =>
    induction g using DirectSum.induction_on with
    | of n g => simp
    | _ => simp_all [LinearMap.add_comp]
  | _ => simp_all [LinearMap.comp_add]

/-- The identity finite sum, concentrated in degree zero. -/
def id (M : RightModuleCat 𝒜) : GradedHom M M := DirectSum.of _ 0 (HomogeneousMap.id M)

/-- The identity finite sum evaluates to the identity linear map. -/
@[simp]
theorem toLinearMap_id (M : RightModuleCat 𝒜) :
    toLinearMap M M (id M) = LinearMap.id := by simp [id]

private theorem of_eq_of_val_eq {M N : RightModuleCat 𝒜} {m n : ℤ}
    (f : HomogeneousMap M N m) (g : HomogeneousMap M N n) (h : m = n)
    (hfg : f.1 = g.1) : DirectSum.of (fun k ↦ HomogeneousMap M N k) m f =
      DirectSum.of (fun k ↦ HomogeneousMap M N k) n g := by
  subst h
  exact congrArg (DirectSum.of _ m) (Subtype.ext hfg)

private theorem category_comp_id (M N : RightModuleCat 𝒜) (f : GradedHom M N) :
    comp M N N f (id N) = f := by
  induction f using DirectSum.induction_on with
  | of n f =>
    rw [id, comp_of_of]
    exact of_eq_of_val_eq _ _ (add_zero n) (LinearMap.id_comp _)
  | _ => simp_all [comp]

private theorem category_id_comp (M N : RightModuleCat 𝒜) (f : GradedHom M N) :
    comp M M N (id M) f = f := by
  induction f using DirectSum.induction_on with
  | of n f =>
    rw [id, comp_of_of]
    exact of_eq_of_val_eq _ _ (zero_add n) (LinearMap.comp_id _)
  | _ => simp_all [comp]

private theorem category_comp_assoc (M N P Q : RightModuleCat 𝒜)
    (f : GradedHom M N) (g : GradedHom N P) (h : GradedHom P Q) :
    comp M P Q (comp M N P f g) h = comp M N Q f (comp N P Q g h) := by
  induction f using DirectSum.induction_on with
  | of m f =>
    induction g using DirectSum.induction_on with
    | of n g =>
      induction h using DirectSum.induction_on with
      | of k h =>
        rw [comp_of_of, comp_of_of, comp_of_of, comp_of_of]
        exact of_eq_of_val_eq _ _ (add_assoc m n k) rfl
      | _ => simp_all
    | _ => simp_all
  | _ => simp_all

/-- Graded right modules, with finite sums of homogeneous maps as morphisms. -/
@[stacks 09MN "graded_category_of_graded_modules"]
instance instCategory : Category (RightModuleCat 𝒜) where
  Hom := GradedHom
  id := id
  comp := fun f g ↦ comp _ _ _ f g
  id_comp := by intros; apply category_id_comp
  comp_id := by intros; apply category_comp_id
  assoc := by intros; apply category_comp_assoc

/-- In the category, the composite of homogeneous morphisms of degrees `m` and `n` is the
homogeneous morphism of degree `m + n` given by their composite. -/
@[simp]
theorem of_comp_of {M N P : RightModuleCat 𝒜} {m n : ℤ}
    (f : HomogeneousMap M N m) (g : HomogeneousMap N P n) :
    CategoryStruct.comp (X := M) (Y := N) (Z := P)
        (DirectSum.of (fun k ↦ HomogeneousMap M N k) m f)
        (DirectSum.of (fun k ↦ HomogeneousMap N P k) n g) =
      (DirectSum.of (fun k ↦ HomogeneousMap M P k) (m + n)
        (HomogeneousMap.comp f g) : M ⟶ P) := comp_of_of f g

/-- The underlying linear map of a categorical composite is the composite of the underlying
linear maps. -/
@[simp]
theorem toLinearMap_category_comp {M N P : RightModuleCat 𝒜} (f : M ⟶ N) (g : N ⟶ P) :
    toLinearMap M P (f ≫ g) = (toLinearMap N P g).comp (toLinearMap M N f) :=
  toLinearMap_comp f g

/-- The underlying linear map of a categorical identity is the identity. -/
@[simp]
theorem toLinearMap_category_id (M : RightModuleCat 𝒜) :
    toLinearMap M M (𝟙 M) = LinearMap.id := toLinearMap_id M

/-- The category of graded right modules is preadditive, with the addition of finite sums of
homogeneous maps. -/
instance instPreadditive : Preadditive (RightModuleCat 𝒜) where
  homGroup := fun X Y ↦ inferInstanceAs (AddCommGroup (GradedHom X Y))
  add_comp := by
    intro M N P f g h
    exact congrArg (fun k : GradedHom N P →+ GradedHom M P ↦ k h) ((comp M N P).map_add f g)
  comp_add := by
    intro M N P f g h
    exact (comp M N P f).map_add g h

private theorem category_comp_smul_left (M N P : RightModuleCat 𝒜) (r : R)
    (f : GradedHom M N) (g : GradedHom N P) : comp M N P (r • f) g = r • comp M N P f g := by
  induction f using DirectSum.induction_on with
  | of m f =>
    induction g using DirectSum.induction_on with
    | of n g =>
      rw [← DirectSum.of_smul, comp_of_of, comp_of_of, ← DirectSum.of_smul]
      exact congrArg (DirectSum.of _ (m + n))
        (Subtype.ext (LinearMap.ext fun x ↦ by simp [HomogeneousMap.comp]))
    | _ => simp_all [smul_add]
  | _ => simp_all [smul_add, comp]

private theorem category_comp_smul_right (M N P : RightModuleCat 𝒜) (f : GradedHom M N)
    (r : R) (g : GradedHom N P) : comp M N P f (r • g) = r • comp M N P f g := by
  induction f using DirectSum.induction_on with
  | of m f =>
    induction g using DirectSum.induction_on with
    | of n g =>
      rw [← DirectSum.of_smul, comp_of_of, comp_of_of, ← DirectSum.of_smul]
      exact congrArg (DirectSum.of _ (m + n)) (Subtype.ext (LinearMap.ext fun x ↦ rfl))
    | _ => simp_all [smul_add]
  | _ => simp_all [smul_add, comp]

/-- The category of graded right modules is `R`-linear. -/
instance instLinear : Linear R (RightModuleCat 𝒜) where
  homModule := fun X Y ↦ inferInstanceAs (Module R (GradedHom X Y))
  smul_comp := by intros; apply category_comp_smul_left
  comp_smul := by intros; apply category_comp_smul_right

/-- The morphisms `M ⟶ N` decompose as the direct sum of the images of the homogeneous maps of
each degree. -/
instance (M N : RightModuleCat 𝒜) :
    DirectSum.Decomposition (DirectSum.lofRange (R := R) (fun n ↦ HomogeneousMap M N n)) :=
  DirectSum.lofRangeDecomposition (R := R) _

/-- The category of graded right modules is graded by the degrees of homogeneous maps. -/
@[stacks 09MN "graded_category_of_graded_modules"]
instance instGradedCategory : GradedCategory R (RightModuleCat 𝒜) where
  grade M N := DirectSum.lofRange (R := R) (fun n ↦ HomogeneousMap M N n)
  decomposition M N := DirectSum.lofRangeDecomposition (R := R) _
  id_mem M := ⟨HomogeneousMap.id M, rfl⟩
  comp_mem := by
    rintro M N P m n _ _ ⟨g, rfl⟩ ⟨f, rfl⟩
    change comp M N P (DirectSum.of _ n f) (DirectSum.of _ m g) ∈
      DirectSum.lofRange (R := R) (fun k ↦ HomogeneousMap M P k) (m + n)
    rw [add_comm m n]
    exact ⟨HomogeneousMap.comp f g, (comp_of_of f g).symm⟩

/-- A morphism has degree `n` if and only if it is a single homogeneous map of degree `n`. -/
@[simp]
theorem mem_grade_iff {M N : RightModuleCat 𝒜} {n : ℤ} {f : M ⟶ N} :
    f ∈ GradedCategory.grade (R := R) M N n ↔
      ∃ g : HomogeneousMap M N n, DirectSum.of _ n g = f := Iff.rfl

/-- The canonical identification of degree-zero morphisms with graded right-module maps. -/
@[stacks 09MN "degree-zero morphisms"]
noncomputable def degreeZeroHomEquiv (𝒜 : ExternallyGradedAlgebra.{u, v} R)
    (M N : RightModuleCat.{u, v, w} 𝒜) :
    { e : GradedCategory.DegreeZero.Hom R (RightModuleCat 𝒜) M N ≃ HomogeneousMap M N 0 //
      ∀ f, (e f).1 = toLinearMap M N f.1 } :=
  let hmem : ∀ f : GradedCategory.DegreeZero.Hom R (RightModuleCat 𝒜) M N,
      ∃ g : HomogeneousMap M N 0,
        DirectSum.of (fun n ↦ HomogeneousMap M N n) 0 g = f.1 :=
    fun f => (mem_grade_iff (R := R) (M := M) (N := N)).mp f.2
  let e : GradedCategory.DegreeZero.Hom R (RightModuleCat 𝒜) M N ≃ HomogeneousMap M N 0 :=
    { toFun := fun f => Classical.choose (hmem f)
      invFun := fun g => ⟨DirectSum.of (fun n ↦ HomogeneousMap M N n) 0 g,
        (mem_grade_iff (R := R) (M := M) (N := N)).mpr ⟨g, rfl⟩⟩
      left_inv := fun f => Subtype.ext (Classical.choose_spec (hmem f))
      right_inv := fun g => (DirectSum.of_injective (β := fun n ↦ HomogeneousMap M N n) 0)
        (Classical.choose_spec (hmem
          ⟨DirectSum.of (fun n ↦ HomogeneousMap M N n) 0 g,
            (mem_grade_iff (R := R) (M := M) (N := N)).mpr ⟨g, rfl⟩⟩)) }
  ⟨e, fun f => by
    change (Classical.choose (hmem f)).1 = toLinearMap M N f.1
    simpa only [toLinearMap_of] using congrArg (toLinearMap M N) (Classical.choose_spec (hmem f))⟩

/-- Under the canonical identification, the identity is the identity homogeneous map. -/
@[stacks 09MN "identities"]
theorem degreeZeroHomEquiv_id (𝒜 : ExternallyGradedAlgebra.{u, v} R)
    (M : RightModuleCat.{u, v, w} 𝒜) :
    ((degreeZeroHomEquiv 𝒜 M M).1
      (GradedCategory.DegreeZero.identity R (RightModuleCat 𝒜) M)) =
      HomogeneousMap.id M := by
  refine HomogeneousMap.ext _ _ fun x ↦ ?_
  rw [(degreeZeroHomEquiv 𝒜 M M).2]
  simp [GradedCategory.DegreeZero.identity, toLinearMap_category_id]

/-- Under the canonical identification, composition is composition of homogeneous maps. -/
@[stacks 09MN "composition"]
theorem degreeZeroHomEquiv_comp (𝒜 : ExternallyGradedAlgebra.{u, v} R)
    {M N P : RightModuleCat.{u, v, w} 𝒜}
    (f : GradedCategory.DegreeZero.Hom R (RightModuleCat 𝒜) M N)
    (g : GradedCategory.DegreeZero.Hom R (RightModuleCat 𝒜) N P) :
    (degreeZeroHomEquiv 𝒜 M P).1
      (GradedCategory.DegreeZero.comp R (RightModuleCat 𝒜) f g) =
      HomogeneousMap.comp ((degreeZeroHomEquiv 𝒜 M N).1 f)
        ((degreeZeroHomEquiv 𝒜 N P).1 g) := by
  refine HomogeneousMap.ext _ _ fun x ↦ ?_
  rw [(degreeZeroHomEquiv 𝒜 M P).2]
  simp only [GradedCategory.DegreeZero.comp, toLinearMap_category_comp,
    LinearMap.comp_apply, HomogeneousMap.comp_val]
  rw [(degreeZeroHomEquiv 𝒜 M N).2, (degreeZeroHomEquiv 𝒜 N P).2]

end RightModuleCat

end ExternallyGraded
