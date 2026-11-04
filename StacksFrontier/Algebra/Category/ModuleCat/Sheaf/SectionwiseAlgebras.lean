module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# The sectionwise tensor and exterior algebras of a presheaf of modules

Let `O` be a presheaf of commutative rings on a site `(C, J)` and `F` a presheaf of `O`-modules.
This file builds the presheaves

`U ↦ Tⁿ_{O(U)}(F(U))` and `U ↦ ⋀ⁿ_{O(U)}(F(U))`

of sectionwise tensor and exterior powers, makes each family into an `ℕ`-graded algebra of
presheaves of modules (`Stacks.GradedAlgebra`) with its degree-one generator, extends an
`ℕ`-graded such algebra by zero to a `ℤ`-graded one, and sheafifies. This gives the tensor and
the exterior algebra of a sheaf of modules as sheaves of graded algebras concentrated in
nonnegative degrees, as in Stacks Section 17.21.

## Main definitions

* `PresheafOfModules.zeroPresheaf`: the zero presheaf of modules, the constant presheaf at the
  trivial module, and `Stacks.BilinearMap.zero`: the zero bilinear map.
* `Stacks.GradedAlgebra.extendFamily` and `Stacks.GradedAlgebra.extend`: an `ℕ`-graded algebra
  of presheaves of modules, extended to `ℤ` by zero in negative degrees.
* `PresheafOfModules.tensorPow` and `PresheafOfModules.extPow`: the presheaves of sectionwise
  tensor and exterior powers, with `tensorPowSections` and `extPowSections` the sectionwise
  identifications of their sections.
* `PresheafOfModules.tensorPowGradedAlgebra` and `extPowGradedAlgebra`: those families as
  `ℕ`-graded algebras of presheaves of modules, with `tensorPowGen` and `extPowGen` their
  degree-one generators.
* `SheafOfModules.sectionwiseTensorAlgebra` and `sectionwiseExteriorAlgebra`: the tensor and
  exterior algebras of a sheaf of modules, as sheaves of graded algebras, with
  `sectionwiseTensorAlgebraGen` and `sectionwiseExteriorAlgebraGen` their degree-one generators.

## Main results

* `PresheafOfModules.zeroPresheaf_section_eq_zero` and
  `Stacks.GradedAlgebra.extendFamily_section_eq_zero`: the zero presheaf, and the extended
  family in a negative degree, have no nonzero sections.
* `Stacks.GradedAlgebra.extendMul_app_eq_zero_of_neg_left` and
  `Stacks.GradedAlgebra.extendMul_app_eq_zero_of_neg_right`: the extended multiplication
  vanishes as soon as one of its two degrees is negative.
* `PresheafOfModules.extPowGen_sq_eq_zero`: the degree-one generator of the sectionwise exterior
  algebra squares to zero, and `SheafOfModules.squareZero_sectionwiseExteriorAlgebraGen`: the
  same after sheafification.
* `SheafOfModules.sectionwiseTensorAlgebra_piece_eq_zero_of_neg` and
  `sectionwiseExteriorAlgebra_piece_eq_zero_of_neg`: both algebras are concentrated in
  nonnegative degrees.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory Opposite PresheafOfModules

universe v u t a w

/-! ### The zero presheaf of modules -/

namespace PresheafOfModules

section Zero

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{t})

/-- The presheaf of abelian groups underlying `PresheafOfModules.zeroPresheaf`: the constant
presheaf at the trivial group. -/
noncomputable def zeroAb : Cᵒᵖ ⥤ AddCommGrpCat.{a} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of PUnit.{a + 1})

/-- The trivial `R.obj X`-module structure on the sections of `PresheafOfModules.zeroAb`. -/
noncomputable instance zeroAbModule (X : Cᵒᵖ) : Module (R.obj X) ((zeroAb.{v, u, a}).obj X) :=
  inferInstanceAs (Module (R.obj X) PUnit.{a + 1})

/-- The zero presheaf of modules: the constant presheaf at the trivial module. -/
noncomputable def zeroPresheaf : PresheafOfModules.{a} R :=
  PresheafOfModules.ofPresheaf zeroAb.{v, u, a} fun {_ _} _ _ _ =>
    Subsingleton.elim (α := PUnit.{a + 1}) _ _

/-- The sections of the zero presheaf of modules form a subsingleton. -/
noncomputable instance zeroPresheafSubsingleton (X : Cᵒᵖ) :
    Subsingleton ((zeroPresheaf.{v, u, t, a} R).obj X) :=
  inferInstanceAs (Subsingleton PUnit.{a + 1})

/-- The zero presheaf of modules has no nonzero sections. -/
theorem zeroPresheaf_section_eq_zero (X : Cᵒᵖ) (m : (zeroPresheaf.{v, u, t, a} R).obj X) :
    m = 0 := Subsingleton.elim _ _

end Zero

end PresheafOfModules

/-! ### The zero bilinear map -/

namespace Stacks.BilinearMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- The zero bilinear map of presheaves of modules. -/
def zero {M N P : PresheafOfModules.{a} R} : BilinearMap M N P where
  app _ := 0
  map_smul_left _ _ _ _ := (smul_zero _).symm
  map_smul_right _ _ _ _ := (smul_zero _).symm
  naturality _ _ _ := map_zero _

/-- The zero bilinear map vanishes on every pair of sections. -/
@[simp]
theorem zero_app {M N P : PresheafOfModules.{a} R} (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    (zero : BilinearMap M N P).app X x y = 0 := rfl

end Stacks.BilinearMap

/-! ### Extending an `ℕ`-graded algebra of presheaves of modules to `ℤ` -/

namespace Stacks.GradedAlgebra

section Extend

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}
  {Q : ℕ → PresheafOfModules.{a} R}

/-- The `ℤ`-indexed family extending an `ℕ`-indexed family of presheaves of modules by the zero
presheaf in negative degrees. -/
noncomputable def extendFamily (Q : ℕ → PresheafOfModules.{a} R) :
    ℤ → PresheafOfModules.{a} R
  | Int.ofNat k => Q k
  | Int.negSucc _ => PresheafOfModules.zeroPresheaf R

/-- In a nonnegative degree `k` the extended family is `Q k`. -/
theorem extendFamily_natCast (k : ℕ) : extendFamily Q (k : ℤ) = Q k := rfl

/-- In a negative degree the extended family has no nonzero sections. -/
theorem extendFamily_section_eq_zero {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (m : (extendFamily Q n).obj X) : m = 0 := by
  match n, hn with
  | Int.negSucc _, _ => exact PresheafOfModules.zeroPresheaf_section_eq_zero R X m

/-- Two sections of propositionally equal presheaves of modules which both vanish are
heterogeneously equal. -/
theorem heq_of_eq_of_subsingleton {M N : PresheafOfModules.{a} R} (h : M = N) {X : Cᵒᵖ}
    {x : M.obj X} {y : N.obj X} (hx : x = 0) (hy : y = 0) : HEq x y := by
  subst h hx hy
  rfl

/-- The multiplication of the extended graded algebra: the given multiplication in nonnegative
degrees, and zero as soon as one of the two degrees is negative. -/
noncomputable def extendMul (A : GradedAlgebra Q) :
    (i j : ℤ) → BilinearMap (extendFamily Q i) (extendFamily Q j) (extendFamily Q (i + j))
  | Int.ofNat a, Int.ofNat b => A.mul a b
  | Int.ofNat _, Int.negSucc _ => BilinearMap.zero
  | Int.negSucc _, _ => BilinearMap.zero

/-- In nonnegative degrees the extended multiplication is the given one. -/
theorem extendMul_app_natCast (A : GradedAlgebra Q) (i j : ℕ) (X : Cᵒᵖ) (x : (Q i).obj X)
    (y : (Q j).obj X) :
    (A.extendMul (i : ℤ) (j : ℤ)).app X x y = (A.mul i j).app X x y := rfl

/-- The extended multiplication vanishes when the first degree is negative. -/
theorem extendMul_app_eq_zero_of_neg_left (A : GradedAlgebra Q) {i : ℤ} (hi : i < 0) (j : ℤ)
    (X : Cᵒᵖ) (x : (extendFamily Q i).obj X) (y : (extendFamily Q j).obj X) :
    (A.extendMul i j).app X x y = 0 := by
  rw [extendFamily_section_eq_zero hi X x, map_zero]
  rfl

/-- The extended multiplication vanishes when the second degree is negative. -/
theorem extendMul_app_eq_zero_of_neg_right (A : GradedAlgebra Q) (i : ℤ) {j : ℤ} (hj : j < 0)
    (X : Cᵒᵖ) (x : (extendFamily Q i).obj X) (y : (extendFamily Q j).obj X) :
    (A.extendMul i j).app X x y = 0 := by
  rw [extendFamily_section_eq_zero hj X y, map_zero]

/-- An `ℕ`-graded algebra of presheaves of modules, extended by zero in negative degrees to a
`ℤ`-graded one. -/
noncomputable def extend (A : GradedAlgebra Q) : GradedAlgebra (extendFamily Q) where
  mul := A.extendMul
  one := A.one
  mul_assoc i j k X x y z := by
    rcases lt_or_ge i 0 with hi | hi
    · exact heq_of_eq_of_subsingleton (congrArg (extendFamily Q) (add_assoc i j k))
        (by rw [A.extendMul_app_eq_zero_of_neg_left hi j X x y, map_zero]; rfl)
        (A.extendMul_app_eq_zero_of_neg_left hi (j + k) X x _)
    rcases lt_or_ge j 0 with hj | hj
    · exact heq_of_eq_of_subsingleton (congrArg (extendFamily Q) (add_assoc i j k))
        (by rw [A.extendMul_app_eq_zero_of_neg_right i hj X x y, map_zero]; rfl)
        (by rw [A.extendMul_app_eq_zero_of_neg_left hj k X y z, map_zero])
    rcases lt_or_ge k 0 with hk | hk
    · exact heq_of_eq_of_subsingleton (congrArg (extendFamily Q) (add_assoc i j k))
        (A.extendMul_app_eq_zero_of_neg_right (i + j) hk X _ z)
        (by rw [A.extendMul_app_eq_zero_of_neg_right j hk X y z, map_zero])
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact A.mul_assoc a b c X x y z
  one_mul i X x := by
    rcases lt_or_ge i 0 with hi | hi
    · exact heq_of_eq_of_subsingleton (congrArg (extendFamily Q) (zero_add i))
        (A.extendMul_app_eq_zero_of_neg_right 0 hi X _ x)
        (extendFamily_section_eq_zero hi X x)
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact A.one_mul a X x
  mul_one i X x := by
    rcases lt_or_ge i 0 with hi | hi
    · exact heq_of_eq_of_subsingleton (congrArg (extendFamily Q) (add_zero i))
        (A.extendMul_app_eq_zero_of_neg_left hi 0 X x _)
        (extendFamily_section_eq_zero hi X x)
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact A.mul_one a X x

/-- In nonnegative degrees the multiplication of `Stacks.GradedAlgebra.extend A` is that of
`A`. -/
theorem extend_mul_app_natCast (A : GradedAlgebra Q) (i j : ℕ) (X : Cᵒᵖ) (x : (Q i).obj X)
    (y : (Q j).obj X) :
    ((A.extend).mul (i : ℤ) (j : ℤ)).app X x y = (A.mul i j).app X x y := rfl

/-- The unit of `Stacks.GradedAlgebra.extend A` is that of `A`. -/
theorem extend_one (A : GradedAlgebra Q) : (A.extend).one = A.one := rfl

end Extend

end Stacks.GradedAlgebra

/-! ### The presheaf of sectionwise tensor powers -/

namespace PresheafOfModules

section TensorPow

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map of the presheaf of sectionwise tensor powers, as an additive map whose
target type is written as a graded piece rather than as a restriction of scalars. -/
noncomputable def tensorPowRestrict (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) n (F.obj X) →+
      TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj Y) n (F.obj Y) :=
  (TensorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)).toAddMonoidHom

/-- As an element of the tensor algebra, the restriction of a homogeneous section is its image
under `TensorAlgebra.mapₛₗ` of the restriction map of `F`. -/
@[simp]
theorem tensorPowRestrict_coe (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) n (F.obj X)) :
    (tensorPowRestrict n F f x : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise tensor powers. -/
noncomputable def tensorPowAb (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : Cᵒᵖ ⥤ AddCommGrpCat.{max w a} where
  obj X := AddCommGrpCat.of
    (TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) n (F.obj X))
  map f := AddCommGrpCat.ofHom (tensorPowRestrict n F f)
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact TensorAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj X => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_id X))
      (fun m => F.map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact TensorAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj Z => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => F.map_comp_apply f g m) x

/-- The `O(X)`-module structure on the degree-`n` piece of `TensorAlgebra (O X) (F X)`. -/
noncomputable instance tensorPowAbModule (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((tensorPowAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) n (F.obj X)))

/-- The presheaf of sectionwise tensor powers: its sections over `X` are the degree-`n`
homogeneous piece of `TensorAlgebra (O X) (F X)`, and its restriction maps are the degree-`n`
pieces of the base changes of the restriction maps of `F`, in the semilinear sense of
`TensorAlgebra.powMapₛₗ`. -/
noncomputable def tensorPow (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (tensorPowAb n F) fun {_ _} _ r _ => Subtype.ext
    (TensorAlgebra.mapₛₗ_smul _ _ r _)

/-- The sections of `tensorPow n F` over `X` are the degree-`n` piece of the tensor algebra of the
sections of `F` over `X`. -/
noncomputable def tensorPowSections (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    (tensorPow n F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) n (F.obj X) :=
  LinearEquiv.refl _ _

/-- The restriction maps of `tensorPow n F` are the base changes of the restriction maps of `F`,
read through the sectionwise identification. -/
theorem tensorPowSections_map (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (tensorPow n F).obj X) :
    (tensorPowSections n F Y ((tensorPow n F).map f x) :
        TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)
        (tensorPowSections n F X x) := rfl

end TensorPow

end PresheafOfModules

/-! ### The presheaf of sectionwise exterior powers -/

namespace PresheafOfModules

section ExtPow

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map of the presheaf of sectionwise exterior powers, as an additive map whose
target type is written as an exterior power rather than as a restriction of scalars. -/
noncomputable def extPowRestrict (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) →+
      ⋀[(O ⋙ forget₂ _ RingCat).obj Y]^n (F.obj Y) :=
  (ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom
    (F.restrictₛₗ f)).toAddMonoidHom

/-- As an element of the exterior algebra, the restriction of a section of an exterior power is
its image under `ExteriorAlgebra.mapₛₗ` of the restriction map of `F`. -/
@[simp]
theorem extPowRestrict_coe (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) :
    (extPowRestrict n F f x : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise exterior powers. -/
noncomputable def extPowAb (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : Cᵒᵖ ⥤ AddCommGrpCat.{max w a} where
  obj X := AddCommGrpCat.of (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X))
  map f := AddCommGrpCat.ofHom (extPowRestrict n F f)
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact ExteriorAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj X => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_id X))
      (fun m => F.map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact ExteriorAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj Z => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => F.map_comp_apply f g m) x

/-- The `O(X)`-module structure on `⋀ⁿ_{O(X)}(F(X))`. -/
noncomputable instance extPowAbModule (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((extPowAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)))

/-- The presheaf of sectionwise exterior powers: its sections over `X` are
`⋀ⁿ_{O(X)}(F(X))`, and its restriction maps are the exterior powers of the restriction maps of
`F`, in the semilinear sense of `ExteriorAlgebra.powMapₛₗ`. -/
noncomputable def extPow (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (extPowAb n F) fun {_ _} _ r _ => Subtype.ext
    (ExteriorAlgebra.mapₛₗ_smul _ _ r _)

/-- The sections of `extPow n F` over `X` are the `n`-th
exterior power of the sections of `F` over `X`. -/
noncomputable def extPowSections (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    (extPow n F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X) :=
  LinearEquiv.refl _ _

/-- The restriction maps of `extPow n F` are the base changes of the restriction maps of `F`,
read through the sectionwise identification. -/
theorem extPowSections_map (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (extPow n F).obj X) :
    (extPowSections n F Y ((extPow n F).map f x) :
        ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)
        (extPowSections n F X x) := rfl

end ExtPow

end PresheafOfModules

/-! ### The sectionwise tensor algebra as a graded algebra of presheaves of modules -/

namespace PresheafOfModules

section TensorPowAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The multiplication of the sectionwise tensor algebra on sections over `X`: the product in
`TensorAlgebra (O X) (F X)` of homogeneous elements of degrees `i` and `j`. -/
noncomputable def tensorPowMulSections (i j : ℕ) (X : Cᵒᵖ) :
    TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) i (F.obj X) →+
      TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) j (F.obj X) →+
        TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) (i + j) (F.obj X) where
  toFun x :=
    { toFun := fun y => ⟨(x : TensorAlgebra _ _) * (y : TensorAlgebra _ _),
        TensorAlgebra.mul_mem_gradedPiece x.2 y.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun y y' => Subtype.ext (by simp [mul_add]) }
  map_zero' := AddMonoidHom.ext fun y => Subtype.ext (by simp)
  map_add' x x' := AddMonoidHom.ext fun y => Subtype.ext (by simp [add_mul])

/-- As an element of the tensor algebra, the product of two homogeneous sections is their product
in `TensorAlgebra (O X) (F X)`. -/
@[simp]
theorem tensorPowMulSections_coe (i j : ℕ) (X : Cᵒᵖ)
    (x : TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) i (F.obj X))
    (y : TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) j (F.obj X)) :
    (tensorPowMulSections F i j X x y :
      TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) = x * y := rfl

/-- The multiplication of the sectionwise tensor algebra. -/
noncomputable def tensorPowMul (i j : ℕ) :
    Stacks.BilinearMap (tensorPow i F) (tensorPow j F) (tensorPow (i + j) F) where
  app X := tensorPowMulSections F i j X
  map_smul_left _ _ _ _ := Subtype.ext (smul_mul_assoc _ _ _)
  map_smul_right _ _ _ _ := Subtype.ext (mul_smul_comm _ _ _)
  naturality _ _ _ := Subtype.ext (map_mul _ _ _)

/-- The unit of the sectionwise tensor algebra: the global section given by the unit of
`TensorAlgebra (O X) (F X)` over every `X`. -/
noncomputable def tensorPowOne : (tensorPow 0 F).sections :=
  PresheafOfModules.sectionsMk
    (fun X => (⟨1, TensorAlgebra.one_mem_gradedPiece⟩ :
      TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) 0 (F.obj X)))
    fun {_ _} _ => Subtype.ext (map_one _)

/-- Two homogeneous sections of the sectionwise tensor algebra whose degrees are propositionally
equal and which are the same element of the tensor algebra are heterogeneously equal. -/
theorem heq_tensorPow {m n : ℕ} (hmn : m = n) {X : Cᵒᵖ}
    {x : (tensorPow m F).obj X} {y : (tensorPow n F).obj X}
    (h : (tensorPowSections m F X x : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      (tensorPowSections n F X y : TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))) :
    HEq x y := by
  subst hmn
  exact heq_of_eq (Subtype.ext h)

/-- The sectionwise tensor algebra of a presheaf of modules, as an `ℕ`-graded algebra of
presheaves of modules on the family of sectionwise tensor powers. -/
noncomputable def tensorPowGradedAlgebra :
    Stacks.GradedAlgebra (fun n : ℕ => tensorPow n F) where
  mul := tensorPowMul F
  one := tensorPowOne F
  mul_assoc i j k _ _ _ _ := heq_tensorPow F (Nat.add_assoc i j k) (mul_assoc _ _ _)
  one_mul i _ _ := heq_tensorPow F (Nat.zero_add i) (one_mul _)
  mul_one i _ _ := heq_tensorPow F (Nat.add_zero i) (mul_one _)

/-- The degree-one generator of the sectionwise tensor algebra: `m ↦ TensorAlgebra.ι m`. -/
noncomputable def tensorPowGen : F ⟶ tensorPow 1 F where
  app X := ModuleCat.ofHom
    { toFun := fun m => (⟨TensorAlgebra.ι _ m, TensorAlgebra.ι_mem_gradedPiece m⟩ :
        TensorAlgebra.gradedPiece ((O ⋙ forget₂ _ RingCat).obj X) 1 (F.obj X))
      map_add' := fun m m' => Subtype.ext (map_add _ m m')
      map_smul' := fun r m => Subtype.ext (map_smul _ r m) }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext
    (TensorAlgebra.mapₛₗ_ι ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) m).symm)

/-- The degree-one generator of the sectionwise tensor algebra sends a section `m` to
`TensorAlgebra.ι m`. -/
@[simp]
theorem tensorPowGen_coe (X : Cᵒᵖ) (m : F.obj X) :
    (tensorPowSections 1 F X (PresheafOfModules.Hom.app (tensorPowGen F) X m) :
      TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) = TensorAlgebra.ι _ m := rfl

end TensorPowAlgebra

end PresheafOfModules

/-! ### The sectionwise exterior algebra as a graded algebra of presheaves of modules -/

namespace PresheafOfModules

section ExtPowAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The multiplication of the sectionwise exterior algebra on sections over `X`: the wedge product
`exteriorPower.wedgeMul` of `ExteriorAlgebra (O X) (F X)`, as a biadditive map. -/
noncomputable def extPowMulSections (i j : ℕ) (X : Cᵒᵖ) :
    (⋀[(O ⋙ forget₂ _ RingCat).obj X]^i (F.obj X)) →+
      (⋀[(O ⋙ forget₂ _ RingCat).obj X]^j (F.obj X)) →+
        ⋀[(O ⋙ forget₂ _ RingCat).obj X]^(i + j) (F.obj X) :=
  AddMonoidHom.mk' (fun x => (exteriorPower.wedgeMul i j x).toAddMonoidHom)
    (fun x x' => AddMonoidHom.ext fun y => Subtype.ext (by simp))

/-- As an element of the exterior algebra, the product of two sections of exterior powers is their
product in `ExteriorAlgebra (O X) (F X)`. -/
@[simp]
theorem extPowMulSections_coe (i j : ℕ) (X : Cᵒᵖ)
    (x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^i (F.obj X))
    (y : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^j (F.obj X)) :
    (extPowMulSections F i j X x y :
      ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) = x * y := rfl

/-- `PresheafOfModules.extPowMulSections` with its type spelled at the sections of `extPow`. -/
noncomputable def extPowMulApp (i j : ℕ) (X : Cᵒᵖ) :
    (extPow i F).obj X →+ (extPow j F).obj X →+ (extPow (i + j) F).obj X :=
  extPowMulSections F i j X

/-- The multiplication of the sectionwise exterior algebra. -/
noncomputable def extPowMul (i j : ℕ) :
    Stacks.BilinearMap (extPow i F) (extPow j F) (extPow (i + j) F) :=
  { app := extPowMulApp F i j
    map_smul_left := fun _ _ _ _ => Subtype.ext (smul_mul_assoc _ _ _)
    map_smul_right := fun _ _ _ _ => Subtype.ext (mul_smul_comm _ _ _)
    naturality := fun _ _ _ => Subtype.ext (map_mul _ _ _) }

/-- The unit of `ExteriorAlgebra (O X) (F X)`, as a section of `extPow 0 F` over `X`. -/
noncomputable def extPowOneSection (X : Cᵒᵖ) : (extPow 0 F).obj X :=
  (⟨1, ExteriorAlgebra.one_mem_exteriorPower⟩ :
    ⋀[(O ⋙ forget₂ _ RingCat).obj X]^0 (F.obj X))

/-- The unit of the sectionwise exterior algebra: the global section given by the unit of
`ExteriorAlgebra (O X) (F X)` over every `X`. -/
noncomputable def extPowOne : (extPow 0 F).sections :=
  PresheafOfModules.sectionsMk (extPowOneSection F) fun {_ _} _ => Subtype.ext (map_one _)

/-- Two sections of the sectionwise exterior powers whose degrees are propositionally equal and
which are the same element of the exterior algebra are heterogeneously equal. -/
theorem heq_extPow {m n : ℕ} (hmn : m = n) {X : Cᵒᵖ}
    {x : (extPow m F).obj X} {y : (extPow n F).obj X}
    (h : (extPowSections m F X x : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      (extPowSections n F X y : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))) :
    HEq x y := by
  subst hmn
  exact heq_of_eq (Subtype.ext h)

/-- The sectionwise exterior algebra of a presheaf of modules, as an `ℕ`-graded algebra of
presheaves of modules on the family of sectionwise exterior powers. -/
noncomputable def extPowGradedAlgebra : Stacks.GradedAlgebra (fun n : ℕ => extPow n F) :=
  { mul := extPowMul F
    one := extPowOne F
    mul_assoc := fun i j k _ _ _ _ => heq_extPow F (Nat.add_assoc i j k) (mul_assoc _ _ _)
    one_mul := fun i _ _ => heq_extPow F (Nat.zero_add i) (one_mul _)
    mul_one := fun i _ _ => heq_extPow F (Nat.add_zero i) (mul_one _) }

/-- `ExteriorAlgebra.ι` with its codomain spelled at the sections of `extPow 1 F`. -/
noncomputable def extPowGenApp (X : Cᵒᵖ) :
    F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (extPow 1 F).obj X :=
  (ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)).codRestrict
    (⋀[(O ⋙ forget₂ _ RingCat).obj X]^1 (F.obj X))
    (fun m => ExteriorAlgebra.ι_mem_exteriorPower m)

/-- The degree-one generator of the sectionwise exterior algebra: `m ↦ ExteriorAlgebra.ι m`. -/
noncomputable def extPowGen : F ⟶ extPow 1 F where
  app X := ModuleCat.ofHom (extPowGenApp F X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext
    (ExteriorAlgebra.mapₛₗ_ι ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) m).symm)

/-- The degree-one generator of the sectionwise exterior algebra sends a section `m` to
`ExteriorAlgebra.ι m`. -/
@[simp]
theorem extPowGen_coe (X : Cᵒᵖ) (m : F.obj X) :
    (extPowSections 1 F X (PresheafOfModules.Hom.app (extPowGen F) X m) :
      ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      ExteriorAlgebra.ι _ m := rfl

/-- The degree-one generator of the sectionwise exterior algebra squares to zero. -/
theorem extPowGen_sq_eq_zero (X : Cᵒᵖ) (x : F.obj X) :
    ((extPowGradedAlgebra F).mul 1 1).app X
        (PresheafOfModules.Hom.app (extPowGen F) X x)
        (PresheafOfModules.Hom.app (extPowGen F) X x) = 0 :=
  Subtype.ext (ExteriorAlgebra.ι_sq_zero (R := (O ⋙ forget₂ _ RingCat).obj X) x)

end ExtPowAlgebra

end PresheafOfModules

/-! ### The sheafified sectionwise tensor and exterior algebras -/

namespace SheafOfModules

section Sheafify

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- The tensor algebra of a sheaf of modules, as a sheaf of graded algebras: the degreewise
sheafification of the sectionwise tensor algebra of `F`, extended by zero into negative
degrees. -/
noncomputable def sectionwiseTensorAlgebra : GradedAlgebra.{w, w} (toRingCat J Osharp) :=
  (PresheafOfModules.tensorPowGradedAlgebra F).extend.sheafify (toRingCatMap J a)

/-- The degree-one generator of `SheafOfModules.sectionwiseTensorAlgebra`: the sheafification of
`PresheafOfModules.tensorPowGen`. -/
noncomputable def sectionwiseTensorAlgebraGen :
    (PresheafOfModules.moduleSheafification J a).obj F ⟶
      (sectionwiseTensorAlgebra J a F).piece 1 :=
  (PresheafOfModules.tensorPowGradedAlgebra F).extend.sheafifyGen (toRingCatMap J a)
    (PresheafOfModules.tensorPowGen F)

/-- `SheafOfModules.sectionwiseTensorAlgebra` is concentrated in nonnegative degrees. -/
theorem sectionwiseTensorAlgebra_piece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (x : ((sectionwiseTensorAlgebra J a F).piece n).val.obj X) : x = 0 :=
  (PresheafOfModules.tensorPowGradedAlgebra F).extend.sheafify_piece_eq_zero
    (toRingCatMap J a) n (fun Y m => Stacks.GradedAlgebra.extendFamily_section_eq_zero hn Y m) X x

/-- The exterior algebra of a sheaf of modules, as a sheaf of graded algebras: the degreewise
sheafification of the sectionwise exterior algebra of `F`, extended by zero into negative
degrees. -/
noncomputable def sectionwiseExteriorAlgebra : GradedAlgebra.{w, w} (toRingCat J Osharp) :=
  (PresheafOfModules.extPowGradedAlgebra F).extend.sheafify (toRingCatMap J a)

/-- The degree-one generator of `SheafOfModules.sectionwiseExteriorAlgebra`. -/
noncomputable def sectionwiseExteriorAlgebraGen :
    (PresheafOfModules.moduleSheafification J a).obj F ⟶
      (sectionwiseExteriorAlgebra J a F).piece 1 :=
  (PresheafOfModules.extPowGradedAlgebra F).extend.sheafifyGen (toRingCatMap J a)
    (PresheafOfModules.extPowGen F)

/-- The degree-one generator of `SheafOfModules.sectionwiseExteriorAlgebra` squares to zero. -/
theorem squareZero_sectionwiseExteriorAlgebraGen :
    GradedAlgebra.SquareZero (sectionwiseExteriorAlgebraGen J a F) :=
  (PresheafOfModules.extPowGradedAlgebra F).extend.squareZero_sheafifyGen (toRingCatMap J a)
    (PresheafOfModules.extPowGen F) (fun X x => PresheafOfModules.extPowGen_sq_eq_zero F X x)

/-- `SheafOfModules.sectionwiseExteriorAlgebra` is concentrated in nonnegative degrees. -/
theorem sectionwiseExteriorAlgebra_piece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (x : ((sectionwiseExteriorAlgebra J a F).piece n).val.obj X) : x = 0 :=
  (PresheafOfModules.extPowGradedAlgebra F).extend.sheafify_piece_eq_zero
    (toRingCatMap J a) n (fun Y m => Stacks.GradedAlgebra.extendFamily_section_eq_zero hn Y m) X x

end Sheafify

end SheafOfModules
