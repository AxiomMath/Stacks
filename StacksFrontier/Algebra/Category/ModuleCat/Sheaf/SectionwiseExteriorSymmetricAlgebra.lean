module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IntGradedExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# The sectionwise exterior algebra of a presheaf of modules

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra` builds the sectionwise
tensor algebra `U ↦ T_{O(U)}(F(U))` of a presheaf of modules as a `Stacks.GradedAlgebra`. This
file does the same for the exterior algebra `U ↦ ⋀_{O(U)}(F(U))`, with its homogeneous pieces,
its multiplication, its unit and its degree-one generator. The symmetric algebra
`U ↦ Sym_{O(U)}(F(U))` is `PresheafOfModules.symPowIntGradedAlgebra` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise`.

## Main definitions

* `ExteriorAlgebra.intPiece`: the exterior powers indexed by `ℤ`, namely `⋀[R]^n M` in degree
  `n ≥ 0` and the zero submodule in negative degrees.
* `ExteriorAlgebra.intPowMapₛₗ`: base change restricted to a `ℤ`-indexed exterior power.
* `PresheafOfModules.exteriorAlgebraPiece`: the presheaves of sectionwise exterior powers.
* `PresheafOfModules.exteriorAlgebraGradedAlgebra`: **the sectionwise exterior algebra as a
  graded algebra of presheaves of modules**, with degree-one generator `exteriorAlgebraGen`.

## Main results

* `PresheafOfModules.exteriorAlgebraPiece_eq_zero_of_neg`: the sectionwise exterior algebra has
  no nonzero sections in a negative degree.
* `PresheafOfModules.exteriorAlgebraGen_squareZero`: the degree-one exterior generator squares
  to zero.

## Implementation notes

The pieces are submodules of one ring, so the graded multiplication is the ring multiplication
of `⋀_{O(U)}(F(U))` in every degree and each law of `Stacks.GradedAlgebra` is the corresponding
ring law transported along an equality of degrees, as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra`. The exterior pieces
`⋀[R]^n M` are Mathlib's `exteriorPower`, an abbreviation for `LinearMap.range (ι R) ^ n`, so
they multiply by `pow_add`. The ring universe `w` and the module universe are not independent;
everything is stated at `max w a`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace ExteriorAlgebra

/-! ### The exterior powers, indexed by the integers -/

section IntPiece

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **The exterior powers of a module, indexed by `ℤ`.** In degree `n ≥ 0` this is Mathlib's
`⋀[R]^n M`; in a negative degree it is the zero submodule. -/
noncomputable def intPiece : ℤ → Submodule R (ExteriorAlgebra R M) :=
  Stacks.IntGraded.extend fun n => ⋀[R]^n M

/-- In degree `Int.ofNat n` the `ℤ`-indexed exterior power is `⋀[R]^n M`. -/
theorem intPiece_ofNat (n : ℕ) : intPiece R M (Int.ofNat n) = ⋀[R]^n M := rfl

/-- In a degree `(n : ℤ)` with `n : ℕ` the `ℤ`-indexed exterior power is `⋀[R]^n M`. -/
@[simp]
theorem intPiece_natCast (n : ℕ) : intPiece R M (n : ℤ) = ⋀[R]^n M := rfl

/-- In a negative degree the `ℤ`-indexed exterior power is the zero submodule. -/
theorem intPiece_eq_bot_of_neg {n : ℤ} (hn : n < 0) : intPiece R M n = ⊥ :=
  Stacks.IntGraded.extend_eq_bot_of_neg (fun k => ⋀[R]^k M) hn

/-- An element of the `ℤ`-indexed exterior power in a negative degree is zero. -/
theorem eq_zero_of_mem_intPiece_of_neg {n : ℤ} (hn : n < 0) {x : ExteriorAlgebra R M}
    (hx : x ∈ intPiece R M n) : x = 0 :=
  Stacks.IntGraded.eq_zero_of_mem_extend_of_neg (fun k => ⋀[R]^k M) hn hx

/-- The degree-one exterior power is the range of `ExteriorAlgebra.ι R`. -/
theorem intPiece_one :
    intPiece R M 1 = LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) :=
  pow_one _

/-- The algebra unit lies in degree zero. -/
theorem one_mem_intPiece_zero : (1 : ExteriorAlgebra R M) ∈ intPiece R M 0 :=
  Submodule.mem_one.mpr ⟨1, map_one _⟩

/-- A degree-one generator lies in degree one. -/
theorem ι_mem_intPiece_one (m : M) : ExteriorAlgebra.ι R m ∈ intPiece R M 1 :=
  (intPiece_one R M).symm ▸ LinearMap.mem_range_self _ m

/-- **The exterior powers multiply as the grading says, in every pair of degrees.** -/
theorem mul_mem_intPiece (i j : ℤ) {x y : ExteriorAlgebra R M} (hx : x ∈ intPiece R M i)
    (hy : y ∈ intPiece R M j) : x * y ∈ intPiece R M (i + j) := by
  cases i with
  | negSucc k =>
      rw [eq_zero_of_mem_intPiece_of_neg R M (by omega) hx, zero_mul]
      exact Submodule.zero_mem _
  | ofNat p =>
      cases j with
      | negSucc k =>
          rw [eq_zero_of_mem_intPiece_of_neg R M (by omega) hy, mul_zero]
          exact Submodule.zero_mem _
      | ofNat q =>
          replace hx : x ∈
            LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ p := hx
          replace hy : y ∈
            LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q := hy
          change x * y ∈
            LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ (p + q)
          rw [pow_add]
          exact Submodule.mul_mem_mul hx hy

variable {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]

/-- Base change carries a `ℤ`-indexed exterior power into the power of the same degree. -/
theorem mapₛₗ_mem_intPiece {R' : Type*} [CommRing R'] {M' : Type*} [AddCommGroup M']
    [Module R' M'] (φ : R' →+* S) (u : M' →ₛₗ[φ] N) (n : ℤ) {x : ExteriorAlgebra R' M'}
    (hx : x ∈ intPiece R' M' n) : mapₛₗ φ u x ∈ intPiece S N n := by
  cases n with
  | ofNat k => exact mapₛₗ_mem_exteriorPower φ u k hx
  | negSucc k =>
      rw [eq_zero_of_mem_intPiece_of_neg R' M' (by omega) hx, map_zero]
      exact Submodule.zero_mem _

end IntPiece

/-- The restriction of `ExteriorAlgebra.mapₛₗ` to a `ℤ`-indexed exterior power, as a
`φ`-semilinear map. -/
noncomputable def intPowMapₛₗ {R S : Type*} [CommRing R] [CommRing S] {M : Type*}
    [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N] (n : ℤ)
    (φ : R →+* S) (u : M →ₛₗ[φ] N) : ↥(intPiece R M n) →ₛₗ[φ] ↥(intPiece S N n) where
  toFun x := ⟨mapₛₗ φ u x, mapₛₗ_mem_intPiece φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (mapₛₗ_smul φ u r x)

/-- The value of `ExteriorAlgebra.intPowMapₛₗ n φ u` at `x` is `ExteriorAlgebra.mapₛₗ φ u x`. -/
@[simp]
theorem intPowMapₛₗ_coe {R S : Type*} [CommRing R] [CommRing S] {M : Type*} [AddCommGroup M]
    [Module R M] {N : Type*} [AddCommGroup N] [Module S N] (n : ℤ) (φ : R →+* S)
    (u : M →ₛₗ[φ] N) (x : ↥(intPiece R M n)) :
    (intPowMapₛₗ n φ u x : ExteriorAlgebra S N) = mapₛₗ φ u x := rfl

end ExteriorAlgebra

namespace PresheafOfModules

/-! ### The presheaves of sectionwise exterior powers, and their graded algebra -/

section Exterior

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map of the presheaf of sectionwise degree-`n` exterior powers. -/
noncomputable def exteriorAlgebraPieceRestrict (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) →+
      ↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) n) :=
  (ExteriorAlgebra.intPowMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom
    (F.restrictₛₗ f)).toAddMonoidHom

/-- The presheaf of abelian groups underlying the presheaf of sectionwise exterior powers. -/
noncomputable def exteriorAlgebraPieceAb (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : Cᵒᵖ ⥤ Ab.{max w a} where
  obj X := AddCommGrpCat.of
    (↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n))
  map f := AddCommGrpCat.ofHom (exteriorAlgebraPieceRestrict n F f)
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

/-- The module structure over `O(X)` on the sections over `X` of the presheaf of abelian groups
of sectionwise degree-`n` exterior powers. -/
noncomputable instance exteriorAlgebraPieceAbModule (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((exteriorAlgebraPieceAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)))

/-- **The presheaf of sectionwise degree-`n` exterior powers.** -/
noncomputable def exteriorAlgebraPiece (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (exteriorAlgebraPieceAb n F) fun {_ _} _ r _ => Subtype.ext
    (ExteriorAlgebra.mapₛₗ_smul _ _ r _)

/-- A local section of a sectionwise exterior power, read as an element of the exterior algebra
of the sections. -/
noncomputable abbrev exteriorAlgebraPieceVal (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece n F).obj X) :
    ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) :=
  (x : ↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)).1

/-- A local section of a sectionwise exterior power is determined by its value in the exterior
algebra of the sections. -/
theorem exteriorAlgebraPieceVal_injective (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Function.Injective (exteriorAlgebraPieceVal n F X) := fun _ _ h => Subtype.ext h

/-- Local sections of the sectionwise exterior powers in equal degrees `i = j` with the same
value in the exterior algebra of the sections are heterogeneously equal. -/
theorem heq_of_exteriorAlgebraPieceVal_eq
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {i j : ℤ} (h : i = j) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece i F).obj X) (y : (exteriorAlgebraPiece j F).obj X)
    (hxy : exteriorAlgebraPieceVal i F X x = exteriorAlgebraPieceVal j F X y) : HEq x y := by
  subst h
  exact heq_of_eq (exteriorAlgebraPieceVal_injective i F X hxy)

/-- The sectionwise exterior algebra has no nonzero sections in a negative degree. -/
theorem exteriorAlgebraPiece_eq_zero_of_neg {n : ℤ} (hn : n < 0)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece n F).obj X) : x = 0 :=
  Subtype.ext (ExteriorAlgebra.eq_zero_of_mem_intPiece_of_neg _ _ hn
    (x : ↥(ExteriorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)).2)

variable (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The graded multiplication of the sectionwise exterior algebra. -/
noncomputable def exteriorAlgebraMul (i j : ℤ) :
    Stacks.BilinearMap (exteriorAlgebraPiece i F) (exteriorAlgebraPiece j F)
      (exteriorAlgebraPiece (i + j) F) where
  app X :=
    { toFun := fun x =>
        { toFun := fun y =>
            ⟨exteriorAlgebraPieceVal i F X x * exteriorAlgebraPieceVal j F X y,
              ExteriorAlgebra.mul_mem_intPiece _ _ i j
                (x : ↥(ExteriorAlgebra.intPiece _ _ i)).2
                (y : ↥(ExteriorAlgebra.intPiece _ _ j)).2⟩
          map_zero' := Subtype.ext (mul_zero _)
          map_add' := fun y y' => Subtype.ext
            (mul_add _ (exteriorAlgebraPieceVal j F X y)
              (exteriorAlgebraPieceVal j F X y')) }
      map_zero' := AddMonoidHom.ext fun _ => Subtype.ext (zero_mul _)
      map_add' := fun x x' => AddMonoidHom.ext fun y => Subtype.ext
        (add_mul (exteriorAlgebraPieceVal i F X x) (exteriorAlgebraPieceVal i F X x')
          (exteriorAlgebraPieceVal j F X y)) }
  map_smul_left _ _ _ _ := Subtype.ext (smul_mul_assoc _ _ _)
  map_smul_right _ _ _ _ := Subtype.ext (mul_smul_comm _ _ _)
  naturality _ _ _ := Subtype.ext (map_mul _ _ _)

/-- The value of a product of sectionwise exterior sections is the product of their values. -/
@[simp]
theorem exteriorAlgebraPieceVal_mul (i j : ℤ) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece i F).obj X) (y : (exteriorAlgebraPiece j F).obj X) :
    exteriorAlgebraPieceVal (i + j) F X ((exteriorAlgebraMul F i j).app X x y) =
      exteriorAlgebraPieceVal i F X x * exteriorAlgebraPieceVal j F X y := rfl

/-- The global unit of the sectionwise exterior algebra. -/
noncomputable def exteriorAlgebraOne : (exteriorAlgebraPiece 0 F).sections :=
  PresheafOfModules.sectionsMk
    (fun X => ⟨1, ExteriorAlgebra.one_mem_intPiece_zero
      ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)⟩)
    fun {_ _} _ => Subtype.ext (map_one _)

/-- The value of the unit of the sectionwise exterior algebra over `X` is `1`. -/
@[simp]
theorem exteriorAlgebraPieceVal_one (X : Cᵒᵖ) :
    exteriorAlgebraPieceVal 0 F X ((exteriorAlgebraOne F).eval X) = 1 := rfl

/-- **The sectionwise exterior algebra of a presheaf of modules, as a graded algebra of
presheaves of modules.** -/
noncomputable def exteriorAlgebraGradedAlgebra :
    Stacks.GradedAlgebra (fun n : ℤ => exteriorAlgebraPiece n F) where
  mul := exteriorAlgebraMul F
  one := exteriorAlgebraOne F
  mul_assoc i j k X x y z :=
    heq_of_exteriorAlgebraPieceVal_eq F (add_assoc i j k) X _ _ (by
      simp only [exteriorAlgebraPieceVal_mul]
      exact mul_assoc _ _ _)
  one_mul i X x :=
    heq_of_exteriorAlgebraPieceVal_eq F (zero_add i) X _ _ (by
      simp only [exteriorAlgebraPieceVal_mul, exteriorAlgebraPieceVal_one]
      exact one_mul _)
  mul_one i X x :=
    heq_of_exteriorAlgebraPieceVal_eq F (add_zero i) X _ _ (by
      simp only [exteriorAlgebraPieceVal_mul, exteriorAlgebraPieceVal_one]
      exact mul_one _)

/-- The multiplication of `exteriorAlgebraGradedAlgebra F` is `exteriorAlgebraMul F`. -/
theorem exteriorAlgebraGradedAlgebra_mul (i j : ℤ) :
    (exteriorAlgebraGradedAlgebra F).mul i j = exteriorAlgebraMul F i j := rfl

/-- The unit of `exteriorAlgebraGradedAlgebra F` is `exteriorAlgebraOne F`. -/
theorem exteriorAlgebraGradedAlgebra_one :
    (exteriorAlgebraGradedAlgebra F).one = exteriorAlgebraOne F := rfl

/-- **The degree-one generator of the sectionwise exterior algebra.** -/
noncomputable def exteriorAlgebraGen : F ⟶ exteriorAlgebraPiece 1 F where
  app X := ModuleCat.ofHom
    { toFun := fun m => ⟨ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) m,
        ExteriorAlgebra.ι_mem_intPiece_one ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) m⟩
      map_add' := fun m m' => Subtype.ext
        (map_add (ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)) m m')
      map_smul' := fun r m => Subtype.ext
        (map_smul (ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)) r m) }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m =>
    Subtype.ext (ExteriorAlgebra.mapₛₗ_ι _ (F.restrictₛₗ f) m).symm)

/-- The value of the degree-one generator at a section `m` over `X` is `ExteriorAlgebra.ι m`. -/
@[simp]
theorem exteriorAlgebraPieceVal_gen (X : Cᵒᵖ) (m : F.obj X) :
    exteriorAlgebraPieceVal 1 F X (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m) =
      ExteriorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) m := rfl

/-- **The degree-one generator of the sectionwise exterior algebra squares to zero.** -/
theorem exteriorAlgebraGen_squareZero (X : Cᵒᵖ) (m : F.obj X) :
    (exteriorAlgebraMul F 1 1).app X
        (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m)
        (PresheafOfModules.Hom.app (exteriorAlgebraGen F) X m) = 0 := by
  refine exteriorAlgebraPieceVal_injective (1 + 1) F X ?_
  rw [exteriorAlgebraPieceVal_mul, exteriorAlgebraPieceVal_gen]
  exact ExteriorAlgebra.ι_sq_zero m

end Exterior

end PresheafOfModules
