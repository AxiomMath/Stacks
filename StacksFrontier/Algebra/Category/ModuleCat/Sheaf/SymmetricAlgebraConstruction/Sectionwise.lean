module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IntGradedExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification

/-!
# The sectionwise symmetric algebra of a presheaf of modules

Let `O` be a presheaf of commutative rings on a site and let `F` be a presheaf of `O`-modules.
`PresheafOfModules.symPow n F` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification`) is the presheaf
`U ↦ Symⁿ_{O(U)}(F(U))` of sectionwise symmetric powers, for `n : ℕ`. This file makes the family of
those presheaves into a `ℤ`-graded algebra of presheaves of modules, a `Stacks.GradedAlgebra`.

Its pieces are built from the integer-indexed symmetric power `SymPow.symmetricPowerInt n R M`,
which is `Symⁿ` for `n ≥ 0` and the zero submodule in a negative degree. Every homogeneous piece is
a submodule of one and the same ring `Sym_R(M)`, and the multiplication in every degree is the
multiplication of that ring. In particular the multiplication is commutative in *all* degrees, not
only in degree one.

## Main definitions

* `SymPow.symmetricPowerInt`: the symmetric power in an integer degree, zero in negative
  degrees, and `SymPow.symMapIntₛₗ`: its base change along a ring homomorphism and a semilinear
  map, the integer-degree form of `SymPow.symMapₛₗ`.
* `PresheafOfModules.symPowInt`: the presheaf of sectionwise symmetric powers in an integer
  degree, with `PresheafOfModules.symPowIntVal` the sectionwise identification of a local section
  with an element of `Sym_{O(U)}(F(U))`.
* `PresheafOfModules.symPowIntMul` and `symPowIntOne`: the multiplication and the unit, namely
  the multiplication and the unit of the symmetric algebra of the sections.
* `PresheafOfModules.symPowIntGradedAlgebra`: **the sectionwise symmetric algebra of `F`**, as a
  `Stacks.GradedAlgebra` on `fun n : ℤ => symPowInt n F`.
* `PresheafOfModules.symPowIntGen`: its degree-one generator `F ⟶ symPowInt 1 F`.

## Main results

* `PresheafOfModules.symPowIntMul_comm`: **homogeneous multiplication is commutative in every pair
  of degrees.**
* `PresheafOfModules.symPowIntGradedAlgebra_genCommutes`: the degree-one case of the previous
  result, as `Stacks.GradedAlgebra.GenCommutes`.
* `PresheafOfModules.symPowInt_eq_zero_of_neg`: a local section in a negative degree vanishes.
* `PresheafOfModules.symPowIntZeroEquiv`: the degree-zero piece is the base, `Sym⁰ F = O`
  sectionwise, by a linear equivalence carrying `1` to the unit and compatible with restriction.

## Implementation notes

**Why the pieces are submodules of a single ring rather than a conditional family.** A graded
algebra indexed by `ℤ` whose nonnegative part is a given `ℕ`-indexed family has to say what the
negative pieces are. Spelling them as the zero object of `PresheafOfModules` makes the
multiplication a definition by cases on the two constructors of `Int` in each of its two
arguments, and then associativity is an eight-case analysis in which the seven degenerate cases
still have to produce a heterogeneous equality. Spelling the degree-`n` piece instead as the
submodule `SymPow.symmetricPowerInt n R M` of `Sym_R(M)` — which *is* zero in negative degrees —
removes the case analysis from everything except `SymPow.symmetricPowerInt_mul_le`, which is
where it belongs: all three laws then follow from `mul_assoc`, `one_mul` and `mul_one` in
`Sym_R(M)` together with the single transport lemma
`PresheafOfModules.symPowInt_heq_of_degree_eq`.

**The transport lemma.** `Stacks.GradedAlgebra` states associativity and the unit laws with
`HEq`, since `(i + j) + k` and `i + (j + k)` are propositionally but not definitionally equal in
`ℤ`, so the two sides live in different homogeneous pieces.
`PresheafOfModules.symPowInt_heq_of_degree_eq` takes the equality of degrees as a hypothesis and
`subst`s it internally, reducing each law to an equality of elements of `Sym_{O(X)}(F(X))`; this
is the same device as `Stacks.heq_of_isSeparated` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification`, at the sectionwise
level where no sheaf condition is available.

**Duplication of the presheaf boilerplate.** `symPowIntAb` repeats the shape of
`PresheafOfModules.symPowAb`, with `SymPow.symmetricPowerInt` in place of
`SymPow.symmetricPower`. The two are not the same presheaf: the former is indexed by `ℤ` and the
latter by `ℕ`, and `symPowInt (n : ℤ) F` has the same sections as `symPow n F` but is not that
term: the two restriction maps are the same function assembled through different bundlings of
`SymmetricAlgebra.mapₛₗ`, so an identification of the two is a separate (easy) step that nothing
below needs.

**Universes.** The ring universe `w` and the module universe are not independent, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification` and for the same
reason: `SymmetricAlgebra R M` for `R : Type w` and `M : Type a` lives in `Type (max w a)`, so
the symmetric powers of a presheaf of modules in universe `a` form a presheaf of modules in
universe `max w a`. Nothing here specializes a universe beyond that.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace SymPow

/-! ### Symmetric powers in an integer degree -/

section IntegerDegree

variable (n : ℤ) (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The symmetric power in an integer degree**: the submodule `Symⁿ_R(M)` of `Sym_R(M)` for
`n ≥ 0`, and the zero submodule for `n < 0`. -/
def symmetricPowerInt : Submodule R (SymmetricAlgebra R M) :=
  Stacks.IntGraded.extend (fun k => SymPow.symmetricPower k R M) n

variable {n}

/-- In a nonnegative degree `k`, the integer-degree symmetric power is `Symᵏ_R(M)`. -/
theorem symmetricPowerInt_natCast (k : ℕ) :
    symmetricPowerInt (k : ℤ) R M = SymPow.symmetricPower k R M := rfl

/-- In a negative degree the integer-degree symmetric power is the zero submodule. -/
theorem symmetricPowerInt_eq_bot_of_neg (hn : n < 0) : symmetricPowerInt n R M = ⊥ :=
  Stacks.IntGraded.extend_eq_bot_of_neg (fun k => SymPow.symmetricPower k R M) hn

/-- An element of the symmetric power in a negative degree is zero. -/
theorem eq_zero_of_neg_of_mem_symmetricPowerInt (hn : n < 0)
    (x : symmetricPowerInt n R M) : x = 0 :=
  Subtype.ext (Submodule.mem_bot R |>.1 (symmetricPowerInt_eq_bot_of_neg R M hn ▸ x.2))

/-- Degree zero is the image of the structure map: `Sym⁰_R(M)` is the unit submodule. -/
theorem symmetricPowerInt_zero_eq_one :
    symmetricPowerInt 0 R M = (1 : Submodule R (SymmetricAlgebra R M)) := by
  rw [show symmetricPowerInt 0 R M = SymPow.symmetricPower 0 R M from rfl,
    SymPow.symmetricPower, pow_zero]

/-- The unit of the symmetric algebra lies in degree zero. -/
theorem one_mem_symmetricPowerInt_zero :
    (1 : SymmetricAlgebra R M) ∈ symmetricPowerInt 0 R M :=
  Submodule.one_le.1 (symmetricPowerInt_zero_eq_one R M).ge

/-- Degree one is the image of the degree-one generator. -/
theorem symmetricPowerInt_one_eq_range :
    symmetricPowerInt 1 R M = LinearMap.range (SymmetricAlgebra.ι R M) := by
  rw [show symmetricPowerInt 1 R M = SymPow.symmetricPower 1 R M from rfl,
    SymPow.symmetricPower, pow_one]

/-- A degree-one generator lies in degree one. -/
theorem ι_mem_symmetricPowerInt_one (m : M) :
    SymmetricAlgebra.ι R M m ∈ symmetricPowerInt 1 R M :=
  (symmetricPowerInt_one_eq_range R M).ge (LinearMap.mem_range_self _ m)

/-- In a degree `Int.negSucc k` the symmetric power is the zero submodule. -/
private theorem symmetricPowerInt_negSucc (k : ℕ) :
    symmetricPowerInt (Int.negSucc k) R M = ⊥ := rfl

/-- **Multiplication is graded.** The product of a degree-`i` and a degree-`j` element lies in
degree `i + j`, in every pair of integer degrees. -/
theorem symmetricPowerInt_mul_le (i j : ℤ) :
    symmetricPowerInt i R M * symmetricPowerInt j R M ≤ symmetricPowerInt (i + j) R M := by
  obtain p | p := i
  · obtain q | q := j
    · exact SymmetricAlgebra.symmetricPower_mul_symmetricPower_le R M p q
    · rw [symmetricPowerInt_negSucc, Submodule.mul_bot]
      exact bot_le
  · rw [symmetricPowerInt_negSucc, Submodule.bot_mul]
    exact bot_le

end IntegerDegree

/-! ### Base change in an integer degree -/

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module S N]

/-- Base change carries the symmetric power in an integer degree into the symmetric power in the
same degree. -/
theorem mapₛₗ_mem_symmetricPowerInt (n : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N)
    {x : SymmetricAlgebra R M} (hx : x ∈ symmetricPowerInt n R M) :
    SymmetricAlgebra.mapₛₗ φ u x ∈ symmetricPowerInt n S N := by
  obtain k | k := n
  · exact SymmetricAlgebra.mapₛₗ_mem_symmetricPower φ u k hx
  · rw [symmetricPowerInt_negSucc, Submodule.mem_bot] at hx
    rw [symmetricPowerInt_negSucc, Submodule.mem_bot, hx, map_zero]

/-- **Base change of the symmetric power in an integer degree**, the integer-degree form of
`SymPow.symMapₛₗ`: the restriction of `SymmetricAlgebra.mapₛₗ φ u` to the degree-`n` pieces, as
a `φ`-semilinear map. -/
noncomputable def symMapIntₛₗ (n : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    symmetricPowerInt n R M →ₛₗ[φ] symmetricPowerInt n S N where
  toFun x := ⟨SymmetricAlgebra.mapₛₗ φ u x, mapₛₗ_mem_symmetricPowerInt n φ u x.2⟩
  map_add' x y := Subtype.ext (map_add (SymmetricAlgebra.mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (SymmetricAlgebra.mapₛₗ_smul φ u r x)

/-- The underlying element of `symMapIntₛₗ n φ u x` is `SymmetricAlgebra.mapₛₗ φ u x`. -/
theorem symMapIntₛₗ_coe (n : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N)
    (x : symmetricPowerInt n R M) :
    (symMapIntₛₗ n φ u x : SymmetricAlgebra S N) = SymmetricAlgebra.mapₛₗ φ u x := rfl

end BaseChange

end SymPow

namespace PresheafOfModules

/-! ### The presheaf of sectionwise symmetric powers in an integer degree -/

section SymPowIntPresheaf

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map of the presheaf of sectionwise symmetric powers in an integer degree, as
an additive map whose target type is written as a symmetric power rather than as a restriction of
scalars. -/
noncomputable def symPowIntRestrict (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+
      SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) :=
  (SymPow.symMapIntₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)).toAddMonoidHom

/-- The underlying element of the restriction of `x` along `f` is the base change of `x` along the
restriction map of `F`. -/
theorem symPowIntRestrict_coe (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (symPowIntRestrict n F f x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise symmetric powers in an
integer degree. -/
noncomputable def symPowIntAb (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : Cᵒᵖ ⥤ Ab.{max w a} where
  obj X := AddCommGrpCat.of
    (SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
  map f := AddCommGrpCat.ofHom (symPowIntRestrict n F f)
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact SymmetricAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj X => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_id X))
      (fun m => F.map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj Z => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => F.map_comp_apply f g m) x

/-- The sections of `symPowIntAb n F` over `X` form a module over `O(X)`, as a submodule of
`Sym_{O(X)}(F(X))`. -/
noncomputable instance symPowIntAbModule (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((symPowIntAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)))

/-- **The presheaf of sectionwise symmetric powers in an integer degree.** Its sections over `X`
are `SymPow.symmetricPowerInt n (O(X)) (F(X))`, namely `Symⁿ_{O(X)}(F(X))` for `n ≥ 0` and zero
in a negative degree, and its restriction maps are the symmetric powers of the restriction maps
of `F`, in the semilinear sense of `SymPow.symMapIntₛₗ`. -/
noncomputable def symPowInt (n : ℤ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (symPowIntAb n F) fun {_ _} _ r _ => Subtype.ext
    (SymmetricAlgebra.mapₛₗ_smul _ _ r _)

variable (n : ℤ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- **The sectionwise identification.** The element of `Sym_{O(X)}(F(X))` underlying a local
section of `symPowInt n F` over `X`. -/
noncomputable def symPowIntVal {n : ℤ} {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
    {X : Cᵒᵖ} (x : (symPowInt n F).obj X) :
    SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) :=
  x.1

/-- The underlying element of a local section of `symPowInt n F` lies in the degree-`n`
symmetric power. -/
theorem symPowIntVal_mem {X : Cᵒᵖ} (x : (symPowInt n F).obj X) :
    symPowIntVal x ∈
      SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) :=
  x.2

/-- Two local sections of `symPowInt n F` agree as soon as their underlying elements of the
symmetric algebra do. -/
theorem symPowIntVal_injective {X : Cᵒᵖ} {x y : (symPowInt n F).obj X}
    (h : symPowIntVal x = symPowIntVal y) : x = y :=
  Subtype.ext h

/-- The restriction maps of `symPowInt n F` are base change of the symmetric algebra along the
restriction maps of `F`, read through the sectionwise identification. -/
theorem symPowIntVal_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (symPowInt n F).obj X) :
    symPowIntVal ((symPowInt n F).map f x) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)
        (symPowIntVal x) := rfl

/-- Two homogeneous local sections of degrees known to be equal are heterogeneously equal as soon
as their underlying elements of the symmetric algebra of the sections are. -/
theorem symPowInt_heq_of_degree_eq {i j : ℤ} (hij : i = j) {X : Cᵒᵖ}
    (x : (symPowInt i F).obj X) (y : (symPowInt j F).obj X)
    (hxy : symPowIntVal x = symPowIntVal y) : HEq x y := by
  subst hij
  exact heq_of_eq (Subtype.ext hxy)

/-- **A local section in a negative degree vanishes.** -/
theorem symPowInt_eq_zero_of_neg (hn : n < 0) (X : Cᵒᵖ) (x : (symPowInt n F).obj X) : x = 0 :=
  SymPow.eq_zero_of_neg_of_mem_symmetricPowerInt _ _ hn x

end SymPowIntPresheaf

/-! ### The sectionwise symmetric algebra -/

section SymPowIntAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- **The multiplication of the sectionwise symmetric algebra**: the multiplication of
`Sym_{O(X)}(F(X))`, which carries degree `i` and degree `j` into degree `i + j` by
`SymPow.symmetricPowerInt_mul_le`. -/
noncomputable def symPowIntMul (i j : ℤ) :
    Stacks.BilinearMap (symPowInt i F) (symPowInt j F) (symPowInt (i + j) F) where
  app := fun _ =>
    { toFun := fun x =>
        { toFun := fun y => ⟨symPowIntVal x * symPowIntVal y,
            SymPow.symmetricPowerInt_mul_le _ _ i j
              (Submodule.mul_mem_mul (symPowIntVal_mem i F x) (symPowIntVal_mem j F y))⟩
          map_zero' := Subtype.ext (mul_zero _)
          map_add' := fun _ _ => Subtype.ext (mul_add _ _ _) }
      map_zero' := AddMonoidHom.ext fun _ => Subtype.ext (zero_mul _)
      map_add' := fun _ _ => AddMonoidHom.ext fun _ => Subtype.ext (add_mul _ _ _) }
  map_smul_left _ _ _ _ := Subtype.ext (Algebra.smul_mul_assoc _ _ _)
  map_smul_right _ _ _ _ := Subtype.ext (mul_smul_comm _ _ _)
  naturality _ _ _ := Subtype.ext (map_mul (SymmetricAlgebra.mapₛₗ _ _) _ _)

/-- The multiplication of the sectionwise symmetric algebra, read on underlying elements of the
symmetric algebra of the sections. -/
theorem symPowIntVal_mul (i j : ℤ) (X : Cᵒᵖ) (x : (symPowInt i F).obj X)
    (y : (symPowInt j F).obj X) :
    symPowIntVal ((symPowIntMul F i j).app X x y) = symPowIntVal x * symPowIntVal y := rfl

/-- **Homogeneous multiplication is commutative in every pair of degrees**: for local sections `x`
of degree `i` and `y` of degree `j`, the products `x * y` and `y * x` agree as heterogeneous
elements of the pieces of degrees `i + j` and `j + i`. -/
theorem symPowIntMul_comm (i j : ℤ) (X : Cᵒᵖ) (x : (symPowInt i F).obj X)
    (y : (symPowInt j F).obj X) :
    HEq ((symPowIntMul F i j).app X x y) ((symPowIntMul F j i).app X y x) :=
  symPowInt_heq_of_degree_eq F (Int.add_comm i j) _ _ (by
    rw [symPowIntVal_mul, symPowIntVal_mul, mul_comm])

/-- **The unit of the sectionwise symmetric algebra**: the unit of `Sym_{O(X)}(F(X))`, which lies
in degree zero and is preserved by the restriction maps because base change is a ring
homomorphism. -/
noncomputable def symPowIntOne : (symPowInt 0 F).sections :=
  PresheafOfModules.sectionsMk
    (fun X => (⟨1, SymPow.one_mem_symmetricPowerInt_zero _ _⟩ :
      SymPow.symmetricPowerInt 0 ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)))
    fun {_ _} _ => Subtype.ext (map_one (SymmetricAlgebra.mapₛₗ _ _))

/-- The unit of the sectionwise symmetric algebra is, over each `X`, the unit of
`Sym_{O(X)}(F(X))`. -/
theorem symPowIntVal_one (X : Cᵒᵖ) : symPowIntVal ((symPowIntOne F).eval X) = 1 := rfl

/-- **The sectionwise symmetric algebra of a presheaf of modules**, as a graded algebra of
presheaves of modules: in degree `n ≥ 0` the presheaf `U ↦ Symⁿ_{O(U)}(F(U))` of sectionwise
symmetric powers, zero in a negative degree, with the multiplication and the unit of the symmetric
algebra of the sections. -/
noncomputable def symPowIntGradedAlgebra :
    Stacks.GradedAlgebra fun n : ℤ => symPowInt n F where
  mul := symPowIntMul F
  one := symPowIntOne F
  mul_assoc i j k X x y z :=
    symPowInt_heq_of_degree_eq F (_root_.add_assoc i j k) _ _ (by
      rw [symPowIntVal_mul, symPowIntVal_mul, symPowIntVal_mul, symPowIntVal_mul, mul_assoc])
  one_mul i X x :=
    symPowInt_heq_of_degree_eq F (zero_add i) _ _ (by
      rw [symPowIntVal_mul, symPowIntVal_one, one_mul])
  mul_one i X x :=
    symPowInt_heq_of_degree_eq F (add_zero i) _ _ (by
      rw [symPowIntVal_mul, symPowIntVal_one, mul_one])

/-- The multiplication of `symPowIntGradedAlgebra F` is `symPowIntMul F`. -/
theorem symPowIntGradedAlgebra_mul (i j : ℤ) :
    (symPowIntGradedAlgebra F).mul i j = symPowIntMul F i j := rfl

/-- The unit of `symPowIntGradedAlgebra F` is `symPowIntOne F`. -/
theorem symPowIntGradedAlgebra_one : (symPowIntGradedAlgebra F).one = symPowIntOne F := rfl

/-! ### The degree-one generator -/

/-- **The degree-one generator of the sectionwise symmetric algebra**: a local section of `F`
viewed as a degree-one element of the symmetric algebra of the sections. -/
noncomputable def symPowIntGen : F ⟶ symPowInt 1 F where
  app X := ModuleCat.ofHom
    { toFun := fun m => (⟨SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) m,
        SymPow.ι_mem_symmetricPowerInt_one _ _ m⟩ :
          SymPow.symmetricPowerInt 1 ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
      map_add' := fun m m' => Subtype.ext (map_add _ m m')
      map_smul' := fun r m => Subtype.ext (map_smul _ r m) }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext
    (SymmetricAlgebra.mapₛₗ_ι ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) m).symm)

/-- The generator carries a local section `m` of `F` to the degree-one element `ι m` of the
symmetric algebra of the sections. -/
theorem symPowIntVal_gen (X : Cᵒᵖ) (m : F.obj X) :
    symPowIntVal (Hom.app (symPowIntGen F) X m) =
      SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) m := rfl

/-- **Degree-one local sections in the image of the generator commute.** -/
theorem symPowIntGradedAlgebra_genCommutes :
    (symPowIntGradedAlgebra F).GenCommutes (symPowIntGen F) := fun _ _ _ =>
  symPowIntVal_injective (1 + 1) F (mul_comm _ _)

/-! ### Degree zero -/

/-- **The degree-zero piece is the base.** `Sym⁰_{O(U)}(F(U))` is the image of `O(U)` under the
structure map of the symmetric algebra, so the degree-zero sections of the sectionwise symmetric
algebra are the sections of the base, by a linear equivalence carrying `1` to the unit. -/
noncomputable def symPowIntZeroEquiv (X : Cᵒᵖ) :
    ((O ⋙ forget₂ _ RingCat).obj X : Type w) ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      (symPowInt 0 F).obj X :=
  SymmetricAlgebra.symmetricPowerZeroEquiv ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)

/-- The degree-zero identification carries `r ∈ O(X)` to `algebraMap r` in `Sym_{O(X)}(F(X))`. -/
theorem symPowIntVal_zeroEquiv (X : Cᵒᵖ) (r : (O ⋙ forget₂ _ RingCat).obj X) :
    symPowIntVal (symPowIntZeroEquiv F X r) = algebraMap _ _ r := rfl

/-- The degree-zero identification carries `1` to the unit of the sectionwise symmetric
algebra. -/
theorem symPowIntZeroEquiv_one (X : Cᵒᵖ) :
    symPowIntZeroEquiv F X 1 = (symPowIntOne F).eval X :=
  symPowIntVal_injective 0 F (by
    rw [symPowIntVal_zeroEquiv, symPowIntVal_one, map_one])

/-- The degree-zero identification is compatible with the restriction maps. -/
theorem symPowIntZeroEquiv_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : (O ⋙ forget₂ _ RingCat).obj X) :
    (symPowInt 0 F).map f (symPowIntZeroEquiv F X r) =
      symPowIntZeroEquiv F Y ((O ⋙ forget₂ _ RingCat).map f r) :=
  symPowIntVal_injective 0 F (by
    rw [symPowIntVal_map, symPowIntVal_zeroEquiv, symPowIntVal_zeroEquiv,
      SymmetricAlgebra.mapₛₗ_algebraMap])

end SymPowIntAlgebra

end PresheafOfModules
