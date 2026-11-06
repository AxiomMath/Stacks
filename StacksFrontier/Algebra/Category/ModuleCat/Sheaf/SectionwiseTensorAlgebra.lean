module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IntGradedExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# The sectionwise tensor algebra of a presheaf of modules, as a graded algebra

Let `O` be a presheaf of commutative rings on a site and `F` a presheaf of `O`-modules. Stacks
Section 17.21 builds the tensor algebra of a *sheaf* of modules as the sheafification of the
sectionwise tensor algebra `U ↦ T_{O(U)}(F(U))`. This file builds the sectionwise object and
makes it a `Stacks.GradedAlgebra`: the family of presheaves of homogeneous pieces, their
multiplication, their unit, and the degree-one generator.

This is the input that `Stacks.GradedAlgebra.sheafify` and
`Stacks.GradedAlgebra.isTensorAlgebra_sheafify` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification` and
`.TensorAlgebraConstruction`) consume, and which the implementation notes of those files record
as missing.

## Main definitions

* `TensorAlgebra.intPiece`: the homogeneous pieces of `TensorAlgebra R M` indexed by `ℤ`, namely
  `LinearMap.range (ι R) ^ n` in degree `n ≥ 0` and the zero submodule in negative degrees. The
  grading index of `Stacks.GradedAlgebra` and `SheafOfModules.GradedAlgebra` is `ℤ`, while the
  tensor algebra is graded by `ℕ`; this is the extension by zero, in the one form in which the
  multiplication stays a single uniform formula.
* `TensorAlgebra.intPowMapₛₗ`: base change restricted to a `ℤ`-indexed piece.
* `PresheafOfModules.tensorAlgebraPiece`: the presheaf of sectionwise degree-`n` pieces, with
  `tensorAlgebraPieceSections` the sectionwise identification of its sections.
* `PresheafOfModules.tensorAlgebraGradedAlgebra`: **the sectionwise tensor algebra as a graded
  algebra of presheaves of modules.**
* `PresheafOfModules.tensorAlgebraGen`: its degree-one generator `F ⟶ tensorAlgebraPiece 1 F`.

## Main results

* `TensorAlgebra.mul_mem_intPiece`: the pieces multiply as the grading says, *including* when one
  of the degrees is negative, where the source piece is zero. This is what lets the graded
  multiplication be ring multiplication in every degree, with no case distinction, and hence
  lets the associativity and unit laws of `tensorAlgebraGradedAlgebra` be the ring laws.
* `PresheafOfModules.tensorAlgebraPiece_eq_zero_of_neg`: the sectionwise algebra has no nonzero
  sections in a negative degree. With `Stacks.GradedAlgebra.sheafify_piece_eq_zero` this is the
  `tensorPiece_eq_zero_of_neg` field of
  `SheafOfModules.TensorExteriorSymmetricAlgebras`, reduced to sectionwise data.
* `PresheafOfModules.tensorAlgebraGen_injective` and `tensorAlgebraGen_surjective`, bundled as
  `tensorAlgebraGenEquiv`: the degree-one generator is an isomorphism onto the degree-one piece,
  which is what the degree-one identification of the bundle is built from.
* `TensorAlgebra.algebraMap_algebraMapInv_of_mem_intPiece_zero` and
  `algebraMapInv_mapₛₗ_of_mem_intPiece_zero`: degree zero is the image of the base ring, and
  base change on it is the ring homomorphism itself. These are the two equations the degree-zero
  identification of the bundle is built from; the identification itself is not formed here, since
  it compares with `PresheafOfModules.unit` and so needs the module universe to be the ring
  universe, which nothing else below does.

## Implementation notes

**Why the pieces are submodules of one ring and not external tensor powers.** `TensorPower R n M`
— Mathlib's `⨂[R]^n M` — is the external `n`-fold tensor product, and the graded multiplication
on it is `TensorPower.gMul`, whose associativity and unit laws hold only up to the transports
`TensorPower.cast`. Taking instead the *internal* pieces `LinearMap.range (ι R) ^ n ⊆
TensorAlgebra R M`, which is the grading `TensorAlgebra.gradedAlgebra` is stated for, the graded
multiplication is the ring multiplication of a single ring in every degree, so every law of
`Stacks.GradedAlgebra` reduces to the corresponding ring law together with one transport of a
subtype along an equality of degrees
(`PresheafOfModules.heq_of_tensorAlgebraPieceVal_eq`). No case distinction on the signs of the
degrees appears anywhere below, which is the point of extending by the zero *submodule* rather
than by a zero object.

**Universes.** The ring universe `w` and the module universe are not independent: `TensorAlgebra
R M` for `R : Type w` and `M : Type a` lives in `Type (max w a)`, so the homogeneous pieces of a
presheaf of modules in universe `a` form presheaves of modules in universe `max w a`. Everything
is stated at `max w a`, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification`; `a = w` recovers the
equal-universe case, which is the one Section 17.21 is stated in.

**No `@[stacks]` tag.** Tag 0FQW is the definition of a sheaf of graded algebras and Section
17.21 is the construction of the three algebras of a *sheaf* of modules; nothing here is the
content of a tag, since nothing here is sheafified.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace TensorAlgebra

/-! ### The homogeneous pieces, indexed by the integers -/

section IntPiece

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **The homogeneous pieces of the tensor algebra, indexed by `ℤ`.** In degree `n ≥ 0` this is
the submodule `LinearMap.range (ι R) ^ n` that `TensorAlgebra.gradedAlgebra` is a grading by;
in a negative degree it is the zero submodule.

The extension is by the zero *submodule* of the same algebra rather than by a zero module, so
that the graded multiplication is ring multiplication in every degree. -/
noncomputable def intPiece : ℤ → Submodule R (TensorAlgebra R M) :=
  Stacks.IntGraded.extend fun n =>
    LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n

/-- In a degree `n ≥ 0` the piece is `LinearMap.range (ι R) ^ n`. -/
theorem intPiece_ofNat (n : ℕ) :
    intPiece R M (Int.ofNat n) =
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n := rfl

/-- In a degree `n ≥ 0`, written as a cast, the piece is `LinearMap.range (ι R) ^ n`. -/
@[simp]
theorem intPiece_natCast (n : ℕ) :
    intPiece R M (n : ℤ) =
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n := rfl

/-- In a negative degree the piece is the zero submodule. -/
theorem intPiece_eq_bot_of_neg {n : ℤ} (hn : n < 0) : intPiece R M n = ⊥ :=
  Stacks.IntGraded.extend_eq_bot_of_neg
    (fun k => LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ k) hn

/-- An element of a piece of negative degree is zero. -/
theorem eq_zero_of_mem_intPiece_of_neg {n : ℤ} (hn : n < 0) {x : TensorAlgebra R M}
    (hx : x ∈ intPiece R M n) : x = 0 :=
  Stacks.IntGraded.eq_zero_of_mem_extend_of_neg
    (fun k => LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ k) hn hx

/-- The degree-zero piece is the submodule `1`, the range of the algebra map. -/
theorem intPiece_zero : intPiece R M 0 = 1 := pow_zero _

/-- The degree-one piece is the range of `ι R`. -/
theorem intPiece_one :
    intPiece R M 1 = LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) :=
  pow_one _

/-- The algebra unit lies in degree zero. -/
theorem one_mem_intPiece_zero : (1 : TensorAlgebra R M) ∈ intPiece R M 0 :=
  Submodule.mem_one.mpr ⟨1, map_one _⟩

/-- The image of a scalar lies in degree zero. -/
theorem algebraMap_mem_intPiece_zero (r : R) :
    algebraMap R (TensorAlgebra R M) r ∈ intPiece R M 0 :=
  (intPiece_zero R M).symm ▸ Submodule.mem_one.mpr ⟨r, rfl⟩

/-- A degree-zero element of the tensor algebra is the image of a scalar, and
`TensorAlgebra.algebraMapInv` names that scalar. -/
theorem algebraMap_algebraMapInv_of_mem_intPiece_zero {x : TensorAlgebra R M}
    (hx : x ∈ intPiece R M 0) : algebraMap R (TensorAlgebra R M) (algebraMapInv x) = x := by
  rw [intPiece_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact congrArg (algebraMap R (TensorAlgebra R M)) (algebraMap_leftInverse M r)

/-- **Base change on degree zero is the ring homomorphism itself**, read through
`TensorAlgebra.algebraMapInv`. This is what makes the degree-zero piece of the sectionwise
tensor algebra the structure presheaf. -/
theorem algebraMapInv_mapₛₗ_of_mem_intPiece_zero {S : Type*} [CommRing S] {N : Type*}
    [AddCommGroup N] [Module S N] (φ : R →+* S) (u : M →ₛₗ[φ] N) {x : TensorAlgebra R M}
    (hx : x ∈ intPiece R M 0) : algebraMapInv (mapₛₗ φ u x) = φ (algebraMapInv x) := by
  conv_lhs => rw [← algebraMap_algebraMapInv_of_mem_intPiece_zero R M hx]
  rw [mapₛₗ_algebraMap, algebraMap_leftInverse]

/-- A degree-one generator lies in degree one. -/
theorem ι_mem_intPiece_one (m : M) : TensorAlgebra.ι R m ∈ intPiece R M 1 :=
  (intPiece_one R M).symm ▸ LinearMap.mem_range_self _ m

/-- **The pieces multiply as the grading says, in every pair of degrees.** When one of the
degrees is negative the corresponding piece is zero, so the product is zero and lies in any
piece; this is what makes the graded multiplication of `tensorAlgebraGradedAlgebra` a single
uniform formula. -/
theorem mul_mem_intPiece (i j : ℤ) {x y : TensorAlgebra R M} (hx : x ∈ intPiece R M i)
    (hy : y ∈ intPiece R M j) : x * y ∈ intPiece R M (i + j) := by
  cases i with
  | negSucc k =>
      simp [eq_zero_of_mem_intPiece_of_neg R M (by omega) hx]
  | ofNat p =>
      cases j with
      | negSucc k =>
          simp [eq_zero_of_mem_intPiece_of_neg R M (by omega) hy]
      | ofNat q =>
          rw [intPiece_ofNat] at hx hy
          rw [show (Int.ofNat p + Int.ofNat q : ℤ) = Int.ofNat (p + q) from rfl,
            intPiece_ofNat, pow_add]
          exact Submodule.mul_mem_mul hx hy

variable {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N]

/-- Base change carries a `ℤ`-indexed homogeneous piece into the piece of the same degree. -/
theorem mapₛₗ_mem_intPiece {R' : Type*} [CommRing R'] {M' : Type*} [AddCommGroup M']
    [Module R' M'] (φ : R' →+* S) (u : M' →ₛₗ[φ] N) (n : ℤ) {x : TensorAlgebra R' M'}
    (hx : x ∈ intPiece R' M' n) : mapₛₗ φ u x ∈ intPiece S N n := by
  cases n with
  | ofNat k =>
      rw [intPiece_ofNat] at hx ⊢
      exact mapₛₗ_mem_pow_range_ι φ u k hx
  | negSucc k =>
      simp [eq_zero_of_mem_intPiece_of_neg R' M' (by omega) hx]

end IntPiece

/-- The restriction of `TensorAlgebra.mapₛₗ` to a `ℤ`-indexed homogeneous piece, as a
`φ`-semilinear map. -/
noncomputable def intPowMapₛₗ {R S : Type*} [CommRing R] [CommRing S] {M : Type*}
    [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N] (n : ℤ)
    (φ : R →+* S) (u : M →ₛₗ[φ] N) : ↥(intPiece R M n) →ₛₗ[φ] ↥(intPiece S N n) where
  toFun x := ⟨mapₛₗ φ u x, mapₛₗ_mem_intPiece φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (mapₛₗ_smul φ u r x)

/-- `TensorAlgebra.intPowMapₛₗ` is `TensorAlgebra.mapₛₗ` on the underlying elements. -/
@[simp]
theorem intPowMapₛₗ_coe {R S : Type*} [CommRing R] [CommRing S] {M : Type*} [AddCommGroup M]
    [Module R M] {N : Type*} [AddCommGroup N] [Module S N] (n : ℤ) (φ : R →+* S)
    (u : M →ₛₗ[φ] N) (x : ↥(intPiece R M n)) :
    (intPowMapₛₗ n φ u x : TensorAlgebra S N) = mapₛₗ φ u x := rfl

end TensorAlgebra

namespace PresheafOfModules

/-! ### The presheaf of sectionwise homogeneous pieces -/

section Piece

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map of the presheaf of sectionwise degree-`n` pieces, as an additive map
whose target type is written as a homogeneous piece rather than as a restriction of scalars. -/
noncomputable def tensorAlgebraPieceRestrict (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) →+
      ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) n) :=
  (TensorAlgebra.intPowMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom
    (F.restrictₛₗ f)).toAddMonoidHom

/-- `PresheafOfModules.tensorAlgebraPieceRestrict` is `TensorAlgebra.mapₛₗ` of the restriction
map of `F` on the underlying elements. -/
@[simp]
theorem tensorAlgebraPieceRestrict_coe (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)) :
    (tensorAlgebraPieceRestrict n F f x :
        TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise degree-`n` pieces. -/
noncomputable def tensorAlgebraPieceAb (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : Cᵒᵖ ⥤ Ab.{max w a} where
  obj X := AddCommGrpCat.of
    (↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n))
  map f := AddCommGrpCat.ofHom (tensorAlgebraPieceRestrict n F f)
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

/-- Over `X`, the sections of `tensorAlgebraPieceAb n F` are a module over `O(X)`, as the
submodule `TensorAlgebra.intPiece` they are. -/
noncomputable instance tensorAlgebraPieceAbModule (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((tensorAlgebraPieceAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)))

/-- **The presheaf of sectionwise degree-`n` pieces of the tensor algebra.** Its sections over
`X` are the degree-`n` piece `TensorAlgebra.intPiece` of `T_{O(X)}(F(X))`, and its restriction
maps are the base changes `TensorAlgebra.intPowMapₛₗ` of the restriction maps of `F`. -/
noncomputable def tensorAlgebraPiece (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (tensorAlgebraPieceAb n F) fun {_ _} _ r _ => Subtype.ext
    (TensorAlgebra.mapₛₗ_smul _ _ r _)

/-- **The sectionwise identification.** The sections of `tensorAlgebraPiece n F` over `X` are
the degree-`n` piece of the tensor algebra of the sections of `F` over `X`. The equivalence is
the identity: the presheaf is defined sectionwise, and this records the identification in the
form a consumer needs. -/
noncomputable def tensorAlgebraPieceSections (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    (tensorAlgebraPiece n F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) :=
  LinearEquiv.refl _ _

/-- A local section of a homogeneous piece, read as an element of the tensor algebra of the
sections. The pieces are submodules of one algebra, but `(tensorAlgebraPiece n F).obj X` is a
`ModuleCat` object rather than syntactically a subtype, so the passage is not found as a
coercion; every statement below is phrased through this. -/
noncomputable abbrev tensorAlgebraPieceVal (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ)
    (x : (tensorAlgebraPiece n F).obj X) :
    TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) :=
  (x : ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)).1

/-- A local section of a homogeneous piece is determined by its value in the tensor algebra of
the sections. -/
theorem tensorAlgebraPieceVal_injective (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Function.Injective (tensorAlgebraPieceVal n F X) := fun _ _ h => Subtype.ext h

/-- **The transport every law of the sectionwise tensor algebra is proved through.** Two local
sections of two homogeneous pieces of equal degrees are heterogeneously equal as soon as they
are the same element of the tensor algebra of the sections. The degrees are free variables
here, so the equality of degrees can be substituted, which it cannot be where the laws of
`Stacks.GradedAlgebra` are stated. -/
theorem heq_of_tensorAlgebraPieceVal_eq
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {i j : ℤ} (h : i = j) (X : Cᵒᵖ)
    (x : (tensorAlgebraPiece i F).obj X) (y : (tensorAlgebraPiece j F).obj X)
    (hxy : tensorAlgebraPieceVal i F X x = tensorAlgebraPieceVal j F X y) : HEq x y := by
  subst h
  exact heq_of_eq (tensorAlgebraPieceVal_injective i F X hxy)

/-- Under the sectionwise identification, the restriction maps of `tensorAlgebraPiece n F` are
the base changes `TensorAlgebra.mapₛₗ` of the restriction maps of `F`. -/
theorem tensorAlgebraPieceSections_map (n : ℤ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (tensorAlgebraPiece n F).obj X) :
    (tensorAlgebraPieceSections n F Y ((tensorAlgebraPiece n F).map f x) :
        TensorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)
        (tensorAlgebraPieceSections n F X x) := rfl

/-- **The sectionwise tensor algebra has no nonzero sections in a negative degree.** With
`Stacks.GradedAlgebra.sheafify_piece_eq_zero` this is the `tensorPiece_eq_zero_of_neg` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras`. -/
theorem tensorAlgebraPiece_eq_zero_of_neg {n : ℤ} (hn : n < 0)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ)
    (x : (tensorAlgebraPiece n F).obj X) : x = 0 :=
  Subtype.ext (TensorAlgebra.eq_zero_of_mem_intPiece_of_neg _ _ hn
    (tensorAlgebraPieceSections n F X x).2)

end Piece

/-! ### The sectionwise tensor algebra as a graded algebra of presheaves of modules -/

section GradedAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- **The graded multiplication of the sectionwise tensor algebra**: ring multiplication in the
tensor algebra of the sections, in every pair of degrees. That it lands in the right piece is
`TensorAlgebra.mul_mem_intPiece`, which holds for negative degrees as well because the pieces
there are zero. -/
noncomputable def tensorAlgebraMul (i j : ℤ) :
    Stacks.BilinearMap (tensorAlgebraPiece i F) (tensorAlgebraPiece j F)
      (tensorAlgebraPiece (i + j) F) where
  app X :=
    { toFun := fun x =>
        { toFun := fun y =>
            ⟨tensorAlgebraPieceVal i F X x * tensorAlgebraPieceVal j F X y,
              TensorAlgebra.mul_mem_intPiece _ _ i j
                (x : ↥(TensorAlgebra.intPiece _ _ i)).2
                (y : ↥(TensorAlgebra.intPiece _ _ j)).2⟩
          map_zero' := Subtype.ext (mul_zero _)
          map_add' := fun y y' => Subtype.ext
            (mul_add _ (tensorAlgebraPieceVal j F X y) (tensorAlgebraPieceVal j F X y')) }
      map_zero' := AddMonoidHom.ext fun _ => Subtype.ext (zero_mul _)
      map_add' := fun x x' => AddMonoidHom.ext fun y => Subtype.ext
        (add_mul (tensorAlgebraPieceVal i F X x) (tensorAlgebraPieceVal i F X x')
          (tensorAlgebraPieceVal j F X y)) }
  map_smul_left _ _ _ _ := Subtype.ext (smul_mul_assoc _ _ _)
  map_smul_right _ _ _ _ := Subtype.ext (mul_smul_comm _ _ _)
  naturality _ _ _ := Subtype.ext (map_mul _ _ _)

/-- The graded multiplication is ring multiplication in the tensor algebra of the sections. -/
@[simp]
theorem tensorAlgebraPieceVal_mul (i j : ℤ) (X : Cᵒᵖ) (x : (tensorAlgebraPiece i F).obj X)
    (y : (tensorAlgebraPiece j F).obj X) :
    tensorAlgebraPieceVal (i + j) F X ((tensorAlgebraMul F i j).app X x y) =
      tensorAlgebraPieceVal i F X x * tensorAlgebraPieceVal j F X y := rfl

/-- The global unit of the sectionwise tensor algebra: the algebra unit over each object. -/
noncomputable def tensorAlgebraOne : (tensorAlgebraPiece 0 F).sections :=
  PresheafOfModules.sectionsMk
    (fun X => ⟨1, TensorAlgebra.one_mem_intPiece_zero
      ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)⟩)
    fun {_ _} _ => Subtype.ext (map_one _)

/-- Over each object the global unit is the algebra unit. -/
@[simp]
theorem tensorAlgebraPieceVal_one (X : Cᵒᵖ) :
    tensorAlgebraPieceVal 0 F X ((tensorAlgebraOne F).eval X) = 1 := rfl

/-- **The sectionwise tensor algebra of a presheaf of modules, as a graded algebra of presheaves
of modules.** This is the sectionwise input that `Stacks.GradedAlgebra.sheafify` and
`Stacks.GradedAlgebra.isTensorAlgebra_sheafify` consume. -/
noncomputable def tensorAlgebraGradedAlgebra :
    Stacks.GradedAlgebra (fun n : ℤ => tensorAlgebraPiece n F) where
  mul := tensorAlgebraMul F
  one := tensorAlgebraOne F
  mul_assoc i j k X x y z :=
    heq_of_tensorAlgebraPieceVal_eq F (add_assoc i j k) X _ _ (by
      simp only [tensorAlgebraPieceVal_mul]
      exact mul_assoc _ _ _)
  one_mul i X x :=
    heq_of_tensorAlgebraPieceVal_eq F (zero_add i) X _ _ (by
      simp only [tensorAlgebraPieceVal_mul, tensorAlgebraPieceVal_one]
      exact one_mul _)
  mul_one i X x :=
    heq_of_tensorAlgebraPieceVal_eq F (add_zero i) X _ _ (by
      simp only [tensorAlgebraPieceVal_mul, tensorAlgebraPieceVal_one]
      exact mul_one _)

/-- **The degree-one generator of the sectionwise tensor algebra**: a local section of `F` is a
degree-one generator of the tensor algebra of the sections. -/
noncomputable def tensorAlgebraGen : F ⟶ tensorAlgebraPiece 1 F where
  app X := ModuleCat.ofHom
    { toFun := fun m => ⟨TensorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) m,
        TensorAlgebra.ι_mem_intPiece_one ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) m⟩
      map_add' := fun m m' => Subtype.ext
        (map_add (TensorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)) m m')
      map_smul' := fun r m => Subtype.ext
        (map_smul (TensorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)) r m) }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m =>
    Subtype.ext (TensorAlgebra.mapₛₗ_ι _ (F.restrictₛₗ f) m).symm)

/-- The degree-one generator sends a local section `m` of `F` to `ι m`. -/
@[simp]
theorem tensorAlgebraPieceVal_gen (X : Cᵒᵖ) (m : F.obj X) :
    tensorAlgebraPieceVal 1 F X (PresheafOfModules.Hom.app (tensorAlgebraGen F) X m) =
      TensorAlgebra.ι _ m := rfl

/-- The degree-one generator is injective on sections: a local section of `F` is determined by
its degree-one image. -/
theorem tensorAlgebraGen_injective (X : Cᵒᵖ) :
    Function.Injective (PresheafOfModules.Hom.app (tensorAlgebraGen F) X) := fun m m' h =>
  (TensorAlgebra.ι_inj ((O ⋙ forget₂ _ RingCat).obj X) m m').1
    (congrArg (tensorAlgebraPieceVal 1 F X) h)

/-- The degree-one piece of the sectionwise tensor algebra is the range of the degree-one
generator. -/
theorem mem_range_ι_of_tensorAlgebraPieceVal_one (X : Cᵒᵖ)
    (z : (tensorAlgebraPiece 1 F).obj X) :
    tensorAlgebraPieceVal 1 F X z ∈
      LinearMap.range (TensorAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) :
        F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] _) :=
  TensorAlgebra.intPiece_one ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) ▸
    (z : ↥(TensorAlgebra.intPiece ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) 1)).2

/-- The degree-one generator is surjective on sections: the degree-one piece of the sectionwise
tensor algebra is the image of `F`. -/
theorem tensorAlgebraGen_surjective (X : Cᵒᵖ) :
    Function.Surjective (PresheafOfModules.Hom.app (tensorAlgebraGen F) X) := fun z => by
  obtain ⟨m, hm⟩ := mem_range_ι_of_tensorAlgebraPieceVal_one F X z
  exact ⟨m, tensorAlgebraPieceVal_injective 1 F X hm⟩

/-- The degree-one generator, as a linear equivalence onto the degree-one piece over each
object of the site. This is the sectionwise form of the degree-one identification
`tensorPieceIso_one` of `SheafOfModules.TensorExteriorSymmetricAlgebras`. -/
noncomputable def tensorAlgebraGenEquiv (X : Cᵒᵖ) :
    F.obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X] (tensorAlgebraPiece 1 F).obj X :=
  LinearEquiv.ofBijective ((tensorAlgebraGen F).app X).hom
    ⟨tensorAlgebraGen_injective F X, tensorAlgebraGen_surjective F X⟩

end GradedAlgebra

end PresheafOfModules
