module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraTotalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# The differential graded algebra of sections of a sheaf of differential graded algebras

Let `(A, d)` be a sheaf of differential graded algebras on a site and let `U` be an object of
the site. Its sections over `U` form a differential graded algebra `A(U)` in the ungraded,
single-type sense of `DifferentialGradedAlgebra`: the underlying ring is the direct sum
`⨁ n, A^n(U)` of the sections of the homogeneous pieces, which
`SheafOfModules.GradedAlgebra.totalSections` already provides, its grading is by the images of
the structure maps of that direct sum, and its differential is the differential of `A` read on
sections, summand by summand.

The coefficient ring is a copy of `ℤ` in the universe of the sections: a sheaf of differential
graded algebras is a sheaf of differential graded modules over a sheaf of rings that need not be
constant, so there is no base commutative ring other than `ℤ` through which the sections are
linear, and `DifferentialGradedAlgebra` wants its coefficients in the same universe as the
algebra.

Restriction along a morphism `a : V ⟶ U` of `Cᵒᵖ` gives a homomorphism `A(V) ⟶ A(U)` of
differential graded algebras.

## Main definitions

* `Stacks.uliftIntAlgebra`: a ring is an algebra over the universe-lifted integers.
* `Stacks.ExternalGrading.intSummand` and `Stacks.ExternalGrading.intSummandEquiv`: the
  degree-`n` summand of an external direct sum, as a submodule over the lifted integers, and
  its identification with the `n`-th term. The ring of sections is graded by these.
* `SheafOfModules.DifferentialGradedAlgebra.sectionAlgebra`: **the differential graded algebra
  `A(U)` of sections over `U`.**
* `SheafOfModules.DifferentialGradedAlgebra.sectionRestriction`: the homomorphism
  `A(V) ⟶ A(U)` of differential graded algebras attached to a morphism `V ⟶ U` of `Cᵒᵖ`.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.sectionAlgebra_d_of`: the differential of the
  section algebra is the differential of `A` on each summand.
* `SheafOfModules.DifferentialGradedAlgebra.sectionRestriction_of`: the restriction
  homomorphism is the restriction map of `A` on each summand.

## Implementation notes

`Stacks.ExternalGrading` already grades an external direct sum of a `DirectSum.GRing` by the
images of its structure maps, but it does so by *additive subgroups*, and
`DifferentialGradedAlgebra` asks for a family of submodules over its coefficient ring. The two
carriers have the same underlying sets, so the graded-monoid and decomposition clauses are the
same proofs; they are repeated here for the submodule-valued family rather than transported,
because `SetLike.GradedMonoid` and `DirectSum.Decomposition` are classes on the carrier *type*
and no transport along an order isomorphism of carriers exists.

The algebra structure over the lifted integers is `Stacks.uliftIntAlgebra`. It is a `def` and
not an instance: it applies to every ring, and a global instance of that shape would be found
in preference to better ones. Its scalar multiplication is taken to be the existing action of
`ULift ℤ`, so the module structure it induces is the one already present.

The degree bookkeeping is carried by `DirectSum.of`: the associativity, unit and Leibniz laws of
a sheaf of differential graded algebras are stated with `HEq` and
`SheafOfModules.gradedCast` because their two sides live in pieces of equal but not syntactically
identical degrees, and `SheafOfModules.of_gradedCast` turns each such transport into an equality
of summands of the direct sum.

## References

* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V)
* [Stacks Project, Tag 061X](https://stacks.math.columbia.edu/tag/061X)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum

universe t a v u

namespace Stacks

/-- **A ring is an algebra over the universe-lifted integers.** The structure map is the integer
cast composed with the identification of `ULift ℤ` with `ℤ`, and the scalar multiplication is the
one already attached to `ULift ℤ`, so the module structure induced by this algebra structure is
the existing one. -/
@[instance_reducible]
def uliftIntAlgebra (X : Type a) [Ring X] : Algebra (ULift.{a, 0} ℤ) X where
  algebraMap := (Int.castRingHom X).comp (ULift.ringEquiv : ULift.{a, 0} ℤ ≃+* ℤ).toRingHom
  smul := (· • ·)
  commutes' _ x := (Int.cast_commute _ x).eq
  smul_def' r x := by
    change (r.down : ℤ) • x = _
    rw [zsmul_eq_mul]
    rfl

attribute [local instance] uliftIntAlgebra

/-- A ring homomorphism is an algebra homomorphism over the lifted integers: a ring
homomorphism preserves integer casts, which are the images of the structure map. -/
def uliftIntAlgHom {X Y : Type a} [Ring X] [Ring Y] (f : X →+* Y) :
    X →ₐ[ULift.{a, 0} ℤ] Y where
  __ := f
  commutes' r := by
    change f ((r.down : ℤ) : X) = ((r.down : ℤ) : Y)
    exact map_intCast f _

/-- The algebra homomorphism `uliftIntAlgHom f` agrees with `f` pointwise. -/
@[simp] theorem uliftIntAlgHom_apply {X Y : Type a} [Ring X] [Ring Y] (f : X →+* Y) (x : X) :
    uliftIntAlgHom f x = f x := rfl

namespace ExternalGrading

variable {ι : Type*} [DecidableEq ι] (T : ι → Type a) [∀ i, AddCommGroup (T i)]

/-- **The `i`-th summand of an external direct sum, as a submodule over the lifted integers.**
Its underlying set is the range of the structure map `T i → ⨁ i, T i`; a submodule over the
integers is an additive subgroup. -/
def intSummand (i : ι) : Submodule (ULift.{a, 0} ℤ) (⨁ i, T i) where
  __ := summand T i
  smul_mem' c x hx := by
    change (c.down : ℤ) • x ∈ summand T i
    exact zsmul_mem hx _

/-- An element of the direct sum lies in the `i`-th summand exactly when it is the image of an
element of `T i`. -/
theorem mem_intSummand_iff {i : ι} {x : ⨁ i, T i} :
    x ∈ intSummand T i ↔ ∃ y : T i, DirectSum.of T i y = x := Iff.rfl

/-- The image of `y : T i` under the structure map lies in the `i`-th summand. -/
theorem of_mem_intSummand (i : ι) (y : T i) : DirectSum.of T i y ∈ intSummand T i := ⟨y, rfl⟩

/-- **The `i`-th summand is additively `T i`.** -/
def intSummandEquiv (i : ι) : T i ≃+ intSummand T i where
  toFun y := ⟨DirectSum.of T i y, of_mem_intSummand T i y⟩
  invFun x := (x : ⨁ i, T i) i
  left_inv y := DirectSum.of_eq_same i y
  right_inv := by
    rintro ⟨x, y, rfl⟩
    exact Subtype.ext (congrArg (DirectSum.of T i) (DirectSum.of_eq_same i y))
  map_add' y y' := Subtype.ext (map_add (DirectSum.of T i) y y')

/-- The element of the `i`-th summand attached to `y : T i` is `DirectSum.of T i y`. -/
@[simp] theorem intSummandEquiv_apply_coe (i : ι) (y : T i) :
    ((intSummandEquiv T i y : intSummand T i) : ⨁ i, T i) = DirectSum.of T i y := rfl

/-- The inverse of `intSummandEquiv` takes an element of the `i`-th summand to its `i`-th
coordinate. -/
@[simp] theorem intSummandEquiv_symm_apply (i : ι) (x : intSummand T i) :
    (intSummandEquiv T i).symm x = (x : ⨁ i, T i) i := rfl

/-- Every element of the `i`-th summand is the image of its `i`-th coordinate. -/
theorem of_coord_eq {i : ι} (x : intSummand T i) :
    DirectSum.of T i ((x : ⨁ i, T i) i) = (x : ⨁ i, T i) :=
  congrArg Subtype.val ((intSummandEquiv T i).apply_symm_apply x)

/-- The componentwise decomposition of an external direct sum into its summands. -/
def intDecomposeHom : (⨁ i, T i) →+ DirectSum ι fun i ↦ intSummand T i :=
  DirectSum.map fun i ↦ (intSummandEquiv T i).toAddMonoidHom

/-- The decomposition carries `DirectSum.of T i y` to the element of the `i`-th summand attached to
`y`. -/
@[simp] theorem intDecomposeHom_of (i : ι) (y : T i) :
    intDecomposeHom T (DirectSum.of T i y) =
      DirectSum.of (fun i ↦ intSummand T i) i (intSummandEquiv T i y) :=
  DirectSum.map_of _ i y

/-- An external direct sum is the internal direct sum of its summands `intSummand T i`. -/
instance intDecomposition : DirectSum.Decomposition (intSummand T) where
  decompose' := intDecomposeHom T
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp [intDecomposeHom]
    | of i y => rw [intDecomposeHom_of, DirectSum.coeAddMonoidHom_of, intSummandEquiv_apply_coe]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp [intDecomposeHom]
    | of i y =>
        obtain ⟨z, hz⟩ := y.2
        rw [DirectSum.coeAddMonoidHom_of, ← hz, intDecomposeHom_of]
        exact congrArg _ (Subtype.ext hz)
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end ExternalGrading

end Stacks

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transport along an equality of degrees is absorbed by the structure map of a direct sum. -/
theorem of_gradedCast {T : ℤ → Type a} [∀ n, AddCommGroup (T n)] {i j : ℤ} (h : i = j)
    (x : T i) : DirectSum.of T j (gradedCast T h x) = DirectSum.of T i x := by
  cases h
  rfl

/-- Two heterogeneously equal elements of pieces of equal degrees have the same image in the
direct sum. -/
theorem of_heq {T : ℤ → Type a} [∀ n, AddCommGroup (T n)] {i j : ℤ} (h : i = j) {x : T i}
    {y : T j} (hxy : x ≍ y) : DirectSum.of T i x = DirectSum.of T j y := by
  subst h
  rw [eq_of_heq hxy]

namespace GradedAlgebra

attribute [local instance] sectionsGOne sectionsGMul sectionsGRing Stacks.uliftIntAlgebra

variable (A : GradedAlgebra.{t, a} R) (U : Cᵒᵖ)

/-- **The summands of the ring of sections are multiplicatively graded.** The unit is the
degree-zero summand of the unit section and the product of the summands of degrees `i` and `j`
is the summand of degree `i + j` of the product of the sections. -/
instance sectionGradedMonoid :
    SetLike.GradedMonoid (Stacks.ExternalGrading.intSummand (A.sectionsPiece U)) where
  one_mem := ⟨GradedMonoid.GOne.one, DirectSum.of_zero_one _⟩
  mul_mem := by
    rintro i j x y ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨GradedMonoid.GMul.mul c d, (DirectSum.of_mul_of c d).symm⟩

/-- The ring of sections over `U` is a graded algebra over the lifted integers, graded by its
summands. -/
instance sectionGradedAlgebra :
    _root_.GradedAlgebra (Stacks.ExternalGrading.intSummand (A.sectionsPiece U)) :=
  { (inferInstance :
      SetLike.GradedMonoid (Stacks.ExternalGrading.intSummand (A.sectionsPiece U))),
    (inferInstance :
      DirectSum.Decomposition (Stacks.ExternalGrading.intSummand (A.sectionsPiece U))) with }

end GradedAlgebra

namespace DifferentialGradedAlgebra

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ)

/-- The differential of `A` on the sections over `U` of the degree-`n` piece, as an additive
map into the next piece. -/
def sectionDApp (n : ℤ) :
    A.toGradedAlgebra.sectionsPiece U n →+ A.toGradedAlgebra.sectionsPiece U (n + 1) :=
  AddMonoidHom.mk' (fun x ↦ (A.complex.d n (n + 1)).val.app U x) fun x y ↦ map_add _ x y

/-- `sectionDApp U n` is the differential `d^n` of `A` evaluated on sections over `U`. -/
@[simp] theorem sectionDApp_apply (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) :
    A.sectionDApp U n x = (A.complex.d n (n + 1)).val.app U x := rfl

/-- The differential of the ring of sections: on the degree-`n` summand it is the differential
of `A`, landing in the degree-`n + 1` summand. -/
def sectionD : A.toGradedAlgebra.totalSections U →+ A.toGradedAlgebra.totalSections U :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) (n + 1)).comp (A.sectionDApp U n)

/-- The differential of the ring of sections carries a degree-`n` section `x` to the degree-`n + 1`
section `d^n x`. -/
@[simp] theorem sectionD_of (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) :
    A.sectionD U (DirectSum.of _ n x) =
      DirectSum.of _ (n + 1) ((A.complex.d n (n + 1)).val.app U x) :=
  DirectSum.toAddMonoid_of _ n x

/-- The differential of the ring of sections, as a map linear over the lifted integers. -/
def sectionDLinear :
    A.toGradedAlgebra.totalSections U →ₗ[ULift.{a, 0} ℤ] A.toGradedAlgebra.totalSections U where
  toFun := A.sectionD U
  map_add' := map_add _
  map_smul' c x := by
    change A.sectionD U ((c.down : ℤ) • x) = (c.down : ℤ) • A.sectionD U x
    exact map_zsmul (A.sectionD U) c.down x

/-- The linear differential `sectionDLinear` agrees with `sectionD` pointwise. -/
@[simp] theorem sectionDLinear_apply (x : A.toGradedAlgebra.totalSections U) :
    A.sectionDLinear U x = A.sectionD U x := rfl

/-- The differential of the ring of sections squares to zero. -/
theorem sectionD_sectionD (x : A.toGradedAlgebra.totalSections U) :
    A.sectionD U (A.sectionD U x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n y =>
      rw [sectionD_of, sectionD_of]
      have h : (A.complex.d n (n + 1) ≫ A.complex.d (n + 1) (n + 1 + 1)) = 0 :=
        A.complex.d_comp_d _ _ _
      have h₂ : (A.complex.d (n + 1) (n + 1 + 1)).val.app U
          ((A.complex.d n (n + 1)).val.app U y) = 0 := by
        rw [← comp_val_app_apply, h, zero_val_app_apply]
      rw [h₂, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- **The differential graded algebra of sections of a sheaf of differential graded algebras
over an object of the site.** Its underlying ring is the direct sum of the sections of the
homogeneous pieces, its grading is by the summands of that direct sum, and its differential is
the differential of `A` read on sections. -/
def sectionAlgebra : _root_.DifferentialGradedAlgebra.{a, a} (ULift.{a, 0} ℤ) where
  A := A.toGradedAlgebra.totalSections U
  grading := Stacks.ExternalGrading.intSummand (A.toGradedAlgebra.sectionsPiece U)
  d := A.sectionDLinear U
  d_comp_d := LinearMap.ext fun x ↦ A.sectionD_sectionD U x
  d_mem := by
    rintro n x ⟨y, rfl⟩
    rw [sectionDLinear_apply, sectionD_of]
    exact Stacks.ExternalGrading.of_mem_intSummand (A.toGradedAlgebra.sectionsPiece U) (n + 1) _
  leibniz := by
    rintro n m x y ⟨p, rfl⟩ ⟨q, rfl⟩
    simp only [GradedAlgebra.of_mul_of_eq, sectionDLinear_apply, sectionD_of,
      toGradedAlgebra_mul]
    rw [A.leibniz n m U p q, map_add, of_gradedCast, map_zsmul, of_gradedCast]

/-- The differential of the section algebra `A(U)` carries a degree-`n` section `x` to the
degree-`n + 1` section `d^n x`. -/
theorem sectionAlgebra_d_of (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) :
    (A.sectionAlgebra U).d (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n x) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) (n + 1)
        ((A.complex.d n (n + 1)).val.app U x) :=
  A.sectionD_of U n x

/-! ### Restriction along a morphism of the site -/

section Restriction

variable {U V : Cᵒᵖ}

/-- Restriction of sections of the degree-`n` piece along a morphism of `Cᵒᵖ`. -/
def sectionRestrictApp (a : V ⟶ U) (n : ℤ) :
    A.toGradedAlgebra.sectionsPiece V n →+ A.toGradedAlgebra.sectionsPiece U n :=
  AddMonoidHom.mk' (fun x ↦ (A.complex.X n).val.map a x) fun x y ↦ map_add _ x y

/-- `sectionRestrictApp a n` is the restriction map of the degree-`n` piece of `A` along `a`. -/
theorem sectionRestrictApp_apply (a : V ⟶ U) (n : ℤ)
    (x : A.toGradedAlgebra.sectionsPiece V n) :
    A.sectionRestrictApp a n x = (A.complex.X n).val.map a x := rfl

/-- Restriction of sections carries the unit of `A` to the unit of `A`: the unit is a global
section. -/
theorem sectionRestrictApp_one (a : V ⟶ U) :
    A.sectionRestrictApp a 0 (A.one.eval V) = A.one.eval U :=
  PresheafOfModules.sections_property A.one a

/-- Restriction of sections is multiplicative: the graded multiplication of `A` is natural in
the object of the site. -/
theorem sectionRestrictApp_mul (a : V ⟶ U) (i j : ℤ)
    (p : A.toGradedAlgebra.sectionsPiece V i) (q : A.toGradedAlgebra.sectionsPiece V j) :
    A.sectionRestrictApp a (i + j) ((A.mul i j).app V p q) =
      (A.mul i j).app U (A.sectionRestrictApp a i p) (A.sectionRestrictApp a j q) :=
  (A.mul i j).naturality a p q

/-- Restriction of sections commutes with the differential of `A`. -/
theorem sectionRestrictApp_sectionDApp (a : V ⟶ U) (n : ℤ)
    (p : A.toGradedAlgebra.sectionsPiece V n) :
    A.sectionRestrictApp a (n + 1) (A.sectionDApp V n p) =
      A.sectionDApp U n (A.sectionRestrictApp a n p) :=
  (PresheafOfModules.naturality_apply (A.complex.d n (n + 1)).val a p).symm

/-- **Restriction of sections as a ring homomorphism** `A(V) ⟶ A(U)`: on each summand it is the
restriction map of `A`, and it is multiplicative because the graded multiplication of `A` is
natural in the object of the site. -/
def sectionRestrictRing (a : V ⟶ U) :
    A.toGradedAlgebra.totalSections V →+* A.toGradedAlgebra.totalSections U :=
  DirectSum.toSemiring
    (fun n ↦ (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n).comp (A.sectionRestrictApp a n))
    (by
      change DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0
          (A.sectionRestrictApp a 0 (A.one.eval V)) = 1
      rw [A.sectionRestrictApp_one a]
      exact DirectSum.of_zero_one _)
    (fun {i j} p q ↦ by
      change DirectSum.of (A.toGradedAlgebra.sectionsPiece U) (i + j)
          (A.sectionRestrictApp a (i + j) ((A.mul i j).app V p q)) = _
      rw [A.sectionRestrictApp_mul a i j p q]
      exact (GradedAlgebra.of_mul_of_eq A.toGradedAlgebra U i j _ _).symm)

/-- On the degree-`n` summand, `sectionRestrictRing a` is the restriction map of the degree-`n`
piece of `A` along `a`. -/
@[simp] theorem sectionRestrictRing_of (a : V ⟶ U) (n : ℤ)
    (x : A.toGradedAlgebra.sectionsPiece V n) :
    A.sectionRestrictRing a (DirectSum.of (A.toGradedAlgebra.sectionsPiece V) n x) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n (A.sectionRestrictApp a n x) :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n).comp (A.sectionRestrictApp a n))
    n x

/-- Restriction of sections commutes with the differential: the differential of `A` is a
morphism of sheaves of modules, so it is natural in the object of the site. -/
theorem sectionRestrictRing_comp_sectionD (a : V ⟶ U) :
    (A.sectionRestrictRing a).toAddMonoidHom.comp (A.sectionD V) =
      (A.sectionD U).comp (A.sectionRestrictRing a).toAddMonoidHom := by
  refine DirectSum.addHom_ext fun n p ↦ ?_
  change A.sectionRestrictRing a (A.sectionD V (DirectSum.of _ n p)) =
    A.sectionD U (A.sectionRestrictRing a (DirectSum.of _ n p))
  rw [sectionD_of, sectionRestrictRing_of, sectionRestrictRing_of, sectionD_of]
  exact congrArg _ (A.sectionRestrictApp_sectionDApp a n p)

/-- Restriction of sections along `a` commutes with the differential, pointwise. -/
theorem sectionRestrictRing_sectionD (a : V ⟶ U) (x : A.toGradedAlgebra.totalSections V) :
    A.sectionRestrictRing a (A.sectionD V x) = A.sectionD U (A.sectionRestrictRing a x) :=
  DFunLike.congr_fun (A.sectionRestrictRing_comp_sectionD a) x

/-- **The homomorphism of differential graded algebras `A(V) ⟶ A(U)`** attached to a morphism
`a : V ⟶ U` of `Cᵒᵖ`: restriction of sections. -/
def sectionRestriction (a : V ⟶ U) : (A.sectionAlgebra V).Hom (A.sectionAlgebra U) where
  toAlgebraHom := Stacks.uliftIntAlgHom (A.sectionRestrictRing a)
  map_grading := by
    rintro n x ⟨p, rfl⟩
    exact ⟨_, (A.sectionRestrictRing_of a n p).symm⟩
  map_d x := A.sectionRestrictRing_sectionD a x

/-- On the degree-`n` summand, the homomorphism `A(V) ⟶ A(U)` attached to `a` is the restriction
map of the degree-`n` piece of `A` along `a`. -/
theorem sectionRestriction_of (a : V ⟶ U) (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece V n) :
    (A.sectionRestriction a).toAlgebraHom
        (DirectSum.of (A.toGradedAlgebra.sectionsPiece V) n x) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n (A.sectionRestrictApp a n x) :=
  A.sectionRestrictRing_of a n x

end Restriction

end DifferentialGradedAlgebra

end SheafOfModules

end
