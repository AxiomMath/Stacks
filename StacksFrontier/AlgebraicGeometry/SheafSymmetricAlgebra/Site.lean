module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.GradedPieces

/-!
# The sectionwise symmetric algebra of a presheaf of modules, as a graded algebra

Let `O` be a presheaf of commutative rings on a site and `F` a presheaf of `O`-modules. This
file makes the family of presheaves of modules

`U ↦ Sym^n_{O(U)}(F(U))`, `n : ℤ`

**into a graded algebra of presheaves of modules** (`Stacks.GradedAlgebra`), with multiplication
the graded multiplication of the symmetric algebra of the sections and unit the unit of that
algebra. It also records the degree-one generator `F ⟶ Sym^1 F`, the commutativity of the
multiplication and the vanishing of the negative-degree pieces.

Unlike the affine construction of `StacksDraft.AlgebraicGeometry.AffineSymmetricAlgebra`, nothing
here is a base change: the sections over `U` are the symmetric powers of the sections of `F` over
`U` taken over the ring `O(U)` itself, so the multiplication is the `O(U)`-bilinear
`Stacks.SymGraded.symMulₗ` with no tensor product interposed, and the restriction maps are the
*semilinear* base change `SymmetricAlgebra.mapₛₗ` of the symmetric algebra along the restriction
maps of `O` and of `F`.

## Main definitions

* `Stacks.SymGraded.gradedMapₛₗ`: the `ℤ`-indexed form of `SymPow.symMapₛₗ`, the restriction of
  `SymmetricAlgebra.mapₛₗ` to the degree-`n` graded pieces, and `Stacks.SymGraded.gradedCongr`,
  the equivalence it induces from a linear equivalence of modules.
* `Stacks.SymGraded.siteGradedPiece`: the presheaf `U ↦ Sym^n_{O(U)}(F(U))`, for `n : ℤ`.
* `Stacks.SymGraded.siteMul` and `Stacks.SymGraded.siteOne`: the graded multiplication as a
  bilinear map of presheaves of modules, and the unit as a global section of degree zero.
* `Stacks.SymGraded.sitePresheafAlgebra`: **the graded algebra of presheaves of modules.**
* `Stacks.SymGraded.siteGen`: the degree-one generator `F ⟶ Sym^1 F`.

## Main results

* `Stacks.SymGraded.mapₛₗ_mem_gradedPiece`: the semilinear base change of the symmetric algebra
  preserves the `ℤ`-graded pieces. For a nonnegative degree this is
  `SymmetricAlgebra.mapₛₗ_mem_symmetricPower`; for a negative one both pieces are zero.
* `Stacks.SymGraded.siteMul_comm`: the multiplication is commutative, in every pair of degrees.
* `Stacks.SymGraded.siteGradedPiece_eq_zero_of_neg`: the negative-degree pieces have no nonzero
  local sections.
* `Stacks.SymGraded.genCommutes_siteGen`: the degree-one local sections in the image of the
  generator commute pairwise.

## Implementation notes

**The ring and the module live in one universe.** `Stacks.SymGraded.gradedPiece` is stated for a
ring and a module in the same universe, so the presheaf of modules here is
`PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)` for `O : Cᵒᵖ ⥤ CommRingCat.{w}`. This covers
the structure sheaf of a scheme and a module over it. The sectionwise symmetric powers of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification` allow a module
universe `max w a`; only `SymmetricAlgebra.mapₛₗ` is used from there.

Nothing is sheafified here, and nothing is said about quasi-coherence.

**Degrees are `ℤ` and `i + j` is not `j + i`.** The associativity, unit and commutativity laws
are heterogeneous equalities, because the two sides of each live in graded pieces whose degrees
are equal integers but not definitionally equal terms. They are all discharged by
`Stacks.SymGraded.heq_gradedPiece_of_coe_eq`, which substitutes the degree equality and reduces
the law to the corresponding law in `SymmetricAlgebra (O(U)) (F(U))` — associativity,
unitality and commutativity of a commutative ring.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u w

namespace Stacks.SymGraded

/-! ### The graded pieces of a semilinear base change -/

section Algebraic

variable {R S : Type w} [CommRing R] [CommRing S]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module S N]

/-- Two homogeneous elements of a symmetric algebra whose degrees are equal and whose underlying
elements are equal are heterogeneously equal. -/
theorem heq_gradedPiece_of_coe_eq {i j : ℤ} (h : i = j) {x : gradedPiece (R := R) M i}
    {y : gradedPiece (R := R) M j}
    (hxy : (x : SymmetricAlgebra R M) = (y : SymmetricAlgebra R M)) : HEq x y := by
  subst h
  exact heq_of_eq (Subtype.ext hxy)

/-- An element of a negative-degree graded piece is zero. -/
private theorem eq_zero_of_mem_gradedPiece_negSucc {k : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ gradedPiece (R := R) M (Int.negSucc k)) : x = 0 :=
  Submodule.mem_bot R |>.1 hx

/-- **The semilinear base change of the symmetric algebra preserves the `ℤ`-graded pieces.** For
a nonnegative degree this is `SymmetricAlgebra.mapₛₗ_mem_symmetricPower`; for a negative one
both pieces are the zero submodule. -/
theorem mapₛₗ_mem_gradedPiece (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℤ)
    {x : SymmetricAlgebra R M} (hx : x ∈ gradedPiece (R := R) M n) :
    SymmetricAlgebra.mapₛₗ φ u x ∈ gradedPiece (R := S) N n := by
  match n with
  | .ofNat k => exact SymmetricAlgebra.mapₛₗ_mem_symmetricPower φ u k hx
  | .negSucc k =>
      rw [eq_zero_of_mem_gradedPiece_negSucc hx, map_zero]
      exact Submodule.zero_mem _

/-- **The semilinear base change of the degree-`n` graded piece**, for `n : ℤ`: the restriction
of `SymmetricAlgebra.mapₛₗ φ u` to the degree-`n` pieces. For `n` a natural number this is
`SymPow.symMapₛₗ`. -/
def gradedMapₛₗ (n : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    gradedPiece (R := R) M n →ₛₗ[φ] gradedPiece (R := S) N n where
  toFun x := ⟨SymmetricAlgebra.mapₛₗ φ u x, mapₛₗ_mem_gradedPiece φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (SymmetricAlgebra.mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (SymmetricAlgebra.mapₛₗ_smul φ u r x)

/-- The underlying element of `gradedMapₛₗ n φ u x` is `SymmetricAlgebra.mapₛₗ φ u x`. -/
@[simp]
theorem gradedMapₛₗ_coe (n : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (x : gradedPiece (R := R) M n) :
    (gradedMapₛₗ n φ u x : SymmetricAlgebra S N) = SymmetricAlgebra.mapₛₗ φ u x := rfl

/-- The semilinear base change is multiplicative for the graded multiplication. -/
theorem gradedMapₛₗ_symMulₗ (i j : ℤ) (φ : R →+* S) (u : M →ₛₗ[φ] N)
    (x : gradedPiece (R := R) M i) (y : gradedPiece (R := R) M j) :
    gradedMapₛₗ (i + j) φ u (symMulₗ M i j x y) =
      symMulₗ N i j (gradedMapₛₗ i φ u x) (gradedMapₛₗ j φ u y) :=
  Subtype.ext (map_mul (SymmetricAlgebra.mapₛₗ φ u) (x : SymmetricAlgebra R M) y)

/-- The semilinear base change carries the degree-zero unit to the degree-zero unit. -/
theorem gradedMapₛₗ_oneG (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    gradedMapₛₗ 0 φ u (oneG M) = oneG N :=
  Subtype.ext (map_one (SymmetricAlgebra.mapₛₗ φ u))

/-- The semilinear base change carries the degree-one generators to the degree-one generators. -/
theorem gradedMapₛₗ_ιG (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    gradedMapₛₗ 1 φ u (ιG M m) = ιG N (u m) :=
  Subtype.ext (SymmetricAlgebra.mapₛₗ_ι φ u m)

end Algebraic

section Congr

variable {R : Type w} [CommRing R] {P Q : Type w} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]

/-- **A linear equivalence of modules induces one of their graded pieces.** This is
`Stacks.SymGraded.gradedMapₛₗ` along the identity ring homomorphism, with the inverse supplied by
the inverse equivalence; the two round trips are `SymmetricAlgebra.mapₛₗ_eq_comp` followed by
`SymmetricAlgebra.mapₛₗ_eq_self`. -/
def gradedCongr (n : ℤ) (e : P ≃ₗ[R] Q) :
    gradedPiece (R := R) P n ≃ₗ[R] gradedPiece (R := R) Q n :=
  { gradedMapₛₗ n (RingHom.id R) e.toLinearMap with
    invFun := gradedMapₛₗ n (RingHom.id R) e.symm.toLinearMap
    left_inv := fun x => Subtype.ext
      ((SymmetricAlgebra.mapₛₗ_eq_comp e.toLinearMap e.symm.toLinearMap LinearMap.id
        (fun _ => rfl) (fun m => (e.symm_apply_apply m).symm) (x : SymmetricAlgebra R P)).symm.trans
          (SymmetricAlgebra.mapₛₗ_eq_self (φ := RingHom.id R) LinearMap.id (fun _ => rfl)
            (fun _ => rfl) (x : SymmetricAlgebra R P)))
    right_inv := fun y => Subtype.ext
      ((SymmetricAlgebra.mapₛₗ_eq_comp e.symm.toLinearMap e.toLinearMap LinearMap.id
        (fun _ => rfl) (fun m => (e.apply_symm_apply m).symm)
          (y : SymmetricAlgebra R Q)).symm.trans
          (SymmetricAlgebra.mapₛₗ_eq_self (φ := RingHom.id R) LinearMap.id (fun _ => rfl)
            (fun _ => rfl) (y : SymmetricAlgebra R Q))) }

/-- The underlying element of `gradedCongr n e x` is the image of `x` under
`SymmetricAlgebra.mapₛₗ` along `e`. -/
@[simp]
theorem gradedCongr_coe (n : ℤ) (e : P ≃ₗ[R] Q) (x : gradedPiece (R := R) P n) :
    (gradedCongr n e x : SymmetricAlgebra R Q) =
      SymmetricAlgebra.mapₛₗ (RingHom.id R) e.toLinearMap (x : SymmetricAlgebra R P) := rfl

end Congr

/-! ### The presheaf of sectionwise graded pieces -/

section Presheaf

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- A restriction map of the presheaf of sectionwise graded pieces, as an additive map whose
target is written as a graded piece rather than as a restriction of scalars. -/
def siteRestrict (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n →+
      gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) n :=
  (gradedMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)).toAddMonoidHom

/-- The underlying element of `siteRestrict F n f x` is the image of `x` under the semilinear
base change of the symmetric algebra along the restriction maps of `O` and `F`. -/
@[simp]
theorem siteRestrict_coe (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n) :
    (siteRestrict F n f x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise graded pieces. -/
def siteGradedPieceAb (n : ℤ) : Cᵒᵖ ⥤ Ab.{w} where
  obj X := AddCommGrpCat.of (gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n)
  map f := AddCommGrpCat.ofHom (siteRestrict F n f)
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

/-- The sections of `Stacks.SymGraded.siteGradedPieceAb F n` over `X` form an `O(X)`-module, the
graded piece `Sym^n_{O(X)}(F(X))`. -/
instance siteGradedPieceAbModule (n : ℤ) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((siteGradedPieceAb F n).obj X) :=
  inferInstanceAs (Module ((O ⋙ forget₂ _ RingCat).obj X)
    (gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n))

/-- **The presheaf of sectionwise degree-`n` graded pieces of the symmetric algebra.** Its
sections over `X` are `Sym^n_{O(X)}(F(X))` for `n ≥ 0` and zero otherwise, and its restriction
maps are the semilinear base changes of the restriction maps of `F`. -/
def siteGradedPiece (n : ℤ) : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (siteGradedPieceAb F n) fun {_ _} _ r _ =>
    Subtype.ext (SymmetricAlgebra.mapₛₗ_smul _ _ r _)

/-- The sections of `Stacks.SymGraded.siteGradedPiece` are the graded pieces of the symmetric
algebra of the sections, on the nose. -/
theorem siteGradedPiece_obj (n : ℤ) (X : Cᵒᵖ) :
    ((siteGradedPiece F n).obj X : Type w) =
      gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) n := rfl

/-- The restriction maps of `Stacks.SymGraded.siteGradedPiece F n` are, on underlying elements,
the semilinear base change of the symmetric algebra along the restriction maps of `O` and `F`. -/
@[simp]
theorem siteGradedPiece_map_val (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (siteGradedPiece F n).obj X) :
    ((siteGradedPiece F n).map f x).val =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x.val := rfl

/-- **The graded multiplication**, as a bilinear map of presheaves of modules. -/
def siteMul (i j : ℤ) :
    Stacks.BilinearMap (siteGradedPiece F i) (siteGradedPiece F j)
      (siteGradedPiece F (i + j)) where
  app X := AddMonoidHom.mk' (fun x => (symMulₗ (F.obj X) i j x).toAddMonoidHom)
    fun x x' => AddMonoidHom.ext fun y =>
      congrArg (fun g : gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) j →ₗ[(O ⋙
          forget₂ _ RingCat).obj X]
          gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (i + j) => g y)
        (map_add (symMulₗ (F.obj X) i j) x x')
  map_smul_left X r x y :=
    congrArg (fun g : gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) j →ₗ[(O ⋙
        forget₂ _ RingCat).obj X]
        gradedPiece (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (i + j) => g y)
      ((symMulₗ (F.obj X) i j).map_smul r x)
  map_smul_right X r x y := (symMulₗ (F.obj X) i j x).map_smul r y
  naturality _ _ _ := Subtype.ext (map_mul _ _ _)

/-- On underlying elements, `siteMul F i j` is the product in the symmetric algebra. -/
@[simp]
theorem siteMul_app_val (i j : ℤ) (X : Cᵒᵖ) (x : (siteGradedPiece F i).obj X)
    (y : (siteGradedPiece F j).obj X) :
    ((siteMul F i j).app X x y).val = x.val * y.val := rfl

/-- **The unit**, as a global section of the degree-zero piece. -/
def siteOne : (siteGradedPiece F 0).sections :=
  PresheafOfModules.sectionsMk (fun X => oneG (F.obj X)) fun {_ _} _ =>
    Subtype.ext (map_one _)

/-- The section `siteOne F` over `X` is the degree-zero unit `oneG (F.obj X)`. -/
@[simp]
theorem siteOne_eval (X : Cᵒᵖ) : (siteOne F).eval X = oneG (F.obj X) := rfl

/-- **The sectionwise symmetric algebra of `F`, as a graded algebra of presheaves of
modules.** -/
def sitePresheafAlgebra : Stacks.GradedAlgebra (siteGradedPiece F) where
  mul := siteMul F
  one := siteOne F
  mul_assoc i j k _ _ _ _ :=
    heq_gradedPiece_of_coe_eq (add_assoc i j k) (_root_.mul_assoc _ _ _)
  one_mul i _ _ := heq_gradedPiece_of_coe_eq (zero_add i) (_root_.one_mul _)
  mul_one i _ _ := heq_gradedPiece_of_coe_eq (add_zero i) (_root_.mul_one _)

/-- The multiplication of `sitePresheafAlgebra F` is `siteMul F`. -/
theorem sitePresheafAlgebra_mul (i j : ℤ) : (sitePresheafAlgebra F).mul i j = siteMul F i j := rfl

/-- The unit of `sitePresheafAlgebra F` is `siteOne F`. -/
theorem sitePresheafAlgebra_one : (sitePresheafAlgebra F).one = siteOne F := rfl

/-- **The multiplication is commutative**, in every pair of degrees. -/
theorem siteMul_comm (i j : ℤ) (X : Cᵒᵖ) (x : (siteGradedPiece F i).obj X)
    (y : (siteGradedPiece F j).obj X) :
    HEq ((siteMul F i j).app X x y) ((siteMul F j i).app X y x) :=
  heq_gradedPiece_of_coe_eq (add_comm i j) (_root_.mul_comm _ _)

/-- **The negative-degree pieces have no nonzero local sections.** -/
theorem siteGradedPiece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (x : (siteGradedPiece F n).obj X) : x = 0 := by
  match n, hn with
  | .negSucc _, _ => exact Subtype.ext (eq_zero_of_mem_gradedPiece_negSucc x.2)

/-! ### The degree-one generator -/

/-- **The degree-one generator** `F ⟶ Sym^1 F`, the sectionwise degree-one inclusion of the
symmetric algebra. -/
def siteGen : F ⟶ siteGradedPiece F 1 where
  app X := ModuleCat.ofHom (ιG (R := (O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext
    (SymmetricAlgebra.mapₛₗ_ι ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) m).symm)

/-- On underlying elements, `siteGen F` over `X` is the canonical map
`SymmetricAlgebra.ι` of the sections of `F` over `X`. -/
@[simp]
theorem siteGen_app_val (X : Cᵒᵖ) (m : F.obj X) :
    (PresheafOfModules.Hom.app (siteGen F) X m).val =
      SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) m := rfl

/-- **The degree-one local sections in the image of the generator commute pairwise.** -/
theorem genCommutes_siteGen :
    (sitePresheafAlgebra F).GenCommutes (siteGen F) := fun _ _ _ =>
  Subtype.ext (_root_.mul_comm _ _)

end Presheaf

end Stacks.SymGraded

end
