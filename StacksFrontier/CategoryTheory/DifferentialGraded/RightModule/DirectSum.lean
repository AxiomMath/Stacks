module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.Biproduct
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# The zero module and direct sums of right differential graded modules

The differential graded category `Mod^dg(C)` of right differential graded modules over a
differential graded category `C` over a commutative ring `R` has a differential graded zero
object and differential graded binary direct sums, both computed degreewise: the zero module is
the one with a single element in every degree at every object, and the direct sum of `M` and `N`
is the module `x ↦ i ↦ M x i × N x i` with componentwise differential and action. Their four
structure morphisms are homogeneous of degree zero and closed, so they assemble into a
`DGCategory.BinaryBiproductData`, and together with the zero module they are exactly axiom (A)
of `DGCategory.DirectSumAxiomA`.

## Main definitions

* `DGCategory.RightModule.zero`: the zero right differential graded module.
* `DGCategory.RightModule.prod`: the direct sum of two right differential graded modules.
* `DGCategory.RightModule.prodInl`, `DGCategory.RightModule.prodInr`,
  `DGCategory.RightModule.prodFst` and `DGCategory.RightModule.prodSnd`: its four structure
  morphisms, homogeneous of degree zero.
* `DGCategory.RightModule.binaryBiproductData`: the direct sum as a differential graded direct
  sum in `Mod^dg(C)`.
* `DGCategory.rightModuleDirectSumAxiom`: axiom (A) for `Mod^dg(C)`.

## Main results

* `DGCategory.RightModule.subsingleton_hom_from_zero` and
  `DGCategory.RightModule.subsingleton_hom_to_zero`: the zero module is a differential graded
  zero object, i.e. there is at most one homogeneous morphism of any degree out of it or into
  it.
* `DGCategory.RightModule.prodInl_closed`, `DGCategory.RightModule.prodInr_closed`,
  `DGCategory.RightModule.prodFst_closed` and `DGCategory.RightModule.prodSnd_closed`: the four
  structure morphisms are cocycles.
* `DGCategory.RightModule.prodFst_prodInl`, `DGCategory.RightModule.prodFst_prodInr`,
  `DGCategory.RightModule.prodSnd_prodInl`, `DGCategory.RightModule.prodSnd_prodInr` and
  `DGCategory.RightModule.prodInl_prodFst_add_prodInr_prodSnd`: the five direct-sum identities.

## Implementation notes

The four structure morphisms have degree zero, so each of their components transports an element
along an equality `i + 0 = j` of degrees; this transport is
`DGCategory.RightModule.objCast`, exactly as for the identity morphism
`DGCategory.RightModule.homId`. Every proof below therefore ends in the normalisation lemmas of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Defs`, which compose two transports
(`DGCategory.RightModule.objCast_objCast`) or absorb one into the differential
(`DGCategory.RightModule.d_objCast`, `DGCategory.RightModule.objCast_d`) or into the action
(`DGCategory.RightModule.act_objCast`).

The closedness of a degree-zero morphism is isolated as
`DGCategory.RightModule.homD_eq_zero_of_comm_d`, which strips the Koszul sign `(-1)^0` and the
subtraction from `DGCategory.RightModule.homD` once and for all, leaving the single equation
saying that the morphism commutes with the two differentials.

## References

* [Stacks Project, Tag 09P4](https://stacks.math.columbia.edu/tag/09P4)
-/

@[expose] public section

namespace DGCategory

universe w v u r

variable {R : Type r} [CommRing R]

namespace RightModule

/-! ### The zero module -/

/-- The zero right differential graded module over `C`: a single element in every degree at
every object, with the only possible differential and action. -/
def zero (C : DGCategory.{v, u} R) : RightModule.{w} C where
  obj _ _ := PUnit.{w + 1}
  addCommGroup _ _ := inferInstance
  module _ _ := inferInstance
  d _ _ := PUnit.unit
  d_add _ _ _ := rfl
  d_smul _ _ _ := rfl
  d_d _ _ _ := rfl
  act _ _ _ := PUnit.unit
  act_add_left _ _ _ _ := rfl
  act_add_right _ _ _ _ := rfl
  act_smul_left _ _ _ _ := rfl
  act_smul_right _ _ _ _ := rfl
  leibniz _ _ _ _ := rfl
  assoc _ _ _ _ _ _ _ := rfl
  act_id _ := rfl

variable {C : DGCategory.{v, u} R}

/-- Each homogeneous part of the zero module is a subsingleton. -/
instance subsingleton_zero_obj (x : C.Obj) (i : ℤ) : Subsingleton ((zero.{w} C).obj x i) :=
  inferInstanceAs (Subsingleton PUnit.{w + 1})

/-- There is at most one homogeneous morphism of a given degree out of the zero module. -/
theorem subsingleton_hom_from_zero (N : RightModule.{w} C) (p : ℤ) :
    Subsingleton (HomogeneousMap (zero.{w} C) N p) := by
  refine ⟨fun φ ψ => ?_⟩
  ext x i j e a
  rw [Subsingleton.elim a 0, app_zero, app_zero]

/-- There is at most one homogeneous morphism of a given degree into the zero module. -/
theorem subsingleton_hom_to_zero (M : RightModule.{w} C) (p : ℤ) :
    Subsingleton (HomogeneousMap M (zero.{w} C) p) := by
  refine ⟨fun φ ψ => ?_⟩
  ext x i j e a
  exact Subsingleton.elim _ _

/-! ### The direct sum of two modules -/

/-- The direct sum of two right differential graded modules: the degreewise product, with the
componentwise differential and the componentwise action. -/
@[implicit_reducible]
def prod (M N : RightModule.{w} C) : RightModule.{w} C where
  obj x i := M.obj x i × N.obj x i
  addCommGroup _ _ := inferInstance
  module _ _ := inferInstance
  d h a := (M.d h a.1, N.d h a.2)
  d_add h a b := Prod.ext (M.d_add h a.1 b.1) (N.d_add h a.2 b.2)
  d_smul h c a := Prod.ext (M.d_smul h c a.1) (N.d_smul h c a.2)
  d_d h₁ h₂ a := Prod.ext (M.d_d h₁ h₂ a.1) (N.d_d h₁ h₂ a.2)
  act h a f := (M.act h a.1 f, N.act h a.2 f)
  act_add_left h a b f := Prod.ext (M.act_add_left h a.1 b.1 f) (N.act_add_left h a.2 b.2 f)
  act_add_right h a f g := Prod.ext (M.act_add_right h a.1 f g) (N.act_add_right h a.2 f g)
  act_smul_left h c a f := Prod.ext (M.act_smul_left h c a.1 f) (N.act_smul_left h c a.2 f)
  act_smul_right h c a f := Prod.ext (M.act_smul_right h c a.1 f) (N.act_smul_right h c a.2 f)
  leibniz h hl a f := Prod.ext (M.leibniz h hl a.1 f) (N.leibniz h hl a.2 f)
  assoc h₁ h₂ h₃ h₄ a g f :=
    Prod.ext (M.assoc h₁ h₂ h₃ h₄ a.1 g f) (N.assoc h₁ h₂ h₃ h₄ a.2 g f)
  act_id a := Prod.ext (M.act_id a.1) (N.act_id a.2)

variable (M N : RightModule.{w} C)

/-- The homogeneous parts of a direct sum are the products of the homogeneous parts. -/
theorem prod_obj (x : C.Obj) (i : ℤ) : (prod M N).obj x i = (M.obj x i × N.obj x i) := rfl

/-- The differential of a direct sum is componentwise. -/
theorem prod_d {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (a : M.obj x i) (b : N.obj x i) :
    (prod M N).d h (a, b) = (M.d h a, N.d h b) := rfl

/-- The action on a direct sum is componentwise. -/
theorem prod_act {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a : M.obj y m) (b : N.obj y m)
    (f : C.Hom x y n) : (prod M N).act h (a, b) f = (M.act h a f, N.act h b f) := rfl

/-- The degree transport of a direct sum is componentwise. -/
theorem prod_objCast (x : C.Obj) {i j : ℤ} (h : i = j) (a : M.obj x i) (b : N.obj x i) :
    (prod M N).objCast x h (a, b) = (M.objCast x h a, N.objCast x h b) := by subst h; rfl

/-! ### The four structure morphisms -/

/-- The underlying graded map of the inclusion of the first summand. -/
def prodInlFun : GradedMap M (prod M N) 0 := fun T =>
  (LinearMap.inl R (M.obj T.x T.j) (N.obj T.x T.j)).comp
    (M.objCast T.x (show T.i = T.j by have := T.hij; omega))

/-- The components of the first inclusion: the transport of the degree, into the first
factor. -/
theorem prodInlFun_apply (x : C.Obj) (i j : ℤ) (e : i + 0 = j) (a : M.obj x i) :
    prodInlFun M N ⟨x, i, j, e⟩ a = (M.objCast x (show i = j by omega) a, 0) := rfl

/-- The inclusion of the first summand of a direct sum, homogeneous of degree zero. -/
def prodInl : HomogeneousMap M (prod M N) 0 := by
  refine ⟨prodInlFun M N, ?_⟩
  intro x y i j n k l hij hik hjl hkl a f
  rw [prodInlFun_apply, prodInlFun_apply, prod_act]
  exact Prod.ext (M.act_objCast (show i = j by omega) (show k = l by omega) hik hjl a f).symm
    (N.act_zero_left hjl f).symm

/-- The value of the first inclusion. -/
@[simp] theorem app_prodInl {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (a : M.obj x i) :
    app (prodInl M N) e a = (M.objCast x (show i = j by omega) a, 0) := rfl

/-- The underlying graded map of the inclusion of the second summand. -/
def prodInrFun : GradedMap N (prod M N) 0 := fun T =>
  (LinearMap.inr R (M.obj T.x T.j) (N.obj T.x T.j)).comp
    (N.objCast T.x (show T.i = T.j by have := T.hij; omega))

/-- The components of the second inclusion: the transport of the degree, into the second
factor. -/
theorem prodInrFun_apply (x : C.Obj) (i j : ℤ) (e : i + 0 = j) (b : N.obj x i) :
    prodInrFun M N ⟨x, i, j, e⟩ b = (0, N.objCast x (show i = j by omega) b) := rfl

/-- The inclusion of the second summand of a direct sum, homogeneous of degree zero. -/
def prodInr : HomogeneousMap N (prod M N) 0 := by
  refine ⟨prodInrFun M N, ?_⟩
  intro x y i j n k l hij hik hjl hkl b f
  rw [prodInrFun_apply, prodInrFun_apply, prod_act]
  exact Prod.ext (M.act_zero_left hjl f).symm
    (N.act_objCast (show i = j by omega) (show k = l by omega) hik hjl b f).symm

/-- The value of the second inclusion. -/
@[simp] theorem app_prodInr {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (b : N.obj x i) :
    app (prodInr M N) e b = (0, N.objCast x (show i = j by omega) b) := rfl

/-- The underlying graded map of the projection onto the first summand. -/
def prodFstFun : GradedMap (prod M N) M 0 := fun T =>
  (M.objCast T.x (show T.i = T.j by have := T.hij; omega)).comp
    (LinearMap.fst R (M.obj T.x T.i) (N.obj T.x T.i))

/-- The components of the first projection: the first factor, transported in degree. -/
theorem prodFstFun_apply (x : C.Obj) (i j : ℤ) (e : i + 0 = j) (a : M.obj x i)
    (b : N.obj x i) :
    prodFstFun M N ⟨x, i, j, e⟩ (a, b) = M.objCast x (show i = j by omega) a := rfl

/-- The projection onto the first summand of a direct sum, homogeneous of degree zero. -/
def prodFst : HomogeneousMap (prod M N) M 0 := by
  refine ⟨prodFstFun M N, ?_⟩
  intro x y i j n k l hij hik hjl hkl a f
  obtain ⟨a₁, a₂⟩ := a
  rw [prod_act, prodFstFun_apply, prodFstFun_apply]
  exact (M.act_objCast (show i = j by omega) (show k = l by omega) hik hjl a₁ f).symm

/-- The value of the first projection. -/
@[simp] theorem app_prodFst {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (a : M.obj x i)
    (b : N.obj x i) : app (prodFst M N) e (a, b) = M.objCast x (show i = j by omega) a := rfl

/-- The underlying graded map of the projection onto the second summand. -/
def prodSndFun : GradedMap (prod M N) N 0 := fun T =>
  (N.objCast T.x (show T.i = T.j by have := T.hij; omega)).comp
    (LinearMap.snd R (M.obj T.x T.i) (N.obj T.x T.i))

/-- The components of the second projection: the second factor, transported in degree. -/
theorem prodSndFun_apply (x : C.Obj) (i j : ℤ) (e : i + 0 = j) (a : M.obj x i)
    (b : N.obj x i) :
    prodSndFun M N ⟨x, i, j, e⟩ (a, b) = N.objCast x (show i = j by omega) b := rfl

/-- The projection onto the second summand of a direct sum, homogeneous of degree zero. -/
def prodSnd : HomogeneousMap (prod M N) N 0 := by
  refine ⟨prodSndFun M N, ?_⟩
  intro x y i j n k l hij hik hjl hkl a f
  obtain ⟨a₁, a₂⟩ := a
  rw [prod_act, prodSndFun_apply, prodSndFun_apply]
  exact (N.act_objCast (show i = j by omega) (show k = l by omega) hik hjl a₂ f).symm

/-- The value of the second projection. -/
@[simp] theorem app_prodSnd {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (a : M.obj x i)
    (b : N.obj x i) : app (prodSnd M N) e (a, b) = N.objCast x (show i = j by omega) b := rfl

/-! ### Closedness of the structure morphisms -/

variable {M N}

/-- A homogeneous morphism of degree zero is closed exactly when it commutes with the two
differentials; this strips the Koszul sign and the subtraction from
`DGCategory.RightModule.homD`. -/
theorem homD_eq_zero_of_comm_d (φ : HomogeneousMap M N 0)
    (h : ∀ (x : C.Obj) (i j : ℤ) (h₁ : i + 0 + 1 = j) (h₂ : i + 1 + 0 = j) (a : M.obj x i),
      N.d h₁ (app φ rfl a) = app φ h₂ (M.d rfl a)) :
    homD φ = 0 := by
  ext x i j e a
  rw [app_homD, zero_app, h x i j (by omega) (by omega) a, Int.natAbs_zero, pow_zero, one_smul,
    sub_self]

variable (M N)

/-- A degree-zero transport commutes with the differential. -/
private theorem d_objCast_zero_add (P : RightModule.{w} C) {x : C.Obj} {i j : ℤ}
    (h₁ : i + 0 + 1 = j) (a : P.obj x i) :
    P.d h₁ (P.objCast x (show i = i + 0 by omega) a) =
      P.objCast x (show i + 1 = j by omega) (P.d rfl a) := by
  rw [P.d_objCast (show i = i + 0 by omega) h₁ (show i + 1 = j by omega),
    P.objCast_d (show i + 1 = j by omega)]

/-- The inclusion of the first summand is closed. -/
theorem prodInl_closed : homD (prodInl M N) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ a => ?_
  rw [app_prodInl, app_prodInl, prod_d]
  exact Prod.ext (d_objCast_zero_add M h₁ a) (N.d_zero h₁)

/-- The inclusion of the second summand is closed. -/
theorem prodInr_closed : homD (prodInr M N) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ b => ?_
  rw [app_prodInr, app_prodInr, prod_d]
  exact Prod.ext (M.d_zero h₁) (d_objCast_zero_add N h₁ b)

/-- The projection onto the first summand is closed. -/
theorem prodFst_closed : homD (prodFst M N) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ a => ?_
  obtain ⟨a₁, a₂⟩ := a
  rw [prod_d, app_prodFst, app_prodFst]
  exact d_objCast_zero_add M h₁ a₁

/-- The projection onto the second summand is closed. -/
theorem prodSnd_closed : homD (prodSnd M N) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ a => ?_
  obtain ⟨a₁, a₂⟩ := a
  rw [prod_d, app_prodSnd, app_prodSnd]
  exact d_objCast_zero_add N h₁ a₂

/-! ### The direct-sum identities -/

/-- The first projection retracts the first inclusion. -/
theorem prodFst_prodInl :
    homComp (by rfl : (0 : ℤ) + 0 = 0) (prodFst M N) (prodInl M N) = homId M := by
  ext x i j e a
  rw [app_homComp, app_prodInl, app_prodFst, app_homId, objCast_objCast]

/-- The first projection kills the second inclusion. -/
theorem prodFst_prodInr :
    homComp (by rfl : (0 : ℤ) + 0 = 0) (prodFst M N) (prodInr M N) = 0 := by
  ext x i j e b
  rw [app_homComp, app_prodInr, app_prodFst, zero_app, map_zero]

/-- The second projection kills the first inclusion. -/
theorem prodSnd_prodInl :
    homComp (by rfl : (0 : ℤ) + 0 = 0) (prodSnd M N) (prodInl M N) = 0 := by
  ext x i j e a
  rw [app_homComp, app_prodInl, app_prodSnd, zero_app, map_zero]

/-- The second projection retracts the second inclusion. -/
theorem prodSnd_prodInr :
    homComp (by rfl : (0 : ℤ) + 0 = 0) (prodSnd M N) (prodInr M N) = homId N := by
  ext x i j e b
  rw [app_homComp, app_prodInr, app_prodSnd, app_homId, objCast_objCast]

/-- The two summands jointly span the direct sum. -/
theorem prodInl_prodFst_add_prodInr_prodSnd :
    homComp (by rfl : (0 : ℤ) + 0 = 0) (prodInl M N) (prodFst M N) +
        homComp (by rfl : (0 : ℤ) + 0 = 0) (prodInr M N) (prodSnd M N) =
      homId (prod M N) := by
  ext x i j e a
  obtain ⟨a₁, a₂⟩ := a
  rw [add_app, app_homComp, app_homComp, app_prodFst, app_prodSnd, app_prodInl, app_prodInr,
    app_homId, prod_objCast, objCast_objCast, objCast_objCast, Prod.mk_add_mk, add_zero,
    zero_add]

/-! ### The direct sum as a differential graded biproduct -/

/-- The direct sum of two right differential graded modules, as a differential graded direct
sum in `Mod^dg(C)`. -/
def binaryBiproductData : BinaryBiproductData (rightModuleCategory.{w} C) M N where
  pt := prod M N
  inl := prodInl M N
  inr := prodInr M N
  fst := prodFst M N
  snd := prodSnd M N
  inl_closed := prodInl_closed M N
  inr_closed := prodInr_closed M N
  fst_closed := prodFst_closed M N
  snd_closed := prodSnd_closed M N
  inl_fst := prodFst_prodInl M N
  inr_fst := prodFst_prodInr M N
  inl_snd := prodSnd_prodInl M N
  inr_snd := prodSnd_prodInr M N
  fst_inl_add_snd_inr := prodInl_prodFst_add_prodInr_prodSnd M N

end RightModule

/-- Axiom (A) for the differential graded category of right differential graded `C`-modules: the
zero module is a differential graded zero object and the degreewise product is a differential
graded direct sum. -/
def rightModuleDirectSumAxiom (C : DGCategory.{v, u} R) :
    DirectSumAxiomA (rightModuleCategory.{w} C) where
  zero := RightModule.zero C
  zero_from N p := RightModule.subsingleton_hom_from_zero N p
  zero_to M p := RightModule.subsingleton_hom_to_zero M p
  binaryBiproduct M N := ⟨RightModule.binaryBiproductData M N⟩

end DGCategory
