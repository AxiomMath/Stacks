module

public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# Right differential graded modules over a differential graded category

Let `C` be a differential graded category over a commutative ring `R`. A *right differential
graded `C`-module* `M` assigns to every object `x` of `C` a differential graded `R`-module
`M x`, and to every homogeneous morphism `f : x ⟶ y` of degree `n` a degree-raising map
`M y ⟶ M x` — the right action `a ↦ a · f` — which is associative and unital for the
composition of `C` and satisfies the graded Leibniz rule with the differential. Equivalently it
is a functor of differential graded categories from `Cᵒᵖ` to the complexes of `R`-modules; the
right-action formulation used here is the one in which no Koszul sign is introduced by passing
to the opposite category, so the action of `C` on a module is literally the composition of `C`.

The motivating example is the representable module `h_X = C(-, X)` of an object `X`, for which
the action is composition; it is constructed in
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Yoneda`.

## Main definitions

* `DGCategory.RightModule`: a right differential graded module over a differential graded
  category.

## Main results

* `DGCategory.RightModule.d_zero`, `DGCategory.RightModule.act_zero_left`,
  `DGCategory.RightModule.act_zero_right`, `DGCategory.RightModule.act_sub_left` and
  `DGCategory.RightModule.act_sub_right`: the elementary consequences of the axioms, matching
  the corresponding lemmas for `DGCategory` itself.
* `DGCategory.RightModule.objCast`: the transport of elements along an equality of degrees,
  with `DGCategory.RightModule.objCast_rfl`, `DGCategory.RightModule.objCast_d` and
  `DGCategory.RightModule.objCast_act`, which rewrite a differential or an action reaching a
  prescribed degree as the canonical one followed by a transport.

## Implementation notes

The degrees of a module are indexed exactly as the degrees of `DGCategory` are: a module is a
family `obj : C.Obj → ℤ → Type w` of `R`-modules rather than a single graded object, and the
differential and the action carry an explicit equality of degrees (`d : i + 1 = j → obj x i →
obj x j`, `act : m + n = k → obj y m → C.Hom x y n → obj x k`) instead of landing in the
canonical degree. This is the device `DGCategory.comp` already uses, and it is what keeps the
composition of homogeneous morphisms of modules free of transports: the degree arithmetic is
absorbed into a proof argument, which is irrelevant definitionally, rather than into a cast of
the ambient type. Where a transport is genuinely unavoidable — the identity morphism, whose
degree equation is `i + 0 = j` — it is `DGCategory.RightModule.objCast`, which is the identity
on the nose at a reflexivity proof.

Giving the action rather than a functor on `Cᵒᵖ` is not a weakening: the opposite of a
differential graded category has composition twisted by the Koszul sign `(-1)^{mn}`, and the
unsigned right action above is the image of a `Cᵒᵖ`-functor under that twist. The unsigned form
is what makes `C(-, X)` a module by `DGCategory.assoc` and `DGCategory.leibniz` verbatim.
-/

@[expose] public section

namespace DGCategory

universe w v u r

/-- A *right differential graded module* over a differential graded category `C` over `R`: a
family of `R`-modules `obj x i` (the degree-`i` part at the object `x`) with a differential
raising the degree by one and squaring to zero, together with a right action of the homogeneous
morphisms of `C` which is `R`-bilinear, associative and unital for the composition of `C` and
obeys the graded Leibniz rule.

As for `DGCategory`, the differential and the action carry an explicit equality of degrees, so
that no transport along the arithmetic of `ℤ` is ever needed to state a composite. -/
structure RightModule {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) where
  /-- The degree-`i` part of the module at the object `x`. -/
  obj : C.Obj → ℤ → Type w
  /-- Each homogeneous part is an additive abelian group. -/
  addCommGroup : ∀ x i, AddCommGroup (obj x i)
  /-- Each homogeneous part is an `R`-module. -/
  module : ∀ x i, @Module R (obj x i) _ (addCommGroup x i).toAddCommMonoid
  /-- The differential, raising the degree by one into a prescribed degree `j`. -/
  d : ∀ {x : C.Obj} {i j : ℤ}, i + 1 = j → obj x i → obj x j
  /-- The differential is additive. -/
  d_add : ∀ {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (a b : obj x i), d h (a + b) = d h a + d h b
  /-- The differential is `R`-linear. -/
  d_smul : ∀ {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (c : R) (a : obj x i),
    d h (c • a) = c • d h a
  /-- `d ∘ d = 0`. -/
  d_d : ∀ {x : C.Obj} {i j k : ℤ} (h₁ : i + 1 = j) (h₂ : j + 1 = k) (a : obj x i),
    d h₂ (d h₁ a) = 0
  /-- The right action of a degree-`n` morphism `f : x ⟶ y` on a degree-`m` element at `y`,
  landing in the prescribed degree `k = m + n` at `x`. -/
  act : ∀ {x y : C.Obj} {m n k : ℤ}, m + n = k → obj y m → C.Hom x y n → obj x k
  /-- The action is additive in the module variable. -/
  act_add_left : ∀ {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a b : obj y m)
    (f : C.Hom x y n), act h (a + b) f = act h a f + act h b f
  /-- The action is additive in the morphism variable. -/
  act_add_right : ∀ {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a : obj y m)
    (f g : C.Hom x y n), act h a (f + g) = act h a f + act h a g
  /-- The action is `R`-linear in the module variable. -/
  act_smul_left : ∀ {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (c : R) (a : obj y m)
    (f : C.Hom x y n), act h (c • a) f = c • act h a f
  /-- The action is `R`-linear in the morphism variable. -/
  act_smul_right : ∀ {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (c : R) (a : obj y m)
    (f : C.Hom x y n), act h a (c • f) = c • act h a f
  /-- The graded Leibniz rule: for `a` of degree `m` and `f` of degree `n`,
  `d (a · f) = (d a) · f + (-1)^m • a · (d f)`. -/
  leibniz : ∀ {x y : C.Obj} {m n k l : ℤ} (h : m + n = k) (hl : k + 1 = l) (a : obj y m)
    (f : C.Hom x y n),
    d hl (act h a f) =
      act (by omega : m + 1 + n = l) (d rfl a) f +
        (-1 : R) ^ m.natAbs • act (by omega : m + (n + 1) = l) a (C.d f)
  /-- Associativity of the action over the composition of `C`. -/
  assoc : ∀ {x y z : C.Obj} {l m n p q s : ℤ}
    (h₁ : m + n = p) (h₂ : l + p = s) (h₃ : l + m = q) (h₄ : q + n = s)
    (a : obj z l) (g : C.Hom y z m) (f : C.Hom x y n),
    act h₂ a (C.comp h₁ g f) = act h₄ (act h₃ a g) f
  /-- The identity acts as the identity. -/
  act_id : ∀ {x : C.Obj} {n : ℤ} (a : obj x n), act (add_zero n) a (C.id x) = a

attribute [instance] RightModule.addCommGroup RightModule.module

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R} (M : RightModule.{w} C)

/-! ### Elementary consequences of the axioms -/

/-- The differential of `M` sends `0` to `0`. -/
@[simp] lemma d_zero {x : C.Obj} {i j : ℤ} (h : i + 1 = j) : M.d h (0 : M.obj x i) = 0 := by
  exact map_zero (AddMonoidHom.mk' (M.d h) (M.d_add h))

/-- The zero element of `M` acted on by any morphism is `0`. -/
@[simp] lemma act_zero_left {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (f : C.Hom x y n) :
    M.act h (0 : M.obj y m) f = 0 := by
  exact map_zero (AddMonoidHom.mk' (fun a => M.act h a f) fun a b => M.act_add_left h a b f)

/-- The action of the zero morphism on any element of `M` is `0`. -/
@[simp] lemma act_zero_right {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a : M.obj y m) :
    M.act h a (0 : C.Hom x y n) = 0 := by
  exact map_zero (AddMonoidHom.mk' (M.act h a) (M.act_add_right h a))

/-- The differential of `M` commutes with subtraction. -/
lemma d_sub {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (a b : M.obj x i) :
    M.d h (a - b) = M.d h a - M.d h b := by
  exact map_sub (AddMonoidHom.mk' (M.d h) (M.d_add h)) a b

/-- The action commutes with subtraction in the module variable. -/
lemma act_sub_left {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a b : M.obj y m)
    (f : C.Hom x y n) : M.act h (a - b) f = M.act h a f - M.act h b f := by
  exact map_sub (AddMonoidHom.mk' (fun a => M.act h a f) fun a b => M.act_add_left h a b f) a b

/-- The action commutes with subtraction in the morphism variable. -/
lemma act_sub_right {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a : M.obj y m)
    (f g : C.Hom x y n) : M.act h a (f - g) = M.act h a f - M.act h a g := by
  exact map_sub (AddMonoidHom.mk' (M.act h a) (M.act_add_right h a)) f g

/-! ### The differential and the action as linear maps -/

/-- The differential of `M` at `x`, from degree `i` to a prescribed degree `j`, as an `R`-linear
map. -/
def dLinear {x : C.Obj} {i j : ℤ} (h : i + 1 = j) : M.obj x i →ₗ[R] M.obj x j where
  toFun := M.d h
  map_add' := M.d_add h
  map_smul' := M.d_smul h

/-- The linear map `M.dLinear h` evaluates to the differential `M.d h`. -/
@[simp] lemma dLinear_apply {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (a : M.obj x i) :
    M.dLinear h a = M.d h a := rfl

/-- The right action of a fixed homogeneous morphism, as an `R`-linear map. -/
def actLinear {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (f : C.Hom x y n) :
    M.obj y m →ₗ[R] M.obj x k where
  toFun a := M.act h a f
  map_add' a b := M.act_add_left h a b f
  map_smul' c a := M.act_smul_left h c a f

/-- The linear map `M.actLinear h f` sends `a` to the action of `f` on `a`. -/
@[simp] lemma actLinear_apply {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (f : C.Hom x y n)
    (a : M.obj y m) : M.actLinear h f a = M.act h a f := rfl

/-! ### Transport along an equality of degrees -/

/-- The transport of elements of `M` at `x` along an equality of degrees. It is the identity at
a reflexivity proof, by `DGCategory.RightModule.objCast_rfl`. -/
def objCast (x : C.Obj) {i j : ℤ} (h : i = j) : M.obj x i →ₗ[R] M.obj x j := by
  subst h; exact LinearMap.id

/-- Transport along a reflexivity proof is the identity. -/
@[simp] lemma objCast_rfl (x : C.Obj) {i : ℤ} (a : M.obj x i) :
    M.objCast x (rfl : i = i) a = a := rfl

/-- Transport along `h` followed by transport along `h'` is transport along `h.trans h'`. -/
@[simp] lemma objCast_objCast (x : C.Obj) {i j k : ℤ} (h : i = j) (h' : j = k)
    (a : M.obj x i) : M.objCast x h' (M.objCast x h a) = M.objCast x (h.trans h') a := by
  subst h; subst h'; rfl

/-- The differential into a prescribed degree is the canonical one followed by a transport. -/
@[simp] lemma objCast_d {x : C.Obj} {i j : ℤ} (h : i + 1 = j) (a : M.obj x i) :
    M.objCast x h (M.d rfl a) = M.d h a := by subst h; rfl

/-- The differential of a transported element is the differential of the original element. -/
lemma d_objCast {x : C.Obj} {i i' j : ℤ} (hi : i = i') (h : i' + 1 = j) (h' : i + 1 = j)
    (a : M.obj x i) : M.d h (M.objCast x hi a) = M.d h' a := by subst hi; rfl

/-- The action into a prescribed degree is the canonical one followed by a transport. -/
@[simp] lemma objCast_act {x y : C.Obj} {m n k : ℤ} (h : m + n = k) (a : M.obj y m)
    (f : C.Hom x y n) : M.objCast x h (M.act rfl a f) = M.act h a f := by subst h; rfl

/-- Acting on a transported element is the transport of the action on the original element. -/
lemma act_objCast {x y : C.Obj} {m m' n k k' : ℤ} (hm : m = m') (hk : k = k')
    (h : m + n = k) (h' : m' + n = k') (a : M.obj y m) (f : C.Hom x y n) :
    M.act h' (M.objCast y hm a) f = M.objCast x hk (M.act h a f) := by subst hm; subst hk; rfl

/-- Acting on a transported element into a fixed target degree is acting on the original
element. -/
lemma act_objCast_left {x y : C.Obj} {m m' n k : ℤ} (hm : m = m') (h : m + n = k)
    (h' : m' + n = k) (a : M.obj y m) (f : C.Hom x y n) :
    M.act h' (M.objCast y hm a) f = M.act h a f := by subst hm; rfl

/-- Transport along an equality of degrees is additive. -/
@[simp] lemma objCast_add (x : C.Obj) {i j : ℤ} (h : i = j) (a b : M.obj x i) :
    M.objCast x h (a + b) = M.objCast x h a + M.objCast x h b := map_add _ _ _

/-- Transport along an equality of degrees is `R`-linear. -/
@[simp] lemma objCast_smul (x : C.Obj) {i j : ℤ} (h : i = j) (c : R) (a : M.obj x i) :
    M.objCast x h (c • a) = c • M.objCast x h a := map_smul _ _ _

end RightModule

end DGCategory
