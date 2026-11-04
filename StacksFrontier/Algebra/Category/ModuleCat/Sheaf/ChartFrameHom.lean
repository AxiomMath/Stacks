module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Morphisms out of a module with local frames on a covering family

Let `O` be a presheaf of commutative rings on a category `C` and let `N` be a presheaf of
`O`-modules.  A *frame* of `N` over an object `W` is a finite family of sections
`e : Fin n → N(W)` whose restriction along every morphism `h : V ⟶ W` is a basis of the
`O(V)`-module `N(V)`; this is the sectionwise form of "`N|_W` is free on `e`".

Given frames `e k` over the members of a family `W : K → C` covering the final object of a
site, and a sheaf of modules `F`, a morphism `N ⟶ F` is the same thing as a family of sections
`s k : Fin (n k) → F(W k)` that transforms like the frames: whenever `V` maps to `W k` by `h` and
to `W l` by `h'`, and `h'^* e l b = ∑ₐ c a • h^* e k a`, then `h'^* s l b = ∑ₐ c a • h^* s k a`.
This is `Stacks.SheafOfModules.ChartFrames.homEquiv`.  It is the input of the comparison of two
modules glued from the same transition data: both corepresent the same functor.

## Main definitions

* `Stacks.SheafOfModules.ChartFrames.IsFrame`: a frame over an object.
* `Stacks.SheafOfModules.ChartFrames.IsFrame.basis`: the basis a frame restricts to.
* `Stacks.SheafOfModules.ChartFrames.Compat`: the transformation rule for a family of sections.
* `Stacks.SheafOfModules.ChartFrames.homEquiv`: the bijection `(N ⟶ F) ≃ {s // Compat s}`.

## Main results

* `Stacks.SheafOfModules.ChartFrames.IsFrame.coord_res`: the coordinates of a restriction are
  the restrictions of the coordinates.
* `Stacks.SheafOfModules.ChartFrames.compat_of_pair`: the transformation rule may be checked
  on a single object through which every pair of morphisms to two members factors.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w t t'

namespace Stacks.SheafOfModules.ChartFrames

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction of a section of a presheaf of modules along a morphism of `C`. -/
abbrev res (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {V W : C}
    (h : V ⟶ W) (x : N.obj (op W)) : N.obj (op V) :=
  N.map h.op x

/-- Restriction along a composite is the composite of the restrictions. -/
theorem res_comp (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {T V W : C}
    (g : T ⟶ V) (h : V ⟶ W) (x : N.obj (op W)) :
    res N (g ≫ h) x = res N g (res N h x) := by
  simp only [res, op_comp]
  exact N.map_comp_apply _ _ x

/-- Restriction along an identity morphism is the identity. -/
theorem res_id (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {W : C}
    (x : N.obj (op W)) : res N (𝟙 W) x = x := by
  simp only [res, op_id]
  exact congrArg (fun f => f x) (congrArg (fun g => (ConcreteCategory.hom g : _ → _))
    (N.map_id (op W)))

/-- Restriction is additive. -/
theorem res_add (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {V W : C}
    (h : V ⟶ W) (x y : N.obj (op W)) : res N h (x + y) = res N h x + res N h y :=
  map_add _ x y

/-- Restriction is semilinear over the restriction map of `O`. -/
theorem res_smul (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {V W : C}
    (h : V ⟶ W) (r : O.obj (op W)) (x : N.obj (op W)) :
    res N h (r • x) = O.map h.op r • res N h x :=
  N.map_smul h.op r x

/-- Restriction commutes with finite sums. -/
theorem res_sum (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {V W : C}
    (h : V ⟶ W) {ι : Type*} (s : Finset ι) (x : ι → N.obj (op W)) :
    res N h (∑ i ∈ s, x i) = ∑ i ∈ s, res N h (x i) :=
  map_sum (N.map h.op).hom x s

/-- The restriction of the zero section is zero. -/
theorem res_zero (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {V W : C}
    (h : V ⟶ W) : res N h (0 : N.obj (op W)) = 0 :=
  map_zero _

/-- A morphism of presheaves of modules commutes with restriction. -/
theorem app_res {N F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)} (φ : N ⟶ F)
    {V W : C} (h : V ⟶ W) (x : N.obj (op W)) :
    φ.app (op V) (res N h x) = res F h (φ.app (op W) x) :=
  PresheafOfModules.naturality_apply φ h.op x

/-- A family `e : Fin n → N(W)` is a *frame* of `N` over `W` when its restriction along every
morphism `h : V ⟶ W` is a basis of the `O(V)`-module `N(V)`. -/
structure IsFrame (N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)) {W : C} {n : ℕ}
    (e : Fin n → N.obj (op W)) : Prop where
  linearIndependent : ∀ {V : C} (h : V ⟶ W),
    LinearIndependent (O.obj (op V)) (fun a => res N h (e a))
  span : ∀ {V : C} (h : V ⟶ W),
    ⊤ ≤ Submodule.span (O.obj (op V)) (Set.range fun a => res N h (e a))

namespace IsFrame

variable {N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)} {W : C} {n : ℕ}
  {e : Fin n → N.obj (op W)}

/-- The basis of `N(V)` a frame restricts to along `h : V ⟶ W`. -/
def basis (he : IsFrame N e) {V : C} (h : V ⟶ W) : Module.Basis (Fin n) (O.obj (op V)) (N.obj (op
    V)) :=
  Module.Basis.mk (he.linearIndependent h) (he.span h)

/-- The `a`-th vector of the basis along `h` is the restriction along `h` of `e a`. -/
@[simp]
theorem basis_apply (he : IsFrame N e) {V : C} (h : V ⟶ W) (a : Fin n) :
    he.basis h a = res N h (e a) :=
  Module.Basis.mk_apply _ _ _

/-- The coordinates of a section in the basis a frame restricts to. -/
abbrev coord (he : IsFrame N e) {V : C} (h : V ⟶ W) (x : N.obj (op V)) : Fin n → O.obj (op V) :=
  fun a => (he.basis h).repr x a

/-- A section is the linear combination of the restricted frame with its coordinates. -/
theorem sum_coord (he : IsFrame N e) {V : C} (h : V ⟶ W) (x : N.obj (op V)) :
    ∑ a, he.coord h x a • res N h (e a) = x := by
  conv_rhs => rw [← (he.basis h).sum_repr x]
  simp only [basis_apply]

/-- Coordinates are characterized by the linear combination they give. -/
theorem coord_eq_of_sum (he : IsFrame N e) {V : C} (h : V ⟶ W) (x : N.obj (op V))
    (c : Fin n → O.obj (op V)) (hc : ∑ a, c a • res N h (e a) = x) : he.coord h x = c := by
  subst hc
  have : ∑ a, c a • res N h (e a) = ∑ a, c a • he.basis h a := by simp only [basis_apply]
  funext a
  show (he.basis h).repr _ a = c a
  rw [this, Module.Basis.repr_sum_self]

/-- A frame restricts to a frame. -/
theorem restrict (he : IsFrame N e) {W' : C} (g : W' ⟶ W) :
    IsFrame N (fun a => res N g (e a)) where
  linearIndependent h := by
    simpa only [← res_comp] using he.linearIndependent (h ≫ g)
  span h := by
    simpa only [← res_comp] using he.span (h ≫ g)

/-- **The coordinates of a restriction are the restrictions of the coordinates.** -/
theorem coord_res (he : IsFrame N e) {V V' : C} (h : V ⟶ W) (g : V' ⟶ V) (x : N.obj (op V)) :
    he.coord (g ≫ h) (res N g x) = fun a => O.map g.op (he.coord h x a) := by
  apply coord_eq_of_sum
  conv_rhs => rw [← he.sum_coord h x]
  rw [res_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [res_smul, res_comp]

/-- Each coordinate of a restriction is the restriction of that coordinate. -/
theorem coord_res_apply (he : IsFrame N e) {V V' : C} (h : V ⟶ W) (g : V' ⟶ V)
    (x : N.obj (op V)) (a : Fin n) :
    he.coord (g ≫ h) (res N g x) a = O.map g.op (he.coord h x a) :=
  congrFun (he.coord_res h g x) a

/-- Coordinates are additive. -/
theorem coord_add (he : IsFrame N e) {V : C} (h : V ⟶ W) (x y : N.obj (op V)) :
    he.coord h (x + y) = he.coord h x + he.coord h y := by
  funext a
  simp [coord]

/-- Coordinates are linear in scalar multiplication. -/
theorem coord_smul (he : IsFrame N e) {V : C} (h : V ⟶ W) (r : O.obj (op V)) (x : N.obj (op V)) :
    he.coord h (r • x) = r • he.coord h x := by
  funext a
  simp [coord]

/-- The coordinates of `e a` over `W` itself are the `a`-th standard basis vector. -/
theorem coord_self (he : IsFrame N e) (a : Fin n) :
    he.coord (𝟙 W) (e a) = Pi.single a 1 := by
  apply coord_eq_of_sum
  simp [res_id, Pi.single_apply]

end IsFrame

/-- The linear combination, with the coordinates of `x` in the frame `e` restricted along `h`,
of the restrictions along `h` of a family `s` of sections of `F`. -/
def lift {N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}
    (F : PresheafOfModules.{t'} (O ⋙ forget₂ CommRingCat RingCat)) {W : C} {n : ℕ}
    {e : Fin n → N.obj (op W)} (he : IsFrame N e) (s : Fin n → F.obj (op W)) {V : C}
    (h : V ⟶ W) (x : N.obj (op V)) : F.obj (op V) :=
  ∑ a, he.coord h x a • res F h (s a)

section Lift

variable {N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}
  (F : PresheafOfModules.{t'} (O ⋙ forget₂ CommRingCat RingCat)) {W : C} {n : ℕ}
  {e : Fin n → N.obj (op W)} (he : IsFrame N e) (s : Fin n → F.obj (op W))

/-- `lift` is additive. -/
theorem lift_add {V : C} (h : V ⟶ W) (x y : N.obj (op V)) :
    lift F he s h (x + y) = lift F he s h x + lift F he s h y := by
  simp only [lift]
  rw [IsFrame.coord_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by rw [Pi.add_apply, add_smul])

/-- `lift` commutes with scalar multiplication. -/
theorem lift_smul {V : C} (h : V ⟶ W) (r : O.obj (op V)) (x : N.obj (op V)) :
    lift F he s h (r • x) = r • lift F he s h x := by
  simp only [lift]
  rw [IsFrame.coord_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun a _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul])

/-- `lift` commutes with restriction. -/
theorem lift_res {V V' : C} (h : V ⟶ W) (g : V' ⟶ V) (x : N.obj (op V)) :
    lift F he s (g ≫ h) (res N g x) = res F g (lift F he s h x) := by
  simp only [lift, IsFrame.coord_res_apply, res_sum, res_smul, res_comp]

/-- The coordinates of the restriction along `h` of `e a` are the `a`-th standard basis vector. -/
theorem coord_frame {V : C} (h : V ⟶ W) (a : Fin n) :
    he.coord h (res N h (e a)) = Pi.single a 1 := by
  apply he.coord_eq_of_sum
  simp [Pi.single_apply]

/-- `lift` sends the restriction of `e a` to the restriction of `s a`. -/
theorem lift_frame {V : C} (h : V ⟶ W) (a : Fin n) :
    lift F he s h (res N h (e a)) = res F h (s a) := by
  unfold lift
  simp [coord_frame he h a, Pi.single_apply]

/-- `lift` as a linear map. -/
def liftₗ {V : C} (h : V ⟶ W) : N.obj (op V) →ₗ[O.obj (op V)] F.obj (op V) where
  toFun := lift F he s h
  map_add' := lift_add F he s h
  map_smul' := lift_smul F he s h

/-- The linear map `liftₗ` evaluates to `lift`. -/
@[simp]
theorem liftₗ_apply {V : C} (h : V ⟶ W) (x : N.obj (op V)) :
    liftₗ F he s h x = lift F he s h x := rfl

end Lift

/-- A morphism of presheaves of modules commutes with `lift`. -/
private theorem app_lift {N F G : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}
    (φ : F ⟶ G) {W : C} {n : ℕ} {e : Fin n → N.obj (op W)} (he : IsFrame N e)
    (s : Fin n → F.obj (op W)) {V : C} (h : V ⟶ W) (x : N.obj (op V)) :
    φ.app (op V) (lift F he s h x) = lift G he (fun a => φ.app (op W) (s a)) h x := by
  unfold lift
  rw [map_sum]
  exact Finset.sum_congr rfl (fun a _ => by rw [map_smul, app_res])

/-- A morphism out of `N` is the `lift` of its values on a frame. -/
private theorem app_eq_lift {N F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}
    (φ : N ⟶ F) {W : C} {n : ℕ} {e : Fin n → N.obj (op W)} (he : IsFrame N e) {V : C}
    (h : V ⟶ W) (x : N.obj (op V)) :
    φ.app (op V) x = lift F he (fun a => φ.app (op W) (e a)) h x := by
  rw [← app_lift]
  exact congrArg (φ.app (op V)) (he.sum_coord h x).symm

section Transition

variable {N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}

/-- The coordinates in the frame restricted along `g`, read along `h`, are the coordinates in the
original frame read along `h ≫ g`. -/
theorem IsFrame.coord_restrict {W W' : C} {n : ℕ} {e : Fin n → N.obj (op W)} (he : IsFrame N e)
    (g : W' ⟶ W) {V : C} (h : V ⟶ W') (x : N.obj (op V)) :
    (he.restrict g).coord h x = he.coord (h ≫ g) x := by
  apply IsFrame.coord_eq_of_sum
  conv_rhs => rw [← he.sum_coord (h ≫ g) x]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [res_comp]

variable {K : Type*} {W : K → C} {n : K → ℕ} {e : ∀ k, Fin (n k) → N.obj (op (W k))}
  (he : ∀ k, IsFrame N (e k))

/-- The transition matrix between the frames over two members, read on an object mapping to both:
the coordinates of the frame over `W l` in the frame over `W k`. -/
def trans {T : C} {k l : K} (α : T ⟶ W k) (β : T ⟶ W l) (a : Fin (n k)) (b : Fin (n l)) :
    O.obj (op T) :=
  (he k).coord α (res N β (e l b)) a

/-- The restriction of a transition matrix is the transition matrix of the composites. -/
theorem trans_res {T T' : C} {k l : K} (g : T' ⟶ T) (α : T ⟶ W k) (β : T ⟶ W l) (a b) :
    O.map g.op (trans he α β a b) = trans he (g ≫ α) (g ≫ β) a b := by
  simp only [trans]
  rw [res_comp, IsFrame.coord_res_apply]

/-- The transition matrix of a frame with itself is the identity matrix. -/
theorem trans_self {T : C} {k : K} (α : T ⟶ W k) (a b : Fin (n k)) :
    trans he α α a b = if a = b then 1 else 0 := by
  simp only [trans]
  rw [coord_frame (he k) α b]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- Transition matrices satisfy the cocycle condition: the product of the transition matrices from
`k` to `l` and from `l` to `m` is the transition matrix from `k` to `m`. -/
theorem trans_comp {T : C} {k l m : K} (α : T ⟶ W k) (β : T ⟶ W l)
    (γ : T ⟶ W m) (a : Fin (n k)) (c : Fin (n m)) :
    ∑ x, trans he α β a x * trans he β γ x c = trans he α γ a c := by
  simp only [trans]
  conv_rhs => rw [← (he l).sum_coord β (res N γ (e m c))]
  simp only [IsFrame.coord, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

end Transition

section HomEquiv

variable {K : Type*} [Fintype K] {W : K → C} {n : K → ℕ}
  {N : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}
  {e : ∀ k, Fin (n k) → N.obj (op (W k))} (he : ∀ k, IsFrame N (e k))

/-- The transformation rule of a family of sections of `F` along the frames `e`: wherever two
members are related, the sections are related by the same coefficients as the frames. -/
def Compat (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (s : ∀ k, Fin (n k) → F.obj (op (W k))) : Prop :=
  ∀ (V : C) (k l : K) (h : V ⟶ W k) (h' : V ⟶ W l) (b : Fin (n l)),
    res F h' (s l b) = lift F (he k) (s k) h (res N h' (e l b))

omit [Fintype K] in
/-- For a compatible family of sections, the `lift` through any member mapped to by `V` is the
same. -/
theorem lift_eq_lift_of_compat (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    {s : ∀ k, Fin (n k) → F.obj (op (W k))} (hs : Compat he F s) {V : C} {k l : K}
    (h : V ⟶ W k) (h' : V ⟶ W l) (x : N.obj (op V)) :
    lift F (he l) (s l) h' x = lift F (he k) (s k) h x := by
  rw [← liftₗ_apply, ← liftₗ_apply, ← (he l).sum_coord h' x, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_smul, map_smul, liftₗ_apply, liftₗ_apply, lift_frame, hs V k l h h' b]

variable {J : GrothendieckTopology C}

/-- The family of local values of the glued morphism at a section `x` over `V`: on a morphism
`g : T ⟶ V` through which `T` maps to some member `W k`, the linear combination of the sections
`s k` with the coordinates of `g^* x`. -/
def localValues (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (s : ∀ k, Fin (n k) → F.obj (op (W k))) (V : C) (x : N.obj (op V)) :
    Presieve.FamilyOfElements (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (Sieve.ofObjects W V).arrows :=
  fun _ g hg => lift F (he hg.choose) (s hg.choose) hg.choose_spec.some (res N g x)

omit [Fintype K] in
/-- For a compatible family, the local value at `g` is the `lift` along any morphism from `T` to a
member. -/
theorem localValues_eq (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    {s : ∀ k, Fin (n k) → F.obj (op (W k))} (hs : Compat he F s) {V : C} (x : N.obj (op V))
    {T : C} (g : T ⟶ V) (hg : (Sieve.ofObjects W V).arrows g) (k : K) (h : T ⟶ W k) :
    localValues he F s V x g hg = lift F (he k) (s k) h (res N g x) :=
  lift_eq_lift_of_compat he F hs _ _ _

omit [Fintype K] in
/-- For a compatible family of sections, the local values form a compatible family of elements. -/
theorem localValues_compatible (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    {s : ∀ k, Fin (n k) → F.obj (op (W k))} (hs : Compat he F s) (V : C) (x : N.obj (op V)) :
    (localValues he F s V x).Compatible := by
  intro T₁ T₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ hcomm
  show res F f₁ (localValues he F s V x g₁ hg₁) = res F f₂ (localValues he F s V x g₂ hg₂)
  rw [localValues_eq he F hs x g₁ hg₁ _ hg₁.choose_spec.some,
    localValues_eq he F hs x g₂ hg₂ _ hg₂.choose_spec.some, ← lift_res, ← lift_res,
    ← res_comp, ← res_comp, hcomm]
  exact lift_eq_lift_of_compat he F hs _ _ _

omit [Fintype K] in
/-- Sections of a sheaf are determined by their restrictions to the objects mapping to a member
of a family covering the final object. -/
theorem sections_ext (hW : J.CoversTop W)
    (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (hF : Presieve.IsSheaf J (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat))
    {V : C} {y z : F.obj (op V)}
    (h : ∀ (T : C) (g : T ⟶ V) (k : K) (_ : T ⟶ W k), res F g y = res F g z) : y = z := by
  refine (hF _ (hW V)).isSeparatedFor.ext (fun T g hg => ?_)
  obtain ⟨k, ⟨hk⟩⟩ := hg
  exact h T g k hk

/-- The value at `x` of the morphism glued from a compatible family of sections. -/
def glueApp (hW : J.CoversTop W) (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (hF : Presieve.IsSheaf J (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat))
    {s : ∀ k, Fin (n k) → F.obj (op (W k))} (hs : Compat he F s) (V : C) (x : N.obj (op V)) :
    F.obj (op V) :=
  (hF _ (hW V)).amalgamate (localValues he F s V x) (localValues_compatible he F hs V x)

section Glue

variable (hW : J.CoversTop W) (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
  (hF : Presieve.IsSheaf J (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat))
  {s : ∀ k, Fin (n k) → F.obj (op (W k))} (hs : Compat he F s)

omit [Fintype K] in
/-- The restriction of the glued value along `g : T ⟶ V` is the `lift` through any member that `T`
maps to. -/
theorem res_glueApp {V : C} (x : N.obj (op V)) {T : C} (g : T ⟶ V) (k : K) (h : T ⟶ W k) :
    res F g (glueApp he hW F hF hs V x) = lift F (he k) (s k) h (res N g x) := by
  have hg : (Sieve.ofObjects W V).arrows g := ⟨k, ⟨h⟩⟩
  have := (hF _ (hW V)).valid_glue (localValues_compatible he F hs V x) g hg
  exact this.trans (localValues_eq he F hs x g hg k h)

omit [Fintype K] in
/-- `glueApp` is additive. -/
theorem glueApp_add (V : C) (x y : N.obj (op V)) :
    glueApp he hW F hF hs V (x + y) = glueApp he hW F hF hs V x + glueApp he hW F hF hs V y := by
  refine sections_ext hW F hF (fun T g k h => ?_)
  rw [res_add, res_glueApp he hW F hF hs _ g k h, res_glueApp he hW F hF hs _ g k h,
    res_glueApp he hW F hF hs _ g k h, res_add, lift_add]

omit [Fintype K] in
/-- `glueApp` commutes with scalar multiplication. -/
theorem glueApp_smul (V : C) (r : O.obj (op V)) (x : N.obj (op V)) :
    glueApp he hW F hF hs V (r • x) = r • glueApp he hW F hF hs V x := by
  refine sections_ext hW F hF (fun T g k h => ?_)
  rw [res_smul, res_glueApp he hW F hF hs _ g k h, res_glueApp he hW F hF hs _ g k h,
    res_smul, lift_smul]

omit [Fintype K] in
/-- `glueApp` commutes with restriction. -/
theorem glueApp_res {V V' : C} (g : V' ⟶ V) (x : N.obj (op V)) :
    glueApp he hW F hF hs V' (res N g x) = res F g (glueApp he hW F hF hs V x) := by
  refine sections_ext hW F hF (fun T t k h => ?_)
  rw [res_glueApp he hW F hF hs _ t k h, ← res_comp F t g,
    res_glueApp he hW F hF hs _ (t ≫ g) k h, res_comp]

/-- **The morphism glued from a compatible family of sections.** -/
def glue : N ⟶ F where
  app X := ModuleCat.ofHom
    { toFun := glueApp he hW F hF hs X.unop
      map_add' := glueApp_add he hW F hF hs X.unop
      map_smul' := glueApp_smul he hW F hF hs X.unop }
  naturality {X Y} f := by
    ext x
    exact glueApp_res he hW F hF hs f.unop x

omit [Fintype K] in
/-- The component of `glue` at `V` sends `x` to `glueApp` at `x`. -/
theorem glue_app_apply (V : C) (x : N.obj (op V)) :
    (glue he hW F hF hs).app (op V) x = glueApp he hW F hF hs V x := rfl

omit [Fintype K] in
/-- The glued morphism sends the frame vector `e k a` to the section `s k a`. -/
theorem glue_app_frame (k : K) (a : Fin (n k)) :
    (glue he hW F hF hs).app (op (W k)) (e k a) = s k a := by
  rw [glue_app_apply]
  refine sections_ext hW F hF (fun T g k' h => ?_)
  rw [res_glueApp he hW F hF hs _ g k' h, hs T k' k h g a]

end Glue

omit [Fintype K] in
/-- The images of the frames under a morphism out of `N` satisfy the transformation rule. -/
theorem compat_of_hom (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (φ : N ⟶ F) : Compat he F (fun k a => φ.app (op (W k)) (e k a)) := by
  intro V k l h h' b
  show res F h' (φ.app _ (e l b)) = lift F (he k) _ h (res N h' (e l b))
  rw [← app_res, app_eq_lift φ (he k) h]

include he in
omit [Fintype K] in
/-- A morphism out of `N` is determined by its values on the frames. -/
theorem hom_ext_of_frames (hW : J.CoversTop W)
    (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (hF : Presieve.IsSheaf J (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)) {φ ψ : N ⟶ F}
    (h : ∀ k a, φ.app (op (W k)) (e k a) = ψ.app (op (W k)) (e k a)) : φ = ψ := by
  ext X x
  obtain ⟨V⟩ := X
  refine sections_ext hW F hF (fun T g k hk => ?_)
  rw [← app_res, ← app_res, app_eq_lift φ (he k) hk, app_eq_lift ψ (he k) hk]
  simp only [h]

/-- **Morphisms out of a module with frames on a covering family are compatible families of
sections.** -/
def homEquiv (hW : J.CoversTop W) (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (hF : Presieve.IsSheaf J (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)) :
    (N ⟶ F) ≃ {s : ∀ k, Fin (n k) → F.obj (op (W k)) // Compat he F s} where
  toFun φ := ⟨fun k a => φ.app (op (W k)) (e k a), compat_of_hom he F φ⟩
  invFun s := glue he hW F hF s.2
  left_inv φ := hom_ext_of_frames he hW F hF
    (fun k a => glue_app_frame he hW F hF (compat_of_hom he F φ) k a)
  right_inv s := Subtype.ext (funext fun k => funext fun a => glue_app_frame he hW F hF s.2 k a)

omit [Fintype K] in
/-- The family of sections attached to a morphism `φ` consists of the images of the frames. -/
@[simp]
theorem homEquiv_apply_coe (hW : J.CoversTop W)
    (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (hF : Presieve.IsSheaf J (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat))
    (φ : N ⟶ F) (k : K) (a : Fin (n k)) :
    (homEquiv he hW F hF φ).1 k a = φ.app (op (W k)) (e k a) := rfl

omit [Fintype K] in
/-- The transformation rule of a family of sections is preserved by every morphism. -/
theorem compat_map {F G : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat)}
    (ψ : F ⟶ G) {s : ∀ k, Fin (n k) → F.obj (op (W k))} (hs : Compat he F s) :
    Compat he G (fun k a => ψ.app (op (W k)) (s k a)) := by
  intro V k l h h' b
  show res G h' (ψ.app _ (s l b)) = lift G (he k) _ h (res N h' (e l b))
  rw [← app_res, hs V k l h h' b, app_lift]

omit [Fintype K] in
/-- **The transformation rule may be checked on pair objects**: if every pair of morphisms from
an object to `W k` and `W l` factors through `P k l`, it suffices to check the rule on `P k l`
itself, along its two maps. -/
theorem compat_of_pair (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    {s : ∀ k, Fin (n k) → F.obj (op (W k))} (P : K → K → C) (p₁ : ∀ k l, P k l ⟶ W k)
    (p₂ : ∀ k l, P k l ⟶ W l)
    (hP : ∀ (V : C) (k l : K) (h : V ⟶ W k) (h' : V ⟶ W l),
      ∃ t : V ⟶ P k l, t ≫ p₁ k l = h ∧ t ≫ p₂ k l = h')
    (hs : ∀ k l (b : Fin (n l)), res F (p₂ k l) (s l b) =
      lift F (he k) (s k) (p₁ k l) (res N (p₂ k l) (e l b))) :
    Compat he F s := by
  intro V k l h h' b
  obtain ⟨t, rfl, rfl⟩ := hP V k l h h'
  rw [res_comp, hs k l b, ← lift_res, ← res_comp]

/-- The transformation rule on pair objects, as a predicate. -/
def PairCompat (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (P : K → K → C) (p₁ : ∀ k l, P k l ⟶ W k) (p₂ : ∀ k l, P k l ⟶ W l)
    (s : ∀ k, Fin (n k) → F.obj (op (W k))) : Prop :=
  ∀ k l (b : Fin (n l)), res F (p₂ k l) (s l b) =
    ∑ a, (he k).coord (p₁ k l) (res N (p₂ k l) (e l b)) a • res F (p₁ k l) (s k a)

omit [Fintype K] in
/-- If every pair of morphisms to `W k` and `W l` factors through `P k l`, the transformation rule
is equivalent to its restriction to the pair objects. -/
theorem compat_iff_pairCompat (F : PresheafOfModules.{t} (O ⋙ forget₂ CommRingCat RingCat))
    (P : K → K → C) (p₁ : ∀ k l, P k l ⟶ W k) (p₂ : ∀ k l, P k l ⟶ W l)
    (hP : ∀ (V : C) (k l : K) (h : V ⟶ W k) (h' : V ⟶ W l),
      ∃ t : V ⟶ P k l, t ≫ p₁ k l = h ∧ t ≫ p₂ k l = h')
    (s : ∀ k, Fin (n k) → F.obj (op (W k))) :
    Compat he F s ↔ PairCompat he F P p₁ p₂ s :=
  ⟨fun h k l b => h (P k l) k l (p₁ k l) (p₂ k l) b,
    fun h => compat_of_pair he F P p₁ p₂ hP h⟩

end HomEquiv

end Stacks.SheafOfModules.ChartFrames
