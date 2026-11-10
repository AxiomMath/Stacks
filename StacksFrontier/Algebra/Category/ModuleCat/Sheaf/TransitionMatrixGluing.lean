module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChartFrameHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Gluing a module from transition matrices on a covering family

Let `O` be a sheaf of commutative rings on a site `(C, J)` with binary products, and let
`W : K → C` be a finite family of objects covering the final object.  For every pair of members
fix a product `P k l` of `W k` and `W l`, and on it a matrix `g k l` of sections of `O`, of size
`n k × n l`.  If the matrices satisfy the cocycle condition `g k l * g l m = g k m` and are the
identity on the diagonal — both read after pulling back to an arbitrary object mapping to the
members — then there is a sheaf of `O`-modules `M` carrying frames `e k` over the members with
`e l = e k * g k l` over `P k l`.

The sections of `M` over `V` are the families of coordinates
`x k : Fin (n k) → O(W k ⨯ V)` related by the matrices: these are the coordinates, with respect
to the frames `e k` pulled back to `W k ⨯ V`, of a section over `V`.

## Main definitions

* `Stacks.SheafOfModules.ChartFrames.GlueData`: the members, the products, the matrices and the
  two conditions.
* `Stacks.SheafOfModules.ChartFrames.GlueData.module`: the glued sheaf of modules.
* `Stacks.SheafOfModules.ChartFrames.GlueData.frame`: its frames over the members.

## Main results

* `Stacks.SheafOfModules.ChartFrames.GlueData.isFrame_frame'`: the frame vectors over each
  member form a frame.
* `Stacks.SheafOfModules.ChartFrames.GlueData.res_p₂_frame'`: the transition relation
  `e l = e k * g k l` over `P k l`.
* `Stacks.SheafOfModules.ChartFrames.GlueData.coord_res_p₂_frame'`: the coordinates of the
  transition between the frames are the matrices `g k l`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u v w

namespace Stacks.SheafOfModules.ChartFrames

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{w})

/-- Pulling back sections of `O` along a morphism. -/
abbrev pb {T T' : C} (f : T ⟶ T') : O.obj.obj (op T') →+* O.obj.obj (op T) :=
  (O.obj.map f.op).hom

omit [HasBinaryProducts C] in
/-- Pulling back along a composite is pulling back twice. -/
theorem pb_comp {T T' T'' : C} (f : T ⟶ T') (f' : T' ⟶ T'') (x : O.obj.obj (op T'')) :
    pb O (f ≫ f') x = pb O f (pb O f' x) := by
  simp [pb]

omit [HasBinaryProducts C] in
/-- Pulling back along the identity is the identity. -/
theorem pb_id {T : C} (x : O.obj.obj (op T)) : pb O (𝟙 T) x = x := by
  simp [pb]

omit [HasBinaryProducts C] in
/-- Pulling back along equal morphisms gives equal sections. -/
theorem pb_congr {T T' : C} {f f' : T ⟶ T'} (h : f = f') (x : O.obj.obj (op T')) :
    pb O f x = pb O f' x := by rw [h]

omit [HasBinaryProducts C] in
  /-- Pulling back twice along morphisms with composite `g` is pulling back along `g`. -/
  private theorem pb_pb_of_comp_eq {T T' T'' : C} {f : T ⟶ T'} {f' : T' ⟶ T''} {g : T ⟶ T''}
      (h : f ≫ f' = g) (x : O.obj.obj (op T'')) : pb O f (pb O f' x) = pb O g x := by
    rw [← pb_comp, h]

/-- The data of a module glued from transition matrices: a finite family of members, a product
of every pair of members, and a matrix of sections of `O` on every such product, subject to the
cocycle condition and to being the identity on the diagonal. -/
structure GlueData (K : Type) [Fintype K] where
  /-- The members. -/
  W : K → C
  /-- The ranks. -/
  n : K → ℕ
  /-- A product of two members. -/
  P : K → K → C
  /-- Its first projection. -/
  p₁ : ∀ k l, P k l ⟶ W k
  /-- Its second projection. -/
  p₂ : ∀ k l, P k l ⟶ W l
  /-- It is a product. -/
  isLimit : ∀ k l, IsLimit (BinaryFan.mk (p₁ k l) (p₂ k l))
  /-- The transition matrices. -/
  g : ∀ k l, Fin (n k) → Fin (n l) → O.obj.obj (op (P k l))

namespace GlueData

variable {O} {K : Type} [Fintype K] (D : GlueData O K)

/-- The morphism into `P k l` with two given components. -/
def pairLift {T : C} {k l : K} (a : T ⟶ D.W k) (b : T ⟶ D.W l) : T ⟶ D.P k l :=
  (D.isLimit k l).lift (BinaryFan.mk a b)

omit [HasBinaryProducts C] in
/-- The first component of `pairLift a b` is `a`. -/
@[simp]
theorem pairLift_p₁ {T : C} {k l : K} (a : T ⟶ D.W k) (b : T ⟶ D.W l) :
    D.pairLift a b ≫ D.p₁ k l = a :=
  (D.isLimit k l).fac (BinaryFan.mk a b) ⟨WalkingPair.left⟩

omit [HasBinaryProducts C] in
/-- The second component of `pairLift a b` is `b`. -/
@[simp]
theorem pairLift_p₂ {T : C} {k l : K} (a : T ⟶ D.W k) (b : T ⟶ D.W l) :
    D.pairLift a b ≫ D.p₂ k l = b :=
  (D.isLimit k l).fac (BinaryFan.mk a b) ⟨WalkingPair.right⟩

omit [HasBinaryProducts C] in
/-- Two morphisms into `P k l` with the same components are equal. -/
theorem pair_ext {T : C} {k l : K} {f f' : T ⟶ D.P k l} (h₁ : f ≫ D.p₁ k l = f' ≫ D.p₁ k l)
    (h₂ : f ≫ D.p₂ k l = f' ≫ D.p₂ k l) : f = f' :=
  BinaryFan.IsLimit.hom_ext (D.isLimit k l) h₁ h₂

omit [HasBinaryProducts C] in
/-- Precomposing `pairLift a b` with `t` is `pairLift (t ≫ a) (t ≫ b)`. -/
theorem comp_pairLift {T T' : C} {k l : K} (t : T' ⟶ T) (a : T ⟶ D.W k) (b : T ⟶ D.W l) :
    t ≫ D.pairLift a b = D.pairLift (t ≫ a) (t ≫ b) :=
  D.pair_ext (by simp) (by simp)

omit [HasBinaryProducts C] in
/-- The morphism into `P k l` with components the two projections is the identity. -/
theorem pairLift_p₁_p₂ {k l : K} : D.pairLift (D.p₁ k l) (D.p₂ k l) = 𝟙 _ :=
  D.pair_ext (by simp) (by simp)

/-- The transition matrix `g k l` pulled back to an object mapping to the two members. -/
abbrev gAt {T : C} {k l : K} (a : T ⟶ D.W k) (b : T ⟶ D.W l) (i : Fin (D.n k))
    (j : Fin (D.n l)) : O.obj.obj (op T) :=
  pb O (D.pairLift a b) (D.g k l i j)

omit [HasBinaryProducts C] in
/-- Pulling back `gAt a b` along `t` gives `gAt (t ≫ a) (t ≫ b)`. -/
theorem pb_gAt {T T' : C} {k l : K} (t : T' ⟶ T) (a : T ⟶ D.W k) (b : T ⟶ D.W l) (i j) :
    pb O t (D.gAt a b i j) = D.gAt (t ≫ a) (t ≫ b) i j := by
  rw [gAt, ← pb_comp, comp_pairLift]

/-- **The cocycle condition**, after pulling back to an arbitrary object mapping to three
members. -/
def Cocycle : Prop :=
  ∀ (k l m : K) {T : C} (a : T ⟶ D.W k) (b : T ⟶ D.W l) (c : T ⟶ D.W m) (i : Fin (D.n k))
    (j : Fin (D.n m)), ∑ x, D.gAt a b i x * D.gAt b c x j = D.gAt a c i j

/-- **The transition matrix of a member with itself is the identity**, after pulling back to an
arbitrary object mapping to that member. -/
def Unit : Prop :=
  ∀ (k : K) {T : C} (a : T ⟶ D.W k) (i j : Fin (D.n k)),
    D.gAt a a i j = if i = j then 1 else 0

/-- The ring map making `O(W k ⨯ V)` an `O(V)`-algebra. -/
abbrev σ (k : K) (V : C) : O.obj.obj (op V) →+* O.obj.obj (op (D.W k ⨯ V)) :=
  pb O (prod.snd : D.W k ⨯ V ⟶ V)

/-- The families of coordinates over `V`. -/
def Amb (V : C) : Type w := ∀ k, Fin (D.n k) → O.obj.obj (op (D.W k ⨯ V))

/-- The families of coordinates form an abelian group under pointwise addition. -/
instance (V : C) : AddCommGroup (D.Amb V) :=
  inferInstanceAs (AddCommGroup (∀ k, Fin (D.n k) → O.obj.obj (op (D.W k ⨯ V))))

/-- A section `r` of `O` over `V` acts on coordinates by multiplication with its pullback
`σ k V r` to `W k ⨯ V`. -/
instance (V : C) : SMul (O.obj.obj (op V)) (D.Amb V) where
  smul r x := fun k i => D.σ k V r * x k i

/-- The coordinates of `r • x` are those of `x` multiplied by `σ k V r`. -/
theorem smul_apply {V : C} (r : O.obj.obj (op V)) (x : D.Amb V) (k : K) (i : Fin (D.n k)) :
    (r • x) k i = D.σ k V r * x k i := rfl

/-- Coordinates add pointwise. -/
theorem add_apply {V : C} (x y : D.Amb V) (k : K) (i : Fin (D.n k)) :
    (x + y) k i = x k i + y k i := rfl

/-- The coordinates of `0` are zero. -/
theorem zero_apply {V : C} (k : K) (i : Fin (D.n k)) : (0 : D.Amb V) k i = 0 := rfl

/-- Two families of coordinates with the same entries are equal. -/
@[ext]
theorem amb_ext {V : C} {x y : D.Amb V} (h : ∀ k i, x k i = y k i) : x = y :=
  funext fun k => funext fun i => h k i

/-- The families of coordinates over `V` form an `O(V)`-module. -/
instance (V : C) : Module (O.obj.obj (op V)) (D.Amb V) where
  one_smul x := by ext k i; simp [smul_apply]
  mul_smul r s x := by ext k i; simp [smul_apply, mul_assoc]
  smul_zero r := by ext k i; simp [smul_apply, zero_apply]
  smul_add r x y := by ext k i; simp [smul_apply, add_apply, mul_add]
  add_smul r s x := by ext k i; simp [smul_apply, add_apply, add_mul]
  zero_smul x := by ext k i; simp [smul_apply, zero_apply]

/-- The relation among the coordinates of a section: over every object `T` mapping to `V` and to
two members, the coordinates with respect to the two frames are related by the transition
matrix. -/
def Rel {V : C} (x : D.Amb V) : Prop :=
  ∀ {T : C} (t : T ⟶ V) (k l : K) (a : T ⟶ D.W k) (b : T ⟶ D.W l) (i : Fin (D.n k)),
    pb O (prod.lift a t) (x k i) = ∑ j, D.gAt a b i j * pb O (prod.lift b t) (x l j)

/-- The sections of the glued module over `V`. -/
def sections (V : C) : Submodule (O.obj.obj (op V)) (D.Amb V) where
  carrier := {x | D.Rel x}
  add_mem' {x y} hx hy := by
    intro T t k l a b i
    rw [add_apply, map_add, hx t k l a b i, hy t k l a b i, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_apply, map_add, mul_add])
  zero_mem' := by
    intro T t k l a b i
    simp [zero_apply]
  smul_mem' r x hx := by
    intro T t k l a b i
    have h1 : ∀ (k' : K) (c : T ⟶ D.W k'), pb O (prod.lift c t) (D.σ k' V r) = pb O t r := by
      intro k' c
      rw [σ, ← pb_comp, prod.lift_snd]
    change pb O (prod.lift a t) (D.σ k V r * x k i) =
      ∑ j, D.gAt a b i j * pb O (prod.lift b t) (D.σ l V r * x l j)
    rw [map_mul, h1, hx t k l a b i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, h1]
    ring

/-- The restriction of coordinates along `f : V' ⟶ V`. -/
def resAmb {V V' : C} (f : V' ⟶ V) (x : D.Amb V) : D.Amb V' :=
  fun k i => pb O (prod.map (𝟙 (D.W k)) f) (x k i)

/-- Pulling back restricted coordinates along `prod.lift a t` is pulling back the original
coordinates along `prod.lift a (t ≫ f)`. -/
theorem pb_lift_resAmb {V V' T : C} (f : V' ⟶ V) (x : D.Amb V) {k : K} (a : T ⟶ D.W k)
    (t : T ⟶ V') (i : Fin (D.n k)) :
    pb O (prod.lift a t) (D.resAmb f x k i) = pb O (prod.lift a (t ≫ f)) (x k i) := by
  exact pb_pb_of_comp_eq O (by ext <;> simp) _

/-- The restriction of a section is a section. -/
theorem resAmb_mem {V V' : C} (f : V' ⟶ V) {x : D.Amb V} (hx : x ∈ D.sections V) :
    D.resAmb f x ∈ D.sections V' := by
  intro T t k l a b i
  rw [pb_lift_resAmb, hx (t ≫ f) k l a b i]
  exact Finset.sum_congr rfl (fun j _ => by rw [pb_lift_resAmb])

/-- Restriction of coordinates is additive. -/
theorem resAmb_add {V V' : C} (f : V' ⟶ V) (x y : D.Amb V) :
    D.resAmb f (x + y) = D.resAmb f x + D.resAmb f y := by
  ext k i
  simp [resAmb, add_apply]

/-- Restriction of coordinates along `f` is semilinear over `pb O f`. -/
theorem resAmb_smul {V V' : C} (f : V' ⟶ V) (r : O.obj.obj (op V)) (x : D.Amb V) :
    D.resAmb f (r • x) = pb O f r • D.resAmb f x := by
  ext k i
  simp only [resAmb, smul_apply, map_mul, σ]
  congr 1
  rw [← pb_comp, ← pb_comp]
  congr 2
  simp

/-- Restriction of coordinates along the identity is the identity. -/
theorem resAmb_id {V : C} (x : D.Amb V) : D.resAmb (𝟙 V) x = x := by
  ext k i
  simp only [resAmb, prod.map_id_id]
  exact pb_id O _

/-- Restriction of coordinates along a composite is restriction twice. -/
theorem resAmb_comp {V V' V'' : C} (f : V' ⟶ V) (f' : V'' ⟶ V') (x : D.Amb V) :
    D.resAmb (f' ≫ f) x = D.resAmb f' (D.resAmb f x) := by
  ext k i
  exact (pb_pb_of_comp_eq O (by ext <;> simp) _).symm

/-- The restriction of sections along `f : V' ⟶ V`, as a semilinear map. -/
def resSections {V V' : C} (f : V' ⟶ V) :
    D.sections V →ₛₗ[pb O f] D.sections V' where
  toFun x := ⟨D.resAmb f x.1, D.resAmb_mem f x.2⟩
  map_add' x y := Subtype.ext (D.resAmb_add f x.1 y.1)
  map_smul' r x := Subtype.ext (D.resAmb_smul f r x.1)

/-- **The glued presheaf of modules.** -/
def presheaf : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of _ (D.sections X.unop)
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((O.obj ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
      (ModuleCat.of _ (D.sections Y.unop)))
    { toFun := D.resSections f.unop
      map_add' := map_add _
      map_smul' := fun r x => (D.resSections f.unop).map_smulₛₗ r x }
  map_id X := by
    ext x
    exact Subtype.ext (D.resAmb_id x.1)
  map_comp f g := by
    ext x
    exact Subtype.ext (D.resAmb_comp f.unop g.unop x.1)

/-- The restriction maps of `presheaf` act on coordinates by `resAmb`. -/
theorem presheaf_map_apply {V V' : C} (f : V' ⟶ V) (x : D.presheaf.obj (op V)) :
    (show ↥(D.sections V') from D.presheaf.map f.op x).1 = D.resAmb f x.1 := rfl

omit [HasBinaryProducts C] [Fintype K] in
/-- If `O` is a sheaf of sets, two sections of `O` over `T` which agree after pulling back along
every arrow of a covering sieve are equal. -/
theorem eq_of_sieve (hO : Presieve.IsSheaf J (O.obj ⋙ CategoryTheory.forget CommRingCat))
    {T : C} {S : Sieve T} (hS : S ∈ J T) {y z : O.obj.obj (op T)}
    (h : ∀ ⦃T' : C⦄ (f : T' ⟶ T), S f → pb O f y = pb O f z) : y = z :=
  (hO S hS).isSeparatedFor.ext (fun _ f hf => h f hf)

variable (hO : Presieve.IsSheaf J (O.obj ⋙ CategoryTheory.forget CommRingCat))
include hO

omit [Fintype K] in
/-- The sections of `O` over `W ⨯ V`, as `V` varies, form a sheaf of sets. -/
theorem isSheaf_prod (W : C) :
    Presieve.IsSheaf J ((Over.star W ⋙ Over.forget W).op ⋙ O.obj ⋙ CategoryTheory.forget
        CommRingCat) := by
  have : (Over.star W ⋙ Over.forget W).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J (J.over W) J
  exact Functor.op_comp_isSheaf_of_isSheaf_type (Over.star W ⋙ Over.forget W) J hO

/-- **The glued presheaf of modules is a sheaf of sets.** -/
theorem isSheaf_types :
    Presieve.IsSheaf J (D.presheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) := by
  intro V S hS x hx
  let xs : ∀ ⦃T : C⦄ (f : T ⟶ V), S f → D.sections T := fun T f hf => x f hf
  have hxs : ∀ ⦃T₁ T₂ Z : C⦄ (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂) (f₁ : T₁ ⟶ V) (f₂ : T₂ ⟶ V)
      (h₁ : S f₁) (h₂ : S f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
        D.resAmb g₁ (xs f₁ h₁).1 = D.resAmb g₂ (xs f₂ h₂).1 :=
    fun _ _ _ g₁ g₂ _ _ h₁ h₂ hc => congrArg Subtype.val (hx g₁ g₂ h₁ h₂ hc)
  let y : ∀ (k : K) (i : Fin (D.n k)), Presieve.FamilyOfElements
      ((Over.star (D.W k) ⋙ Over.forget (D.W k)).op ⋙ O.obj ⋙ CategoryTheory.forget CommRingCat)
      S.arrows := fun k i T f hf => (xs f hf).1 k i
  have hy : ∀ k i, (y k i).Compatible := fun k i _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hc =>
    congrFun (congrFun (hxs g₁ g₂ f₁ f₂ h₁ h₂ hc) k) i
  let z : D.Amb V := fun k i => (isSheaf_prod hO (D.W k) S hS).amalgamate (y k i) (hy k i)
  have hz : ∀ ⦃T : C⦄ (f : T ⟶ V) (hf : S f), D.resAmb f z = (xs f hf).1 := by
    intro T f hf
    ext k i
    exact (isSheaf_prod hO (D.W k) S hS).valid_glue (hy k i) f hf
  have hzmem : z ∈ D.sections V := by
    intro T t k l a b i
    refine eq_of_sieve hO (J.pullback_stable t hS) (fun T' h hh => ?_)
    have h₁ : ∀ (k' : K) (c : T ⟶ D.W k') (i' : Fin (D.n k')),
        pb O h (pb O (prod.lift c t) (z k' i')) =
          pb O (prod.lift (h ≫ c) (𝟙 T')) ((xs (h ≫ t) hh).1 k' i') := by
      intro k' c i'
      rw [← hz (h ≫ t) hh, pb_lift_resAmb]
      exact pb_pb_of_comp_eq O (by ext <;> simp) _
    rw [h₁, map_sum, (xs (h ≫ t) hh).2 (𝟙 T') k l (h ≫ a) (h ≫ b) i]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, h₁, pb_gAt]
  refine ⟨(⟨z, hzmem⟩ : D.sections V), fun T f hf => Subtype.ext (hz f hf), fun w hw => ?_⟩
  apply Subtype.ext
  ext k i
  refine (isSheaf_prod hO (D.W k) S hS).isSeparatedFor.ext (fun T f hf => ?_)
  change D.resAmb f (show D.sections V from w).1 k i = D.resAmb f z k i
  rw [hz f hf]
  exact congrFun (congrFun (congrArg Subtype.val (hw f hf)) k) i

variable [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})]

/-- **The glued sheaf of modules.** -/
def module : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) where
  val := D.presheaf
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat)
    ((isSheaf_iff_isSheaf_of_type _ _).2 (D.isSheaf_types hO))

/-- The underlying presheaf of `module` is `presheaf`. -/
theorem module_val : (D.module hO).val = D.presheaf := rfl

/-! ### The frames -/

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of the frame vector `e k i` of the glued module: the column `i` of the
transition matrices into `k`. -/
def frameAmb (k : K) (i : Fin (D.n k)) : D.Amb (D.W k) :=
  fun l j => pb O (D.pairLift (prod.fst : D.W l ⨯ D.W k ⟶ D.W l) prod.snd) (D.g l k j i)

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- Pulling back the coordinates of `e k i` along `prod.lift a t` gives the column `i` of the
transition matrix pulled back along `a` and `t`. -/
theorem pb_lift_frameAmb {T : C} {k l : K} (i : Fin (D.n k)) (a : T ⟶ D.W l) (t : T ⟶ D.W k)
    (j : Fin (D.n l)) : pb O (prod.lift a t) (D.frameAmb k i l j) = D.gAt a t j i := by
  rw [frameAmb, ← pb_comp, comp_pairLift, prod.lift_fst, prod.lift_snd]

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of `e k i` restricted along `h : V ⟶ W k` are the column `i` of the
transition matrices pulled back to `W l ⨯ V`. -/
theorem resAmb_frameAmb {V : C} {k : K} (h : V ⟶ D.W k) (i : Fin (D.n k)) (l : K)
    (j : Fin (D.n l)) :
    D.resAmb h (D.frameAmb k i) l j = D.gAt (prod.fst : D.W l ⨯ V ⟶ D.W l) (prod.snd ≫ h) j i := by
  rw [resAmb, frameAmb, ← pb_comp, comp_pairLift]
  simp

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- Under the cocycle condition, the coordinates of `e k i` form a section. -/
theorem frameAmb_mem (hC : D.Cocycle) (k : K) (i : Fin (D.n k)) :
    D.frameAmb k i ∈ D.sections (D.W k) := by
  intro T t l m a b j
  rw [pb_lift_frameAmb, ← hC l m k a b t j i]
  exact Finset.sum_congr rfl fun x _ => by rw [pb_lift_frameAmb]

variable {D}

/-- **The frame vector `e k i` of the glued module.** -/
def frame (hC : D.Cocycle) (k : K) (i : Fin (D.n k)) : (D.module hO).val.obj (op (D.W k)) :=
  (⟨D.frameAmb k i, D.frameAmb_mem hC k i⟩ : D.sections (D.W k))

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- Restriction in `presheaf` acts on coordinates by `resAmb`. -/
theorem res_val {V V' : C} (f : V' ⟶ V) (x : D.sections V) :
    (show D.sections V' from res D.presheaf f x).1 = D.resAmb f x.1 := rfl

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- Scalar multiplication in `presheaf` acts on coordinates by scalar multiplication. -/
theorem smul_val {V : C} (r : O.obj.obj (op V)) (x : D.sections V) :
    (show D.sections V from r • (show D.presheaf.obj (op V) from x)).1 = r • x.1 := rfl

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of a finite sum of sections of `presheaf` are the sum of the coordinates. -/
theorem sum_val {V : C} {ι : Type*} (s : Finset ι) (x : ι → D.sections V) :
    (show D.sections V from ∑ i ∈ s, (show D.presheaf.obj (op V) from x i)).1 =
      ∑ i ∈ s, (x i).1 := by
  change ((∑ i ∈ s, x i : D.sections V) : D.Amb V) = _
  exact Submodule.coe_sum _ _ _

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The entries of a finite sum of families of coordinates are the sums of the entries. -/
theorem amb_sum_apply {V : C} {ι : Type*} (s : Finset ι) (x : ι → D.Amb V) (k : K)
    (i : Fin (D.n k)) : (∑ j ∈ s, x j) k i = ∑ j ∈ s, x j k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

variable (D)

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of a section of the glued presheaf. -/
abbrev val {V : C} (x : D.presheaf.obj (op V)) : D.Amb V := (show D.sections V from x).1

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- A section of `presheaf` is determined by its coordinates. -/
theorem val_injective {V : C} {x y : D.presheaf.obj (op V)} (h : D.val x = D.val y) : x = y :=
  Subtype.ext h

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of a sum are the sum of the coordinates. -/
theorem val_add {V : C} (x y : D.presheaf.obj (op V)) : D.val (x + y) = D.val x + D.val y := rfl

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of `r • x` are `r` times the coordinates of `x`. -/
theorem val_smul {V : C} (r : O.obj.obj (op V)) (x : D.presheaf.obj (op V)) :
    D.val (r • x) = r • D.val x := rfl

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of a restriction are the restricted coordinates. -/
theorem val_res {V V' : C} (f : V' ⟶ V) (x : D.presheaf.obj (op V)) :
    D.val (res D.presheaf f x) = D.resAmb f (D.val x) := rfl

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of a finite sum are the sum of the coordinates. -/
theorem val_sum {V : C} {ι : Type*} (s : Finset ι) (x : ι → D.presheaf.obj (op V)) :
    D.val (∑ i ∈ s, x i) = ∑ i ∈ s, D.val (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, val_add, ih]

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of a section of `presheaf` satisfy the transition relation `Rel`. -/
theorem val_mem {V : C} (x : D.presheaf.obj (op V)) : D.Rel (D.val x) :=
  (show D.sections V from x).2

/-- The frame vectors, as sections of the glued presheaf. -/
abbrev frame' (hC : D.Cocycle) (k : K) (i : Fin (D.n k)) : D.presheaf.obj (op (D.W k)) :=
  (⟨D.frameAmb k i, D.frameAmb_mem hC k i⟩ : D.sections (D.W k))

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinates of `frame' hC k i` are `frameAmb k i`. -/
theorem val_frame' (hC : D.Cocycle) (k : K) (i : Fin (D.n k)) :
    D.val (D.frame' hC k i) = D.frameAmb k i := rfl

/-- The coordinate map attached to a morphism into a member. -/
def coordMap {V : C} {k : K} (h : V ⟶ D.W k) :
    D.presheaf.obj (op V) →ₗ[O.obj.obj (op V)] (Fin (D.n k) → O.obj.obj (op V)) where
  toFun x i := pb O (prod.lift h (𝟙 V)) (D.val x k i)
  map_add' x y := by
    funext i
    simp only [val_add, add_apply, map_add, Pi.add_apply]
  map_smul' r x := by
    funext i
    simp only [val_smul, smul_apply, map_mul, σ, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [← pb_comp, prod.lift_snd, pb_id]

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The coordinate map sends the restriction of the frame vector `e k i` to the `i`-th standard
basis vector. -/
theorem coordMap_frame (hU : D.Unit) (hC : D.Cocycle) {V : C} {k : K} (h : V ⟶ D.W k)
    (i : Fin (D.n k)) : D.coordMap h (res D.presheaf h (D.frame' hC k i)) = Pi.single i 1 := by
  funext i'
  change pb O (prod.lift h (𝟙 V)) (D.resAmb h (D.frameAmb k i) k i') = _
  rw [pb_lift_resAmb, pb_lift_frameAmb, Category.id_comp, hU k h i' i]
  simp [Pi.single_apply, eq_comm]

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
  /-- The coordinates of a combination of the restricted frame vectors `e k i`. -/
  private theorem val_sum_smul_res_frame' (hC : D.Cocycle) {V : C} {k : K} (h : V ⟶ D.W k)
      (c : Fin (D.n k) → O.obj.obj (op V)) (l : K) (j : Fin (D.n l)) :
      D.val (∑ i, c i • res D.presheaf h (D.frame' hC k i)) l j =
        ∑ i, D.gAt (prod.fst : D.W l ⨯ V ⟶ D.W l) (prod.snd ≫ h) j i * D.σ l V (c i) := by
    rw [val_sum, amb_sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [val_smul, smul_apply, val_res, val_frame', resAmb_frameAmb, mul_comm]

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- Every section over `V` is the combination of the restricted frame vectors `e k i` with
coefficients its coordinates `coordMap h x i`. -/
theorem sum_coordMap (hC : D.Cocycle) {V : C} {k : K} (h : V ⟶ D.W k)
    (x : D.presheaf.obj (op V)) :
    ∑ i, D.coordMap h x i • res D.presheaf h (D.frame' hC k i) = x := by
  apply val_injective
  ext l j
  rw [val_sum_smul_res_frame']
  have hx := D.val_mem x (prod.snd : D.W l ⨯ V ⟶ V) l k prod.fst (prod.snd ≫ h) j
  rw [prod.lift_fst_snd, pb_id] at hx
  rw [hx]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact pb_pb_of_comp_eq O (by ext <;> simp) _

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- **The frame vectors of the glued presheaf form a frame.** -/
theorem isFrame_frame' (hU : D.Unit) (hC : D.Cocycle) (k : K) :
    IsFrame D.presheaf (D.frame' hC k) where
  linearIndependent h := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrArg (fun x => D.coordMap h x i) hc
    simp only [map_sum, map_smul, coordMap_frame D hU hC, map_zero] at this
    simpa [Pi.single_apply] using this
  span h := by
    intro x _
    rw [← D.sum_coordMap hC h x]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- **The transition relation of the glued frames**: over `P k l`, the frame over `W l` is the
frame over `W k` times the transition matrix. -/
theorem res_p₂_frame' (hC : D.Cocycle) (k l : K) (j : Fin (D.n l)) :
    res D.presheaf (D.p₂ k l) (D.frame' hC l j) =
      ∑ i, D.g k l i j • res D.presheaf (D.p₁ k l) (D.frame' hC k i) := by
  apply val_injective
  ext m x
  rw [val_sum_smul_res_frame', val_res, val_frame', resAmb_frameAmb, ← hC m k l prod.fst
    (prod.snd ≫ D.p₁ k l) (prod.snd ≫ D.p₂ k l) x j]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [gAt, ← comp_pairLift, pairLift_p₁_p₂, Category.comp_id]

omit hO [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- **The coordinates of the transition between the glued frames are the given matrices.** -/
theorem coord_res_p₂_frame' (hU : D.Unit) (hC : D.Cocycle) (k l : K) (b : Fin (D.n l))
    (a : Fin (D.n k)) :
    (D.isFrame_frame' hU hC k).coord (D.p₁ k l) (res D.presheaf (D.p₂ k l) (D.frame' hC l b)) a =
      D.g k l a b :=
  congrFun (IsFrame.coord_eq_of_sum _ _ _ _ (D.res_p₂_frame' hC k l b).symm) a

omit [HasBinaryProducts C] hO
  [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The identity condition may be checked on the diagonal of each member. -/
theorem unit_of_diag
    (h : ∀ k (i j : Fin (D.n k)),
      pb O (D.pairLift (𝟙 (D.W k)) (𝟙 (D.W k))) (D.g k k i j) = if i = j then 1 else 0) :
    D.Unit := by
  intro k T a i j
  rw [gAt, show D.pairLift a a = a ≫ D.pairLift (𝟙 (D.W k)) (𝟙 (D.W k)) by
    rw [comp_pairLift, Category.comp_id], pb_comp, h k i j]
  split_ifs <;> simp

omit [HasBinaryProducts C] hO
  [ReflectsLimitsOfSize.{v, max v u} (CategoryTheory.forget AddCommGrpCat.{w})] in
/-- The cocycle condition may be checked on a triple product of each three members. -/
theorem cocycle_of_triple (Q : K → K → K → C) (q₁ : ∀ k l m, Q k l m ⟶ D.W k)
    (q₂ : ∀ k l m, Q k l m ⟶ D.W l) (q₃ : ∀ k l m, Q k l m ⟶ D.W m)
    (hQ : ∀ (k l m : K) {T : C} (a : T ⟶ D.W k) (b : T ⟶ D.W l) (c : T ⟶ D.W m),
      ∃ t : T ⟶ Q k l m, t ≫ q₁ k l m = a ∧ t ≫ q₂ k l m = b ∧ t ≫ q₃ k l m = c)
    (h : ∀ (k l m : K) (i : Fin (D.n k)) (j : Fin (D.n m)),
      ∑ x, D.gAt (q₁ k l m) (q₂ k l m) i x * D.gAt (q₂ k l m) (q₃ k l m) x j =
        D.gAt (q₁ k l m) (q₃ k l m) i j) :
    D.Cocycle := by
  intro k l m T a b c i j
  obtain ⟨t, rfl, rfl, rfl⟩ := hQ k l m a b c
  simpa only [map_sum, map_mul, pb_gAt] using congrArg (pb O t) (h k l m i j)

end GlueData

end Stacks.SheafOfModules.ChartFrames
