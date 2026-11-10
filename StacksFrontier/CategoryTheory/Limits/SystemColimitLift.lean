module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.CategoryTheory.Limits.SystemColimit

/-!
# Systems over a preorder as functors on a filtered category

Let `I` be a preordered set and let `(A, T)` be a system over `I` in the sense of
`CategoryTheory.Limits.IsSystemColimit`: an object `A i` for every index and, for `j ≤ i`, a
transition map `T : A j ⟶ A i`, satisfying the cocycle condition `T_{kj} = T_{ki} ∘ T_{ij}` but not
necessarily the identity law `T_{ii} = 𝟙`. Such a system is not a functor on `I`, but it is a
functor on the preorder `SystemLift I = I × ℕ` in which `(j, n) ≤ (k, m)` exactly when the two
pairs are equal or `j ≤ k` and `n < m`: the second coordinate separates every non-identity arrow
from the identities, so that the transition map `T_{jj}` is only ever used along a strict
inequality `n < m`. If `I` is directed then so is `SystemLift I`, and the colimits of the system
are exactly the colimits of that functor.

This makes Mathlib's theory of filtered colimits available for systems which satisfy the
cocycle condition only, such as the systems of sheaves of [Stacks, Tag 0EZL].

## Main definitions

* `CategoryTheory.Limits.SystemLift I`: the preorder `I × ℕ` described above.
* `CategoryTheory.Limits.SystemLift.functor`: the functor `SystemLift I ⥤ 𝒞` attached to a
  system satisfying the cocycle condition.
* `CategoryTheory.Limits.SystemLift.cocone`: the cocone attached to a compatible family of maps.

## Main results

* `CategoryTheory.Limits.SystemLift.isSystemColimit_iff`: a compatible family of maps is a colimit
  of the system if and only if the attached cocone is a colimit cocone.
* `CategoryTheory.Limits.IsSystemColimit.of_forall_exists` and
  `CategoryTheory.Limits.IsSystemColimit.exists_eq` /
  `CategoryTheory.Limits.IsSystemColimit.exists_eq_zero`: over a directed index set, the colimits
  of systems of abelian groups are characterized elementwise: every element of the colimit comes
  from some stage, and an element of a stage which maps to zero already dies under a transition
  map.
* `CategoryTheory.Limits.IsSystemColimit.exists_eq_of_exact`,
  `CategoryTheory.Limits.IsSystemColimit.exists_eq_zero_of_exact` and
  `CategoryTheory.Limits.IsSystemColimit.of_exact`: **the four and five lemmas for colimits of
  systems of abelian groups**. Given exact sequences of systems and of their colimits, compatible
  with the transition maps and the legs, the two elementwise halves of being a colimit propagate
  to the middle term from its neighbours.
* `CategoryTheory.Limits.IsSystemColimit.of_addEquiv`: colimits of systems of abelian groups can
  be transported along additive isomorphisms, also between different universes.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

universe w v u

/-- The preorder on `I × ℕ` in which `(j, n) ≤ (k, m)` exactly when the pairs are equal or
`j ≤ k` and `n < m`. Systems over `I` satisfying the cocycle condition are functors on it. -/
def SystemLift (I : Type w) : Type w := I × ℕ

namespace SystemLift

variable {I : Type w} [Preorder I]

/-- The preorder on `SystemLift I` in which `x ≤ y` exactly when `x = y`, or the index of `x` is
at most that of `y` and the level of `x` is strictly less than that of `y`. -/
instance : Preorder (SystemLift I) where
  le x y := x = y ∨ ((x : I × ℕ).1 ≤ (y : I × ℕ).1 ∧ (x : I × ℕ).2 < (y : I × ℕ).2)
  le_refl x := Or.inl rfl
  le_trans x y z := by
    rintro (rfl | ⟨h₁, h₂⟩) (rfl | ⟨h₃, h₄⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h₃, h₄⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁.trans h₃, h₂.trans h₄⟩

/-- The element `(i, n)` of `SystemLift I`. -/
def mk (i : I) (n : ℕ) : SystemLift I := (i, n)

/-- The index of `I` underlying an element of `SystemLift I`. -/
def idx (x : SystemLift I) : I := (x : I × ℕ).1

/-- The level underlying an element of `SystemLift I`. -/
def lvl (x : SystemLift I) : ℕ := (x : I × ℕ).2

omit [Preorder I] in
/-- The index of `mk i n` is `i`. -/
@[simp] lemma idx_mk (i : I) (n : ℕ) : (mk i n).idx = i := rfl

omit [Preorder I] in
/-- The level of `mk i n` is `n`. -/
@[simp] lemma lvl_mk (i : I) (n : ℕ) : (mk i n).lvl = n := rfl

/-- `x ≤ y` in `SystemLift I` if and only if `x = y`, or `x.idx ≤ y.idx` and `x.lvl < y.lvl`. -/
lemma le_def {x y : SystemLift I} : x ≤ y ↔ x = y ∨ (x.idx ≤ y.idx ∧ x.lvl < y.lvl) := Iff.rfl

/-- If `i ≤ j` and `n < m`, then `mk i n ≤ mk j m`. -/
lemma mk_le_mk {i j : I} {n m : ℕ} (h : i ≤ j) (hnm : n < m) : mk i n ≤ mk j m :=
  Or.inr ⟨h, hnm⟩

/-- If `x ≤ y` in `SystemLift I`, then `x.idx ≤ y.idx` in `I`. -/
lemma idx_le_idx {x y : SystemLift I} (h : x ≤ y) : x.idx ≤ y.idx := by
  rcases h with rfl | ⟨h, -⟩
  · exact le_rfl
  · exact h

/-- If `x ≤ y` and the level of `x` is not less than that of `y`, then `x = y`. -/
lemma eq_of_le_of_not_lt {x y : SystemLift I} (h : x ≤ y) (h' : ¬ x.lvl < y.lvl) : x = y :=
  (le_def.mp h).resolve_right fun h'' => h' h''.2

/-- `SystemLift I` is nonempty when `I` is. -/
instance [Nonempty I] : Nonempty (SystemLift I) := inferInstanceAs (Nonempty (I × ℕ))

/-- `SystemLift I` is directed when `I` is. -/
instance [IsDirected I (· ≤ ·)] : IsDirected (SystemLift I) (· ≤ ·) where
  directed x y := by
    obtain ⟨k, hx, hy⟩ := directed_of (· ≤ ·) x.idx y.idx
    exact ⟨mk k (max x.lvl y.lvl + 1), Or.inr ⟨hx, Nat.lt_succ_of_le (le_max_left _ _)⟩,
      Or.inr ⟨hy, Nat.lt_succ_of_le (le_max_right _ _)⟩⟩

/-- `SystemLift I` is filtered when `I` is directed and nonempty. -/
instance [IsDirected I (· ≤ ·)] [Nonempty I] : IsFiltered (SystemLift I) :=
  isFiltered_of_directed_le_nonempty _

variable {𝒞 : Type u} [Category.{v} 𝒞] (A : Iᵒᵖ → 𝒞)
  (T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i))
  (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)

/-- The transition map of a system between two indices `i ≤ j` of `I`. -/
def tr {i j : I} (h : i ≤ j) : A (Opposite.op i) ⟶ A (Opposite.op j) :=
  T (homOfLE h).op

include hT in
/-- The transition maps of a system satisfying the cocycle condition compose:
`tr A T h₁ ≫ tr A T h₂ = tr A T (h₁.trans h₂)`. -/
lemma tr_comp {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    tr A T h₁ ≫ tr A T h₂ = tr A T (h₁.trans h₂) :=
  (hT _ _).symm

/-- The map of the functor attached to a system, along `x ≤ y` in `SystemLift I`: the transition
map of the system when the levels increase strictly, and the identity otherwise. -/
def map {x y : SystemLift I} (h : x ≤ y) : A (Opposite.op x.idx) ⟶ A (Opposite.op y.idx) :=
  if hlt : x.lvl < y.lvl then tr A T (idx_le_idx h)
  else eqToHom (by rw [eq_of_le_of_not_lt h hlt])

/-- Along `x ≤ y` with `x.lvl < y.lvl`, `map A T` is the transition map of the system. -/
lemma map_of_lt {x y : SystemLift I} (h : x ≤ y) (hlt : x.lvl < y.lvl) :
    map A T h = tr A T (idx_le_idx h) :=
  dite_eq_left hlt

/-- Along `x ≤ x`, `map A T` is the identity. -/
lemma map_self (x : SystemLift I) : map A T (le_refl x) = 𝟙 _ := by
  rw [map, dite_eq_right (lt_irrefl _)]
  rfl

include hT in
/-- For a system satisfying the cocycle condition, `map A T` is compatible with composition. -/
lemma map_comp {x y z : SystemLift I} (h₁ : x ≤ y) (h₂ : y ≤ z) :
    map A T (h₁.trans h₂) = map A T h₁ ≫ map A T h₂ := by
  by_cases hxy : x.lvl < y.lvl
  · by_cases hyz : y.lvl < z.lvl
    · rw [map_of_lt A T _ (hxy.trans hyz), map_of_lt A T _ hxy, map_of_lt A T _ hyz,
        tr_comp A T hT]
    · obtain rfl := eq_of_le_of_not_lt h₂ hyz
      rw [map_self, Category.comp_id]
  · obtain rfl := eq_of_le_of_not_lt h₁ hxy
    rw [map_self, Category.id_comp]

/-- **The functor attached to a system** satisfying the cocycle condition. -/
def functor : SystemLift I ⥤ 𝒞 where
  obj x := A (Opposite.op x.idx)
  map f := map A T (leOfHom f)
  map_id x := map_self A T x
  map_comp f g := map_comp A T hT (leOfHom f) (leOfHom g)

/-- The functor attached to a system sends `x` to `A (op x.idx)`. -/
@[simp] lemma functor_obj (x : SystemLift I) : (functor A T hT).obj x = A (Opposite.op x.idx) :=
  rfl

/-- The functor attached to a system sends `f : x ⟶ y` to `map A T (leOfHom f)`. -/
lemma functor_map {x y : SystemLift I} (f : x ⟶ y) :
    (functor A T hT).map f = map A T (leOfHom f) := rfl

variable {A T}

/-- If an element `z` is killed by the image under `G'` of `map A T h`, it is killed by the image
under `G'` of the transition map of the system along `idx_le_idx h`. -/
lemma map_tr_apply_eq_zero.{t} (G' : 𝒞 ⥤ AddCommGrpCat.{t}) {x y : SystemLift I} (h : x ≤ y)
    {z : G'.obj (A (Opposite.op x.idx))} (hz : G'.map (map A T h) z = 0) :
    G'.map (T (homOfLE (idx_le_idx h)).op) z = 0 := by
  by_cases hlt : x.lvl < y.lvl
  · rwa [map_of_lt A T h hlt] at hz
  · obtain rfl := eq_of_le_of_not_lt h hlt
    rw [map_self, Functor.map_id] at hz
    rw [show z = 0 from hz, map_zero]

/-- The cocone attached to a family of maps compatible with the transition maps. -/
def cocone {B : 𝒞} (ψ : ∀ i, A i ⟶ B) (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j) :
    Cocone (functor A T hT) where
  pt := B
  ι :=
    { app x := ψ (Opposite.op x.idx)
      naturality x y f := by
        change map A T (leOfHom f) ≫ ψ _ = ψ _ ≫ 𝟙 _
        rw [Category.comp_id]
        by_cases hlt : x.lvl < y.lvl
        · rw [map_of_lt A T _ hlt]
          exact hψ _
        · obtain rfl := eq_of_le_of_not_lt (leOfHom f) hlt
          rw [map_self, Category.id_comp] }

/-- The leg of `cocone hT ψ hψ` at `x` is `ψ (op x.idx)`. -/
@[simp] lemma cocone_ι_app {B : 𝒞} (ψ : ∀ i, A i ⟶ B)
    (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j) (x : SystemLift I) :
    (cocone hT ψ hψ).ι.app x = ψ (Opposite.op x.idx) := rfl

/-- A cocone over the functor attached to a system has the same leg at every level. -/
lemma ι_app_eq (s : Cocone (functor A T hT)) (i : I) (n : ℕ) :
    s.ι.app (mk i n) = s.ι.app (mk i 0) := by
  have e₁ : mk i n ≤ mk i (n + 1) := mk_le_mk (le_refl i) (Nat.lt_succ_self n)
  have e₂ : mk i 0 ≤ mk i (n + 1) := mk_le_mk (le_refl i) (Nat.succ_pos n)
  have h₁ := s.w (homOfLE e₁)
  have h₂ := s.w (homOfLE e₂)
  rw [functor_map, map_of_lt A T e₁ (Nat.lt_succ_self n)] at h₁
  rw [functor_map, map_of_lt A T e₂ (Nat.succ_pos n)] at h₂
  exact h₁.symm.trans h₂

/-- The family of maps underlying a cocone over the functor attached to a system. -/
def legs (s : Cocone (functor A T hT)) (i : Iᵒᵖ) : A i ⟶ s.pt := s.ι.app (mk i.unop 0)

/-- The family of maps underlying a cocone over the functor attached to a system is compatible with
the transition maps. -/
lemma ι_app_compatible (s : Cocone (functor A T hT)) {i j : Iᵒᵖ} (a : i ⟶ j) :
    T a ≫ legs hT s i = legs hT s j := by
  have e : mk j.unop 0 ≤ mk i.unop 1 := mk_le_mk (leOfHom a.unop) Nat.zero_lt_one
  have h := s.w (homOfLE e)
  rw [functor_map, map_of_lt A T e Nat.zero_lt_one] at h
  change T a ≫ s.ι.app (mk i.unop 0) = s.ι.app (mk j.unop 0)
  rwa [← ι_app_eq hT s i.unop 1]

/-- **The colimits of a system are the colimits of the attached functor.** -/
theorem isSystemColimit_iff {B : 𝒞} (ψ : ∀ i, A i ⟶ B)
    (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j) :
    IsSystemColimit A T B ψ ↔ Nonempty (IsColimit (cocone hT ψ hψ)) := by
  refine ⟨fun h => ⟨{ desc := fun s => h.desc (legs hT s) (ι_app_compatible hT s)
                      fac := fun s x => ?_
                      uniq := fun s m hm => h.hom_ext hψ fun i =>
                        (hm (mk i.unop 0)).trans (h.fac _ (ι_app_compatible hT s) i).symm }⟩,
    fun ⟨hc⟩ G τ hτ => ?_⟩
  · change ψ (Opposite.op x.idx) ≫ _ = _
    rw [h.fac]
    exact (ι_app_eq hT s x.idx x.lvl).symm
  · let s : Cocone (functor A T hT) := cocone hT τ hτ
    exact ⟨hc.desc s, fun i => hc.fac s (mk i.unop 0),
      fun χ hχ => hc.uniq s χ fun x => hχ (Opposite.op x.idx)⟩

end SystemLift

/-! ### Systems of abelian groups -/

namespace IsSystemColimit

variable {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{w, v}]
  {A : Iᵒᵖ → AddCommGrpCat.{v}} {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)}
  (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)
  {B : AddCommGrpCat.{v}} {ψ : ∀ i, A i ⟶ B}
  (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j)

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- The forgetful functor of abelian groups preserves the filtered colimits indexed by
`SystemLift I`. -/
lemma preservesColimitsOfShape_forget [IsDirected I (· ≤ ·)] [Nonempty I] :
    PreservesColimitsOfShape (SystemLift I) (forget AddCommGrpCat.{v}) :=
  have : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, w, w} _
  inferInstance

attribute [local instance] preservesColimitsOfShape_forget

include hT hψ in
/-- **Every element of a colimit of a system of abelian groups comes from a stage.** -/
theorem exists_eq (h : IsSystemColimit A T B ψ) (b : B) : ∃ (i : Iᵒᵖ) (x : A i), ψ i x = b := by
  obtain ⟨hc⟩ := (SystemLift.isSystemColimit_iff hT ψ hψ).mp h
  obtain ⟨x, y, hy⟩ := Concrete.isColimit_exists_rep _ hc b
  exact ⟨Opposite.op x.idx, y, hy⟩

include hT hψ in
/-- **An element of a stage of a system of abelian groups which maps to zero in a colimit already
dies under a transition map.** -/
theorem exists_eq_zero (h : IsSystemColimit A T B ψ) {i : Iᵒᵖ} (x : A i) (hx : ψ i x = 0) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i), T a x = 0 := by
  obtain ⟨hc⟩ := (SystemLift.isSystemColimit_iff hT ψ hψ).mp h
  have hx' : (SystemLift.cocone hT ψ hψ).ι.app (SystemLift.mk i.unop 0) x =
      (SystemLift.cocone hT ψ hψ).ι.app (SystemLift.mk i.unop 0) 0 := by
    rwa [map_zero]
  obtain ⟨k, f, g, hfg⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hc
    (i := SystemLift.mk i.unop 0) (j := SystemLift.mk i.unop 0) x 0).mp hx'
  rw [map_zero] at hfg
  exact ⟨_, _, SystemLift.map_tr_apply_eq_zero (𝟭 _) (leOfHom f) (z := x) hfg⟩

omit [Nonempty I] [UnivLE.{w, v}] in
include hT hψ in
/-- If every element of a stage which maps to zero under `ψ` dies under a transition map, then a
compatible family `τ` agrees on any two elements of stages with the same image under `ψ`. -/
theorem apply_eq_apply_of_forall_exists
    (hinj : ∀ (i : Iᵒᵖ) (x : A i), ψ i x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), T a x = 0)
    {G : AddCommGrpCat.{v}} (τ : ∀ i, A i ⟶ G) (hτ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ τ i = τ j)
    {i i' : Iᵒᵖ} {x : A i} {x' : A i'} (hxx' : ψ i x = ψ i' x') : τ i x = τ i' x' := by
  obtain ⟨j, hj, hj'⟩ := directed_of (· ≤ ·) i.unop i'.unop
  let a : Opposite.op j ⟶ i := (homOfLE hj).op
  let a' : Opposite.op j ⟶ i' := (homOfLE hj').op
  have h0 : ψ (Opposite.op j) (T a x - T a' x') = 0 := by
    rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hψ, hψ, hxx',
      sub_self]
  obtain ⟨k, b, hk⟩ := hinj _ _ h0
  rw [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← hT, ← hT] at hk
  rw [← hτ (b ≫ a), ← hτ (b ≫ a'), ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hk]

omit [Nonempty I] [UnivLE.{w, v}] in
include hT hψ in
/-- **The elementwise characterization of colimits of systems of abelian groups**: a compatible
family of maps is a colimit of the system as soon as every element of the target comes from a
stage and every element of a stage which maps to zero dies under a transition map. -/
theorem of_forall_exists (hsurj : ∀ b : B, ∃ (i : Iᵒᵖ) (x : A i), ψ i x = b)
    (hinj : ∀ (i : Iᵒᵖ) (x : A i), ψ i x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), T a x = 0) :
    IsSystemColimit A T B ψ := by
  classical
  intro G τ hτ
  have hwd : ∀ {i i' : Iᵒᵖ} {x : A i} {x' : A i'}, ψ i x = ψ i' x' → τ i x = τ i' x' :=
    apply_eq_apply_of_forall_exists hT hψ hinj τ hτ
  choose i x hx using hsurj
  let χ : B ⟶ G := AddCommGrpCat.ofHom
    { toFun b := τ (i b) (x b)
      map_zero' := by
        rw [hwd (show ψ (i 0) (x 0) = ψ (i 0) 0 by rw [hx, map_zero]), map_zero]
      map_add' b b' := by
        obtain ⟨j, hj, hj'⟩ := directed_of (· ≤ ·) (i b).unop (i b').unop
        let a : Opposite.op j ⟶ i b := (homOfLE hj).op
        let a' : Opposite.op j ⟶ i b' := (homOfLE hj').op
        have e : ψ (i (b + b')) (x (b + b')) = ψ (Opposite.op j) (T a (x b) + T a' (x b')) := by
          rw [hx, map_add, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hψ, hψ,
            hx, hx]
        rw [hwd e, map_add, ← ConcreteCategory.comp_apply,
          ← ConcreteCategory.comp_apply, hτ, hτ] }
  refine ⟨χ, fun j => ?_, fun χ' hχ' => ?_⟩
  · ext y
    exact hwd (hx _)
  · ext b
    change χ' b = τ (i b) (x b)
    conv_lhs => rw [← hx b]
    rw [← ConcreteCategory.comp_apply, hχ']

/-- **Colimits of systems of abelian groups from colimit cocones of the attached functor.** If a
functor `G'` to abelian groups carries the cocone attached to a compatible family to a colimit
cocone, then the images of the family under `G'` form a colimit of the image system. -/
theorem of_isColimit_mapCocone {𝒞 : Type*} [Category* 𝒞] {A : Iᵒᵖ → 𝒞}
    {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)}
    (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a) {B : 𝒞}
    {ψ : ∀ i, A i ⟶ B} (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j)
    (G' : 𝒞 ⥤ AddCommGrpCat.{v}) (hc : IsColimit (G'.mapCocone (SystemLift.cocone hT ψ hψ))) :
    IsSystemColimit (fun i => G'.obj (A i)) (fun a => G'.map (T a)) (G'.obj B)
      (fun i => G'.map (ψ i)) := by
  have hT' : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
      G'.map (T (a ≫ b)) = G'.map (T b) ≫ G'.map (T a) := fun a b => by rw [hT, G'.map_comp]
  have hψ' : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G'.map (T a) ≫ G'.map (ψ i) = G'.map (ψ j) :=
    fun a => by rw [← G'.map_comp, hψ]
  refine of_forall_exists hT' hψ' (fun b => ?_) (fun i y hy => ?_)
  · obtain ⟨x, y, hy⟩ := Concrete.isColimit_exists_rep _ hc b
    exact ⟨Opposite.op x.idx, y, hy⟩
  · have hy' : (G'.mapCocone (SystemLift.cocone hT ψ hψ)).ι.app (SystemLift.mk i.unop 0) y =
        (G'.mapCocone (SystemLift.cocone hT ψ hψ)).ι.app (SystemLift.mk i.unop 0) 0 := by
      rwa [map_zero]
    obtain ⟨k, f, g, hfg⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hc
      (i := SystemLift.mk i.unop 0) (j := SystemLift.mk i.unop 0) y 0).mp hy'
    rw [map_zero] at hfg
    exact ⟨_, _, SystemLift.map_tr_apply_eq_zero G' (leOfHom f) hfg⟩

end IsSystemColimit

/-! ### Transport, and the four and five lemmas -/

namespace IsSystemColimit

universe v'

variable {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]

/-- **Colimits of systems of abelian groups are transported along additive isomorphisms**, which
may change the universe of the groups. -/
theorem of_addEquiv [UnivLE.{w, v}] [UnivLE.{w, v'}] {A : Iᵒᵖ → AddCommGrpCat.{v}}
    {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)}
    (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)
    {B : AddCommGrpCat.{v}} {ψ : ∀ i, A i ⟶ B} (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j)
    (h : IsSystemColimit A T B ψ) {A' : Iᵒᵖ → AddCommGrpCat.{v'}}
    {T' : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A' j ⟶ A' i)} {B' : AddCommGrpCat.{v'}}
    {ψ' : ∀ i, A' i ⟶ B'} (e : ∀ i, A i ≃+ A' i) (eB : B ≃+ B')
    (he : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A j), e i (T a x) = T' a (e j x))
    (heB : ∀ i x, eB (ψ i x) = ψ' i (e i x)) :
    IsSystemColimit A' T' B' ψ' := by
  have hT'x : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (y : A' j), T' a y = e i (T a ((e j).symm y)) :=
    fun a y => by rw [he, AddEquiv.apply_symm_apply]
  have hψ'x : ∀ i (y : A' i), ψ' i y = eB (ψ i ((e i).symm y)) :=
    fun i y => by rw [heB, AddEquiv.apply_symm_apply]
  have hT' : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T' (a ≫ b) = T' b ≫ T' a := by
    intro i j k a b
    ext y
    rw [ConcreteCategory.comp_apply, hT'x, hT'x, hT'x, hT, ConcreteCategory.comp_apply,
      AddEquiv.symm_apply_apply]
  have hψ' : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T' a ≫ ψ' i = ψ' j := by
    intro i j a
    ext y
    rw [ConcreteCategory.comp_apply, hT'x, hψ'x, hψ'x, AddEquiv.symm_apply_apply,
      ← ConcreteCategory.comp_apply, hψ]
  refine of_forall_exists hT' hψ' (fun b => ?_) (fun i x hx => ?_)
  · obtain ⟨i, x, hx⟩ := h.exists_eq hT hψ (eB.symm b)
    exact ⟨i, e i x, by rw [← heB, hx, AddEquiv.apply_symm_apply]⟩
  · obtain ⟨y, rfl⟩ := (e i).surjective x
    obtain ⟨j, a, ha⟩ := h.exists_eq_zero hT hψ y
      (eB.injective (by rw [heB, hx, map_zero]))
    exact ⟨j, a, by rw [← he, ha, map_zero]⟩

/-- A system of zero groups with a zero colimit. -/
theorem of_subsingleton [UnivLE.{w, v}] {A : Iᵒᵖ → AddCommGrpCat.{v}}
    {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)}
    (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)
    {B : AddCommGrpCat.{v}} {ψ : ∀ i, A i ⟶ B} (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j)
    [∀ i, Subsingleton (A i)] [Subsingleton B] : IsSystemColimit A T B ψ :=
  of_forall_exists hT hψ (fun b => ⟨Classical.arbitrary _, 0, Subsingleton.elim _ b⟩)
    (fun i _ _ => ⟨i, 𝟙 i, Subsingleton.elim _ _⟩)

end IsSystemColimit

namespace IsSystemColimit

variable {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **The four lemma for colimits of systems, surjectivity half.** Let `A₂ → A₃ → A₄ → A₅` be
maps of systems of abelian groups, `B₂ → B₃ → B₄ → B₅` maps of abelian groups compatible with
families of legs `ψₖ : Aₖ ⟶ Bₖ`, the stages exact at `A₄` and the colimit row exact at `B₃` and a
complex at `B₄`. If every element of `B₂` and of `B₄` comes from a stage, and every element of a
stage of `A₅` which maps to zero dies under a transition map, then every element of `B₃` comes
from a stage. -/
theorem exists_eq_of_exact {A₂ A₃ A₄ A₅ : Iᵒᵖ → AddCommGrpCat.{v}}
    {T₃ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₃ j ⟶ A₃ i)} {T₄ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₄ j ⟶ A₄ i)}
    {T₅ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₅ j ⟶ A₅ i)}
    {B₂ B₃ B₄ B₅ : AddCommGrpCat.{v}} {ψ₂ : ∀ i, A₂ i ⟶ B₂} {ψ₃ : ∀ i, A₃ i ⟶ B₃}
    {ψ₄ : ∀ i, A₄ i ⟶ B₄} {ψ₅ : ∀ i, A₅ i ⟶ B₅}
    (u : ∀ i, A₂ i ⟶ A₃ i) (v : ∀ i, A₃ i ⟶ A₄ i) (w : ∀ i, A₄ i ⟶ A₅ i)
    (u' : B₂ ⟶ B₃) (v' : B₃ ⟶ B₄) (w' : B₄ ⟶ B₅)
    (hw : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₄ j), w i (T₄ a x) = T₅ a (w j x))
    (hψ₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₃ j), ψ₃ i (T₃ a x) = ψ₃ j x)
    (hψ₄ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₄ j), ψ₄ i (T₄ a x) = ψ₄ j x)
    (hu' : ∀ i x, u' (ψ₂ i x) = ψ₃ i (u i x)) (hv' : ∀ i x, v' (ψ₃ i x) = ψ₄ i (v i x))
    (hw' : ∀ i x, w' (ψ₄ i x) = ψ₅ i (w i x))
    (hexA₄ : ∀ i x, w i x = 0 → ∃ y, v i y = x)
    (hexB₃ : ∀ b, v' b = 0 → ∃ c, u' c = b) (hexB₄ : ∀ b, w' (v' b) = 0)
    (hsurj₂ : ∀ b : B₂, ∃ (i : Iᵒᵖ) (x : A₂ i), ψ₂ i x = b)
    (hsurj₄ : ∀ b : B₄, ∃ (i : Iᵒᵖ) (x : A₄ i), ψ₄ i x = b)
    (hinj₅ : ∀ (i : Iᵒᵖ) (x : A₅ i), ψ₅ i x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), T₅ a x = 0)
    (b : B₃) : ∃ (i : Iᵒᵖ) (x : A₃ i), ψ₃ i x = b := by
  obtain ⟨i, x₄, hx₄⟩ := hsurj₄ (v' b)
  obtain ⟨j, a, ha⟩ := hinj₅ i (w i x₄) (by rw [← hw', hx₄, hexB₄])
  obtain ⟨x₃, hx₃⟩ := hexA₄ j (T₄ a x₄) (by rw [hw, ha])
  obtain ⟨c, hc⟩ := hexB₃ (b - ψ₃ j x₃) (by rw [map_sub, hv', hx₃, hψ₄, hx₄, sub_self])
  obtain ⟨k, x₂, hx₂⟩ := hsurj₂ c
  obtain ⟨l, hlj, hlk⟩ := directed_of (· ≤ ·) j.unop k.unop
  refine ⟨Opposite.op l, T₃ (homOfLE hlj).op x₃ + T₃ (homOfLE hlk).op (u k x₂), ?_⟩
  rw [map_add, hψ₃, hψ₃, ← hu', hx₂, hc, add_sub_cancel]

/-- **The four lemma for colimits of systems, injectivity half.** Let `A₁ → A₂ → A₃ → A₄` be maps
of systems of abelian groups, `B₁ → B₂ → B₃ → B₄` maps of abelian groups compatible with families
of legs `ψₖ : Aₖ ⟶ Bₖ`, the stages a complex at `A₂` and exact at `A₃`, and the colimit row exact
at `B₂`. If every element of `B₁` comes from a stage, and every element of a stage of `A₂` or of
`A₄` which maps to zero dies under a transition map, then so does every element of a stage of
`A₃`. -/
theorem exists_eq_zero_of_exact {A₁ A₂ A₃ A₄ : Iᵒᵖ → AddCommGrpCat.{v}}
    {T₁ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₁ j ⟶ A₁ i)} {T₂ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₂ j ⟶ A₂ i)}
    {T₃ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₃ j ⟶ A₃ i)} {T₄ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₄ j ⟶ A₄ i)}
    (hT₃ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₃ (a ≫ b) = T₃ b ≫ T₃ a)
    {B₁ B₂ B₃ B₄ : AddCommGrpCat.{v}} {ψ₁ : ∀ i, A₁ i ⟶ B₁} {ψ₂ : ∀ i, A₂ i ⟶ B₂}
    {ψ₃ : ∀ i, A₃ i ⟶ B₃} {ψ₄ : ∀ i, A₄ i ⟶ B₄}
    (t : ∀ i, A₁ i ⟶ A₂ i) (u : ∀ i, A₂ i ⟶ A₃ i) (v : ∀ i, A₃ i ⟶ A₄ i)
    (t' : B₁ ⟶ B₂) (u' : B₂ ⟶ B₃) (v' : B₃ ⟶ B₄)
    (ht : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₁ j), t i (T₁ a x) = T₂ a (t j x))
    (hu : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₂ j), u i (T₂ a x) = T₃ a (u j x))
    (hv : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₃ j), v i (T₃ a x) = T₄ a (v j x))
    (hψ₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₂ j), ψ₂ i (T₂ a x) = ψ₂ j x)
    (hψ₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₃ j), ψ₃ i (T₃ a x) = ψ₃ j x)
    (ht' : ∀ i x, t' (ψ₁ i x) = ψ₂ i (t i x)) (hu' : ∀ i x, u' (ψ₂ i x) = ψ₃ i (u i x))
    (hv' : ∀ i x, v' (ψ₃ i x) = ψ₄ i (v i x))
    (hexA₂ : ∀ i x, u i (t i x) = 0) (hexA₃ : ∀ i x, v i x = 0 → ∃ y, u i y = x)
    (hexB₂ : ∀ b, u' b = 0 → ∃ c, t' c = b)
    (hsurj₁ : ∀ b : B₁, ∃ (i : Iᵒᵖ) (x : A₁ i), ψ₁ i x = b)
    (hinj₂ : ∀ (i : Iᵒᵖ) (x : A₂ i), ψ₂ i x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), T₂ a x = 0)
    (hinj₄ : ∀ (i : Iᵒᵖ) (x : A₄ i), ψ₄ i x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), T₄ a x = 0)
    (i : Iᵒᵖ) (x₃ : A₃ i) (hx₃ : ψ₃ i x₃ = 0) : ∃ (j : Iᵒᵖ) (a : j ⟶ i), T₃ a x₃ = 0 := by
  obtain ⟨j, a, ha⟩ := hinj₄ i (v i x₃) (by rw [← hv', hx₃, map_zero])
  obtain ⟨x₂, hx₂⟩ := hexA₃ j (T₃ a x₃) (by rw [hv, ha])
  obtain ⟨b₁, hb₁⟩ := hexB₂ (ψ₂ j x₂) (by rw [hu', hx₂, hψ₃, hx₃])
  obtain ⟨k, x₁, hx₁⟩ := hsurj₁ b₁
  obtain ⟨l, hlj, hlk⟩ := directed_of (· ≤ ·) j.unop k.unop
  let c : Opposite.op l ⟶ j := (homOfLE hlj).op
  let d : Opposite.op l ⟶ k := (homOfLE hlk).op
  obtain ⟨m, e, he⟩ := hinj₂ _ (T₂ c x₂ - T₂ d (t k x₁))
    (by rw [map_sub, hψ₂, hψ₂, ← ht', hx₁, hb₁, sub_self])
  rw [map_sub, sub_eq_zero] at he
  refine ⟨m, e ≫ c ≫ a, ?_⟩
  rw [hT₃, hT₃, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← hx₂, ← hu, ← hu, he,
    ← ht, ← ht, hexA₂]

/-- **The five lemma for colimits of systems of abelian groups.** In the situation of
`exists_eq_of_exact` and `exists_eq_zero_of_exact`, if the legs of `A₂` and `A₄` exhibit colimits,
every element of `B₁` comes from a stage and every element of a stage of `A₅` which maps to zero
dies under a transition map, then the legs of `A₃` exhibit `B₃` as the colimit of the system
`A₃`. -/
theorem of_exact [Nonempty I] [UnivLE.{w, v}] {A₁ A₂ A₃ A₄ A₅ : Iᵒᵖ → AddCommGrpCat.{v}}
    {T₁ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₁ j ⟶ A₁ i)} {T₂ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₂ j ⟶ A₂ i)}
    {T₃ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₃ j ⟶ A₃ i)} {T₄ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₄ j ⟶ A₄ i)}
    {T₅ : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A₅ j ⟶ A₅ i)}
    (hT₂ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₂ (a ≫ b) = T₂ b ≫ T₂ a)
    (hT₃ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₃ (a ≫ b) = T₃ b ≫ T₃ a)
    (hT₄ : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T₄ (a ≫ b) = T₄ b ≫ T₄ a)
    {B₁ B₂ B₃ B₄ B₅ : AddCommGrpCat.{v}} {ψ₁ : ∀ i, A₁ i ⟶ B₁} {ψ₂ : ∀ i, A₂ i ⟶ B₂}
    {ψ₃ : ∀ i, A₃ i ⟶ B₃} {ψ₄ : ∀ i, A₄ i ⟶ B₄} {ψ₅ : ∀ i, A₅ i ⟶ B₅}
    (hψ₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₂ a ≫ ψ₂ i = ψ₂ j)
    (hψ₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₃ a ≫ ψ₃ i = ψ₃ j)
    (hψ₄ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T₄ a ≫ ψ₄ i = ψ₄ j)
    (t : ∀ i, A₁ i ⟶ A₂ i) (u : ∀ i, A₂ i ⟶ A₃ i) (v : ∀ i, A₃ i ⟶ A₄ i)
    (w : ∀ i, A₄ i ⟶ A₅ i) (t' : B₁ ⟶ B₂) (u' : B₂ ⟶ B₃) (v' : B₃ ⟶ B₄) (w' : B₄ ⟶ B₅)
    (ht : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₁ j), t i (T₁ a x) = T₂ a (t j x))
    (hu : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₂ j), u i (T₂ a x) = T₃ a (u j x))
    (hv : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₃ j), v i (T₃ a x) = T₄ a (v j x))
    (hw : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₄ j), w i (T₄ a x) = T₅ a (w j x))
    (ht' : ∀ i x, t' (ψ₁ i x) = ψ₂ i (t i x)) (hu' : ∀ i x, u' (ψ₂ i x) = ψ₃ i (u i x))
    (hv' : ∀ i x, v' (ψ₃ i x) = ψ₄ i (v i x)) (hw' : ∀ i x, w' (ψ₄ i x) = ψ₅ i (w i x))
    (hexA₂ : ∀ i x, u i (t i x) = 0) (hexA₃ : ∀ i x, v i x = 0 → ∃ y, u i y = x)
    (hexA₄ : ∀ i x, w i x = 0 → ∃ y, v i y = x)
    (hexB₂ : ∀ b, u' b = 0 → ∃ c, t' c = b) (hexB₃ : ∀ b, v' b = 0 → ∃ c, u' c = b)
    (hexB₄ : ∀ b, w' (v' b) = 0)
    (hsurj₁ : ∀ b : B₁, ∃ (i : Iᵒᵖ) (x : A₁ i), ψ₁ i x = b)
    (h₂ : IsSystemColimit A₂ T₂ B₂ ψ₂) (h₄ : IsSystemColimit A₄ T₄ B₄ ψ₄)
    (hinj₅ : ∀ (i : Iᵒᵖ) (x : A₅ i), ψ₅ i x = 0 → ∃ (j : Iᵒᵖ) (a : j ⟶ i), T₅ a x = 0) :
    IsSystemColimit A₃ T₃ B₃ ψ₃ := by
  have e₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₂ j), ψ₂ i (T₂ a x) = ψ₂ j x := fun a x => by
    rw [← ConcreteCategory.comp_apply, hψ₂]
  have e₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₃ j), ψ₃ i (T₃ a x) = ψ₃ j x := fun a x => by
    rw [← ConcreteCategory.comp_apply, hψ₃]
  have e₄ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) (x : A₄ j), ψ₄ i (T₄ a x) = ψ₄ j x := fun a x => by
    rw [← ConcreteCategory.comp_apply, hψ₄]
  exact of_forall_exists hT₃ hψ₃ (exists_eq_of_exact u v w u' v' w' hw e₃ e₄ hu' hv' hw' hexA₄
    hexB₃ hexB₄ (h₂.exists_eq hT₂ hψ₂) (h₄.exists_eq hT₄ hψ₄) hinj₅)
    (exists_eq_zero_of_exact hT₃ t u v t' u' v' ht hu hv e₂ e₃ ht' hu' hv' hexA₂ hexA₃ hexB₂
      hsurj₁ (fun _ x hx => h₂.exists_eq_zero hT₂ hψ₂ x hx)
      (fun _ x hx => h₄.exists_eq_zero hT₄ hψ₄ x hx))

end IsSystemColimit

end CategoryTheory.Limits
