module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Ideal
public import Mathlib.Data.NNRat.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.Category.Ring.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanRepresentableSystem

/-!
# A quasi-coherent system over a McQuillan base whose limit does not surject

Let `(Vᵢ)` be an inverse system of vector spaces over a field `K`, indexed by a directed set
`I`, with surjective transition maps `qᵢⱼ : Vᵢ → Vⱼ` for `j ≤ i`. This file builds a ring `P`,
ideals `𝔍ᵢ ⊆ P` decreasing along `I` and nil modulo one another, and modules `Mᵢ` over
`Aᵢ = P/𝔍ᵢ` with surjective transition maps `Mᵢ → Mⱼ` whose kernel is exactly `𝔍ⱼ Mᵢ`, together
with compatible surjections `Mᵢ → Vᵢ`. The trivial square-zero extensions `Rᵢ = Aᵢ ⊕ Mᵢ` then
satisfy `Rⱼ = Rᵢ ⊗_{Aᵢ} Aⱼ`, while their inverse limit maps onto `Vᵢ` through `lim Vᵢ`. This is
the algebra behind Stacks 0CBE: when `lim Vᵢ = 0` the projections `lim Rᵢ → Rᵢ` are not
surjective, whereas every `Aᵢ` is a quotient of the one ring `P`.

The construction differs from the iteration sketched in the source, which adjoins square-zero
variables one kernel element at a time and is shown in
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemEnlargement` not to close up. Here
the variables are given *rational* exponents: `P` is spanned by the monomials `t^a` with
`a : I →₀ ℚ≥0`, and `𝔍ᵢ` is spanned by the monomials having an exponent `≥ 1` somewhere or a
positive exponent at some index `l ≥ i`. The ideal `𝔍ᵢ / 𝔍ₖ` is then nil but idempotent, which
is what lets a kernel element be divided by a variable inside the kernel itself. The module
`Mᵢ` consists of the finitely supported families `(v_c)` indexed by exponents
`c : I →₀ ℚ` with `-1 < c_l ≤ 0`, where `v_c` lies in the subspace `Uᵢ(supp c)` of `Vᵢ`; the
monomial `t^a` sends the term at `c` to the term at `c + a`, or to zero when `c + a` leaves the
box. The subspace `Uᵢ(F)` consists of the vectors of `Vᵢ` which lift to a stage above `F` by an
element killed in every `V_l`, `l ∈ F`.

## Main definitions

* `Stacks.FractionalSystem.SurjSystem`: an inverse system of types with surjective maps.
* `Stacks.FractionalSystem.U`: the subspaces `Uᵢ(F)`.
* `Stacks.FractionalSystem.P`, `Stacks.FractionalSystem.ideal`: the ring `P` and the ideals `𝔍ᵢ`.
* `Stacks.FractionalSystem.M`: the modules `Mᵢ`, and `Stacks.FractionalSystem.Mmap` their
  transition maps.

## Main results

* `Stacks.FractionalSystem.ker_Mmap`: the kernel of `Mᵢ → Mⱼ` is `𝔍ⱼ Mᵢ`.
* `Stacks.FractionalSystem.surjective_Mmap`: the transition maps are surjective.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public noncomputable section

namespace Stacks.FractionalSystem

open AddMonoidAlgebra

universe u

/-- An inverse system of types indexed by a preorder, with surjective transition maps. -/
structure SurjSystem (I : Type u) [Preorder I] where
  /-- The stage over an index. -/
  obj : I → Type u
  /-- The transition map from a larger index to a smaller one. -/
  map : ∀ {i j : I}, j ≤ i → obj i → obj j
  map_refl : ∀ (i : I) (x : obj i), map le_rfl x = x
  map_map : ∀ {i j k : I} (hjk : k ≤ j) (hij : j ≤ i) (x : obj i),
    map hjk (map hij x) = map (hjk.trans hij) x
  surjective_map : ∀ {i j : I} (h : j ≤ i), Function.Surjective (map h)

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (Sy : SurjSystem I)
variable (K : Type u) [Field K]

/-! ### The vector spaces `Vᵢ` and the subspaces `Uᵢ(F)` -/

/-- The vector space `Vᵢ`, free on the stage `Sᵢ`. -/
abbrev V (i : I) : Type u := Sy.obj i →₀ K

/-- The transition map `Vᵢ → Vⱼ`. -/
def q {i j : I} (h : j ≤ i) : V Sy K i →ₗ[K] V Sy K j :=
  Finsupp.lmapDomain K K (Sy.map h)

omit [IsDirected I (· ≤ ·)] in
/-- The transition maps `qᵢⱼ` compose: `qⱼₖ ∘ qᵢⱼ = qᵢₖ`. -/
theorem q_q {i j k : I} (hjk : k ≤ j) (hij : j ≤ i) (v : V Sy K i) :
    q Sy K hjk (q Sy K hij v) = q Sy K (hjk.trans hij) v := by
  simp only [q, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x
  exact Sy.map_map hjk hij x

omit [IsDirected I (· ≤ ·)] in
/-- The transition map `qᵢᵢ` is the identity. -/
theorem q_refl (i : I) (v : V Sy K i) : q Sy K (le_refl i) v = v := by
  simp only [q, Finsupp.lmapDomain_apply]
  have : Sy.map (le_refl i) = id := funext (Sy.map_refl i)
  rw [this, Finsupp.mapDomain_id]

omit [IsDirected I (· ≤ ·)] in
/-- The transition maps `qᵢⱼ : Vᵢ → Vⱼ` are surjective. -/
theorem surjective_q {i j : I} (h : j ≤ i) : Function.Surjective (q Sy K h) :=
  Finsupp.mapDomain_surjective (Sy.surjective_map h)

/-- A finite set of indices together with one more index has an upper bound. -/
theorem exists_upper (i : I) (F : Finset I) : ∃ k, i ≤ k ∧ ∀ l ∈ F, l ≤ k := by
  classical
  have : Nonempty I := ⟨i⟩
  obtain ⟨k, hk⟩ := (insert i F).exists_le
  exact ⟨k, hk i (Finset.mem_insert_self _ _), fun l hl => hk l (Finset.mem_insert_of_mem hl)⟩

/-- The predicate defining `Uᵢ(F)` at a fixed stage `k` above `i` and `F`. -/
def IsLiftAt (i : I) (F : Finset I) (k : I) (hik : i ≤ k) (hF : ∀ l ∈ F, l ≤ k)
    (v : V Sy K i) : Prop :=
  ∃ w : V Sy K k, q Sy K hik w = v ∧ ∀ l (hl : l ∈ F), q Sy K (hF l hl) w = 0

omit [IsDirected I (· ≤ ·)] in
/-- Lifting a witness of `IsLiftAt` to a higher stage. -/
theorem IsLiftAt.mono {i : I} {F : Finset I} {k k' : I} {hik : i ≤ k} {hF : ∀ l ∈ F, l ≤ k}
    (hkk' : k ≤ k') {v : V Sy K i} (h : IsLiftAt Sy K i F k hik hF v) :
    IsLiftAt Sy K i F k' (hik.trans hkk') (fun l hl => (hF l hl).trans hkk') v := by
  obtain ⟨w, hw, hwF⟩ := h
  obtain ⟨w', hw'⟩ := surjective_q Sy K hkk' w
  refine ⟨w', ?_, fun l hl => ?_⟩
  · rw [← q_q Sy K hik hkk', hw', hw]
  · rw [← q_q Sy K (hF l hl) hkk', hw', hwF l hl]

omit [IsDirected I (· ≤ ·)] in
/-- Pushing a witness of `IsLiftAt` down to a lower stage. -/
theorem IsLiftAt.down {i : I} {F : Finset I} {k k' : I} {hik' : i ≤ k'}
    {hF' : ∀ l ∈ F, l ≤ k'} (hik : i ≤ k) (hF : ∀ l ∈ F, l ≤ k) (hkk' : k ≤ k')
    {v : V Sy K i} (h : IsLiftAt Sy K i F k' hik' hF' v) : IsLiftAt Sy K i F k hik hF v := by
  obtain ⟨w, hw, hwF⟩ := h
  refine ⟨q Sy K hkk' w, ?_, fun l hl => ?_⟩
  · rw [q_q, hw]
  · rw [q_q, hwF l hl]

/-- The witnesses of `IsLiftAt` at any two admissible stages correspond. -/
theorem isLiftAt_iff {i : I} {F : Finset I} {k k' : I} (hik : i ≤ k) (hF : ∀ l ∈ F, l ≤ k)
    (hik' : i ≤ k') (hF' : ∀ l ∈ F, l ≤ k') (v : V Sy K i) :
    IsLiftAt Sy K i F k hik hF v ↔ IsLiftAt Sy K i F k' hik' hF' v := by
  obtain ⟨k'', hk, hk'⟩ := directed_of (· ≤ ·) k k'
  exact ⟨fun h => (h.mono Sy K hk).down Sy K hik' hF' hk',
    fun h => (h.mono Sy K hk').down Sy K hik hF hk⟩

/-- The subspace `Uᵢ(F) ⊆ Vᵢ` of the vectors which lift, to a stage `k` above `i` and every
member of `F`, by an element of `V_k` killed in `V_l` for every `l ∈ F`. It does not depend on
the stage `k` (`Stacks.FractionalSystem.isLiftAt_iff`). -/
def U (i : I) (F : Finset I) : Submodule K (V Sy K i) where
  carrier := {v | IsLiftAt Sy K i F (exists_upper i F).choose (exists_upper i F).choose_spec.1
    (exists_upper i F).choose_spec.2 v}
  add_mem' := by
    rintro v v' ⟨w, hw, hwF⟩ ⟨w', hw', hwF'⟩
    refine ⟨w + w', by rw [map_add, hw, hw'], fun l hl => ?_⟩
    rw [map_add, hwF l hl, hwF' l hl, add_zero]
  zero_mem' := ⟨0, map_zero _, fun _ _ => map_zero _⟩
  smul_mem' := by
    rintro a v ⟨w, hw, hwF⟩
    refine ⟨a • w, by rw [map_smul, hw], fun l hl => ?_⟩
    rw [map_smul, hwF l hl, smul_zero]

/-- Membership in `Uᵢ(F)` may be tested at any stage `k` above `i` and every member of `F`. -/
theorem mem_U_iff {i : I} {F : Finset I} {k : I} (hik : i ≤ k) (hF : ∀ l ∈ F, l ≤ k)
    (v : V Sy K i) : v ∈ U Sy K i F ↔ IsLiftAt Sy K i F k hik hF v :=
  isLiftAt_iff Sy K _ _ hik hF v

/-- `Uᵢ(F)` is antitone in `F`: `F ⊆ F'` implies `Uᵢ(F') ≤ Uᵢ(F)`. -/
theorem U_anti {i : I} {F F' : Finset I} (h : F ⊆ F') : U Sy K i F' ≤ U Sy K i F := by
  intro v hv
  obtain ⟨k, hik, hF'⟩ := exists_upper i F'
  rw [mem_U_iff Sy K hik hF'] at hv
  rw [mem_U_iff Sy K hik (fun l hl => hF' l (h hl))]
  obtain ⟨w, hw, hwF⟩ := hv
  exact ⟨w, hw, fun l hl => hwF l (h hl)⟩

/-- `Uᵢ(∅)` is all of `Vᵢ`. -/
theorem U_empty (i : I) : U Sy K i ∅ = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  rw [mem_U_iff Sy K (le_refl i) (by simp)]
  exact ⟨v, q_refl Sy K i v, by simp⟩

/-- `Uᵢ(F)` is zero when `F` contains an index `l ≥ i`. -/
theorem U_eq_bot {i : I} {F : Finset I} {l : I} (hl : l ∈ F) (hil : i ≤ l) :
    U Sy K i F = ⊥ := by
  refine eq_bot_iff.mpr fun v hv => ?_
  obtain ⟨k, hik, hF⟩ := exists_upper i F
  rw [mem_U_iff Sy K hik hF] at hv
  obtain ⟨w, hw, hwF⟩ := hv
  rw [Submodule.mem_bot, ← hw, ← q_q Sy K hil (hF l hl), hwF l hl, map_zero]

/-- The image of `Uᵢ(F)` under `qᵢⱼ` is `Uⱼ(F)`. -/
theorem map_U {i j : I} (h : j ≤ i) (F : Finset I) :
    (U Sy K i F).map (q Sy K h) = U Sy K j F := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨k, hik, hF⟩ := exists_upper i F
    rw [SetLike.mem_coe, mem_U_iff Sy K hik hF] at hv
    rw [mem_U_iff Sy K (h.trans hik) hF]
    obtain ⟨w, hw, hwF⟩ := hv
    exact ⟨w, by rw [← q_q Sy K h hik, hw], hwF⟩
  · intro v' hv'
    obtain ⟨k, hik, hF⟩ := exists_upper i F
    rw [mem_U_iff Sy K (h.trans hik) hF] at hv'
    obtain ⟨w, hw, hwF⟩ := hv'
    refine ⟨q Sy K hik w, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_U_iff Sy K hik hF]
      exact ⟨w, rfl, hwF⟩
    · rw [q_q, hw]

open scoped Classical in
/-- A vector of `Uᵢ(F)` killed by `qᵢⱼ` lies in `Uᵢ(F ∪ {j})`. -/
theorem mem_U_insert {i j : I} (h : j ≤ i) {F : Finset I} {v : V Sy K i}
    (hv : v ∈ U Sy K i F) (hq : q Sy K h v = 0) : v ∈ U Sy K i (insert j F) := by
  obtain ⟨k, hik, hF⟩ := exists_upper i F
  rw [mem_U_iff Sy K hik hF] at hv
  have hF' : ∀ l ∈ insert j F, l ≤ k := by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact h.trans hik
    · exact hF l hl
  rw [mem_U_iff Sy K hik hF']
  obtain ⟨w, hw, hwF⟩ := hv
  refine ⟨w, hw, fun l hl => ?_⟩
  rcases Finset.mem_insert.mp hl with rfl | hl
  · rw [← q_q Sy K h hik, hw, hq]
  · exact hwF l hl


/-! ### The modules `Mᵢ` -/

/-- The exponents indexing the terms of the modules: `c : I →₀ ℚ` with `-1 < c_l ≤ 0` for
every `l`. -/
def Box (c : I →₀ ℚ) : Prop := ∀ l, -1 < c l ∧ c l ≤ 0

omit [Preorder I] [IsDirected I (· ≤ ·)] in
/-- The zero exponent lies in the box. -/
theorem box_zero : Box (0 : I →₀ ℚ) := fun l => by simp

open scoped Classical in
/-- The subspace of `Vᵢ` allowed as the coefficient of the term at the exponent `c`. -/
def W (i : I) (c : I →₀ ℚ) : Submodule K (V Sy K i) :=
  if Box c then U Sy K i c.support else ⊥

/-- On the box, the coefficient space at `c` is `Uᵢ(supp c)`. -/
theorem W_of_box {i : I} {c : I →₀ ℚ} (hc : Box c) : W Sy K i c = U Sy K i c.support := by
  simp [W, hc]

/-- Off the box, the coefficient space at `c` is zero. -/
theorem W_of_not_box {i : I} {c : I →₀ ℚ} (hc : ¬ Box c) : W Sy K i c = ⊥ := by
  simp [W, hc]

/-- The module `Mᵢ`: the finitely supported families of vectors of `Vᵢ` indexed by the
exponents `c`, whose term at `c` vanishes off the box and lies in `Uᵢ(supp c)` on it. -/
def M (i : I) : Submodule K ((I →₀ ℚ) →₀ V Sy K i) where
  carrier := {m | ∀ c, m c ∈ W Sy K i c}
  add_mem' := by
    intro m m' hm hm' c
    exact (W Sy K i c).add_mem (hm c) (hm' c)
  zero_mem' := fun c => (W Sy K i c).zero_mem
  smul_mem' := by
    intro a m hm c
    exact (W Sy K i c).smul_mem a (hm c)

/-- An element of `Mᵢ` has nonzero terms only at exponents in the box. -/
theorem box_of_mem_M {i : I} {m : (I →₀ ℚ) →₀ V Sy K i} (hm : m ∈ M Sy K i) {c : I →₀ ℚ}
    (hc : m c ≠ 0) : Box c := by
  by_contra h
  have := hm c
  rw [W_of_not_box Sy K h, Submodule.mem_bot] at this
  exact hc this

/-- A single term `v t^c` with `c` in the box and `v ∈ Uᵢ(supp c)` lies in `Mᵢ`. -/
theorem single_mem_M {i : I} {c : I →₀ ℚ} (hc : Box c) {v : V Sy K i}
    (hv : v ∈ U Sy K i c.support) : Finsupp.single c v ∈ M Sy K i := by
  classical
  intro d
  by_cases hd : c = d
  · subst hd
    rw [Finsupp.single_eq_same, W_of_box Sy K hc]
    exact hv
  · rw [Finsupp.single_apply, ite_eq_right hd]
    exact Submodule.zero_mem _

/-! ### The action of the monomials -/

open scoped Classical in
/-- The ambient shift by an exponent `a`: the term at `c` moves to `c + a`, and terms leaving
the box are dropped. -/
def shiftAmb (i : I) (a : I →₀ ℚ) :
    ((I →₀ ℚ) →₀ V Sy K i) →ₗ[K] ((I →₀ ℚ) →₀ V Sy K i) where
  toFun m := (Finsupp.mapDomain (· + a) m).filter Box
  map_add' m m' := by rw [Finsupp.mapDomain_add, Finsupp.filter_add]
  map_smul' r m := by
    rw [Finsupp.mapDomain_smul, Finsupp.filter_smul, RingHom.id_apply]

omit [IsDirected I (· ≤ ·)] in
open scoped Classical in
/-- The term of the shift by `a` at `c` is the term at `c - a` if `c` is in the box, and zero
otherwise. -/
theorem shiftAmb_apply (i : I) (a : I →₀ ℚ) (m : (I →₀ ℚ) →₀ V Sy K i) (c : I →₀ ℚ) :
    shiftAmb Sy K i a m c = if Box c then m (c - a) else 0 := by
  change ((Finsupp.mapDomain (· + a) m).filter Box) c = _
  rw [Finsupp.filter_apply]
  congr 1
  have h : c = (c - a) + a := (sub_add_cancel c a).symm
  conv_lhs => rw [h]
  exact Finsupp.mapDomain_apply_of_injective (add_left_injective a) m (c - a)

/-- A nonnegative exponent. -/
abbrev Nonneg (a : I →₀ ℚ) : Prop := ∀ l, 0 ≤ a l

/-- The shift by a nonnegative exponent maps `Mᵢ` into itself. -/
theorem shiftAmb_mem {i : I} {a : I →₀ ℚ} (ha : Nonneg a) {m : (I →₀ ℚ) →₀ V Sy K i}
    (hm : m ∈ M Sy K i) : shiftAmb Sy K i a m ∈ M Sy K i := by
  intro c
  rw [shiftAmb_apply]
  split_ifs with hc
  · by_cases hmc : m (c - a) = 0
    · rw [hmc]
      exact Submodule.zero_mem _
    · have hb := box_of_mem_M Sy K hm hmc
      have h := hm (c - a)
      rw [W_of_box Sy K hb] at h
      rw [W_of_box Sy K hc]
      refine U_anti Sy K (fun l hl => ?_) h
      rw [Finsupp.mem_support_iff] at hl ⊢
      rw [Finsupp.sub_apply]
      intro h3
      linarith [lt_of_le_of_ne (hc l).2 hl, ha l]
  · exact Submodule.zero_mem _

/-- The shift by a nonnegative exponent, as an endomorphism of `Mᵢ`. -/
def shift (i : I) (a : I →₀ ℚ) (ha : Nonneg a) : M Sy K i →ₗ[K] M Sy K i :=
  (shiftAmb Sy K i a).restrict (fun _ hm => shiftAmb_mem Sy K ha hm)

/-- The underlying family of `shift a m` is the ambient shift of `m`. -/
theorem shift_apply_coe (i : I) (a : I →₀ ℚ) (ha : Nonneg a) (m : M Sy K i) :
    (shift Sy K i a ha m : (I →₀ ℚ) →₀ V Sy K i) = shiftAmb Sy K i a m := rfl

/-- The shift by the zero exponent is the identity of `Mᵢ`. -/
theorem shift_zero (i : I) : shift Sy K i 0 (fun _ => le_refl _) = LinearMap.id := by
  refine LinearMap.ext fun m => Subtype.ext (Finsupp.ext fun c => ?_)
  rw [shift_apply_coe, shiftAmb_apply, sub_zero, LinearMap.id_apply]
  split_ifs with hc
  · rfl
  · by_contra h
    exact hc (box_of_mem_M Sy K m.2 (Ne.symm h))

/-- The shift by `a + b` is the composite of the shifts by `a` and by `b`. -/
theorem shift_add (i : I) {a b : I →₀ ℚ} (ha : Nonneg a) (hb : Nonneg b) :
    shift Sy K i (a + b) (fun l => by simpa using add_nonneg (ha l) (hb l)) =
      shift Sy K i a ha ∘ₗ shift Sy K i b hb := by
  refine LinearMap.ext fun m => Subtype.ext (Finsupp.ext fun c => ?_)
  rw [LinearMap.comp_apply, shift_apply_coe, shift_apply_coe, shift_apply_coe,
    shiftAmb_apply, shiftAmb_apply, shiftAmb_apply]
  split_ifs with hc hca
  · rw [sub_sub, add_comm a b]
  · by_contra h
    refine hca fun l => ?_
    have h1 := (box_of_mem_M Sy K m.2 h l).1
    simp only [Finsupp.sub_apply, Finsupp.add_apply] at h1 ⊢
    constructor <;> linarith [(hc l).2, ha l, hb l]
  · rfl

/-! ### The ring `P` and its action -/

/-- The exponent monoid of the ring `P`. -/
abbrev G (I : Type u) : Type u := I →₀ ℚ≥0

/-- The ring `P`, spanned by the monomials `t^a`, `a : I →₀ ℚ≥0`. -/
abbrev P (I : Type u) : Type u := AddMonoidAlgebra K (G I)

/-- An exponent of `P` viewed as a rational exponent. -/
def toRat (a : G I) : I →₀ ℚ := Finsupp.mapRange (↑) NNRat.coe_zero a

omit [Preorder I] [IsDirected I (· ≤ ·)] in
/-- The value of `toRat a` at `l` is `a l` viewed in `ℚ`. -/
theorem toRat_apply (a : G I) (l : I) : toRat a l = (a l : ℚ) := rfl

omit [Preorder I] [IsDirected I (· ≤ ·)] in
/-- `toRat` is additive. -/
theorem toRat_add (a b : G I) : toRat (a + b) = toRat a + toRat b := by
  ext l
  simp [toRat_apply]

omit [Preorder I] [IsDirected I (· ≤ ·)] in
/-- `toRat` sends the zero exponent to zero. -/
theorem toRat_zero : toRat (0 : G I) = 0 := by
  ext l
  simp [toRat_apply]

omit [Preorder I] [IsDirected I (· ≤ ·)] in
/-- An exponent of `P` is a nonnegative rational exponent. -/
theorem nonneg_toRat (a : G I) : Nonneg (toRat a) := fun l => by
  rw [toRat_apply]
  exact NNRat.coe_nonneg _

/-- The monomials acting on `Mᵢ` by shifting. -/
def shiftHom (i : I) : Multiplicative (G I) →* Module.End K (M Sy K i) where
  toFun a := shift Sy K i (toRat a.toAdd) (nonneg_toRat _)
  map_one' := by
    change shift Sy K i (toRat 0) _ = 1
    simp only [toRat_zero]
    exact shift_zero Sy K i
  map_mul' a b := by
    change shift Sy K i (toRat (a.toAdd + b.toAdd)) _ =
      shift Sy K i (toRat a.toAdd) _ ∘ₗ shift Sy K i (toRat b.toAdd) _
    simp only [toRat_add]
    exact shift_add Sy K i (nonneg_toRat _) (nonneg_toRat _)

/-- The action of `P` on `Mᵢ`. -/
def act (i : I) : P K I →ₐ[K] Module.End K (M Sy K i) :=
  AddMonoidAlgebra.lift K (Module.End K (M Sy K i)) (G I) (shiftHom Sy K i)

/-- `Mᵢ` is a `P`-module through `Stacks.FractionalSystem.act`. -/
instance (i : I) : Module (P K I) (M Sy K i) := Module.compHom _ (act Sy K i).toRingHom

/-- The scalar action of `x : P` on `Mᵢ` is `act i x`. -/
theorem smul_def (i : I) (x : P K I) (m : M Sy K i) : x • m = act Sy K i x m := rfl

/-- The monomial `t^a` acts on `Mᵢ` as the shift by `a`. -/
theorem single_smul (i : I) (a : G I) (m : M Sy K i) :
    (AddMonoidAlgebra.single a (1 : K) : P K I) • m =
      shift Sy K i (toRat a) (nonneg_toRat a) m := by
  rw [smul_def, act, AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-! ### The ideals `𝔍ᵢ` and the rings `Aᵢ = P/𝔍ᵢ` -/

/-- The exponents of the monomials generating `𝔍ᵢ`: an exponent `≥ 1` somewhere, or a positive
exponent at an index `l ≥ i`. -/
def gens (i : I) : Set (G I) := {a | (∃ l, 1 ≤ a l) ∨ (∃ l, i ≤ l ∧ 0 < a l)}

/-- The ideal `𝔍ᵢ ⊆ P`, spanned by the monomials with exponent in `gens i`. -/
def ideal (i : I) : Ideal (P K I) := Ideal.span (AddMonoidAlgebra.of' K (G I) '' gens i)

omit [IsDirected I (· ≤ ·)] in
/-- The monomial `t^a` with `a ∈ gens i` lies in `𝔍ᵢ`. -/
theorem of'_mem_ideal {i : I} {a : G I} (ha : a ∈ gens i) :
    AddMonoidAlgebra.of' K (G I) a ∈ ideal K i :=
  Ideal.subset_span ⟨a, ha, rfl⟩

omit [IsDirected I (· ≤ ·)] in
/-- The ideals decrease along `I`: `𝔍ᵢ ≤ 𝔍ⱼ` for `j ≤ i`. -/
theorem ideal_anti {i j : I} (h : j ≤ i) : ideal K i ≤ ideal K j := by
  apply Ideal.span_mono
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨a, ?_, rfl⟩
  rcases ha with ha | ⟨l, hl, ha⟩
  · exact Or.inl ha
  · exact Or.inr ⟨l, h.trans hl, ha⟩

/-- The shift by an exponent in `gens i` is zero on `Mᵢ`. -/
theorem shift_eq_zero_of_mem_gens {i : I} {a : G I} (ha : a ∈ gens i) (m : M Sy K i) :
    shift Sy K i (toRat a) (nonneg_toRat a) m = 0 := by
  refine Subtype.ext (Finsupp.ext fun c => ?_)
  rw [shift_apply_coe, shiftAmb_apply, Submodule.coe_zero, Finsupp.zero_apply]
  split_ifs with hc
  · by_contra h
    have hb := box_of_mem_M Sy K m.2 h
    rcases ha with ⟨l, hl⟩ | ⟨l, hil, hl⟩
    · have h1 := (hb l).1
      have h2 := (hc l).2
      have h3 : (1 : ℚ) ≤ a l := by exact_mod_cast hl
      simp only [Finsupp.sub_apply, toRat_apply] at h1
      linarith
    · have hmem := m.2 (c - toRat a)
      have hl' : l ∈ (c - toRat a).support := by
        rw [Finsupp.mem_support_iff, Finsupp.sub_apply, toRat_apply]
        have h2 := (hc l).2
        have h3 : (0 : ℚ) < a l := by exact_mod_cast hl
        intro h0
        linarith
      rw [W_of_box Sy K hb, U_eq_bot Sy K hl' hil, Submodule.mem_bot] at hmem
      exact h hmem
  · rfl

/-- `𝔍ᵢ` acts trivially on `Mᵢ`. -/
theorem isTorsionBySet (i : I) : Module.IsTorsionBySet (P K I) (M Sy K i) (ideal K i) := by
  rw [ideal, ← Module.isTorsionBySet_iff_is_torsion_by_span]
  rintro m ⟨_, a, ha, rfl⟩
  change (AddMonoidAlgebra.single a (1 : K) : P K I) • m = 0
  rw [single_smul]
  exact shift_eq_zero_of_mem_gens Sy K ha m

/-- The stage ring `Aᵢ = P/𝔍ᵢ`. -/
abbrev A (i : I) : Type u := P K I ⧸ ideal K i

/-- `Mᵢ` is an `Aᵢ`-module, since `𝔍ᵢ` acts trivially on it. -/
instance (i : I) : Module (A K i) (M Sy K i) := (isTorsionBySet Sy K i).module

/-- The right action of `Aᵢ` on `Mᵢ`, equal to the left action. -/
instance (i : I) : Module (A K i)ᵐᵒᵖ (M Sy K i) :=
  Module.compHom _ ((RingEquiv.toOpposite (A K i)).symm.toRingHom)

/-- The left and right actions of `Aᵢ` on `Mᵢ` agree. -/
instance (i : I) : IsCentralScalar (A K i) (M Sy K i) := ⟨fun _ _ => rfl⟩

/-- The class of `x : P` in `Aᵢ` acts on `Mᵢ` as `x` does. -/
theorem mk_smul (i : I) (x : P K I) (m : M Sy K i) :
    (Ideal.Quotient.mk (ideal K i) x : A K i) • m = x • m := rfl

/-- The transition map `Aᵢ → Aⱼ`. -/
def Amap {i j : I} (h : j ≤ i) : A K i →+* A K j := Ideal.Quotient.factor (ideal_anti K h)

omit [IsDirected I (· ≤ ·)] in
/-- The map `Aᵢ → Aⱼ` sends the class of `x : P` to the class of `x`. -/
theorem Amap_mk {i j : I} (h : j ≤ i) (x : P K I) :
    Amap K h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
  Ideal.Quotient.factor_mk _ _

omit [IsDirected I (· ≤ ·)] in
/-- The transition maps `Aᵢ → Aⱼ` are surjective. -/
theorem surjective_Amap {i j : I} (h : j ≤ i) : Function.Surjective (Amap K h) :=
  Ideal.Quotient.factor_surjective _

omit [IsDirected I (· ≤ ·)] in
/-- The kernel of `Aᵢ → Aⱼ` is nil: `𝔍ⱼ` lies in the radical of `𝔍ᵢ`. -/
theorem isNilpotent_of_mem_ker_Amap {i j : I} (h : j ≤ i) {x : A K i}
    (hx : x ∈ RingHom.ker (Amap K h)) : IsNilpotent x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Amap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  have hle : ideal K j ≤ (ideal K i).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    rcases ha with ha | ⟨l, _, hl⟩
    · exact Ideal.le_radical (of'_mem_ideal K (Or.inl ha))
    · obtain ⟨n, hn⟩ := exists_nat_ge (1 / (a l : ℚ))
      refine ⟨n, ?_⟩
      rw [AddMonoidAlgebra.of'_apply, AddMonoidAlgebra.single_pow, one_pow]
      refine of'_mem_ideal K (Or.inl ⟨l, ?_⟩)
      have hpos : (0 : ℚ) < a l := by exact_mod_cast hl
      rw [div_le_iff₀ hpos] at hn
      rw [Finsupp.smul_apply, nsmul_eq_mul]
      exact_mod_cast hn
  obtain ⟨n, hn⟩ := hle hx
  exact ⟨n, by rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem]⟩

/-! ### The transition maps of the modules -/

/-- The ambient transition map, applying `qᵢⱼ` to every coefficient. -/
def MmapAmb {i j : I} (h : j ≤ i) :
    ((I →₀ ℚ) →₀ V Sy K i) →ₗ[K] ((I →₀ ℚ) →₀ V Sy K j) :=
  Finsupp.mapRange.linearMap (q Sy K h)

omit [IsDirected I (· ≤ ·)] in
/-- The ambient transition map applies `qᵢⱼ` to the term at each exponent `c`. -/
theorem MmapAmb_apply {i j : I} (h : j ≤ i) (m : (I →₀ ℚ) →₀ V Sy K i) (c : I →₀ ℚ) :
    MmapAmb Sy K h m c = q Sy K h (m c) := rfl

/-- The image of the coefficient space at `c` under `qᵢⱼ` is the coefficient space at `c`. -/
private theorem map_W {i j : I} (h : j ≤ i) (c : I →₀ ℚ) :
    (W Sy K i c).map (q Sy K h) = W Sy K j c := by
  by_cases hc : Box c
  · rw [W_of_box Sy K hc, W_of_box Sy K hc, map_U]
  · rw [W_of_not_box Sy K hc, W_of_not_box Sy K hc, Submodule.map_bot]

/-- The ambient transition map sends `Mᵢ` into `Mⱼ`. -/
theorem MmapAmb_mem {i j : I} (h : j ≤ i) {m : (I →₀ ℚ) →₀ V Sy K i} (hm : m ∈ M Sy K i) :
    MmapAmb Sy K h m ∈ M Sy K j := by
  intro c
  rw [MmapAmb_apply, ← map_W Sy K h]
  exact ⟨m c, hm c, rfl⟩

/-- The transition map `Mᵢ → Mⱼ`. -/
def Mmap {i j : I} (h : j ≤ i) : M Sy K i →ₗ[K] M Sy K j :=
  (MmapAmb Sy K h).restrict (fun _ hm => MmapAmb_mem Sy K h hm)

/-- The underlying family of `Mmap h m` is the ambient transition map applied to `m`. -/
theorem Mmap_apply_coe {i j : I} (h : j ≤ i) (m : M Sy K i) :
    (Mmap Sy K h m : (I →₀ ℚ) →₀ V Sy K j) = MmapAmb Sy K h m := rfl

/-- The transition map `Mᵢ → Mⱼ` commutes with the shifts. -/
theorem Mmap_shift {i j : I} (h : j ≤ i) (a : I →₀ ℚ) (ha : Nonneg a) (m : M Sy K i) :
    Mmap Sy K h (shift Sy K i a ha m) = shift Sy K j a ha (Mmap Sy K h m) := by
  refine Subtype.ext (Finsupp.ext fun c => ?_)
  rw [Mmap_apply_coe, shift_apply_coe, shift_apply_coe, MmapAmb_apply, shiftAmb_apply,
    shiftAmb_apply, Mmap_apply_coe, MmapAmb_apply]
  split_ifs
  · rfl
  · exact map_zero _

/-- The transition map `Mᵢ → Mⱼ` is `P`-linear. -/
theorem Mmap_smul {i j : I} (h : j ≤ i) (x : P K I) (m : M Sy K i) :
    Mmap Sy K h (x • m) = x • Mmap Sy K h m := by
  induction x using AddMonoidAlgebra.induction_on with
  | of g =>
    rw [AddMonoidAlgebra.of_apply, single_smul, single_smul, Mmap_shift]
  | add x y hx hy => rw [add_smul, add_smul, map_add, hx, hy]
  | smul r x hx =>
    rw [smul_def, smul_def, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      map_smul, ← smul_def, ← smul_def, hx]

/-- The transition map `Mᵢ → Mⱼ` is semilinear over `Aᵢ → Aⱼ`. -/
theorem Mmap_smul_A {i j : I} (h : j ≤ i) (a : A K i) (m : M Sy K i) :
    Mmap Sy K h (a • m) = Amap K h a • Mmap Sy K h m := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mk_smul, Amap_mk, mk_smul, Mmap_smul]

/-- The transition map `Mᵢ → Mᵢ` is the identity. -/
theorem Mmap_refl (i : I) (m : M Sy K i) : Mmap Sy K (le_refl i) m = m := by
  refine Subtype.ext (Finsupp.ext fun c => ?_)
  rw [Mmap_apply_coe, MmapAmb_apply, q_refl]

/-- The transition maps of the modules compose: `Mⱼ → Mₖ` after `Mᵢ → Mⱼ` is `Mᵢ → Mₖ`. -/
theorem Mmap_Mmap {i j k : I} (hjk : k ≤ j) (hij : j ≤ i) (m : M Sy K i) :
    Mmap Sy K hjk (Mmap Sy K hij m) = Mmap Sy K (hjk.trans hij) m := by
  refine Subtype.ext (Finsupp.ext fun c => ?_)
  rw [Mmap_apply_coe, MmapAmb_apply, Mmap_apply_coe, MmapAmb_apply, Mmap_apply_coe,
    MmapAmb_apply, q_q]

open scoped Classical in
/-- The transition maps `Mᵢ → Mⱼ` are surjective. -/
theorem surjective_Mmap {i j : I} (h : j ≤ i) : Function.Surjective (Mmap Sy K h) := by
  intro n
  have hlift : ∀ c, ∃ v ∈ W Sy K i c, q Sy K h v = (n : (I →₀ ℚ) →₀ V Sy K j) c := by
    intro c
    have h1 := n.2 c
    rw [← map_W Sy K h] at h1
    exact h1
  choose pre hpre hqpre using hlift
  let pre' : (I →₀ ℚ) → V Sy K i := fun c =>
    if (n : (I →₀ ℚ) →₀ V Sy K j) c = 0 then 0 else pre c
  let m : (I →₀ ℚ) →₀ V Sy K i :=
    Finsupp.onFinset (n : (I →₀ ℚ) →₀ V Sy K j).support pre' (by
      intro c hc
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hc (by simp [pre', h0]))
  have hm : m ∈ M Sy K i := by
    intro c
    change pre' c ∈ W Sy K i c
    by_cases h0 : (n : (I →₀ ℚ) →₀ V Sy K j) c = 0
    · simp [pre', h0]
    · simpa [pre', h0] using hpre c
  refine ⟨⟨m, hm⟩, Subtype.ext (Finsupp.ext fun c => ?_)⟩
  rw [Mmap_apply_coe, MmapAmb_apply]
  change q Sy K h (pre' c) = _
  by_cases h0 : (n : (I →₀ ℚ) →₀ V Sy K j) c = 0
  · simp only [pre', h0, ite_true, map_zero]
  · simpa [pre', h0] using hqpre c

/-- **The representability identity.** The kernel of `Mᵢ → Mⱼ` is `𝔍ⱼ Mᵢ`, that is the
submodule generated by the kernel of `Aᵢ → Aⱼ`. A term `v t^c` of the kernel is divided by the
monomial `t_j^ε`, `ε = (1 + c_j)/2`, inside `Mᵢ`: the quotient `v t^{c - ε e_j}` is again a term
of `Mᵢ` because `v` dies in `Vⱼ`. -/
theorem Mmap_eq_zero_iff {i j : I} (h : j ≤ i) (m : M Sy K i) :
    Mmap Sy K h m = 0 ↔
      m ∈ (RingHom.ker (Amap K h)) • (⊤ : Submodule (A K i) (M Sy K i)) := by
  classical
  constructor
  · intro hm
    have hq : ∀ c, q Sy K h ((m : (I →₀ ℚ) →₀ V Sy K i) c) = 0 := by
      intro c
      have := congrArg (fun n : M Sy K j => (n : (I →₀ ℚ) →₀ V Sy K j) c) hm
      simpa [Mmap_apply_coe, MmapAmb_apply] using this
    -- each term of `m` lies in `𝔍ⱼ Mᵢ`
    have hterm : ∀ c, (m : (I →₀ ℚ) →₀ V Sy K i) c ≠ 0 →
        ∃ t : M Sy K i, (t : (I →₀ ℚ) →₀ V Sy K i) =
          Finsupp.single c ((m : (I →₀ ℚ) →₀ V Sy K i) c) ∧
          t ∈ (RingHom.ker (Amap K h)) • (⊤ : Submodule (A K i) (M Sy K i)) := by
      intro c hc
      have hb := box_of_mem_M Sy K m.2 hc
      set v := (m : (I →₀ ℚ) →₀ V Sy K i) c with hv
      have hcj := hb j
      let ε : ℚ≥0 := ⟨(1 + c j) / 2, by linarith [hcj.1]⟩
      have hε : (ε : ℚ) = (1 + c j) / 2 := rfl
      let e : G I := Finsupp.single j ε
      have he : toRat e = Finsupp.single j ((1 + c j) / 2) := by
        ext l
        rw [toRat_apply]
        by_cases hl : l = j
        · subst hl; simp [e, hε]
        · simp [e, Ne.symm hl]
      set c' := c - toRat e with hc'
      have hc'l : ∀ l, c' l = if l = j then (c j - 1) / 2 else c l := by
        intro l
        rw [hc', Finsupp.sub_apply, he]
        by_cases hl : l = j
        · subst hl; simp; ring
        · simp [hl]
      have hbc' : Box c' := by
        intro l
        rw [hc'l l]
        split_ifs with hl
        · subst hl; constructor <;> linarith [hcj.1, hcj.2]
        · exact hb l
      have hsupp : c'.support ⊆ insert j c.support := by
        intro l hl
        rw [Finsupp.mem_support_iff, hc'l l] at hl
        by_cases hlj : l = j
        · exact Finset.mem_insert.mpr (Or.inl hlj)
        · rw [ite_eq_right hlj] at hl
          exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hl)
      have hvU : v ∈ U Sy K i c.support := by
        have := m.2 c
        rwa [W_of_box Sy K hb] at this
      have hvU' : v ∈ U Sy K i c'.support :=
        U_anti Sy K hsupp (mem_U_insert Sy K h hvU (hq c))
      let t' : M Sy K i := ⟨Finsupp.single c' v, single_mem_M Sy K hbc' hvU'⟩
      have heg : e ∈ gens j := Or.inr ⟨j, le_rfl, by
        change (0 : ℚ≥0) < Finsupp.single j ε j
        rw [Finsupp.single_eq_same]
        change (0 : ℚ) < (1 + c j) / 2
        linarith [hcj.1]⟩
      refine ⟨(Ideal.Quotient.mk (ideal K i) (AddMonoidAlgebra.of' K (G I) e) : A K i) • t',
        ?_, ?_⟩
      · rw [mk_smul, AddMonoidAlgebra.of'_apply, single_smul, shift_apply_coe]
        ext d : 1
        rw [shiftAmb_apply]
        by_cases hd : d = c
        · subst hd
          rw [ite_eq_left hb, Finsupp.single_eq_same, Finsupp.single_eq_same]
        · have hR : Finsupp.single c v d = 0 := by
            rw [Finsupp.single_apply, ite_eq_right (Ne.symm hd)]
          have hL : Finsupp.single c' v (d - toRat e) = 0 := by
            rw [Finsupp.single_apply, ite_eq_right]
            intro hcd
            apply hd
            have := congrArg (· + toRat e) hcd
            simp only [hc', sub_add_cancel] at this
            exact this.symm
          change (if Box d then Finsupp.single c' v (d - toRat e) else 0) = _
          rw [hR, hL, ite_self]
      · refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        rw [RingHom.mem_ker, Amap_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact of'_mem_ideal K heg
    choose! t ht htmem using hterm
    have hsum : m = ∑ c ∈ (m : (I →₀ ℚ) →₀ V Sy K i).support, t c := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      conv_lhs => rw [← Finsupp.sum_single (m : (I →₀ ℚ) →₀ V Sy K i)]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [ht c (Finsupp.mem_support_iff.mp hc)]
    rw [hsum]
    exact Submodule.sum_mem _ fun c hc => htmem c (Finsupp.mem_support_iff.mp hc)
  · intro hm
    refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun x y hx hy => ?_)
    · rw [Mmap_smul_A, RingHom.mem_ker.mp ha, zero_smul]
    · rw [map_add, hx, hy, add_zero]

/-! ### The stage rings `Rᵢ = Aᵢ ⊕ Mᵢ` -/

/-- The stage ring `Rᵢ = Aᵢ ⊕ Mᵢ`, the trivial square-zero extension of `Aᵢ` by `Mᵢ`. -/
abbrev R (i : I) : Type u := TrivSqZeroExt (A K i) (M Sy K i)

/-- The transition map `Rᵢ → Rⱼ`. -/
def Rmap {i j : I} (h : j ≤ i) : R Sy K i →+* R Sy K j :=
  Stacks.SqZeroExtension.map (Amap K h) (Mmap Sy K h).toAddMonoidHom
    (fun a m => Mmap_smul_A Sy K h a m)

/-- The `Aⱼ`-component of `Rmap h x` is the image of the `Aᵢ`-component of `x`. -/
theorem Rmap_fst {i j : I} (h : j ≤ i) (x : R Sy K i) : (Rmap Sy K h x).fst = Amap K h x.fst :=
  rfl

/-- The `Mⱼ`-component of `Rmap h x` is the image of the `Mᵢ`-component of `x`. -/
theorem Rmap_snd {i j : I} (h : j ≤ i) (x : R Sy K i) : (Rmap Sy K h x).snd = Mmap Sy K h x.snd :=
  rfl

/-- `Rⱼ = Rᵢ ⊗_{Aᵢ} Aⱼ`: the kernel of `Rᵢ → Rⱼ` is generated by the kernel of `Aᵢ → Aⱼ`. -/
theorem ker_Rmap {i j : I} (h : j ≤ i) :
    RingHom.ker (Rmap Sy K h) =
      Ideal.map (TrivSqZeroExt.inlHom (A K i) (M Sy K i)) (RingHom.ker (Amap K h)) :=
  Stacks.SqZeroExtension.ker_map _ _ _ (fun m => Mmap_eq_zero_iff Sy K h m)

/-- The transition maps `Rᵢ → Rⱼ` are surjective. -/
theorem surjective_Rmap {i j : I} (h : j ≤ i) : Function.Surjective (Rmap Sy K h) :=
  Stacks.SqZeroExtension.surjective_map _ _ _ (surjective_Amap K h) (surjective_Mmap Sy K h)

/-- The kernel of `Rᵢ → Rⱼ` is nil. -/
theorem isNilpotent_of_mem_ker_Rmap {i j : I} (h : j ≤ i) {x : R Sy K i}
    (hx : x ∈ RingHom.ker (Rmap Sy K h)) : IsNilpotent x := by
  have h0 := (Stacks.SqZeroExtension.map_eq_zero_iff _ _ _).mp (RingHom.mem_ker.mp hx)
  rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
  apply Commute.isNilpotent_add (Commute.all _ _)
  · exact (isNilpotent_of_mem_ker_Amap K h (RingHom.mem_ker.mpr h0.1)).map
      (TrivSqZeroExt.inlHom (A K i) (M Sy K i))
  · exact ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩

omit [IsDirected I (· ≤ ·)] in
/-- The transition map `Aᵢ → Aᵢ` is the identity. -/
theorem Amap_refl (i : I) (a : A K i) : Amap K (le_refl i) a = a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Amap_mk K _ x

omit [IsDirected I (· ≤ ·)] in
/-- The transition maps of the rings `Aᵢ` compose. -/
theorem Amap_Amap {i j k : I} (hjk : k ≤ j) (hij : j ≤ i) (a : A K i) :
    Amap K hjk (Amap K hij a) = Amap K (hjk.trans hij) a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Amap_mk, Amap_mk, Amap_mk]

/-- The transition map `Rᵢ → Rᵢ` is the identity. -/
theorem Rmap_refl (i : I) (x : R Sy K i) : Rmap Sy K (le_refl i) x = x :=
  TrivSqZeroExt.ext (Amap_refl K i x.fst) (Mmap_refl Sy K i x.snd)

/-- The transition maps of the rings `Rᵢ` compose. -/
theorem Rmap_Rmap {i j k : I} (hjk : k ≤ j) (hij : j ≤ i) (x : R Sy K i) :
    Rmap Sy K hjk (Rmap Sy K hij x) = Rmap Sy K (hjk.trans hij) x :=
  TrivSqZeroExt.ext (Amap_Amap K hjk hij x.fst) (Mmap_Mmap Sy K hjk hij x.snd)

/-- The transition map `Rᵢ → Rⱼ` restricts to `Aᵢ → Aⱼ` on `Aᵢ ⊆ Rᵢ`. -/
theorem Rmap_inl {i j : I} (h : j ≤ i) (a : A K i) :
    Rmap Sy K h (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (Amap K h a) :=
  TrivSqZeroExt.ext rfl (map_zero (Mmap Sy K h))

/-! ### The inverse systems of rings -/

open CategoryTheory

/-- The inverse system of the rings `Aᵢ`. -/
def Afun : Iᵒᵖ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (A K i.unop)
  map f := CommRingCat.ofHom (Amap K (leOfHom f.unop))
  map_id i := CommRingCat.hom_ext (RingHom.ext fun a => Amap_refl K i.unop a)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun a =>
    (Amap_Amap K (leOfHom g.unop) (leOfHom f.unop) a).symm)

/-- The inverse system of the rings `Rᵢ`. -/
def Rfun : Iᵒᵖ ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (R Sy K i.unop)
  map f := CommRingCat.ofHom (Rmap Sy K (leOfHom f.unop))
  map_id i := CommRingCat.hom_ext (RingHom.ext fun x => Rmap_refl Sy K i.unop x)
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun x =>
    (Rmap_Rmap Sy K (leOfHom g.unop) (leOfHom f.unop) x).symm)

/-- The structure maps `Aᵢ → Rᵢ`. -/
def inlNat : Afun K ⟶ Rfun Sy K where
  app i := CommRingCat.ofHom (TrivSqZeroExt.inlHom (A K i.unop) (M Sy K i.unop))
  naturality _ _ f := CommRingCat.hom_ext (RingHom.ext fun a =>
    (Rmap_inl Sy K (leOfHom f.unop) a).symm)

/-! ### The projections to `Vᵢ` -/

/-- The projection `Rᵢ → Vᵢ` onto the coefficient of the term at the exponent `0`. -/
def proj (i : I) (x : R Sy K i) : V Sy K i := (x.snd : (I →₀ ℚ) →₀ V Sy K i) 0

/-- The projections to `Vᵢ` are compatible with the transition maps. -/
theorem proj_Rmap {i j : I} (h : j ≤ i) (x : R Sy K i) :
    proj Sy K j (Rmap Sy K h x) = q Sy K h (proj Sy K i x) := rfl

/-- The projection `Rᵢ → Vᵢ` is surjective. -/
theorem surjective_proj (i : I) : Function.Surjective (proj Sy K i) := by
  intro v
  refine ⟨TrivSqZeroExt.inr ⟨Finsupp.single 0 v, single_mem_M Sy K box_zero ?_⟩, ?_⟩
  · rw [Finsupp.support_zero, U_empty]
    trivial
  · change Finsupp.single (0 : I →₀ ℚ) v 0 = v
    exact Finsupp.single_eq_same

end Stacks.FractionalSystem

end
