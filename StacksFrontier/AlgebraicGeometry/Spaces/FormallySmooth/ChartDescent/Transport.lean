module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartDescent.Torsor

/-!
# Transporting lifts between two charts of a formally étale chart

Let `X` be a functor on the `κ`-small commutative `A'`-algebras, let `P` be an `A'`-algebra and
let `a` be a *chart*: a natural map `(P →ₐ[A'] R) → X(R)`. The chart is *formally étale* when
every lifting problem along a square-zero surjection `q : R → Q` has exactly one solution.

Given two maps `c₁, c₂ : P →ₐ[A'] Q` with the same image under `a`, formal étaleness transports
the lifts of `c₁` along `q` bijectively onto the lifts of `c₂`: a lift `ℓ` of `c₁` goes to the
unique lift of `c₂` with the same image under `a`. This file proves that the transport is
*affine*: there is an `R`-linear map `τ` between the two modules of derivations with
`Θ (D +ᵥ ℓ) = τ D +ᵥ Θ ℓ`.

## Main definitions

* `AlgebraicGeometry.Space.ChartDescent.SmallAlg`: the `κ`-small `A'`-algebras.
* `AlgebraicGeometry.Space.ChartDescent.Chart`: a natural map out of `Hom(P, -)`.
* `AlgebraicGeometry.Space.ChartDescent.Chart.IsFormallyEtale`: the unique lifting property.
* `AlgebraicGeometry.Space.ChartDescent.Chart.transport`: the transport `Θ`.
* `AlgebraicGeometry.Space.ChartDescent.Chart.transportDer`: the linear map `τ`.
* `AlgebraicGeometry.Space.ChartDescent.relAlg`: the algebra of quadruples `(b₁, b₂, b₃, b₄)` with
  a common reduction and `b₄ - b₃ = b (b₂ - b₁)`.

## Main results

* `AlgebraicGeometry.Space.ChartDescent.Chart.transport_relation`: the transport preserves
  relations `ℓ₄ - ℓ₃ = b (ℓ₂ - ℓ₁)` among lifts.
* `AlgebraicGeometry.Space.ChartDescent.Chart.transport_addD`: `Θ (D +ᵥ ℓ) = τ D +ᵥ Θ ℓ`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space.ChartDescent

universe u

variable (A' : Type u) [CommRing A'] (κ : Cardinal.{u})

/-- The `κ`-small commutative `A'`-algebras. -/
abbrev smallAlg : ObjectProperty (CommAlgCat.{u} A') := fun R ↦ Cardinal.mk R < κ

/-- The category of `κ`-small commutative `A'`-algebras. -/
abbrev SmallAlg := (smallAlg A' κ).FullSubcategory

variable {A' κ}

/-- A `κ`-small `A'`-algebra as an object. -/
abbrev SmallAlg.mk (R : Type u) [CommRing R] [Algebra A' R] (h : Cardinal.mk R < κ) :
    SmallAlg A' κ :=
  ⟨CommAlgCat.of A' R, h⟩

/-- A map of `A'`-algebras as a morphism of `κ`-small algebras. -/
abbrev SmallAlg.homMk {R : SmallAlg A' κ} {R' : SmallAlg A' κ} (f : R.obj →ₐ[A'] R'.obj) :
    R ⟶ R' :=
  ObjectProperty.homMk (CommAlgCat.ofHom f)

/-- The underlying algebra map of `SmallAlg.homMk f` is `f`. -/
@[simp] theorem SmallAlg.homMk_hom {R R' : SmallAlg A' κ} (f : R.obj →ₐ[A'] R'.obj) :
    (SmallAlg.homMk f).hom.hom = f := rfl

/-- `SmallAlg.homMk` sends composition of algebra maps to composition of morphisms. -/
theorem SmallAlg.homMk_comp {R R' R'' : SmallAlg A' κ} (f : R.obj →ₐ[A'] R'.obj)
    (g : R'.obj →ₐ[A'] R''.obj) :
    SmallAlg.homMk f ≫ SmallAlg.homMk g = SmallAlg.homMk (g.comp f) := rfl

/-- A chart of a functor on `κ`-small algebras by an `A'`-algebra `P`: a natural map out of the
functor of points of `P`. -/
structure Chart (X : SmallAlg A' κ ⥤ Type u) (P : Type u) [CommRing P] [Algebra A' P] where
  /-- The map on points. -/
  app : ∀ R : SmallAlg A' κ, (P →ₐ[A'] R.obj) → X.obj R
  /-- Naturality. -/
  natural : ∀ {R R' : SmallAlg A' κ} (f : R ⟶ R') (ℓ : P →ₐ[A'] R.obj),
    X.map f (app R ℓ) = app R' (f.hom.hom.comp ℓ)

namespace Chart

variable {X : SmallAlg A' κ ⥤ Type u} {P : Type u} [CommRing P] [Algebra A' P]
  (a : Chart X P)

/-- A chart is formally étale when every lifting problem along a square-zero surjection of
`κ`-small algebras has exactly one solution. -/
def IsFormallyEtale : Prop :=
  ∀ (R Q : SmallAlg A' κ) (q : R ⟶ Q), Function.Surjective q.hom.hom →
    (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ^ 2 = ⊥ →
    ∀ (c : P →ₐ[A'] Q.obj) (z : X.obj R), X.map q z = a.app Q c →
      ∃! ℓ : P →ₐ[A'] R.obj, q.hom.hom.comp ℓ = c ∧ a.app R ℓ = z

variable {a}

section Transport

variable (ha : a.IsFormallyEtale) {R Q : SmallAlg A' κ} (q : R ⟶ Q)
  (hq : Function.Surjective q.hom.hom)
  (hsq : (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ^ 2 = ⊥)
  {c₁ c₂ : P →ₐ[A'] Q.obj} (hc : a.app Q c₁ = a.app Q c₂)

include hc in
/-- For a lift `ℓ` of `c₁`, the image of `a.app R ℓ` in `X(Q)` is `a.app Q c₂`. -/
theorem map_app_lift (ℓ : Lifts q.hom.hom c₁) : X.map q (a.app R ℓ.1) = a.app Q c₂ := by
  rw [a.natural, ℓ.2, hc]

/-- **The transport of lifts between two charts with the same image.** -/
noncomputable def transport (ℓ : Lifts q.hom.hom c₁) : Lifts q.hom.hom c₂ :=
  ⟨(ha R Q q hq hsq c₂ (a.app R ℓ.1) (map_app_lift q hc ℓ)).exists.choose,
    (ha R Q q hq hsq c₂ (a.app R ℓ.1) (map_app_lift q hc ℓ)).exists.choose_spec.1⟩

/-- The transport of `ℓ` has the same image under the chart as `ℓ`. -/
theorem app_transport (ℓ : Lifts q.hom.hom c₁) :
    a.app R (transport ha q hq hsq hc ℓ).1 = a.app R ℓ.1 :=
  (ha R Q q hq hsq c₂ (a.app R ℓ.1) (map_app_lift q hc ℓ)).exists.choose_spec.2

/-- The transport is characterized by its image under the chart. -/
theorem eq_transport (ℓ : Lifts q.hom.hom c₁) (m : Lifts q.hom.hom c₂)
    (hm : a.app R m.1 = a.app R ℓ.1) : m = transport ha q hq hsq hc ℓ :=
  Subtype.ext ((ha R Q q hq hsq c₂ (a.app R ℓ.1) (map_app_lift q hc ℓ)).unique
    ⟨m.2, hm⟩ ⟨(transport ha q hq hsq hc ℓ).2, app_transport ha q hq hsq hc ℓ⟩)

end Transport

end Chart

/-! ### The algebra of quadruples satisfying one linear relation -/

section Relation

variable {R : Type u} [CommRing R] [Algebra A' R] {Q : Type u} [CommRing Q] [Algebra A' Q]
  (q : R →ₐ[A'] Q) (hsq : (RingHom.ker (q : R →+* Q)) ^ 2 = ⊥)

/-- If the kernel of `q` has square zero, the product of two elements of the kernel vanishes. -/
theorem mul_eq_zero_of_ker (hsq : (RingHom.ker (q : R →+* Q)) ^ 2 = ⊥) {x y : R}
    (hx : q x = 0) (hy : q y = 0) : x * y = 0 :=
  mul_eq_zero_of_mem hsq (RingHom.mem_ker.2 hx) (RingHom.mem_ker.2 hy)

/-- The quadruples `(b₁, b₂, b₃, b₄)` with a common reduction and `b₄ - b₃ = b (b₂ - b₁)`. -/
def relAlg (b : R) : Subalgebra A' (R × R × R × R) where
  carrier := {v | q v.1 = q v.2.1 ∧ q v.1 = q v.2.2.1 ∧ q v.1 = q v.2.2.2 ∧
    v.2.2.2 - v.2.2.1 = b * (v.2.1 - v.1)}
  mul_mem' := by
    rintro ⟨x₁, x₂, x₃, x₄⟩ ⟨y₁, y₂, y₃, y₄⟩ ⟨hx₂, hx₃, hx₄, hx⟩ ⟨hy₂, hy₃, hy₄, hy⟩
    simp only [Set.mem_ofPred_eq, Prod.mk_mul_mk, map_mul] at *
    refine ⟨by rw [hx₂, hy₂], by rw [hx₃, hy₃], by rw [hx₄, hy₄], ?_⟩
    have k : ∀ {s t : R}, q s = q t → q (t - s) = 0 := fun h ↦ by rw [map_sub, h, sub_self]
    have e₂ := mul_eq_zero_of_ker q hsq (k hx₂) (k hy₂)
    have e₃ := mul_eq_zero_of_ker q hsq (k hx₃) (k hy₃)
    have e₄ := mul_eq_zero_of_ker q hsq (k hx₄) (k hy₄)
    linear_combination x₁ * hy + y₁ * hx + e₄ - e₃ - b * e₂
  add_mem' := by
    rintro ⟨x₁, x₂, x₃, x₄⟩ ⟨y₁, y₂, y₃, y₄⟩ ⟨hx₂, hx₃, hx₄, hx⟩ ⟨hy₂, hy₃, hy₄, hy⟩
    simp only [Set.mem_ofPred_eq, Prod.mk_add_mk, map_add] at *
    refine ⟨by rw [hx₂, hy₂], by rw [hx₃, hy₃], by rw [hx₄, hy₄], ?_⟩
    linear_combination hx + hy
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, Prod.algebraMap_apply, sub_self, mul_zero, and_self]

variable (b : R)

/-- The first coordinate of a quadruple. -/
def relFst : relAlg q hsq b →ₐ[A'] R := (AlgHom.fst A' R _).comp (relAlg q hsq b).val

/-- The four coordinate maps of the quadruple algebra. -/
def relProj (k : Fin 4) : relAlg q hsq b →ₐ[A'] R :=
  match k with
  | 0 => (AlgHom.fst A' R _).comp (relAlg q hsq b).val
  | 1 => ((AlgHom.fst A' R _).comp (AlgHom.snd A' R _)).comp (relAlg q hsq b).val
  | 2 => (((AlgHom.fst A' R _).comp (AlgHom.snd A' R _)).comp (AlgHom.snd A' R _)).comp
      (relAlg q hsq b).val
  | 3 => (((AlgHom.snd A' R _).comp (AlgHom.snd A' R _)).comp (AlgHom.snd A' R _)).comp
      (relAlg q hsq b).val

/-- The reduction of a quadruple. -/
def relRed : relAlg q hsq b →ₐ[A'] Q := q.comp (relProj q hsq b 0)

/-- Each coordinate of a quadruple has the same reduction, namely `relRed`. -/
theorem relRed_eq (k : Fin 4) : q.comp (relProj q hsq b k) = relRed q hsq b := by
  ext ⟨⟨x₁, x₂, x₃, x₄⟩, h₂, h₃, h₄, -⟩
  fin_cases k
  · rfl
  · exact h₂.symm
  · exact h₃.symm
  · exact h₄.symm

/-- If `q` is surjective, so is the reduction of quadruples. -/
theorem relRed_surjective (hq : Function.Surjective q) :
    Function.Surjective (relRed q hsq b) := by
  intro y
  obtain ⟨r, rfl⟩ := hq y
  exact ⟨⟨(r, r, r, r), rfl, rfl, rfl, by simp⟩, rfl⟩

/-- The kernel of the reduction of quadruples has square zero. -/
theorem relRed_ker_sq :
    (RingHom.ker ((relRed q hsq b : relAlg q hsq b →ₐ[A'] Q) :
      relAlg q hsq b →+* Q)) ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro X hX Y hY
  have hx : q X.1.1 = 0 := hX
  have hy : q Y.1.1 = 0 := hY
  have h : ∀ Z : relAlg q hsq b, q Z.1.1 = 0 →
      q Z.1.2.1 = 0 ∧ q Z.1.2.2.1 = 0 ∧ q Z.1.2.2.2 = 0 :=
    fun Z hz ↦ ⟨Z.2.1 ▸ hz, Z.2.2.1 ▸ hz, Z.2.2.2.1 ▸ hz⟩
  obtain ⟨hx₂, hx₃, hx₄⟩ := h X hx
  obtain ⟨hy₂, hy₃, hy₄⟩ := h Y hy
  rw [Ideal.mem_bot]
  refine Subtype.ext ?_
  change (X.1.1 * Y.1.1, X.1.2.1 * Y.1.2.1, X.1.2.2.1 * Y.1.2.2.1, X.1.2.2.2 * Y.1.2.2.2) =
    (0, 0, 0, 0)
  rw [mul_eq_zero_of_ker q hsq hx hy, mul_eq_zero_of_ker q hsq hx₂ hy₂,
    mul_eq_zero_of_ker q hsq hx₃ hy₃, mul_eq_zero_of_ker q hsq hx₄ hy₄]

/-- The quadruple algebra has cardinality at most that of `R × R × R × R`. -/
theorem relAlg_card_le : Cardinal.mk (relAlg q hsq b) ≤ Cardinal.mk (R × R × R × R) :=
  Cardinal.mk_le_of_injective Subtype.val_injective

variable {P : Type u} [CommRing P] [Algebra A' P]

/-- A quadruple of maps satisfying the relation, as one map into the quadruple algebra. -/
def relLift (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : P →ₐ[A'] R) (h₂ : q.comp ℓ₂ = q.comp ℓ₁)
    (h₃ : q.comp ℓ₃ = q.comp ℓ₁) (h₄ : q.comp ℓ₄ = q.comp ℓ₁)
    (h : ∀ x, ℓ₄ x - ℓ₃ x = b * (ℓ₂ x - ℓ₁ x)) : P →ₐ[A'] relAlg q hsq b :=
  AlgHom.codRestrict (ℓ₁.prod (ℓ₂.prod (ℓ₃.prod ℓ₄))) (relAlg q hsq b) fun x ↦
    ⟨(DFunLike.congr_fun h₂ x).symm, (DFunLike.congr_fun h₃ x).symm,
      (DFunLike.congr_fun h₄ x).symm, h x⟩

/-- The coordinates of `relLift` are the four given maps. -/
theorem relProj_relLift (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : P →ₐ[A'] R) (h₂ : q.comp ℓ₂ = q.comp ℓ₁)
    (h₃ : q.comp ℓ₃ = q.comp ℓ₁) (h₄ : q.comp ℓ₄ = q.comp ℓ₁)
    (h : ∀ x, ℓ₄ x - ℓ₃ x = b * (ℓ₂ x - ℓ₁ x)) :
    (relProj q hsq b 0).comp (relLift q hsq b ℓ₁ ℓ₂ ℓ₃ ℓ₄ h₂ h₃ h₄ h) = ℓ₁ ∧
    (relProj q hsq b 1).comp (relLift q hsq b ℓ₁ ℓ₂ ℓ₃ ℓ₄ h₂ h₃ h₄ h) = ℓ₂ ∧
    (relProj q hsq b 2).comp (relLift q hsq b ℓ₁ ℓ₂ ℓ₃ ℓ₄ h₂ h₃ h₄ h) = ℓ₃ ∧
    (relProj q hsq b 3).comp (relLift q hsq b ℓ₁ ℓ₂ ℓ₃ ℓ₄ h₂ h₃ h₄ h) = ℓ₄ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The coordinates `M₁, …, M₄` of a map `M` into the quadruple algebra satisfy
`M₄ x - M₃ x = b (M₂ x - M₁ x)`. -/
theorem relation_of_map (M : P →ₐ[A'] relAlg q hsq b) (x : P) :
    (relProj q hsq b 3).comp M x - (relProj q hsq b 2).comp M x =
      b * ((relProj q hsq b 1).comp M x - (relProj q hsq b 0).comp M x) :=
  (M x).2.2.2.2

end Relation

/-! ### The transport is affine -/

namespace Chart

variable {X : SmallAlg A' κ ⥤ Type u} {P : Type u} [CommRing P] [Algebra A' P]
  {a : Chart X P} (ha : a.IsFormallyEtale) (hκ : Cardinal.aleph0 ≤ κ)
  {R Q : SmallAlg A' κ} (q : R ⟶ Q)
  (hq : Function.Surjective q.hom.hom)
  (hsq : (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ^ 2 = ⊥)
  {c₁ c₂ : P →ₐ[A'] Q.obj} (hc : a.app Q c₁ = a.app Q c₂)

include hκ in
/-- For `ℵ₀ ≤ κ`, the quadruple algebra over a `κ`-small algebra is `κ`-small. -/
theorem relAlg_card_lt (b : R.obj) :
    Cardinal.mk (relAlg q.hom.hom hsq b) < κ := by
  refine (relAlg_card_le q.hom.hom hsq b).trans_lt ?_
  have hR : Cardinal.mk R.obj < κ := R.property
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt hκ hR (Cardinal.mul_lt_of_lt hκ hR (Cardinal.mul_lt_of_lt hκ hR hR))

include hκ in
/-- **The transport preserves affine relations among lifts.** -/
theorem transport_relation (b : R.obj) (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lifts q.hom.hom c₁)
    (h : ∀ x, ℓ₄.1 x - ℓ₃.1 x = b * (ℓ₂.1 x - ℓ₁.1 x)) (x : P) :
    (transport ha q hq hsq hc ℓ₄).1 x - (transport ha q hq hsq hc ℓ₃).1 x =
      b * ((transport ha q hq hsq hc ℓ₂).1 x - (transport ha q hq hsq hc ℓ₁).1 x) := by
  let RA : SmallAlg A' κ := SmallAlg.mk (relAlg q.hom.hom hsq b) (relAlg_card_lt hκ q hsq b)
  let red : RA ⟶ Q := SmallAlg.homMk (relRed q.hom.hom hsq b)
  let pr : Fin 4 → (RA ⟶ R) := fun k ↦ SmallAlg.homMk (relProj q.hom.hom hsq b k)
  have e : ∀ ℓ : Lifts q.hom.hom c₁, q.hom.hom.comp ℓ.1 = q.hom.hom.comp ℓ₁.1 :=
    fun ℓ ↦ ℓ.2.trans ℓ₁.2.symm
  let L : P →ₐ[A'] relAlg q.hom.hom hsq b :=
    relLift q.hom.hom hsq b ℓ₁.1 ℓ₂.1 ℓ₃.1 ℓ₄.1 (e ℓ₂) (e ℓ₃) (e ℓ₄) h
  have hL : (relRed q.hom.hom hsq b).comp L = c₁ := ℓ₁.2
  have hz : X.map red (a.app RA L) = a.app Q c₂ := by
    rw [a.natural]
    change a.app Q ((relRed q.hom.hom hsq b).comp L) = _
    rw [hL, hc]
  obtain ⟨M, ⟨hMred, hMa⟩, -⟩ := ha RA Q red (relRed_surjective q.hom.hom hsq b hq)
    (relRed_ker_sq q.hom.hom hsq b) c₂ (a.app RA L) hz
  have key : ∀ (k : Fin 4) (ℓ : Lifts q.hom.hom c₁), (relProj q.hom.hom hsq b k).comp L = ℓ.1 →
      ∀ x, (relProj q.hom.hom hsq b k).comp M x = (transport ha q hq hsq hc ℓ).1 x := by
    intro k ℓ hk x
    have hred : q.hom.hom.comp ((relProj q.hom.hom hsq b k).comp M) = c₂ := by
      rwa [← AlgHom.comp_assoc, relRed_eq]
    refine congrArg (fun m : Lifts q.hom.hom c₂ ↦ m.1 x)
      (eq_transport ha q hq hsq hc ℓ ⟨_, hred⟩ ?_)
    change a.app R ((pr k).hom.hom.comp M) = _
    rw [← a.natural, hMa, a.natural]
    change a.app R ((relProj q.hom.hom hsq b k).comp L) = _
    rw [hk]
  rw [← key 0 ℓ₁ rfl x, ← key 1 ℓ₂ rfl x, ← key 2 ℓ₃ rfl x, ← key 3 ℓ₄ rfl x]
  exact relation_of_map q.hom.hom hsq b M x

/-- Membership in the kernel of `q`. -/
theorem mem_ker_iff (r : R.obj) :
    r ∈ RingHom.ker (q.hom.hom : R.obj →+* Q.obj) ↔ q.hom.hom r = 0 := RingHom.mem_ker

/-- Adding a derivation to a lift of `c₁`. -/
noncomputable abbrev addD (ref : Lifts q.hom.hom c₁)
    (D : sqDer (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ref.1) (ℓ : Lifts q.hom.hom c₁) :
    Lifts q.hom.hom c₁ :=
  ⟨vaddHom (mem_ker_iff q) hsq ref.2 D ℓ, vaddHom_reduce (mem_ker_iff q) hsq ref.2 D ℓ⟩

include hκ in
/-- **The linear part of the transport.** -/
noncomputable def transportDer (ref₁ : Lifts q.hom.hom c₁) (ref₂ : Lifts q.hom.hom c₂) :
    sqDer (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ref₁.1 →ₗ[R.obj]
      sqDer (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ref₂.1 where
  toFun D := vsubDer (mem_ker_iff q) hsq ref₂.2
    (transport ha q hq hsq hc (addD q hsq ref₁ D ref₁)) (transport ha q hq hsq hc ref₁)
  map_add' D E := Subtype.ext <| LinearMap.ext fun x ↦ by
    change (_ : R.obj) - _ = ((_ : R.obj) - _) + ((_ : R.obj) - _)
    have h := transport_relation ha hκ q hq hsq hc 1 ref₁ (addD q hsq ref₁ D ref₁)
      (addD q hsq ref₁ E ref₁) (addD q hsq ref₁ (D + E) ref₁) (fun y ↦ by
        change (ref₁.1 y + ((D : _ →ₗ[A'] _) y + (E : _ →ₗ[A'] _) y)) -
          (ref₁.1 y + (E : _ →ₗ[A'] _) y) = 1 * ((ref₁.1 y + (D : _ →ₗ[A'] _) y) - ref₁.1 y)
        ring) x
    simp only [AlgHom.toLinearMap_apply]
    linear_combination h
  map_smul' b D := Subtype.ext <| LinearMap.ext fun x ↦ by
    change (_ : R.obj) - _ = b * ((_ : R.obj) - _)
    have h := transport_relation ha hκ q hq hsq hc b ref₁ (addD q hsq ref₁ D ref₁)
      ref₁ (addD q hsq ref₁ (b • D) ref₁) (fun y ↦ by
        change (ref₁.1 y + b * (D : _ →ₗ[A'] _) y) - ref₁.1 y =
          b * ((ref₁.1 y + (D : _ →ₗ[A'] _) y) - ref₁.1 y)
        ring) x
    simp only [AlgHom.toLinearMap_apply]
    linear_combination h

/-- **The transport is affine over its linear part.** -/
theorem transport_addD (ref₁ : Lifts q.hom.hom c₁) (ref₂ : Lifts q.hom.hom c₂)
    (D : sqDer (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ref₁.1)
    (ℓ : Lifts q.hom.hom c₁) (x : P) :
    (transport ha q hq hsq hc (addD q hsq ref₁ D ℓ)).1 x =
      (transport ha q hq hsq hc ℓ).1 x +
        ((transportDer ha hκ q hq hsq hc ref₁ ref₂ D : sqDer _ ref₂.1) : P →ₗ[A'] R.obj) x := by
  have h := transport_relation ha hκ q hq hsq hc 1 ref₁ (addD q hsq ref₁ D ref₁) ℓ
    (addD q hsq ref₁ D ℓ) (fun y ↦ by
      change (ℓ.1 y + (D : _ →ₗ[A'] _) y) - ℓ.1 y =
        1 * ((ref₁.1 y + (D : _ →ₗ[A'] _) y) - ref₁.1 y)
      ring) x
  change (_ : R.obj) = _ + ((_ : R.obj) - _)
  simp only [AlgHom.toLinearMap_apply]
  linear_combination h

end Chart

end AlgebraicGeometry.Space.ChartDescent

end
