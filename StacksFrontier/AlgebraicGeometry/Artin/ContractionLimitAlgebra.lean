module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Descending a ring map into a limit of completions to a stage

This is the ring-theoretic skeleton of the "algebra" paragraphs of the proof of Stacks 0GI5. Let
`k ↦ Â_k` and `k ↦ Ĉ_k` be two systems of rings over a cofiltered index category, with a natural
map `α : Â ⟶ Ĉ` and compatible maps `ρ_A : Â_k ⟶ Â`, `ρ_C : Ĉ_k ⟶ Ĉ` to two rings `Â`, `Ĉ`
receiving `α_l : Â ⟶ Ĉ`. In the source `Â_k`, `Ĉ_k` are the completions of the coordinate rings
`A_k` of the stages and `C_k` of the descended witness, and `Â`, `Ĉ` those of the limit.

Given ring maps `φ : B ⟶ Â` and `ψ : B ⟶ Ĉ_{k₀}` agreeing in `Ĉ`, the goal is a stage `k` and a
ring map `φ_k : B ⟶ Â_k` lifting `φ` and `ψ`. The source chooses topological generators of `B`
over the base ring; here the input is packaged into four statements about the systems:

* `hcoker`: elements of `Ĉ_{k₀}` that land in the image of `Â` in `Ĉ` land, at a later stage, in
  the image of `Â_k` (the cokernels of `A_k → C_k` are finite and `I`-power torsion);
* `hker`: the kernel of `α_l` comes from the kernels of the `α_k` (same for the kernels);
* `hopen`: once `ψ` lands in the image of `α_k`, being liftable at a stage is decided by finitely
  many elements of `B` (an open ideal of `B` lifts by Artin–Rees, and `B` is of finite type over
  the base modulo it);
* `hL`: an element of `Â_k` killed by `α_k` and `ρ_A` dies at a later stage.

The elements of `B` liftable at a stage form a subring
(`AlgebraicGeometry.Artin.StageLift.goodSubring`), and the lift is well defined at a later stage
by `hL`.

## Main results

* `AlgebraicGeometry.Artin.StageLift.exists_stage_ringHom`: the lift.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory Opposite

universe v w

namespace AlgebraicGeometry.Artin.StageLift

variable {K : Type*} [Category K]
  {Ah Ch : Kᵒᵖ ⥤ CommRingCat.{v}} (α : Ah ⟶ Ch)
  {Al Cl : CommRingCat.{v}} (αl : Al ⟶ Cl)
  (ρA : ∀ k : K, Ah.obj (op k) ⟶ Al) (ρC : ∀ k : K, Ch.obj (op k) ⟶ Cl)
  (hρA : ∀ {k k' : K} (g : k' ⟶ k), Ah.map g.op ≫ ρA k' = ρA k)
  (hρC : ∀ {k k' : K} (g : k' ⟶ k), Ch.map g.op ≫ ρC k' = ρC k)
  {B : Type w} [CommRing B] (φ : B →+* Al) {k₀ : K} (ψ : B →+* Ch.obj (op k₀))

/-- An element `b` of `B` is *liftable at the stage* `f : k ⟶ k₀` when some element of `Â_k` maps
to `φ b` in `Â` and to the image of `ψ b` in `Ĉ_k`. -/
def IsGoodAt {k : K} (f : k ⟶ k₀) (b : B) : Prop :=
  ∃ x : Ah.obj (op k), (ρA k).hom x = φ b ∧
    (α.app (op k)).hom x = (Ch.map f.op).hom (ψ b)

include hρA in
/-- The map `ρ_A k' ∘ Â(g)` agrees with `ρ_A k` on elements, for `g : k' ⟶ k`. -/
theorem ρA_map_apply {k k' : K} (g : k' ⟶ k) (x : Ah.obj (op k)) :
    (ρA k').hom ((Ah.map g.op).hom x) = (ρA k).hom x := by
  rw [← hρA g]
  rfl

include hρC in
/-- The map `ρ_C k' ∘ Ĉ(g)` agrees with `ρ_C k` on elements, for `g : k' ⟶ k`. -/
theorem ρC_map_apply {k k' : K} (g : k' ⟶ k) (x : Ch.obj (op k)) :
    (ρC k').hom ((Ch.map g.op).hom x) = (ρC k).hom x := by
  rw [← hρC g]
  rfl

/-- Naturality of `α` on elements: `α_{k'} (Â(g) x) = Ĉ(g) (α_k x)` for `g : k' ⟶ k`. -/
theorem α_map_apply {k k' : K} (g : k' ⟶ k) (x : Ah.obj (op k)) :
    (α.app (op k')).hom ((Ah.map g.op).hom x) = (Ch.map g.op).hom ((α.app (op k)).hom x) := by
  simp

/-- Functoriality of `Ĉ` on elements: `Ĉ(g ≫ f) c = Ĉ(g) (Ĉ(f) c)`. -/
theorem Ch_map_comp_apply {k k' : K} (g : k' ⟶ k) (f : k ⟶ k₀) (c : Ch.obj (op k₀)) :
    (Ch.map (g ≫ f).op).hom c = (Ch.map g.op).hom ((Ch.map f.op).hom c) := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- If `α_k x = Ĉ(f) c`, then `α_{k'} (Â(g) x) = Ĉ(g ≫ f) c` for `g : k' ⟶ k`. -/
private theorem α_map_apply_eq {k k' : K} (g : k' ⟶ k) (f : k ⟶ k₀) {x : Ah.obj (op k)}
    {c : Ch.obj (op k₀)} (h : (α.app (op k)).hom x = (Ch.map f.op).hom c) :
    (α.app (op k')).hom ((Ah.map g.op).hom x) = (Ch.map (g ≫ f).op).hom c := by
  rw [α_map_apply, h, Ch_map_comp_apply]

include hρA in
/-- Liftability is preserved when passing to a later stage. -/
theorem IsGoodAt.mono {k k' : K} {f : k ⟶ k₀} {b : B} (h : IsGoodAt α ρA φ ψ f b)
    (g : k' ⟶ k) : IsGoodAt α ρA φ ψ (g ≫ f) b := by
  obtain ⟨x, hx₁, hx₂⟩ := h
  refine ⟨(Ah.map g.op).hom x, ?_, ?_⟩
  · rw [ρA_map_apply ρA hρA, hx₁]
  · exact α_map_apply_eq α g f hx₂

/-- The elements liftable at a fixed stage form a subring of `B`. -/
def goodSubring {k : K} (f : k ⟶ k₀) : Subring B where
  carrier := {b | IsGoodAt α ρA φ ψ f b}
  mul_mem' := by
    rintro a b ⟨x, hx₁, hx₂⟩ ⟨y, hy₁, hy₂⟩
    exact ⟨x * y, by rw [map_mul, hx₁, hy₁, map_mul], by rw [map_mul, hx₂, hy₂, map_mul, map_mul]⟩
  one_mem' := ⟨1, by rw [map_one, map_one], by rw [map_one, map_one, map_one]⟩
  add_mem' := by
    rintro a b ⟨x, hx₁, hx₂⟩ ⟨y, hy₁, hy₂⟩
    exact ⟨x + y, by rw [map_add, hx₁, hy₁, map_add], by rw [map_add, hx₂, hy₂, map_add, map_add]⟩
  zero_mem' := ⟨0, by rw [map_zero, map_zero], by rw [map_zero, map_zero, map_zero]⟩
  neg_mem' := by
    rintro a ⟨x, hx₁, hx₂⟩
    exact ⟨-x, by rw [map_neg, hx₁, map_neg], by rw [map_neg, hx₂, map_neg, map_neg]⟩

/-- An element lies in `goodSubring` if and only if it is liftable at the given stage. -/
theorem mem_goodSubring {k : K} (f : k ⟶ k₀) (b : B) :
    b ∈ goodSubring α ρA φ ψ f ↔ IsGoodAt α ρA φ ψ f b := Iff.rfl

variable [IsCofiltered K]

include hρA hρC in
/-- **One element at a time.** Once `ψ` lands in the image of `α_k`, every element of `B` becomes
liftable at a later stage, by correcting a preimage with an element of the kernel of `α` coming
from `hker`. -/
theorem exists_isGoodAt_of_range
    (hρ : ∀ {k : K} (x : Ah.obj (op k)),
      αl.hom ((ρA k).hom x) = (ρC k).hom ((α.app (op k)).hom x))
    (hφψ : ∀ b, αl.hom (φ b) = (ρC k₀).hom (ψ b))
    (hker : ∀ y : Al, αl.hom y = 0 →
      ∃ (k : K) (z : Ah.obj (op k)), (α.app (op k)).hom z = 0 ∧ (ρA k).hom z = y)
    {k : K} (f : k ⟶ k₀)
    (hrange : ∀ b, (Ch.map f.op).hom (ψ b) ∈ (α.app (op k)).hom.range) (b : B) :
    ∃ (k' : K) (g : k' ⟶ k), IsGoodAt α ρA φ ψ (g ≫ f) b := by
  obtain ⟨x, hx⟩ := hrange b
  have hy : αl.hom (φ b - (ρA k).hom x) = 0 := by
    rw [map_sub, hρ, hx, ρC_map_apply ρC hρC, hφψ, sub_self]
  obtain ⟨kz, z, hz₁, hz₂⟩ := hker _ hy
  refine ⟨IsCofiltered.min k kz, IsCofiltered.minToLeft k kz,
    (Ah.map (IsCofiltered.minToLeft k kz).op).hom x +
      (Ah.map (IsCofiltered.minToRight k kz).op).hom z, ?_, ?_⟩
  · rw [map_add, ρA_map_apply ρA hρA, ρA_map_apply ρA hρA, hz₂, add_sub_cancel]
  · rw [map_add, α_map_apply_eq α _ f hx, α_map_apply, hz₁, map_zero, add_zero]

include hρA hρC in
/-- **Finitely many elements at a time.** -/
theorem exists_forall_mem_isGoodAt
    (hρ : ∀ {k : K} (x : Ah.obj (op k)),
      αl.hom ((ρA k).hom x) = (ρC k).hom ((α.app (op k)).hom x))
    (hφψ : ∀ b, αl.hom (φ b) = (ρC k₀).hom (ψ b))
    (hker : ∀ y : Al, αl.hom y = 0 →
      ∃ (k : K) (z : Ah.obj (op k)), (α.app (op k)).hom z = 0 ∧ (ρA k).hom z = y)
    {k : K} (f : k ⟶ k₀)
    (hrange : ∀ b, (Ch.map f.op).hom (ψ b) ∈ (α.app (op k)).hom.range) (s : Finset B) :
    ∃ (k' : K) (g : k' ⟶ k), ∀ b ∈ s, IsGoodAt α ρA φ ψ (g ≫ f) b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, by simp⟩
  | insert b s _ ih =>
    obtain ⟨k₂, g₂, h₂⟩ := ih
    have hrange₂ : ∀ b', (Ch.map (g₂ ≫ f).op).hom (ψ b') ∈ (α.app (op k₂)).hom.range := by
      intro b'
      obtain ⟨x, hx⟩ := hrange b'
      exact ⟨_, α_map_apply_eq α g₂ f hx⟩
    obtain ⟨k₃, g₃, h₃⟩ :=
      exists_isGoodAt_of_range α αl ρA ρC hρA hρC φ ψ hρ hφψ hker (g₂ ≫ f) hrange₂ b
    refine ⟨k₃, g₃ ≫ g₂, fun b' hb' => ?_⟩
    rw [Category.assoc]
    rcases Finset.mem_insert.1 hb' with rfl | hb'
    · exact h₃
    · exact (h₂ b' hb').mono α ρA hρA φ ψ g₃

include hρA hρC in
/-- **The lift at a stage.** With the four inputs described in the module documentation, the
ring map `φ : B ⟶ Â` descends to a ring map `B ⟶ Â_k` at some stage `f : k ⟶ k₀` which maps to
`φ` in `Â` and to the image of `ψ` in `Ĉ_k`. -/
theorem exists_stage_ringHom
    (hρ : ∀ {k : K} (x : Ah.obj (op k)),
      αl.hom ((ρA k).hom x) = (ρC k).hom ((α.app (op k)).hom x))
    (hφψ : ∀ b, αl.hom (φ b) = (ρC k₀).hom (ψ b))
    (hcoker : ∃ (k₁ : K) (f₁ : k₁ ⟶ k₀), ∀ c : Ch.obj (op k₀),
      (ρC k₀).hom c ∈ αl.hom.range →
        (Ch.map f₁.op).hom c ∈ (α.app (op k₁)).hom.range)
    (hker : ∀ y : Al, αl.hom y = 0 →
      ∃ (k : K) (z : Ah.obj (op k)), (α.app (op k)).hom z = 0 ∧ (ρA k).hom z = y)
    (hopen : ∀ {k : K} (f : k ⟶ k₀),
      (∀ b, (Ch.map f.op).hom (ψ b) ∈ (α.app (op k)).hom.range) →
        ∃ s : Finset B, ∀ {k' : K} (g : k' ⟶ k),
          (∀ b ∈ s, IsGoodAt α ρA φ ψ (g ≫ f) b) → ∀ b, IsGoodAt α ρA φ ψ (g ≫ f) b)
    (hL : ∀ {k : K}, ∃ (k' : K) (g : k' ⟶ k), ∀ x : Ah.obj (op k),
      (α.app (op k)).hom x = 0 → (ρA k).hom x = 0 → (Ah.map g.op).hom x = 0) :
    ∃ (k : K) (f : k ⟶ k₀) (φk : B →+* Ah.obj (op k)),
      (∀ b, (ρA k).hom (φk b) = φ b) ∧
        ∀ b, (α.app (op k)).hom (φk b) = (Ch.map f.op).hom (ψ b) := by
  classical
  obtain ⟨k₁, f₁, hf₁⟩ := hcoker
  have hrange₁ : ∀ b, (Ch.map f₁.op).hom (ψ b) ∈ (α.app (op k₁)).hom.range :=
    fun b => hf₁ _ ⟨φ b, hφψ b⟩
  obtain ⟨s, hs⟩ := hopen f₁ hrange₁
  obtain ⟨k₂, g₂, h₂⟩ :=
    exists_forall_mem_isGoodAt α αl ρA ρC hρA hρC φ ψ hρ hφψ hker f₁ hrange₁ s
  obtain ⟨k₃, g₃, hg₃⟩ := hL (k := k₂)
  choose w hw₁ hw₂ using hs g₂ h₂
  have huniq : ∀ (b : B) (x : Ah.obj (op k₂)), (ρA k₂).hom x = φ b →
      (α.app (op k₂)).hom x = (Ch.map (g₂ ≫ f₁).op).hom (ψ b) →
        (Ah.map g₃.op).hom x = (Ah.map g₃.op).hom (w b) := by
    intro b x hx₁ hx₂
    rw [← sub_eq_zero, ← map_sub]
    exact hg₃ _ (by rw [map_sub, hx₂, hw₂, sub_self]) (by rw [map_sub, hx₁, hw₁, sub_self])
  let φk : B →+* Ah.obj (op k₃) :=
    { toFun := fun b => (Ah.map g₃.op).hom (w b)
      map_one' := (huniq 1 1 (by rw [map_one, map_one])
        (by rw [map_one, map_one, map_one])).symm.trans (map_one _)
      map_mul' := fun a b => (huniq (a * b) (w a * w b) (by rw [map_mul, hw₁, hw₁, map_mul])
        (by rw [map_mul, hw₂, hw₂, map_mul, map_mul])).symm.trans (map_mul _ _ _)
      map_zero' := (huniq 0 0 (by rw [map_zero, map_zero])
        (by rw [map_zero, map_zero, map_zero])).symm.trans (map_zero _)
      map_add' := fun a b => (huniq (a + b) (w a + w b) (by rw [map_add, hw₁, hw₁, map_add])
        (by rw [map_add, hw₂, hw₂, map_add, map_add])).symm.trans (map_add _ _ _) }
  refine ⟨k₃, g₃ ≫ g₂ ≫ f₁, φk, fun b => ?_, fun b => ?_⟩
  · show (ρA k₃).hom ((Ah.map g₃.op).hom (w b)) = φ b
    rw [ρA_map_apply ρA hρA, hw₁]
  · exact α_map_apply_eq α g₃ _ (hw₂ b)

end AlgebraicGeometry.Artin.StageLift

end
