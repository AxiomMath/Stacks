module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Milnor patching of modules along a fibre product of rings

Let `β : B → A` be a ring map and let `π : A' → A` be a surjection with kernel `I`, so that
`A ≅ A'/I`.  Write `B' = B ×_A A' = {(b, a') | β b = π a'}` for the fibre product ring, that is
`RingHom.pullback β π`.  For an `A'`-module `M'` the canonical `A`-module `M' ⊗_{A'} A` is
identified with `M'/IM'`.

Modules are glued over this square through the fibre product category
`Mod_B ×_{Mod_A} Mod_{A'}`, whose objects are triples `(N, M', φ)` consisting of a `B`-module
`N`, an `A'`-module `M'` and an isomorphism `φ : N ⊗_B A ≅ M'/IM'` of `A`-modules, and whose
morphisms `(N₁, M'₁, φ₁) → (N₂, M'₂, φ₂)` are pairs of a `B`-linear `a : N₁ → N₂` and an
`A'`-linear `b : M'₁ → M'₂` whose square commutes.  The patching functor sends `(N, M', φ)` to
the `B'`-module `N ×_{φ, M} M'` of pairs agreeing in `M'/IM'`.

## Main definitions

* `MilnorPatching.QuotKerSMulTop` is the `A`-module `M'/IM'`.
* `MilnorPatching.StructureEquiv` is the type of structure isomorphisms `φ`, and
  `MilnorPatching.IsMorphism` the commuting-square condition on a pair `(a, b)`.
* `MilnorPatching.fibreProd` is the glued `B'`-module `N ×_{φ, M} M'`, and
  `MilnorPatching.fibreProdMap` the map it induces from a morphism.

## Main results

* `MilnorPatching.fibreProdMap_surjective` is Stacks Tag 08KJ: the glued map is surjective as
  soon as both of its components are.

## Implementation notes

`β` is taken to be `algebraMap B A`, so the `B`-algebra structure on `A` carries it.  The
tensor product `N ⊗_B A` is formalized as the `A`-module `A ⊗[B] N`, whose `A`-module structure
comes from the left factor, with `can_N n := (1 : A) ⊗ₜ n`; and `M'/IM'` is `M' ⧸ (I • ⊤)` with
`can_{M'} := Submodule.Quotient.mk`.  The fibre product ring is Mathlib's `RingHom.pullback`,
which is also the ring underlying `RingFibreProduct.Situation` in
`StacksFrontier.RingTheory.FibreProduct`.

## References

* [Stacks Project, Tag 08KH](https://stacks.math.columbia.edu/tag/08KH)
* [Stacks Project, Tag 08KJ](https://stacks.math.columbia.edu/tag/08KJ)
-/

@[expose] public section

-- Notational conventions:
-- * `β : B →+* A` is taken to be `algebraMap B A` (the `B`-algebra structure on `A`).
-- * `N ⊗_B A` is formalized as the `A`-module `A ⊗[B] N` (the order of factors is
--   irrelevant; we use the convention that gives `A ⊗[B] N` its `A`-module structure
--   from the left factor), and `can_N n := (1 : A) ⊗ₜ n`.
-- * `M'/IM'` is `M' ⧸ (I • ⊤)` and `can_{M'} := Submodule.Quotient.mk`.

namespace MilnorPatching

noncomputable section

variable {A A' : Type*} [CommRing A] [CommRing A']
variable (π : A' →+* A) [RingHomSurjective π]

-- Main Definition(s)

/-- `M'/IM'`, the `A`-module identified with `M' ⊗_{A'} A`. -/
abbrev QuotKerSMulTop (M' : Type*) [AddCommGroup M'] [Module A' M'] : Type _ :=
  M' ⧸ ((RingHom.ker π) • (⊤ : Submodule A' M'))

/-- The `A`-module structure on `M'/IM'` coming from the identification `A ≅ A'/I`
(here `I = ker π`).  Concretely, `a • mk m'` is computed by lifting `a` to `A'/I`
through the isomorphism `A ≅ A'/I`. -/
instance QuotKerSMulTop.module (M' : Type*) [AddCommGroup M'] [Module A' M'] :
    Module A (QuotKerSMulTop π M') :=
  Module.compHom _ ((RingHom.quotientKerEquivOfSurjective
    π.surjective).symm : A →+* (A' ⧸ RingHom.ker π))

/-- The element `π a' ∈ A` acts on `M'/IM'` exactly as `a' ∈ A'`. -/
@[simp] theorem QuotKerSMulTop.smul_mk {M' : Type*} [AddCommGroup M'] [Module A' M']
    (a' : A') (m' : M') :
    (π a') • (Submodule.Quotient.mk m' : QuotKerSMulTop π M') =
      Submodule.Quotient.mk (a' • m') := by
  have h : (RingHom.quotientKerEquivOfSurjective π.surjective).symm (π a')
      = Ideal.Quotient.mk (RingHom.ker π) a' := by
    apply (RingHom.quotientKerEquivOfSurjective π.surjective).injective
    rw [RingEquiv.apply_symm_apply]; rfl
  show ((RingHom.quotientKerEquivOfSurjective π.surjective).symm (π a'))
        • (Submodule.Quotient.mk m' : QuotKerSMulTop π M') = _
  rw [h]
  exact Module.Quotient.mk_smul_mk M' (RingHom.ker π) a' m'

variable (B : Type*) [CommRing B] [Algebra B A]

omit [RingHomSurjective π] in
/-- The defining equation of `B'`: `β (pr_B c) = π (pr_{A'} c)` for every `c ∈ B'`. -/
theorem algebraMap_pullbackFst_eq_pullbackSnd (c : RingHom.pullback (algebraMap B A) π) :
    algebraMap B A (RingHom.pullbackFst (algebraMap B A) π c) =
      π (RingHom.pullbackSnd (algebraMap B A) π c) := c.property

variable (N M' : Type*) [AddCommGroup N] [Module B N] [AddCommGroup M'] [Module A' M']

/-- The type of structure isomorphisms `φ : N ⊗_B A ≅ M'/IM'` (an object of the
fibre product category is a triple `(N, M', φ)`). -/
abbrev StructureEquiv := (TensorProduct B A N) ≃ₗ[A] (QuotKerSMulTop π M')

/-- `StructureEquiv`, under the name used in the Stacks 08KJ statement. -/
abbrev StructIso := StructureEquiv π B N M'

variable {N M'}

/-- A `B`-module is a `B'`-module via the projection `B' → B`. -/
local instance instModuleOfFst {X : Type*} [AddCommGroup X] [Module B X] :
    Module (RingHom.pullback (algebraMap B A) π) X :=
  Module.compHom X (RingHom.pullbackFst (algebraMap B A) π)

/-- An `A'`-module is a `B'`-module via the projection `B' → A'`.  Where a type carries
both a `Module B` and a `Module A'` instance, this one takes precedence. -/
local instance instModuleOfSnd {X : Type*} [AddCommGroup X] [Module A' X] :
    Module (RingHom.pullback (algebraMap B A) π) X :=
  Module.compHom X (RingHom.pullbackSnd (algebraMap B A) π)

/-- The functor `F` on objects: the `B'`-submodule
`N ×_{φ, M} M' = {(n, m') | φ (can_N n) = can_{M'} m'}` of `N × M'`. -/
def fibreProd (φ : StructureEquiv π B N M') :
    Submodule (RingHom.pullback (algebraMap B A) π) (N × M') where
  carrier := { p | φ ((1 : A) ⊗ₜ[B] p.1) = Submodule.Quotient.mk p.2 }
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at *
    rw [TensorProduct.tmul_add, map_add, hp, hq, ← Submodule.Quotient.mk_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero,
      TensorProduct.tmul_zero, map_zero]
    rw [← Submodule.Quotient.mk_zero]
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_ofPred_eq] at *
    change φ ((1 : A) ⊗ₜ[B] ((RingHom.pullbackFst (algebraMap B A) π c) • p.1))
      = Submodule.Quotient.mk ((RingHom.pullbackSnd (algebraMap B A) π c) • p.2)
    rw [TensorProduct.tmul_smul,
      algebra_compatible_smul A (RingHom.pullbackFst (algebraMap B A) π c), map_smul, hp,
      algebraMap_pullbackFst_eq_pullbackSnd, QuotKerSMulTop.smul_mk]

/-- A pair `(n, m')` lies in `N ×_{φ, M} M'` exactly when `φ (can_N n) = can_{M'} m'`. -/
@[simp] theorem mem_fibreProd {φ : StructureEquiv π B N M'} {p : N × M'} :
    p ∈ fibreProd π B φ ↔ φ ((1 : A) ⊗ₜ[B] p.1) = Submodule.Quotient.mk p.2 := Iff.rfl

-- The morphism structure and the functor `F` on morphisms.

variable {N₁ N₂ M₁' M₂' : Type*}
  [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₂] [Module B N₂]
  [AddCommGroup M₁'] [Module A' M₁'] [AddCommGroup M₂'] [Module A' M₂']

/-- The map `b̄ : M'₁/IM'₁ → M'₂/IM'₂` induced on quotients by an `A'`-linear map
`b : M'₁ → M'₂`. -/
def QuotKerSMulTop.map (b : M₁' →ₗ[A'] M₂') :
    (QuotKerSMulTop π M₁') →ₗ[A'] (QuotKerSMulTop π M₂') :=
  Submodule.mapQ _ _ b (Submodule.smul_top_le_comap_smul_top _ b)

omit [RingHomSurjective π] in
/-- The induced map `b̄` sends the class of `m'` to the class of `b m'`. -/
@[simp] theorem QuotKerSMulTop.map_mk (b : M₁' →ₗ[A'] M₂') (m' : M₁') :
    QuotKerSMulTop.map π b (Submodule.Quotient.mk m') = Submodule.Quotient.mk (b m') := by
  rw [QuotKerSMulTop.map, Submodule.mapQ_apply]

variable (N₁ N₂ M₁' M₂') in
/-- A morphism `(N₁, M'₁, φ₁) → (N₂, M'₂, φ₂)` in the fibre product category is a
pair `(a, b)` of a `B`-linear `a : N₁ → N₂` and an `A'`-linear `b : M'₁ → M'₂` whose
square commutes, i.e. `φ₂ ∘ (a ⊗ id) = b̄ ∘ φ₁`. -/
structure IsMorphism (φ₁ : StructureEquiv π B N₁ M₁') (φ₂ : StructureEquiv π B N₂ M₂')
    (a : N₁ →ₗ[B] N₂) (b : M₁' →ₗ[A'] M₂') : Prop where
  compat : ∀ x : TensorProduct B A N₁,
    φ₂ (LinearMap.baseChange A a x) = QuotKerSMulTop.map π b (φ₁ x)

section

variable {π B}

/-- The compatibility of a morphism `(a, b)`, evaluated on the generators `1 ⊗ n`. -/
private theorem IsMorphism.compat_tmul {φ₁ : StructureEquiv π B N₁ M₁'}
    {φ₂ : StructureEquiv π B N₂ M₂'} {a : N₁ →ₗ[B] N₂} {b : M₁' →ₗ[A'] M₂'}
    (hab : IsMorphism π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b) (n : N₁) :
    φ₂ ((1 : A) ⊗ₜ[B] a n) = QuotKerSMulTop.map π b (φ₁ ((1 : A) ⊗ₜ[B] n)) := by
  rw [← hab.compat, LinearMap.baseChange_tmul]

/-- A morphism `(a, b)` of the fibre product category sends `N₁ ×_{φ₁} M'₁` into
`N₂ ×_{φ₂} M'₂`. -/
theorem IsMorphism.map_mem_fibreProd {φ₁ : StructureEquiv π B N₁ M₁'}
    {φ₂ : StructureEquiv π B N₂ M₂'} {a : N₁ →ₗ[B] N₂} {b : M₁' →ₗ[A'] M₂'}
    (hab : IsMorphism π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b)
    {n : N₁} {m' : M₁'} (hp : (n, m') ∈ fibreProd π B φ₁) :
    (a n, b m') ∈ fibreProd π B φ₂ := by
  simp only [mem_fibreProd] at hp ⊢
  rw [hab.compat_tmul, hp, QuotKerSMulTop.map_mk]

end

/-- The functor `F` on morphisms: the `B'`-linear map
`F(a, b) : N₁ ×_{φ₁} M'₁ → N₂ ×_{φ₂} M'₂`, `(n, m') ↦ (a n, b m')`. -/
def fibreProdMap (φ₁ : StructureEquiv π B N₁ M₁') (φ₂ : StructureEquiv π B N₂ M₂')
    (a : N₁ →ₗ[B] N₂) (b : M₁' →ₗ[A'] M₂') (hab : IsMorphism π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b) :
    fibreProd π B φ₁ →ₗ[RingHom.pullback (algebraMap B A) π] fibreProd π B φ₂ where
  toFun p := ⟨(a p.val.1, b p.val.2), hab.map_mem_fibreProd p.property⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add, map_add]
  map_smul' c p := Subtype.ext <| Prod.ext (a.map_smul _ _) (b.map_smul _ _)

variable (N₁ N₂ M₁' M₂') in
/-- `fibreProdMap`, under the name used in the Stacks 08KJ statement. -/
abbrev Fmor (φ₁ : StructIso π B N₁ M₁') (φ₂ : StructIso π B N₂ M₂')
    (a : N₁ →ₗ[B] N₂) (b : M₁' →ₗ[A'] M₂') (hab : IsMorphism π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b) :
    fibreProd π B φ₁ →ₗ[RingHom.pullback (algebraMap B A) π] fibreProd π B φ₂ :=
  fibreProdMap π B φ₁ φ₂ a b hab

/-- `F(a, b)` is given on underlying pairs by `(n, m') ↦ (a n, b m')`. -/
@[simp] theorem fibreProdMap_coe_apply {φ₁ : StructureEquiv π B N₁ M₁'}
    {φ₂ : StructureEquiv π B N₂ M₂'} {a : N₁ →ₗ[B] N₂} {b : M₁' →ₗ[A'] M₂'}
    (hab : IsMorphism π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b) (p : fibreProd π B φ₁) :
    (fibreProdMap π B φ₁ φ₂ a b hab p : N₂ × M₂') = (a p.val.1, b p.val.2) := rfl

-- Main Statement(s)

/-- **Theorem (Stacks Tag `08KJ`, Lemma 15.6.6).**  If both component maps
`a : N₁ → N₂` and `b : M'₁ → M'₂` of a morphism in the fibre product category are
surjective, then the induced `B'`-linear map `F(a, b)` is surjective. -/
@[stacks 08KJ]
theorem fibreProdMap_surjective
    (φ₁ : StructIso π B N₁ M₁') (φ₂ : StructIso π B N₂ M₂')
    (a : N₁ →ₗ[B] N₂) (b : M₁' →ₗ[A'] M₂') (hab : IsMorphism π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b)
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    Function.Surjective (Fmor π B N₁ N₂ M₁' M₂' φ₁ φ₂ a b hab) := by
  show Function.Surjective (fibreProdMap π B φ₁ φ₂ a b hab)
  -- Key surjectivity for the ideal-smul submodules: `b (I • ⊤) ⊇ I • ⊤`.
  have key_image : ((RingHom.ker π) • (⊤ : Submodule A' M₂')) ≤
      Submodule.map b ((RingHom.ker π) • (⊤ : Submodule A' M₁')) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hb]
  intro y₂
  -- destructure the target element
  obtain ⟨⟨n₂, m₂'⟩, hy₂⟩ := y₂
  simp only [mem_fibreProd] at hy₂
  -- pick a preimage of n₂ under a
  obtain ⟨n₁, rfl⟩ := ha n₂
  -- pick any lift of φ₁ (1 ⊗ n₁)
  obtain ⟨mt, hmt⟩ := Submodule.Quotient.mk_surjective _ (φ₁ ((1 : A) ⊗ₜ[B] n₁))
  -- compute mk m₂' = mk (b mt)
  -- hy₂ : φ₂ (1 ⊗ a n₁) = mk m₂'
  rw [hab.compat_tmul, ← hmt, QuotKerSMulTop.map_mk] at hy₂
  -- hy₂ : mk (b mt) = mk m₂'
  -- so m₂' - b mt ∈ I • ⊤
  have hmem : m₂' - b mt ∈ ((RingHom.ker π) • (⊤ : Submodule A' M₂')) := by
    rw [← Submodule.Quotient.eq]
    exact hy₂.symm
  -- find preimage j ∈ I • ⊤ in M₁'
  obtain ⟨j, hj, hbj⟩ := key_image hmem
  -- the desired element
  refine ⟨⟨(n₁, mt + j), ?_⟩, ?_⟩
  · -- (n₁, mt + j) ∈ fibreProd
    simp only [mem_fibreProd]
    rw [← hmt, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).mpr hj, add_zero]
  · -- F(a,b) sends it to (a n₁, m₂')
    apply Subtype.ext
    simp only [fibreProdMap_coe_apply]
    rw [Prod.ext_iff]
    refine ⟨rfl, ?_⟩
    show b (mt + j) = m₂'
    rw [map_add, hbj]
    abel

end

end MilnorPatching
