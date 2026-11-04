module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Modules over a trivial square-zero extension from a bilinear pairing

The construction of the system `Φ = (Λ, Jᵢ, (Mᵢ) → (Vᵢ))` of the discussion of Stacks 0CBE
enlarges `Λ` by variables `x_u` with `x_u x_{u'} = 0` and enlarges each `Mᵢ` by vectors
`ε_{i,u}` on which the new variables act by `x_u ε_{i,u} = ξ_u`. This file is the algebra of
one such enlargement, stripped of the indices: a ring `Λ ⊕ W` with `W` of square zero acting
on a module `M ⊕ V`, where the only non-obvious part of the action is a pairing
`W × V → M`, `(w, v) ↦ π w v`.

Both the ring and the module are *trivial* extensions — `W` and `V` are plain `Λ`-modules and
the ring is Mathlib's `TrivSqZeroExt Λ W` — so all the content is in the compatibility the
pairing has to satisfy: the action of `Λ ⊕ W` on `M ⊕ V` by

`(r, w) • (m, v) = (r • m + π w v, r • v)`

is associative exactly because `π` is `Λ`-bilinear, which is why the pairing is taken to be a
`LinearMap` into a `LinearMap` rather than a plain function of two arguments. In the situation
of Stacks 0CBE this is the reason the system has to be built inside the class of data whose
augmentation ideal annihilates the elements `ξ_u`: without that, `π` is not `Λ`-bilinear and
the enlarged module is not a module over the enlarged ring at all.

The module `M ⊕ V` is a type synonym `Paired π` for `M × V`, because the module structure
depends on `π`, which the type `M × V` does not mention.

## Main definitions

* `Stacks.SqZeroExtension.Paired`: the type `M × V`, with the module structure over
  `TrivSqZeroExt Λ W` determined by a `Λ`-bilinear pairing `π : W → V → M`.
* `Stacks.SqZeroExtension.Paired.mk`, `Stacks.SqZeroExtension.Paired.fst` and
  `Stacks.SqZeroExtension.Paired.snd`: its constructor and its two components.
* `Stacks.SqZeroExtension.Paired.map`: the `TrivSqZeroExt Λ W`-linear map between two such
  modules over *the same* ring attached to maps of the components commuting with the pairings.

## Main results

* `Stacks.SqZeroExtension.Paired.instModule`: `Paired π` is a module over
  `TrivSqZeroExt Λ W`; the bilinearity of `π` is what makes the action associative.
* `Stacks.SqZeroExtension.Paired.inr_smul`: **the divisibility identity.** A new variable
  `w ∈ W` acts on `(m, v)` by `π w v`, so every value of the pairing is divisible by the part
  of the ring which comes from `W`. This is the reason the step of Stacks 0CBE kills the
  obstruction: `ξ = x_u ε_{i,u}` lands in `J'ⱼ M'ᵢ`.
* `Stacks.SqZeroExtension.Paired.map_eq_zero_iff` and
  `Stacks.SqZeroExtension.Paired.surjective_map`: the kernel of such a map is computed
  componentwise and it is surjective as soon as both components are.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public section

namespace Stacks.SqZeroExtension

universe u

open TrivSqZeroExt

variable {Λ : Type u} [CommRing Λ]
  {W : Type u} [AddCommGroup W] [Module Λ W] [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W]
  {M V : Type u} [AddCommGroup M] [Module Λ M] [AddCommGroup V] [Module Λ V]

/-- The type `M × V`, to be given the module structure over the trivial square-zero extension
`TrivSqZeroExt Λ W` in which an element `w` of `W` sends `(m, v)` to `(π w v, 0)`. In the step
of Stacks 0CBE, `M` is a stage `Mᵢ` of the system, `V` is the span of the new vectors
`ε_{i,u}`, `W` is the span of the new variables `x_u`, and `π` pairs `x_u` with `ε_{i,u}` to
the image of `ξ_u` in `Mᵢ`. -/
def Paired (_π : W →ₗ[Λ] V →ₗ[Λ] M) : Type u := M × V

namespace Paired

variable {π : W →ₗ[Λ] V →ₗ[Λ] M}

/-- The additive group structure of `Paired π`, that of the product `M × V`. -/
instance instAddCommGroup : AddCommGroup (Paired π) := inferInstanceAs (AddCommGroup (M × V))

/-- The element of `Paired π` with components `m` and `v`. -/
def mk (π : W →ₗ[Λ] V →ₗ[Λ] M) (m : M) (v : V) : Paired π := (m, v)

/-- The `M`-component of an element of `Paired π`. -/
def fst (z : Paired π) : M := Prod.fst (α := M) (β := V) z

/-- The `V`-component of an element of `Paired π`. -/
def snd (z : Paired π) : V := Prod.snd (α := M) (β := V) z

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The `M`-component of `mk π m v` is `m`. -/
@[simp] theorem fst_mk (m : M) (v : V) : fst (mk π m v) = m := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The `V`-component of `mk π m v` is `v`. -/
@[simp] theorem snd_mk (m : M) (v : V) : snd (mk π m v) = v := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- An element of `Paired π` is the element built from its two components. -/
@[simp] theorem mk_fst_snd (z : Paired π) : mk π (fst z) (snd z) = z := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- Two elements of `Paired π` with the same components are equal. -/
@[ext] theorem ext {z z' : Paired π} (h₁ : fst z = fst z') (h₂ : snd z = snd z') : z = z' :=
  Prod.ext (α := M) (β := V) h₁ h₂

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The `M`-component of `0` is `0`. -/
@[simp] theorem fst_zero : fst (0 : Paired π) = 0 := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The `V`-component of `0` is `0`. -/
@[simp] theorem snd_zero : snd (0 : Paired π) = 0 := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The `M`-component of a sum is the sum of the `M`-components. -/
@[simp] theorem fst_add (z z' : Paired π) : fst (z + z') = fst z + fst z' := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The `V`-component of a sum is the sum of the `V`-components. -/
@[simp] theorem snd_add (z z' : Paired π) : snd (z + z') = snd z + snd z' := rfl

omit [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] in
/-- The element of `Paired π` with both components zero is `0`. -/
@[simp] theorem mk_zero_zero : mk π (0 : M) (0 : V) = 0 := rfl

/-- The module structure of `Paired π` over the trivial square-zero extension
`TrivSqZeroExt Λ W`: the pair `(r, w)` acts on `(m, v)` by `(r • m + π w v, r • v)`. The
`Λ`-bilinearity of the pairing `π` is exactly what makes this action associative. -/
instance instModule : Module (TrivSqZeroExt Λ W) (Paired π) where
  smul a z := mk π (a.fst • fst z + π a.snd (snd z)) (a.fst • snd z)
  one_smul z := by
    refine ext ?_ ?_
    · change (1 : TrivSqZeroExt Λ W).fst • fst z + π (1 : TrivSqZeroExt Λ W).snd (snd z) = fst z
      rw [fst_one, snd_one, one_smul, map_zero, LinearMap.zero_apply, add_zero]
    · change (1 : TrivSqZeroExt Λ W).fst • snd z = snd z
      rw [fst_one, one_smul]
  mul_smul a b z := by
    refine ext ?_ ?_
    · change (a * b).fst • fst z + π (a * b).snd (snd z)
        = a.fst • (b.fst • fst z + π b.snd (snd z)) + π a.snd (b.fst • snd z)
      rw [fst_mul, snd_mul, op_smul_eq_smul, map_add, LinearMap.add_apply, map_smul,
        map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_add, mul_smul,
        map_smul]
      abel
    · change (a * b).fst • snd z = a.fst • (b.fst • snd z)
      rw [fst_mul, mul_smul]
  smul_zero a := by
    refine ext ?_ ?_
    · change a.fst • fst (0 : Paired π) + π a.snd (snd (0 : Paired π)) = 0
      rw [fst_zero, snd_zero, smul_zero, map_zero, add_zero]
    · change a.fst • snd (0 : Paired π) = 0
      rw [snd_zero, smul_zero]
  smul_add a z z' := by
    refine ext ?_ ?_
    · change a.fst • fst (z + z') + π a.snd (snd (z + z'))
        = a.fst • fst z + π a.snd (snd z) + (a.fst • fst z' + π a.snd (snd z'))
      rw [fst_add, snd_add, smul_add, map_add]
      abel
    · change a.fst • snd (z + z') = a.fst • snd z + a.fst • snd z'
      rw [snd_add, smul_add]
  add_smul a b z := by
    refine ext ?_ ?_
    · change (a + b).fst • fst z + π (a + b).snd (snd z)
        = a.fst • fst z + π a.snd (snd z) + (b.fst • fst z + π b.snd (snd z))
      rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul, map_add,
        LinearMap.add_apply]
      abel
    · change (a + b).fst • snd z = a.fst • snd z + b.fst • snd z
      rw [TrivSqZeroExt.fst_add, add_smul]
  zero_smul z := by
    refine ext ?_ ?_
    · change (0 : TrivSqZeroExt Λ W).fst • fst z + π (0 : TrivSqZeroExt Λ W).snd (snd z) = 0
      rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, zero_smul, map_zero,
        LinearMap.zero_apply, add_zero]
    · change (0 : TrivSqZeroExt Λ W).fst • snd z = 0
      rw [TrivSqZeroExt.fst_zero, zero_smul]

/-- The `M`-component of `a • z` is `a.fst • fst z + π a.snd (snd z)`. -/
@[simp] theorem fst_smul (a : TrivSqZeroExt Λ W) (z : Paired π) :
    fst (a • z) = a.fst • fst z + π a.snd (snd z) := rfl

/-- The `V`-component of `a • z` is `a.fst • snd z`. -/
@[simp] theorem snd_smul (a : TrivSqZeroExt Λ W) (z : Paired π) :
    snd (a • z) = a.fst • snd z := rfl

/-- An element of `Λ` acts on `Paired π` componentwise. -/
theorem inl_smul (r : Λ) (z : Paired π) :
    (inl r : TrivSqZeroExt Λ W) • z = mk π (r • fst z) (r • snd z) := by
  refine ext ?_ ?_
  · rw [fst_smul, fst_mk, fst_inl, snd_inl, map_zero, LinearMap.zero_apply, add_zero]
  · rw [snd_smul, snd_mk, fst_inl]

/-- **The divisibility identity.** An element `w` of `W`, viewed in the square-zero extension
`TrivSqZeroExt Λ W`, sends `z` to the value of the pairing on `w` and the second component of
`z`. In the step of Stacks 0CBE this says `x_u ε_{i,u} = ξ_u`, which is what puts a given
element of a kernel `Ker(Mᵢ → Mⱼ)` into the submodule `J'ⱼ M'ᵢ` of the enlarged system. -/
theorem inr_smul (w : W) (z : Paired π) :
    (inr w : TrivSqZeroExt Λ W) • z = mk π (π w (snd z)) 0 := by
  refine ext ?_ ?_
  · rw [fst_smul, fst_mk, fst_inr, snd_inr, zero_smul, zero_add]
  · rw [snd_smul, snd_mk, fst_inr, zero_smul]

section Map

variable {M₁ M₂ V₁ V₂ : Type u} [AddCommGroup M₁] [Module Λ M₁] [AddCommGroup M₂]
  [Module Λ M₂] [AddCommGroup V₁] [Module Λ V₁] [AddCommGroup V₂] [Module Λ V₂]
  {π₁ : W →ₗ[Λ] V₁ →ₗ[Λ] M₁} {π₂ : W →ₗ[Λ] V₂ →ₗ[Λ] M₂}

/-- The map of modules over `TrivSqZeroExt Λ W` attached to `Λ`-linear maps `p` and `q` of the
two components which commute with the pairings. In the step of Stacks 0CBE this is the
transition morphism `M'ᵢ → M'ⱼ`: both are modules over the *same* enlarged ring, so the
transition is linear rather than merely semilinear. -/
def map (p : M₁ →ₗ[Λ] M₂) (q : V₁ →ₗ[Λ] V₂) (h : ∀ (w : W) (v : V₁), p (π₁ w v) = π₂ w (q v)) :
    Paired π₁ →ₗ[TrivSqZeroExt Λ W] Paired π₂ where
  toFun z := mk π₂ (p (fst z)) (q (snd z))
  map_add' z z' := by
    refine ext ?_ ?_ <;> simp
  map_smul' a z := by
    refine ext ?_ ?_ <;> simp [h]

/-- The `M`-component of `map p q h z` is `p` applied to the `M`-component of `z`. -/
@[simp] theorem fst_map (p : M₁ →ₗ[Λ] M₂) (q : V₁ →ₗ[Λ] V₂)
    (h : ∀ (w : W) (v : V₁), p (π₁ w v) = π₂ w (q v)) (z : Paired π₁) :
    fst (map p q h z) = p (fst z) := rfl

/-- The `V`-component of `map p q h z` is `q` applied to the `V`-component of `z`. -/
@[simp] theorem snd_map (p : M₁ →ₗ[Λ] M₂) (q : V₁ →ₗ[Λ] V₂)
    (h : ∀ (w : W) (v : V₁), p (π₁ w v) = π₂ w (q v)) (z : Paired π₁) :
    snd (map p q h z) = q (snd z) := rfl

/-- The kernel of such a map is computed componentwise. -/
theorem map_eq_zero_iff (p : M₁ →ₗ[Λ] M₂) (q : V₁ →ₗ[Λ] V₂)
    (h : ∀ (w : W) (v : V₁), p (π₁ w v) = π₂ w (q v)) {z : Paired π₁} :
    map p q h z = 0 ↔ p (fst z) = 0 ∧ q (snd z) = 0 := by
  refine ⟨fun hz => ⟨?_, ?_⟩, fun hz => ext ?_ ?_⟩
  · rw [← fst_map p q h z, hz, fst_zero]
  · rw [← snd_map p q h z, hz, snd_zero]
  · rw [fst_map, fst_zero, hz.1]
  · rw [snd_map, snd_zero, hz.2]

/-- Such a map is surjective as soon as both of its components are. -/
theorem surjective_map (p : M₁ →ₗ[Λ] M₂) (q : V₁ →ₗ[Λ] V₂)
    (h : ∀ (w : W) (v : V₁), p (π₁ w v) = π₂ w (q v)) (hp : Function.Surjective p)
    (hq : Function.Surjective q) : Function.Surjective (map p q h) := fun z => by
  obtain ⟨m, hm⟩ := hp (fst z)
  obtain ⟨v, hv⟩ := hq (snd z)
  exact ⟨mk π₁ m v, ext (by rw [fst_map, fst_mk, hm]) (by rw [snd_map, snd_mk, hv])⟩

end Map

end Paired

end Stacks.SqZeroExtension

end
