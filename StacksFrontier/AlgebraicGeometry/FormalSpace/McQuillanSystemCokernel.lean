module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemStep
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The cokernel-filling step of the system of Stacks 0CBE, and the obstruction to iterating

The claim of the discussion of Stacks 0CBE asks for a system
`Φ = (Λ, Jᵢ ⊂ Λ, (Mᵢ))` with `Mⱼ = Mᵢ/Jⱼ Mᵢ` for `i > j`. That equality has two halves: the
transition `Mᵢ/JⱼMᵢ → Mⱼ` must be injective, and it must be **onto**. The one-step extension
`Φ ↦ Φ'` of `StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemStep` is the first half
only, and it destroys the second: `M'ⱼ` gains a vector `ε_{j,u}` for every `u` with `s(u) ≥ j`
while the image of `M'ᵢ` carries only those with `s(u) ≥ i`. So a second, cokernel-filling
step is needed, and Stacks does not give one. This file is that step, and the exact reason the
two steps cannot be alternated.

## The step

For every stage `b` and every `y ∈ M_b` a new generator `e_{b,y}` is adjoined to each stage
`i > b`; the transition `Mᵢ → Mⱼ` keeps `e_{b,y}` when `b < j` and sends it to the image of
`y` in `Mⱼ` when `j ≤ b`. In particular `e_{j,y} ∈ M^†ᵢ` maps to `y` for every `i > j`, which
is exactly the missing surjectivity. The new generators cannot span free `Λ`-modules: for
`b < j < i` the condition `Jⱼ M^†ᵢ ⊂ Ker(M^†ᵢ → M^†ⱼ)` forces `Jⱼ` to kill `e_{b,y}` at the
stage `j`, so the generator at the stage `i` spans `Λ/Jᵢ`, which the antitonicity of the
ideals makes compatible with the transitions. Three of the required properties then hold for
one and the same reason, namely that each `Mᵢ` is a module over `Λ/Jᵢ` — the condition
`Annihilated` below, which is how Stacks 0CBE states the datum (`Λ/Jᵢ ⊕ Mᵢ` is a
`Λ/Jᵢ`-algebra) but which `IsSystem` does not record. The index is taken linearly ordered,
because the transition of a generator is defined by the dichotomy `b < j` or `j ≤ b`.

## The obstruction to alternating the two steps

`IsSystem` carries one condition beyond those of Stacks: the augmentation ideal annihilates
every kernel `Ker(Mᵢ → Mⱼ)`. That condition is not decoration — without it the pairing
`x_u ε_{i,u} = ξ_u` is not `Λ`-bilinear and `M'ᵢ` is not a module over `Λ'` at all, so it is
what makes the step `Φ ↦ Φ'` well defined. The cokernel-filling step **destroys it**, and
`smul_eq_zero_of_isSystem_fill` says exactly how much: if `Φ^†` satisfies it for one pair
`j < i`, then the augmentation ideal annihilates the whole of `Mᵢ`. The reason is forced by
surjectivity alone: `y := -tr(m)` acquires a generator `e_{j,y}` with
`tr(m + e_{j,y}) = 0`, and the two summands of `m + e_{j,y}` are scaled separately, so the
condition applied to this kernel element says `a · m = 0` for every `m`.

And `augExt_smul_mk_ne_zero` says that the step `Φ ↦ Φ'` always produces a `Φ'` violating
that conclusion as soon as it does anything at all: `x_u` lies in the augmentation ideal of
`Λ'` and `x_u ε_{s(u),u} = ξ_u ≠ 0`. Putting the two together, `not_isSystem_fill_ext`: for
any system with a nonzero kernel element, the cokernel-filling step applied to `Φ'` is **not**
an `IsSystem`, so the step `Φ ↦ Φ'` cannot be applied again. The iteration of the discussion
of Stacks 0CBE therefore cannot be run by alternating the kernel-killing step with any
cokernel-filling construction of this shape; the lemma itself is proved, by a system with
idempotent rather than square-zero ideals, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverMcQuillan`.

What *is* achieved is everything Stacks itself demands of a system, plus the surjectivity:
`isStacksSystem_fill`, `annihilated_fill` and `surjective_trFill`. So the cokernel half of the
claim is not the difficulty; the difficulty is concentrated in making the kernel-killing step
well defined without asking the augmentation ideal to annihilate the kernels, i.e. in finding
an enlargement of `Λ` other than `Λ ⊕ K^{(U)}` whose ideals `J'ₖ` are still of square zero.
There is none: `StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemEnlargement` shows
that *every* enlargement of `Λ` which makes the kernels divisible by square-zero ideals forces
`Jⱼ` to annihilate `Ker(Mᵢ → Mⱼ)`, and that the obstruction below survives with that weaker
condition in place of the one on the augmentation ideal.

One further caveat, recorded here because it is invisible to `IsSystem`: the datum of Stacks
0CBE also carries a map to a system `(Vᵢ)` of vector spaces with `lim Vᵢ = 0`. A generator
present at *every* stage above `b` would have to be sent to a compatible family in `(Vᵢ)` over
the cofinal set `{i | b < i}` lifting its image in `V_b`, i.e. to an element of `lim Vᵢ = 0`;
so carrying the map to `(Vᵢ)` requires capping each generator at one stage, after which a
single step covers the old module `Mⱼ` but not the new generators, and only the colimit of the
iteration has surjective transitions. The uncapped construction below proves the stronger
statement about `IsSystem` data; the obstruction above is unaffected either way, since it uses
one generator at one pair of stages.

## Main definitions

* `Stacks.CBESystem.IsStacksSystem`: the datum of Stacks 0CBE exactly as the source states it,
  i.e. `IsSystem` without the condition on the augmentation ideal.
* `Stacks.CBESystem.Annihilated`: each `Mᵢ` is a module over `Λ/Jᵢ`.
* `Stacks.CBESystem.Gen`, `Stacks.CBESystem.GenAt`: the new generators `e_{b,y}` and those of
  them present at a stage.
* `Stacks.CBESystem.Fill`: the stage module `M^†ᵢ = Mᵢ ⊕ (Λ/Jᵢ)^{(GenAt i)}`.
* `Stacks.CBESystem.trFill`: the transition maps of the filled system.

## Main results

* `Stacks.CBESystem.isStacksSystem_fill`: **the filled system is again a system in the sense of
  Stacks 0CBE**, and `Stacks.CBESystem.annihilated_fill` that its stages are again modules over
  the `Λ/Jᵢ`.
* `Stacks.CBESystem.surjective_trFill`: **its transition maps are surjective**, which is the
  half of `Mⱼ = Mᵢ/JⱼMᵢ` the step of Stacks 0CBE does not provide.
* `Stacks.CBESystem.trFill_inl`: `Φ → Φ^†` is a morphism of systems.
* `Stacks.CBESystem.smul_eq_zero_of_isSystem_fill` and
  `Stacks.CBESystem.not_isSystem_fill`: **the obstruction.** If the filled system satisfies the
  condition on the augmentation ideal for one pair of stages, that ideal annihilates the whole
  stage module.
* `Stacks.CBESystem.augExt_smul_mk_ne_zero` and
  `Stacks.CBESystem.not_isSystem_fill_ext`: **the two steps do not alternate.** The
  kernel-killing step produces a stage module not annihilated by the augmentation ideal, so the
  cokernel-filling step applied to its output is not an `IsSystem`.
* `Stacks.CBESystem.exists_isSystem_with_nonzero_ker`: the hypotheses of the last statement are
  jointly satisfiable, so the obstruction is not vacuous.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public section

namespace Stacks.CBESystem

universe u

open TrivSqZeroExt Stacks.SqZeroExtension

noncomputable section

/-! ### The datum of Stacks 0CBE, and the stage-module condition -/

section Core

variable {K Λ I : Type u} [Field K] [CommRing Λ] [Preorder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]

/-- The datum `Φ = (Λ, Jᵢ ⊂ Λ, (Mᵢ))` of the discussion of Stacks 0CBE with exactly the
properties the source asks of it: `Λ` is an augmented `K`-algebra, the `Jᵢ` are square-zero
ideals decreasing along the index, and the `Mᵢ` form an inverse system of `Λ`-modules whose
transitions kill `Jⱼ Mᵢ` for `i > j`.

This is `Stacks.CBESystem.IsSystem` with its last condition — that the augmentation ideal
annihilate the kernels, which the source does not state and which is what makes the step
`Φ ↦ Φ'` well defined — dropped. The cokernel-filling step of this file preserves this weaker
datum and, by `smul_eq_zero_of_isSystem_fill`, cannot preserve the stronger one. -/
structure IsStacksSystem (aug : Λ →+* K) (unit : K →+* Λ) (J : I → Ideal Λ)
    (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) : Prop where
  /-- The augmentation is a section of the unit, i.e. `Λ` is an augmented `K`-algebra. -/
  aug_unit : ∀ c : K, aug (unit c) = c
  /-- The transition map of an index to itself is the identity. -/
  tr_self : ∀ {i : I} (m : M i), tr (le_refl i) m = m
  /-- The transition maps compose. -/
  tr_tr : ∀ {i j k : I} (hji : j ≤ i) (hkj : k ≤ j) (m : M i),
    tr hkj (tr hji m) = tr (hkj.trans hji) m
  /-- Each ideal `Jᵢ` is of square zero. -/
  sq_zero : ∀ i : I, J i * J i = ⊥
  /-- The ideals decrease along the index. -/
  antitone : ∀ {i j : I}, j ≤ i → J i ≤ J j
  /-- `Jⱼ Mᵢ` is killed by the transition map `Mᵢ → Mⱼ` for `i > j`. -/
  smul_tr : ∀ {i j : I} (hji : j < i) {a : Λ}, a ∈ J j → ∀ m : M i, tr hji.le (a • m) = 0

variable {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

/-- A system in the sense of this file's `IsSystem` is in particular one in the sense of the
source. -/
theorem IsSystem.toIsStacksSystem (h : IsSystem aug unit J tr) :
    IsStacksSystem aug unit J tr where
  aug_unit := h.aug_unit
  tr_self := h.tr_self
  tr_tr := h.tr_tr
  sq_zero := h.sq_zero
  antitone := h.antitone
  smul_tr := h.smul_tr

/-- Each stage `Mᵢ` of the datum is a module over `Λ/Jᵢ`, which is how Stacks 0CBE states it:
the stage ring `Λ/Jᵢ ⊕ Mᵢ` is a `Λ/Jᵢ`-algebra. The condition is not part of `IsSystem`, it is
satisfied by the initial datum, it is preserved by the one-step extension
(`annihilated_ext`), and it is what the cokernel-filling step of this file runs on. -/
def Annihilated (J : I → Ideal Λ) (M : I → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module Λ (M i)] : Prop :=
  ∀ (i : I) ⦃a : Λ⦄, a ∈ J i → ∀ m : M i, a • m = 0

/-- The initial datum `Φ₀ = (K, (0), (Vᵢ))` has `Λ/Jᵢ = K` acting on `Vᵢ`. -/
theorem annihilated_initial {K I : Type u} [Field K] [Preorder I] {V : I → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] :
    Annihilated (fun _ : I => (⊥ : Ideal K)) V := by
  intro i a ha m
  rw [show a = (0 : K) from (Submodule.mem_bot K).mp ha, zero_smul]

/-- **The one-step extension preserves the stage-module condition.** The new variables are
annihilated by the augmentation ideal, hence by each `Jᵢ`, and a value of the pairing with a
coefficient supported in `{u | i ≤ t(u)}` has already died at the stage `i`. -/
theorem annihilated_ext (h : IsSystem aug unit J tr) (hann : Annihilated J M) :
    Annihilated (Jext h) (fun i => Paired (pair h i)) := by
  intro i x hx z
  refine Paired.ext ?_ ?_
  · rw [Paired.fst_smul, Paired.fst_zero, hann i hx.1 (Paired.fst z), zero_add, pair_apply]
    have h0 := tr_pairFun_eq_zero h (le_refl i) (TrivSqZeroExt.snd x) (Paired.snd z) hx.2
    rwa [h.tr_self] at h0
  · rw [Paired.snd_smul, Paired.snd_zero, AugSpan.smul_eq, h.aug_eq_zero hx.1, zero_smul]

end Core

/-! ### The new generators and the filled stage modules -/

section Fill

variable {K Λ I : Type u} [Field K] [CommRing Λ] [LinearOrder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
  {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

/-- An element of some stage of the system, together with the stage it lives at: the datum of
one cokernel-filling generator `e_{b,y}`, which is adjoined to every stage above `b` and maps
to `y` at the stage `b`. -/
structure Gen (M : I → Type u) : Type u where
  /-- The stage the element to be lifted lives at. -/
  base : I
  /-- The element to be lifted. -/
  elt : M base

/-- The generators present at the stage `i`, namely those whose base is strictly below it. -/
abbrev GenAt (M : I → Type u) (i : I) : Type u := {g : Gen M // g.base < i}

/-- The stage module of the cokernel-filling step: `M^†ᵢ = Mᵢ ⊕ (Λ/Jᵢ)^{(GenAt i)}`. Each new
generator spans `Λ/Jᵢ` rather than `Λ`, which is what the condition `Jⱼ M^†ᵢ ⊂ Ker(M^†ᵢ → M^†ⱼ)`
forces, and the antitonicity of the ideals is what makes the coefficients transition. -/
abbrev Fill (J : I → Ideal Λ) (M : I → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module Λ (M i)] (i : I) : Type u :=
  M i × (GenAt M i →₀ (Λ ⧸ J i))

/-! ### Two auxiliary facts about the coefficient modules -/

/-- An element of an ideal annihilates the quotient by it. -/
theorem smul_quot_eq_zero {p : Ideal Λ} {a : Λ} (ha : a ∈ p) (c : Λ ⧸ p) : a • c = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective p c
  rw [← map_smul p.mkQ a b, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  exact Ideal.mul_mem_right b p ha

/-- An element of an ideal annihilates every family of elements of the quotient by it. -/
theorem smul_finsupp_quot_eq_zero {p : Ideal Λ} {a : Λ} (ha : a ∈ p) {α : Type u}
    (w : α →₀ (Λ ⧸ p)) : a • w = 0 := by
  ext g
  rw [Finsupp.smul_apply, smul_quot_eq_zero ha, Finsupp.zero_apply]

/-! ### The transition maps of the filled system -/

/-- The reduction `Λ/Jᵢ → Λ/Jⱼ` of coefficients along `j ≤ i`, available because the ideals
decrease. -/
def fillCoeff (hS : IsStacksSystem aug unit J tr) {i j : I} (hji : j ≤ i) :
    (Λ ⧸ J i) →ₗ[Λ] (Λ ⧸ J j) :=
  Submodule.liftQ _ (J j).mkQ (by rw [Submodule.ker_mkQ]; exact hS.antitone hji)

/-- The reduction `Λ/Jᵢ → Λ/Jⱼ` sends the class of `a` to the class of `a`. -/
@[simp] theorem fillCoeff_mk (hS : IsStacksSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (a : Λ) :
    fillCoeff hS hji (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := by
  rw [fillCoeff, Submodule.liftQ_apply, Submodule.mkQ_apply]

/-- The reduction of coefficients along `i ≤ i` is the identity. -/
theorem fillCoeff_self (hS : IsStacksSystem aug unit J tr) {i : I} (c : Λ ⧸ J i) :
    fillCoeff hS (le_refl i) c = c := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (J i) c
  rw [Submodule.mkQ_apply, fillCoeff_mk]

/-- The reductions of coefficients compose: reducing along `j ≤ i` and then along `k ≤ j` is
reducing along `k ≤ i`. -/
theorem fillCoeff_trans (hS : IsStacksSystem aug unit J tr) {i j k : I} (hji : j ≤ i)
    (hkj : k ≤ j) (c : Λ ⧸ J i) :
    fillCoeff hS hkj (fillCoeff hS hji c) = fillCoeff hS (hkj.trans hji) c := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (J i) c
  rw [Submodule.mkQ_apply, fillCoeff_mk, fillCoeff_mk, fillCoeff_mk]

/-- The contribution of one new generator to the old part of a lower stage: the generator
`e_{b,y}` present at the stage `i` is sent to the image of `y` in `Mⱼ` whenever `j ≤ b`. It is
well defined on `Λ/Jᵢ` because `Jᵢ ⊂ J_b` annihilates `M_b`. -/
def fillSpan (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M) {i j : I}
    (g : GenAt M i) (hjb : j ≤ g.1.base) : (Λ ⧸ J i) →ₗ[Λ] M j :=
  Submodule.liftQ _ (LinearMap.toSpanSingleton Λ (M j) (tr hjb g.1.elt)) (fun a ha => by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul,
      hann g.1.base (hS.antitone g.2.le ha) g.1.elt, map_zero])

/-- The map `fillSpan` sends the class of `a` to `a` times the image in `Mⱼ` of the element
lifted by the generator. -/
@[simp] theorem fillSpan_mk (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (g : GenAt M i) (hjb : j ≤ g.1.base) (a : Λ) :
    fillSpan hS hann g hjb (Submodule.Quotient.mk a) = a • tr hjb g.1.elt := by
  rw [fillSpan, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]

/-- The part of the transition map which lands in the old stage module `Mⱼ`: the generators
whose base is at or above `j` are sent there, the others are kept. -/
def fillOld (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M) {i : I} (j : I) :
    (GenAt M i →₀ (Λ ⧸ J i)) →ₗ[Λ] M j :=
  Finsupp.lsum Λ fun g => if hb : g.1.base < j then 0 else fillSpan hS hann g (not_lt.mp hb)

/-- The part of the transition map which lands in the new generators of the stage `j`: the
generators whose base is strictly below `j` are kept, with their coefficients reduced. -/
def fillNew (hS : IsStacksSystem aug unit J tr) {i j : I} (hji : j ≤ i) :
    (GenAt M i →₀ (Λ ⧸ J i)) →ₗ[Λ] (GenAt M j →₀ (Λ ⧸ J j)) :=
  Finsupp.lsum Λ fun g => if hb : g.1.base < j then
    (Finsupp.lsingle (⟨g.1, hb⟩ : GenAt M j)).comp (fillCoeff hS hji) else 0

/-- A generator whose base is strictly below `j` contributes nothing to the old part of the
stage `j`. -/
theorem fillOld_single_of_lt (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (g : GenAt M i) (hb : g.1.base < j) (c : Λ ⧸ J i) :
    fillOld hS hann j (Finsupp.single g c) = 0 := by
  rw [fillOld, Finsupp.lsum_single, dite_eq_left hb, LinearMap.zero_apply]

/-- A generator whose base is at or above `j` contributes `fillSpan` of its coefficient to the
old part of the stage `j`. -/
theorem fillOld_single_of_le (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (g : GenAt M i) (hb : ¬ g.1.base < j) (c : Λ ⧸ J i) :
    fillOld hS hann j (Finsupp.single g c) = fillSpan hS hann g (not_lt.mp hb) c := by
  rw [fillOld, Finsupp.lsum_single, dite_eq_right hb]

/-- A generator whose base is strictly below `j` is sent to the same generator of the stage `j`,
with its coefficient reduced. -/
theorem fillNew_single_of_lt (hS : IsStacksSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (g : GenAt M i) (hb : g.1.base < j) (c : Λ ⧸ J i) :
    fillNew hS hji (Finsupp.single g c)
      = Finsupp.single (⟨g.1, hb⟩ : GenAt M j) (fillCoeff hS hji c) := by
  rw [fillNew, Finsupp.lsum_single, dite_eq_left hb]
  rfl

/-- A generator whose base is at or above `j` contributes nothing to the new generators of the
stage `j`. -/
theorem fillNew_single_of_le (hS : IsStacksSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (g : GenAt M i) (hb : ¬ g.1.base < j) (c : Λ ⧸ J i) :
    fillNew hS hji (Finsupp.single g c) = 0 := by
  rw [fillNew, Finsupp.lsum_single, dite_eq_right hb, LinearMap.zero_apply]

/-- The transition map of the filled system: the given transition on the old part, the
generators with base below `j` kept, and those with base at or above `j` replaced by the image
of the element they lift. -/
def trFill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M) {i j : I}
    (hji : j ≤ i) : Fill J M i →ₗ[Λ] Fill J M j :=
  LinearMap.prod
    ((tr hji).comp (LinearMap.fst Λ (M i) (GenAt M i →₀ (Λ ⧸ J i))) +
      (fillOld hS hann j).comp (LinearMap.snd Λ (M i) (GenAt M i →₀ (Λ ⧸ J i))))
    ((fillNew hS hji).comp (LinearMap.snd Λ (M i) (GenAt M i →₀ (Λ ⧸ J i))))

/-- The old part of `trFill` is the given transition on the old part plus `fillOld` of the
new part. -/
@[simp] theorem fst_trFill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (hji : j ≤ i) (z : Fill J M i) :
    (trFill hS hann hji z).1 = tr hji z.1 + fillOld hS hann j z.2 := rfl

/-- The new part of `trFill` is `fillNew` of the new part. -/
@[simp] theorem snd_trFill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (hji : j ≤ i) (z : Fill J M i) :
    (trFill hS hann hji z).2 = fillNew hS hji z.2 := rfl

/-- The map `Mᵢ → M^†ᵢ` commutes with the transitions: `Φ → Φ^†` is a morphism of systems. -/
theorem trFill_inl (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M) {i j : I}
    (hji : j ≤ i) (m : M i) :
    trFill hS hann hji ((m, 0) : Fill J M i) = ((tr hji m, 0) : Fill J M j) := by
  refine Prod.ext ?_ ?_
  · rw [fst_trFill, map_zero, add_zero]
  · rw [snd_trFill, map_zero]

/-! ### The filled system is a system -/

/-- **The cokernel-filling step preserves the stage-module condition.** -/
theorem annihilated_fill (hann : Annihilated J M) : Annihilated J (Fill J M) := by
  intro i a ha z
  refine Prod.ext ?_ ?_
  · exact hann i ha z.1
  · exact smul_finsupp_quot_eq_zero ha z.2

/-- The generators present at the stage `i` contribute nothing to the old part of that same
stage. -/
theorem fillOld_self (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M) {i : I}
    (w : GenAt M i →₀ (Λ ⧸ J i)) : fillOld hS hann i w = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add f g hf hg => rw [map_add, hf, hg, add_zero]
  | single g c => exact fillOld_single_of_lt hS hann g g.2 c

/-- The map `fillNew` along `i ≤ i` is the identity. -/
theorem fillNew_self (hS : IsStacksSystem aug unit J tr) {i : I}
    (w : GenAt M i →₀ (Λ ⧸ J i)) : fillNew hS (le_refl i) w = w := by
  induction w using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add f g hf hg => rw [map_add, hf, hg]
  | single g c => rw [fillNew_single_of_lt hS (le_refl i) g g.2 c, fillCoeff_self]

/-- The old parts are compatible with composition: for `k ≤ j ≤ i`, transporting `fillOld` at
`j` down to `k` and adding `fillOld` at `k` of `fillNew` gives `fillOld` at `k`. -/
theorem fillOld_trans (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j k : I} (hji : j ≤ i) (hkj : k ≤ j) (w : GenAt M i →₀ (Λ ⧸ J i)) :
    tr hkj (fillOld hS hann j w) + fillOld hS hann k (fillNew hS hji w)
      = fillOld hS hann k w := by
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero]
  | add f g hf hg =>
    rw [map_add, map_add, map_add, map_add, map_add, ← hf, ← hg]
    abel
  | single g c =>
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (J i) c
    rw [Submodule.mkQ_apply]
    rcases lt_or_ge g.1.base k with hbk | hkb
    · have hbj : g.1.base < j := lt_of_lt_of_le hbk hkj
      rw [fillOld_single_of_lt hS hann g hbj, map_zero,
        fillNew_single_of_lt hS hji g hbj, fillCoeff_mk,
        fillOld_single_of_lt hS hann (⟨g.1, hbj⟩ : GenAt M j) hbk,
        fillOld_single_of_lt hS hann g hbk, add_zero]
    · rcases lt_or_ge g.1.base j with hbj | hjb
      · rw [fillOld_single_of_lt hS hann g hbj, map_zero,
          fillNew_single_of_lt hS hji g hbj, fillCoeff_mk,
          fillOld_single_of_le hS hann (⟨g.1, hbj⟩ : GenAt M j) (not_lt.mpr hkb),
          fillSpan_mk, fillOld_single_of_le hS hann g (not_lt.mpr hkb), fillSpan_mk,
          zero_add]
      · rw [fillNew_single_of_le hS hji g (not_lt.mpr hjb), map_zero,
          fillOld_single_of_le hS hann g (not_lt.mpr hjb), fillSpan_mk,
          fillOld_single_of_le hS hann g (not_lt.mpr hkb), fillSpan_mk, add_zero,
          map_smul, hS.tr_tr]

/-- The maps `fillNew` compose: along `j ≤ i` and then `k ≤ j` is along `k ≤ i`. -/
theorem fillNew_trans (hS : IsStacksSystem aug unit J tr) {i j k : I} (hji : j ≤ i)
    (hkj : k ≤ j) (w : GenAt M i →₀ (Λ ⧸ J i)) :
    fillNew hS hkj (fillNew hS hji w) = fillNew hS (hkj.trans hji) w := by
  induction w using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single g c =>
    rcases lt_or_ge g.1.base k with hbk | hkb
    · have hbj : g.1.base < j := lt_of_lt_of_le hbk hkj
      rw [fillNew_single_of_lt hS hji g hbj, fillNew_single_of_lt hS hkj _ hbk,
        fillNew_single_of_lt hS (hkj.trans hji) g hbk, fillCoeff_trans]
    · rcases lt_or_ge g.1.base j with hbj | hjb
      · rw [fillNew_single_of_lt hS hji g hbj,
          fillNew_single_of_le hS hkj _ (not_lt.mpr hkb),
          fillNew_single_of_le hS (hkj.trans hji) g (not_lt.mpr hkb)]
      · rw [fillNew_single_of_le hS hji g (not_lt.mpr hjb), map_zero,
          fillNew_single_of_le hS (hkj.trans hji) g (not_lt.mpr hkb)]

/-- **The cokernel-filling step of a system of Stacks 0CBE is again such a system.** The ring
and the ideals are untouched, so only the inverse-system axioms and the condition
`Jⱼ M^†ᵢ ⊂ Ker(M^†ᵢ → M^†ⱼ)` are at issue; the latter holds for the new generators because the
generator at the stage `i` spans `Λ/Jᵢ` and because each `Mᵢ` is a module over `Λ/Jᵢ`. -/
theorem isStacksSystem_fill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M) :
    IsStacksSystem (M := Fill J M) aug unit J (fun {_ _} hji => trFill hS hann hji) where
  aug_unit := hS.aug_unit
  tr_self {i} z := by
    refine Prod.ext ?_ ?_
    · rw [fst_trFill, hS.tr_self, fillOld_self, add_zero]
    · rw [snd_trFill, fillNew_self]
  tr_tr {i j k} hji hkj z := by
    refine Prod.ext ?_ ?_
    · rw [fst_trFill, fst_trFill, snd_trFill, fst_trFill, map_add, hS.tr_tr,
        add_assoc, fillOld_trans]
    · rw [snd_trFill, snd_trFill, snd_trFill, fillNew_trans]
  sq_zero := hS.sq_zero
  antitone := hS.antitone
  smul_tr {i j} hji {a} ha z := by
    refine Prod.ext ?_ ?_
    · rw [fst_trFill, Prod.smul_fst, Prod.smul_snd, hS.smul_tr hji ha z.1, map_smul,
        hann j ha _, add_zero, Prod.fst_zero]
    · rw [snd_trFill, Prod.smul_snd, map_smul, smul_finsupp_quot_eq_zero ha, Prod.snd_zero]

/-! ### The transitions of the filled system are surjective -/

/-- For `j < i` the map `fillNew` onto the new generators of the stage `j` is surjective. -/
theorem surjective_fillNew (hS : IsStacksSystem aug unit J tr) {i j : I} (hji : j < i) :
    Function.Surjective (fillNew hS hji.le) := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | single g' c =>
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (J j) c
    refine ⟨Finsupp.single (⟨g'.1, lt_trans g'.2 hji⟩ : GenAt M i)
      (Submodule.Quotient.mk b), ?_⟩
    rw [fillNew_single_of_lt hS hji.le _ g'.2, fillCoeff_mk, Submodule.mkQ_apply]

/-- The transition of `m` plus the generator `e_{j,y}` of the stage `i` is `tr m + y`. -/
private theorem trFill_add_single_base (hS : IsStacksSystem aug unit J tr)
    (hann : Annihilated J M) {i j : I} (hji : j < i) (m : M i) (y : M j) :
    trFill hS hann hji.le
        ((m, Finsupp.single (⟨⟨j, y⟩, hji⟩ : GenAt M i) (Submodule.Quotient.mk 1))
          : Fill J M i)
      = ((tr hji.le m + y, 0) : Fill J M j) := by
  refine Prod.ext ?_ ?_
  · rw [fst_trFill, fillOld_single_of_le hS hann _ (lt_irrefl j), fillSpan_mk, one_smul,
      hS.tr_self]
  · rw [snd_trFill, fillNew_single_of_le hS hji.le _ (lt_irrefl j)]

/-- **The transitions of the filled system are surjective**, which is the half of
`Mⱼ = Mᵢ/JⱼMᵢ` that the one-step extension of Stacks 0CBE does not give: an element `y` of the
old stage `Mⱼ` is the image of the generator `e_{j,y}`, and a new generator of the stage `j` is
the image of itself. -/
theorem surjective_trFill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (hji : j < i) : Function.Surjective (trFill hS hann hji.le) := by
  intro v
  obtain ⟨w, hw⟩ := surjective_fillNew hS hji v.2
  refine ⟨(0, w) + (0, Finsupp.single (⟨⟨j, v.1 - fillOld hS hann j w⟩, hji⟩ : GenAt M i)
    (Submodule.Quotient.mk 1)), ?_⟩
  rw [map_add, trFill_add_single_base, map_zero, zero_add]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, fst_trFill, map_zero, zero_add, add_sub_cancel]
  · rw [Prod.snd_add, snd_trFill, hw, add_zero]

/-- The explicit compatible lift: for `j < i` the generator `e_{j,y}` of the stage `i` is a
preimage of `y ∈ Mⱼ`. This is the element the step is built to provide. -/
theorem trFill_single_base (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (hji : j < i) (y : M j) :
    trFill hS hann hji.le
        ((0, Finsupp.single (⟨⟨j, y⟩, hji⟩ : GenAt M i) (Submodule.Quotient.mk 1))
          : Fill J M i)
      = ((y, 0) : Fill J M j) := by
  rw [trFill_add_single_base, map_zero, zero_add]

/-! ### The obstruction: the filled system is not a system in the sense of `IsSystem` -/

/-- **The obstruction.** Suppose the filled system satisfies the condition of `IsSystem` that
the augmentation ideal annihilate the kernels, for a single pair of stages `j < i`. Then that
ideal annihilates the whole of `Mᵢ`.

The reason is surjectivity alone. Given `m ∈ Mᵢ`, the element `y = -tr(m)` of `Mⱼ` has a
generator `e_{j,y}` at the stage `i`, and `m + e_{j,y}` lies in the kernel of the transition.
The two summands of `M^†ᵢ = Mᵢ ⊕ (Λ/Jᵢ)^{(GenAt i)}` are scaled separately, so the condition
applied to this kernel element says `a · m = 0`. -/
theorem smul_eq_zero_of_isSystem_fill (hS : IsStacksSystem aug unit J tr)
    (hann : Annihilated J M)
    (hF : IsSystem (M := Fill J M) aug unit J (fun {_ _} hji => trFill hS hann hji))
    {i j : I} (hji : j < i) {a : Λ} (ha : aug a = 0) (m : M i) : a • m = 0 := by
  have hker : trFill hS hann hji.le
      ((m, Finsupp.single (⟨⟨j, -(tr hji.le m)⟩, hji⟩ : GenAt M i)
        (Submodule.Quotient.mk 1)) : Fill J M i) = 0 := by
    rw [trFill_add_single_base, add_neg_cancel, Prod.mk_zero_zero]
  have hz := hF.aug_ann hji ha _ hker
  have := congrArg Prod.fst hz
  rwa [Prod.smul_fst, Prod.fst_zero] at this

/-- **The filled system is not a system in the sense of `IsSystem`** as soon as the
augmentation ideal fails to annihilate one stage module, so the kernel-killing step of Stacks
0CBE cannot be applied to it. -/
theorem not_isSystem_fill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (hji : j < i) {a : Λ} (ha : aug a = 0) {m : M i} (hm : a • m ≠ 0) :
    ¬ IsSystem (M := Fill J M) aug unit J (fun {_ _} hji => trFill hS hann hji) :=
  fun hF => hm (smul_eq_zero_of_isSystem_fill hS hann hF hji ha m)

end Fill

/-! ### The two steps do not alternate -/

section Interleave

variable {K Λ I : Type u} [Field K] [CommRing Λ] [LinearOrder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
  {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

/-- **The one-step extension always leaves a stage module not annihilated by the augmentation
ideal**, as soon as some kernel of the system is nonzero: the new variable `x_u` of the triple
`u = (s, t, ξ)` lies in the augmentation ideal of `Λ'` and `x_u ε_{s,u} = ξ ≠ 0`. This is the
identity `inr_single_smul_mk` read as a non-vanishing statement. -/
theorem augExt_smul_mk_ne_zero (h : IsSystem aug unit J tr) {s t : I} (hts : t < s) {ξ : M s}
    (hξ : tr hts.le ξ = 0) (hne : ξ ≠ 0) :
    ∃ x : ExtRing aug tr, augExt aug tr x = 0 ∧
      x • Paired.mk (pair h s) 0
          (AugSpan.single aug (⟨⟨s, t, hts, ξ, hξ⟩, le_refl s⟩ : Cone tr s)) ≠ 0 := by
  refine ⟨TrivSqZeroExt.inr (AugSpan.single aug (⟨s, t, hts, ξ, hξ⟩ : Triple tr)), ?_, ?_⟩
  · rw [augExt_apply, TrivSqZeroExt.fst_inr, map_zero]
  · rw [inr_single_smul_mk h hts ξ hξ]
    intro hz
    refine hne ?_
    have := congrArg Paired.fst hz
    rwa [Paired.fst_mk, Paired.fst_zero] at this

/-- **The two steps of the construction of Stacks 0CBE do not alternate.** Let `Φ` be a system
with a nonzero element `ξ` of a kernel `Ker(M_s → M_t)` — which is exactly the situation the
kernel-killing step `Φ ↦ Φ'` exists to address. Then the cokernel-filling step applied to `Φ'`
is not a system in the sense of `IsSystem`, so the kernel-killing step cannot be applied to it:
the augmentation ideal of `Λ'` does not annihilate `M'_s`, because `x_u ε_{s,u} = ξ`, while
`smul_eq_zero_of_isSystem_fill` shows the filled system would force it to.

So the iteration `Φₙ = (Φₙ₋₁)'` of the discussion of Stacks 0CBE cannot be interleaved with a
cokernel-filling step of this shape, and the claim that a system with `Mⱼ = Mᵢ/JⱼMᵢ` exists is
not established by that route. What the route does establish is the weaker datum of
`isStacksSystem_fill`: every condition the source itself imposes, together with the missing
surjectivity. -/
theorem not_isSystem_fill_ext (h : IsSystem aug unit J tr) (hann : Annihilated J M)
    {s t : I} (hts : t < s) {ξ : M s} (hξ : tr hts.le ξ = 0) (hne : ξ ≠ 0) :
    ¬ IsSystem (M := Fill (Jext h) (fun i => Paired (pair h i)))
      (augExt aug tr) (unitExt unit tr) (Jext h)
      (fun {_ _} hji =>
        trFill (isSystem_ext h).toIsStacksSystem (annihilated_ext h hann) hji) := by
  obtain ⟨x, hx0, hxne⟩ := augExt_smul_mk_ne_zero h hts hξ hne
  exact not_isSystem_fill _ _ hts hx0 hxne

end Interleave

/-! ### The obstruction is not vacuous -/

section Witness

/-- The transition maps of the simplest datum with a nonzero kernel: every stage is the field
itself and every transition between two distinct stages is zero. -/
def constTr (K : Type u) [Field K] {I : Type u} [LinearOrder I] {i j : I} (_hji : j ≤ i) :
    K →ₗ[K] K :=
  if j < i then 0 else LinearMap.id

/-- The transition `constTr` between distinct stages is zero. -/
theorem constTr_eq_zero (K : Type u) [Field K] {I : Type u} [LinearOrder I] {i j : I}
    (hji : j ≤ i) (h : j < i) : constTr K hji = 0 := ite_eq_left h

/-- The transition `constTr` along `j ≤ i` with `¬ j < i` is the identity. -/
theorem constTr_eq_id (K : Type u) [Field K] {I : Type u} [LinearOrder I] {i j : I}
    (hji : j ≤ i) (h : ¬ j < i) : constTr K hji = LinearMap.id := ite_eq_right h

/-- The transition `constTr` along `i ≤ i` fixes every element. -/
theorem constTr_self (K : Type u) [Field K] {I : Type u} [LinearOrder I] {i : I} (c : K) :
    constTr K (le_refl i) c = c := by
  rw [constTr_eq_id K (le_refl i) (lt_irrefl i), LinearMap.id_coe, id_eq]

/-- The transition `constTr` along `j < i` sends every element to zero. -/
theorem constTr_of_lt (K : Type u) [Field K] {I : Type u} [LinearOrder I] {i j : I}
    (hji : j < i) (c : K) : constTr K hji.le c = 0 := by
  rw [constTr_eq_zero K hji.le hji, LinearMap.zero_apply]

/-- The constant datum is a system: it is the initial datum `Φ₀ = (K, (0), (Vᵢ))` of Stacks
0CBE for the constant system of one-dimensional vector spaces with vanishing transitions. -/
theorem isSystem_const (K : Type u) [Field K] (I : Type u) [LinearOrder I] :
    IsSystem (M := fun _ : I => K) (RingHom.id K) (RingHom.id K) (fun _ : I => (⊥ : Ideal K))
      (fun {_ _} hji => constTr K hji) :=
  isSystem_initial _ (fun {_} c => constTr_self K c) (by
    intro i j k hji hkj c
    rcases eq_or_lt_of_le hkj with rfl | hkj'
    · rw [constTr_eq_id K hkj (lt_irrefl k), LinearMap.id_coe, id_eq]
    · rw [constTr_eq_zero K hkj hkj', LinearMap.zero_apply,
        constTr_eq_zero K (hkj.trans hji) (lt_of_lt_of_le hkj' hji), LinearMap.zero_apply])

/-- **The hypotheses of `not_isSystem_fill_ext` are jointly satisfiable**, so the obstruction is
not vacuous: whenever the index has two distinct comparable stages there is a system, whose
stages are modules over the `Λ/Jᵢ`, with a nonzero element in one of its kernels — which is
exactly the situation in which the kernel-killing step of Stacks 0CBE has something to do. -/
theorem exists_isSystem_with_nonzero_ker (K : Type u) [Field K] {I : Type u} [LinearOrder I]
    {s t : I} (hts : t < s) :
    ∃ (trV : ∀ (i j : I), j ≤ i → K →ₗ[K] K)
      (_ : IsSystem (M := fun _ : I => K) (RingHom.id K) (RingHom.id K)
        (fun _ : I => (⊥ : Ideal K)) (fun {i j} hji => trV i j hji)),
      Annihilated (fun _ : I => (⊥ : Ideal K)) (fun _ : I => K) ∧
        ∃ ξ : K, trV s t hts.le ξ = 0 ∧ ξ ≠ 0 :=
  ⟨fun _ _ hji => constTr K hji, isSystem_const K I,
    annihilated_initial, 1, constTr_of_lt K hts 1, one_ne_zero⟩

end Witness

end

end Stacks.CBESystem

end
