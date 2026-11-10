module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemCokernel

/-!
# No enlargement of `Λ` can run the iteration of Stacks 0CBE

The construction sketched in the discussion of Stacks 0CBE builds a system
`Φ = (Λ, Jᵢ ⊂ Λ, (Mᵢ))` with `Mⱼ = Mᵢ/JⱼMᵢ` by iterating a step which makes the kernels
`Ker(Mᵢ → Mⱼ)` divisible: it enlarges `Λ` by square-zero variables `x_u` and each `Mᵢ` by
vectors `ε_{i,u}` with `x_u ε_{i,u} = ξ_u`, so that `ξ_u ∈ J'ⱼ M'ᵢ`. Two concrete enlargements
have already been examined in
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemStep` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemCokernel`: the source's own
`Λ' = Λ[x_u]/(x_ux_{u'})`, whose ideals `J'ₖ` are *not* of square zero, and the repair
`Λ' = Λ ⊕ K^{(U)}`, whose ideals are, but which forces the augmentation ideal of `Λ'` to
annihilate every kernel — a condition the cokernel-filling step of that second file destroys.

That left one question open: is there some *other* enlargement of `Λ`, with square-zero `J'ₖ`,
which does not force an annihilation condition of that kind? This file answers it, and the
answer is no — for a reason that uses nothing about the shape of the enlargement.

## The forced annihilation condition

`IsKernelKilling` is the datum of an arbitrary enlargement: a ring map `φ : Λ → Λ'`, ideals
`J'ₖ ⊂ Λ'` of square zero containing the images of the `Jₖ`, modules `M'ᵢ` over `Λ'`, and
injections `Mᵢ ↪ M'ᵢ` semilinear over `φ`, such that each kernel `Ker(Mᵢ → Mⱼ)` becomes
divisible by `J'ⱼ` — which is the one thing the step of Stacks 0CBE exists to achieve. Nothing
is assumed about how `Λ'` or `M'ᵢ` are built, nor that `M'` is again an inverse system.

For such a datum, `IsKernelKilling.smul_ker_eq_zero`: `Jⱼ` annihilates `Ker(Mᵢ → Mⱼ)`. The
proof is three lines of ideal theory. Write `ξ ∈ Ker(Mᵢ → Mⱼ)` as `ξ = Σ b_l z_l` with
`b_l ∈ J'ⱼ`; for `a ∈ Jⱼ` the element `φ(a)` also lies in `J'ⱼ`, so every `φ(a) b_l` lies in
`J'ⱼ · J'ⱼ = 0` and `φ(a) ξ = 0`. Divisibility by a square-zero ideal and annihilation by it
are the same thing.

So the annihilation condition is not an artefact of the choice `Λ ⊕ K^{(U)}`: *any* enlargement
that does what the step is for forces `Jⱼ · Ker(Mᵢ → Mⱼ) = 0`, the condition `KerAnnihilated`
below. It is weaker than the condition `IsSystem` carries (the augmentation ideal contains
every `Jₖ`, so `IsSystem.kerAnnihilated`), it holds for the initial datum `Φ₀ = (K, (0), (Vᵢ))`
and is preserved by the step; it is exactly what the cokernel-filling step cannot have.

## The iteration still does not run

`smul_eq_zero_of_kerAnnihilated_fill` is the obstruction of
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemCokernel` with its hypothesis
weakened from `IsSystem` to `KerAnnihilated`: if the filled system `Φ^†` has `Jⱼ` annihilating
one kernel `Ker(M^†ᵢ → M^†ⱼ)`, then `Jⱼ` annihilates the whole of `Mᵢ`. Surjectivity alone
forces it — `y = -tr(m)` acquires a generator `e_{j,y}` with `tr(m + e_{j,y}) = 0`, and the two
summands of `M^†ᵢ` are scaled separately.

Against that, `mem_Jext_smul_ne_zero`: the kernel-killing step always produces a system in which
`J'ₜ` does *not* annihilate `M'ₛ`, as soon as it has anything to do, since `x_u ∈ J'ₜ` and
`x_u ε_{s,u} = ξ ≠ 0`. Hence `not_kerAnnihilated_fill_ext` and the conclusion
`not_isKernelKilling_fill_ext`: **after one kernel-killing step and one cokernel-filling step,
no enlargement whatsoever makes the kernels divisible again.** The route of Stacks 0CBE is
closed, not merely for the enlargement the source writes down nor for the one that repairs it,
but for every enlargement of `Λ`.

The hypotheses are jointly satisfiable — `exists_isSystem_with_nonzero_ker` of the previous
file — and the notion being contradicted is not empty: `isKernelKilling_ext` exhibits the step
of Stacks 0CBE itself as an `IsKernelKilling` datum. The lemma itself is proved, by a system
whose ideals are idempotent rather than square-zero, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverMcQuillan`.

## How large an enlargement may be

The candidate `Λ' = Λ ⊕ ⨁_u (Λ/Nᵤ)·x_u`, with each new variable spanning a quotient of `Λ`
rather than `K` or `Λ` itself, is covered by the above, but it is worth recording how little
room it has: `smul_eq_zero_of_inl_mem_of_inr_mem` says that a square-zero ideal of a trivial
square-zero extension containing both `a` and `x_u` has `a x_u = 0`, so `J'ₖ ∋ Jₖ, x_u` for
every `k ≤ t(u)` forces `Nᵤ ⊇ Σ_{k ≤ t(u)} Jₖ`. The largest admissible coefficient module for
`x_u` is therefore `Λ/Σ_{k ≤ t(u)} Jₖ`, which is the candidate at its most generous; it sits
strictly between the source's `Λ` and the `K` of the repair, and the pairing `x_u ε_{i,u} = ξ_u`
then asks of the datum that `Σ_{k ≤ t(u)} Jₖ` annihilate `ξ_u` — more than the `Jₜ₍ᵤ₎ξ_u = 0`
which `IsKernelKilling` already forces on every enlargement, and which the filling step
destroys.

## Main definitions

* `Stacks.CBESystem.IsKernelKilling`: an arbitrary enlargement of a system which makes its
  kernels divisible by the enlarged square-zero ideals.
* `Stacks.CBESystem.KerAnnihilated`: the condition `Jⱼ · Ker(Mᵢ → Mⱼ) = 0`.

## Main results

* `Stacks.CBESystem.IsKernelKilling.smul_ker_eq_zero` and
  `Stacks.CBESystem.IsKernelKilling.kerAnnihilated`: **every enlargement forces the annihilation
  condition.**
* `Stacks.CBESystem.isKernelKilling_ext`: the step of Stacks 0CBE is such an enlargement, so the
  notion is not empty.
* `Stacks.CBESystem.smul_eq_zero_of_kerAnnihilated_fill`: if the filled system satisfies the
  condition for one pair of stages, `Jⱼ` annihilates the whole of `Mᵢ`.
* `Stacks.CBESystem.not_isKernelKilling_fill_ext`: **no enlargement of the filled extension
  exists.** One kernel-killing step followed by one cokernel-filling step reaches a system whose
  kernels cannot be made divisible by any enlargement at all.
* `Stacks.CBESystem.smul_eq_zero_of_inl_mem_of_inr_mem`: the bound on the coefficient modules of
  the new variables.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public section

namespace Stacks.CBESystem

universe u

open TrivSqZeroExt Stacks.SqZeroExtension

/-! ### Divisibility by a square-zero ideal is annihilation by it -/

section SqZero

variable {R : Type u} [CommRing R] {X : Type u} [AddCommGroup X] [Module R X]

/-- An element of a square-zero ideal annihilates every element of a module divisible by that
ideal. This is the whole mechanism of the obstruction of this file: the step of Stacks 0CBE
exists to make the kernels `Ker(Mᵢ → Mⱼ)` divisible by the square-zero ideal `J'ⱼ`, and
divisibility by such an ideal is the same as being annihilated by it. -/
theorem smul_eq_zero_of_mem_smul_top {p : Ideal R} (hp : p * p = ⊥) {a : R} (ha : a ∈ p)
    {x : X} (hx : x ∈ p • (⊤ : Submodule R X)) : a • x = 0 := by
  have hmem : a • x ∈ p • (p • (⊤ : Submodule R X)) := Submodule.smul_mem_smul ha hx
  rwa [← Submodule.smul_assoc, Ideal.smul_eq_mul, hp, Submodule.bot_smul,
    Submodule.mem_bot] at hmem

/-- A square-zero ideal of a trivial square-zero extension `Λ ⊕ W` containing both a scalar `a`
and a vector `w` has `a • w = 0`. Applied to `J'ₖ ∋ Jₖ, x_u` for `k ≤ t(u)` this bounds the
coefficient module of the new variable `x_u` of the step of Stacks 0CBE: it can be at most the
quotient of `Λ` by the sum of the ideals `Jₖ` with `k ≤ t(u)`. -/
theorem smul_eq_zero_of_inl_mem_of_inr_mem {Λ W : Type u} [CommRing Λ] [AddCommGroup W]
    [Module Λ W] [Module Λᵐᵒᵖ W] [IsCentralScalar Λ W] {p : Ideal (TrivSqZeroExt Λ W)}
    (hp : p * p = ⊥) {a : Λ} (ha : (inl a : TrivSqZeroExt Λ W) ∈ p) {w : W}
    (hw : (inr w : TrivSqZeroExt Λ W) ∈ p) : a • w = 0 := by
  have hmem : (inl a : TrivSqZeroExt Λ W) * inr w ∈ p * p := Ideal.mul_mem_mul ha hw
  rw [hp, Submodule.mem_bot, inl_mul_inr] at hmem
  have hsnd := congrArg TrivSqZeroExt.snd hmem
  rwa [snd_inr, TrivSqZeroExt.snd_zero] at hsnd

end SqZero

/-! ### An arbitrary enlargement, and the condition it forces -/

section Enlargement

variable {Λ I : Type u} [CommRing Λ] [Preorder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]

/-- The condition `Jⱼ · Ker(Mᵢ → Mⱼ) = 0` for `i > j`, which `IsKernelKilling.kerAnnihilated`
shows every enlargement of the system forces on it. It is weaker than the condition the
augmentation ideal annihilate the kernels, which `Stacks.CBESystem.IsSystem` carries, because
each `Jₖ` lies in the augmentation ideal. -/
def KerAnnihilated (J : I → Ideal Λ) (M : I → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module Λ (M i)] (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) : Prop :=
  ∀ {i j : I} (hji : j < i) {a : Λ}, a ∈ J j → ∀ m : M i, tr hji.le m = 0 → a • m = 0

/-- An enlargement of a system `Φ = (Λ, Jᵢ, (Mᵢ))` which makes its kernels divisible, which is
the one thing the step of the discussion of Stacks 0CBE exists to achieve: a ring map
`φ : Λ → Λ'`, ideals `J'ₖ` of `Λ'` of square zero which receive the `Jₖ`, modules `M'ᵢ` over
`Λ'`, and injections `Mᵢ ↪ M'ᵢ` semilinear over `φ`, such that the image of `Ker(Mᵢ → Mⱼ)` lies
in `J'ⱼ M'ᵢ`.

Nothing is assumed about *how* `Λ'` and the `M'ᵢ` are built — not that `Λ'` is an extension of
`Λ` by square-zero variables, nor that the `M'ᵢ` form an inverse system, nor that `Φ'` is again
a system. The point of taking the datum this weak is `smul_ker_eq_zero`: the conclusion holds
for every enlargement whatever, so the annihilation condition that obstructs the iteration of
Stacks 0CBE cannot be avoided by choosing a different one. The step of that discussion is an
instance, by `isKernelKilling_ext`. -/
structure IsKernelKilling (J : I → Ideal Λ) (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j)
    {Λ' : Type u} [CommRing Λ'] (φ : Λ →+* Λ') (J' : I → Ideal Λ')
    (M' : I → Type u) [∀ i, AddCommGroup (M' i)] [∀ i, Module Λ' (M' i)]
    (incl : ∀ i : I, M i →+ M' i) : Prop where
  /-- The enlarged ideals are of square zero, as a system of Stacks 0CBE requires. -/
  sq_zero : ∀ k : I, J' k * J' k = ⊥
  /-- The enlarged ideal `J'ₖ` receives the ideal `Jₖ`. -/
  map_mem : ∀ {k : I} {a : Λ}, a ∈ J k → φ a ∈ J' k
  /-- The inclusion of a stage module is semilinear over `φ`. -/
  incl_smul : ∀ (i : I) (a : Λ) (m : M i), incl i (a • m) = φ a • incl i m
  /-- The enlargement does not collapse a stage module. -/
  incl_injective : ∀ i : I, Function.Injective (incl i)
  /-- **The purpose of the enlargement:** every element of `Ker(Mᵢ → Mⱼ)` becomes divisible by
  the enlarged ideal `J'ⱼ`, so that it dies in `M'ᵢ/J'ⱼM'ᵢ`. -/
  mem_smul_top : ∀ {i j : I} (hji : j < i) (m : M i), tr hji.le m = 0 →
    incl i m ∈ J' j • (⊤ : Submodule Λ' (M' i))

variable {J : I → Ideal Λ} {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}
  {Λ' : Type u} [CommRing Λ'] {φ : Λ →+* Λ'} {J' : I → Ideal Λ'}
  {M' : I → Type u} [∀ i, AddCommGroup (M' i)] [∀ i, Module Λ' (M' i)]
  {incl : ∀ i : I, M i →+ M' i}

/-- In an enlargement, `Jⱼ` kills the image of `Ker(Mᵢ → Mⱼ)`: the kernel is divisible by the
square-zero ideal `J'ⱼ`, and `Jⱼ` maps into `J'ⱼ`. -/
theorem IsKernelKilling.incl_smul_ker_eq_zero
    (hE : IsKernelKilling J tr φ J' M' incl) {i j : I} (hji : j < i) {a : Λ} (ha : a ∈ J j)
    {m : M i} (hm : tr hji.le m = 0) : incl i (a • m) = 0 := by
  rw [hE.incl_smul]
  exact smul_eq_zero_of_mem_smul_top (hE.sq_zero j) (hE.map_mem ha) (hE.mem_smul_top hji m hm)

/-- **Every enlargement forces the annihilation condition.** If the kernels of a system become
divisible by the enlarged square-zero ideals, then `Jⱼ` already annihilates `Ker(Mᵢ → Mⱼ)` in
the system itself.

This is why no choice of enlargement can rescue the iteration of Stacks 0CBE. The source's
`Λ[x_u]/(x_ux_{u'})` fails because its `J'ₖ` are not of square zero; the repair `Λ ⊕ K^{(U)}`
has square-zero `J'ₖ` but forces the augmentation ideal to annihilate the kernels. The present
statement shows that the second failure is unavoidable in a weaker but still fatal form:
divisibility by a square-zero ideal *is* annihilation by it. -/
theorem IsKernelKilling.smul_ker_eq_zero (hE : IsKernelKilling J tr φ J' M' incl)
    {i j : I} (hji : j < i) {a : Λ} (ha : a ∈ J j) {m : M i} (hm : tr hji.le m = 0) :
    a • m = 0 :=
  hE.incl_injective i <| by
    rw [hE.incl_smul_ker_eq_zero hji ha hm, map_zero]

/-- **Every enlargement forces the annihilation condition**, stated as `KerAnnihilated`. -/
theorem IsKernelKilling.kerAnnihilated (hE : IsKernelKilling J tr φ J' M' incl) :
    KerAnnihilated J M tr := by
  intro _ _ hji _ ha m hm
  exact hE.smul_ker_eq_zero hji ha hm

/-- The annihilation condition holds whenever all the ideals vanish, in particular for the
initial datum `Φ₀ = (K, (0), (Vᵢ))` of Stacks 0CBE. -/
theorem kerAnnihilated_bot (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) :
    KerAnnihilated (fun _ : I => (⊥ : Ideal Λ)) M tr := by
  intro _ _ _ a ha m _
  rw [(Submodule.mem_bot Λ).mp ha, zero_smul]

/-- A system in the sense of `Stacks.CBESystem.IsSystem` satisfies the annihilation condition,
because each `Jₖ` lies in the augmentation ideal. So the condition forced by an arbitrary
enlargement is weaker than the one the repaired step of Stacks 0CBE has to assume. -/
theorem IsSystem.kerAnnihilated {K : Type u} [Field K] {aug : Λ →+* K} {unit : K →+* Λ}
    (h : IsSystem aug unit J tr) : KerAnnihilated J M tr := by
  intro _ _ hji _ ha m hm
  exact h.aug_ann hji (h.aug_eq_zero ha) m hm

end Enlargement

/-! ### The step of Stacks 0CBE is an enlargement -/

section Instance

variable {K Λ I : Type u} [Field K] [CommRing Λ] [Preorder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
  {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

noncomputable section

/-- The inclusion `Mᵢ → M'ᵢ` of a stage module into its one-step extension, as an additive
map: it adds no new vectors. -/
def inclPaired (h : IsSystem aug unit J tr) (i : I) : M i →+ Paired (pair h i) where
  toFun m := Paired.mk (pair h i) m 0
  map_zero' := Paired.mk_zero_zero
  map_add' m m' := Paired.ext rfl (by
    rw [Paired.snd_mk, Paired.snd_add, Paired.snd_mk, Paired.snd_mk, add_zero])

/-- The inclusion `inclPaired h i` sends `m` to the pair `(m, 0)`. -/
@[simp] theorem inclPaired_apply (h : IsSystem aug unit J tr) (i : I) (m : M i) :
    inclPaired h i m = Paired.mk (pair h i) m 0 := rfl

/-- **The step of Stacks 0CBE is an enlargement in the sense of `IsKernelKilling`**, so the
notion the obstruction of this file contradicts is not an empty one. The ideals `J'ₖ` of the
extended algebra are of square zero and receive the `Jₖ`, the stage modules gain no relations,
and `mk_mem_Jext_smul_top` is precisely the divisibility of the kernels. -/
theorem isKernelKilling_ext (h : IsSystem aug unit J tr) :
    IsKernelKilling J tr (TrivSqZeroExt.inlHom Λ (AugSpan aug (Triple tr))) (Jext h)
      (fun i => Paired (pair h i)) (inclPaired h) where
  sq_zero := (isSystem_ext h).sq_zero
  map_mem ha := inl_mem_Jext h ha
  incl_smul i a m := by
    rw [inclPaired_apply, inclPaired_apply]
    change Paired.mk (pair h i) (a • m) 0 = (TrivSqZeroExt.inl a) • Paired.mk (pair h i) m 0
    rw [Paired.inl_smul, Paired.fst_mk, Paired.snd_mk, smul_zero]
  incl_injective i m m' hmm := by
    have := congrArg Paired.fst hmm
    rwa [inclPaired_apply, inclPaired_apply, Paired.fst_mk, Paired.fst_mk] at this
  mem_smul_top hji m hm := mk_mem_Jext_smul_top h hji m hm

end

end Instance

/-! ### The cokernel-filling step destroys the forced condition -/

section Fill

variable {K Λ I : Type u} [Field K] [CommRing Λ] [LinearOrder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
  {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

noncomputable section

/-- **The obstruction, with the hypothesis weakened to the condition every enlargement forces.**
Suppose the cokernel-filling step `Φ ↦ Φ^†` produces a system in which `Jⱼ` annihilates one
kernel `Ker(M^†ᵢ → M^†ⱼ)`. Then `Jⱼ` annihilates the whole of `Mᵢ`.

This is `Stacks.CBESystem.smul_eq_zero_of_isSystem_fill` with `IsSystem` replaced by
`KerAnnihilated`, which by `IsKernelKilling.kerAnnihilated` is all that an enlargement of any
shape gives. The reason is surjectivity alone: the element `y = -tr(m)` of `Mⱼ` has a generator
`e_{j,y}` at the stage `i`, the element `m + e_{j,y}` lies in the kernel of the transition, and
the two summands of `M^†ᵢ = Mᵢ ⊕ (Λ/Jᵢ)^{(GenAt i)}` are scaled separately. -/
theorem smul_eq_zero_of_kerAnnihilated_fill (hS : IsStacksSystem aug unit J tr)
    (hann : Annihilated J M)
    (hF : KerAnnihilated J (Fill J M) (fun {_ _} hji => trFill hS hann hji))
    {i j : I} (hji : j < i) {a : Λ} (ha : a ∈ J j) (m : M i) : a • m = 0 := by
  have hker : trFill hS hann hji.le
      ((m, Finsupp.single (⟨⟨j, -(tr hji.le m)⟩, hji⟩ : GenAt M i)
        (Submodule.Quotient.mk 1)) : Fill J M i) = 0 := by
    refine Prod.ext ?_ ?_
    · rw [fst_trFill, fillOld_single_of_le hS hann _ (lt_irrefl j), fillSpan_mk, one_smul,
        hS.tr_self, Prod.fst_zero, add_neg_cancel]
    · rw [snd_trFill, fillNew_single_of_le hS hji.le _ (lt_irrefl j), Prod.snd_zero]
  have hz := hF hji ha _ hker
  have hfst := congrArg Prod.fst hz
  rwa [Prod.smul_fst, Prod.fst_zero] at hfst

/-- **The filled system does not satisfy the forced condition** as soon as some `Jⱼ` fails to
annihilate one stage module, so by `IsKernelKilling.kerAnnihilated` it admits no enlargement
whatever making its kernels divisible. -/
theorem not_kerAnnihilated_fill (hS : IsStacksSystem aug unit J tr) (hann : Annihilated J M)
    {i j : I} (hji : j < i) {a : Λ} (ha : a ∈ J j) {m : M i} (hm : a • m ≠ 0) :
    ¬ KerAnnihilated J (Fill J M) (fun {_ _} hji => trFill hS hann hji) :=
  fun hF => hm (smul_eq_zero_of_kerAnnihilated_fill hS hann hF hji ha m)

/-- **The kernel-killing step always leaves a stage module on which an extended ideal acts
nontrivially**, as soon as some kernel of the system is nonzero: the new variable `x_u` of the
triple `u = (s, t, ξ)` lies in `J'ₜ` and `x_u ε_{s,u} = ξ ≠ 0`. This is the identity
`inr_single_smul_mk` read against the ideal `Jext h t` rather than against the augmentation
ideal, which is what the weakened obstruction consumes. -/
theorem mem_Jext_smul_ne_zero (h : IsSystem aug unit J tr) {s t : I} (hts : t < s) {ξ : M s}
    (hξ : tr hts.le ξ = 0) (hne : ξ ≠ 0) :
    ∃ x : ExtRing aug tr, x ∈ Jext h t ∧
      x • Paired.mk (pair h s) 0
          (AugSpan.single aug (⟨⟨s, t, hts, ξ, hξ⟩, le_refl s⟩ : Cone tr s)) ≠ 0 := by
  refine ⟨TrivSqZeroExt.inr (AugSpan.single aug (⟨s, t, hts, ξ, hξ⟩ : Triple tr)),
    inr_single_mem_Jext h ⟨s, t, hts, ξ, hξ⟩ (le_refl t), ?_⟩
  rw [inr_single_smul_mk h hts ξ hξ]
  intro hz
  refine hne ?_
  have hfst := congrArg Paired.fst hz
  rwa [Paired.fst_mk, Paired.fst_zero] at hfst

end

end Fill

/-! ### No enlargement of the filled extension exists -/

section NoEnlargement

variable {K Λ I : Type u} [Field K] [CommRing Λ] [LinearOrder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
  {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

noncomputable section

/-- **The condition forced by every enlargement fails after one step of each kind.** Let `Φ` be
a system with a nonzero element `ξ` of a kernel `Ker(M_s → M_t)` — the situation the
kernel-killing step exists to address. Apply the kernel-killing step and then the
cokernel-filling step. The resulting system does not satisfy `KerAnnihilated`: the extended
ideal `J'ₜ` does not annihilate `M'_s`, because `x_u ε_{s,u} = ξ`, while
`smul_eq_zero_of_kerAnnihilated_fill` shows the filled system would force it to. -/
theorem not_kerAnnihilated_fill_ext (h : IsSystem aug unit J tr) (hann : Annihilated J M)
    {s t : I} (hts : t < s) {ξ : M s} (hξ : tr hts.le ξ = 0) (hne : ξ ≠ 0) :
    ¬ KerAnnihilated (Jext h) (Fill (Jext h) (fun i => Paired (pair h i)))
      (fun {_ _} hji =>
        trFill (isSystem_ext h).toIsStacksSystem (annihilated_ext h hann) hji) := by
  obtain ⟨x, hx, hxne⟩ := mem_Jext_smul_ne_zero h hts hξ hne
  exact not_kerAnnihilated_fill _ _ hts hx hxne

/-- **No enlargement of `Λ` runs the iteration of Stacks 0CBE.** Let `Φ` be a system with a
nonzero element of a kernel `Ker(M_s → M_t)`, apply the kernel-killing step of Stacks 0CBE and
then any cokernel-filling step of the shape of
`StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemCokernel`. The system so reached
admits **no** enlargement making its kernels divisible by square-zero ideals: not the
enlargement `Λ[x_u]/(x_ux_{u'})` the source writes down, not the repair `Λ ⊕ K^{(U)}`, and not
any other, whatever ring `Λ'`, ideals `J'ₖ` and modules `M'ᵢ` it is built from.

Both halves are needed and neither is avoidable. The cokernel-filling step is needed because the
kernel-killing step destroys the surjectivity of the transitions, which is half of the equality
`Mⱼ = Mᵢ/JⱼMᵢ` the lemma of Stacks 0CBE rests on. An enlargement making the kernels divisible
is needed because that is the other half. And the first forces `Jⱼ` to annihilate the whole of
`Mᵢ` (`smul_eq_zero_of_kerAnnihilated_fill`) while the second has just made it not do so
(`mem_Jext_smul_ne_zero`).

So the iteration of the discussion of Stacks 0CBE cannot be run in this way, and the existence
of a system with `Mⱼ = Mᵢ/JⱼMᵢ` is not established by that route. What the route does establish
is the weaker datum of `isStacksSystem_fill`: every condition the source itself imposes,
together with the missing surjectivity. -/
theorem not_isKernelKilling_fill_ext (h : IsSystem aug unit J tr) (hann : Annihilated J M)
    {s t : I} (hts : t < s) {ξ : M s} (hξ : tr hts.le ξ = 0) (hne : ξ ≠ 0)
    {Λ' : Type u} [CommRing Λ'] (φ : ExtRing aug tr →+* Λ') (J' : I → Ideal Λ')
    (M' : I → Type u) [∀ i, AddCommGroup (M' i)] [∀ i, Module Λ' (M' i)]
    (incl : ∀ i : I, Fill (Jext h) (fun i => Paired (pair h i)) i →+ M' i) :
    ¬ IsKernelKilling (Jext h)
        (fun {_ _} hji =>
          trFill (isSystem_ext h).toIsStacksSystem (annihilated_ext h hann) hji)
        φ J' M' incl :=
  fun hE => not_kerAnnihilated_fill_ext h hann hts hξ hne hE.kerAnnihilated

end

end NoEnlargement

end Stacks.CBESystem

end
