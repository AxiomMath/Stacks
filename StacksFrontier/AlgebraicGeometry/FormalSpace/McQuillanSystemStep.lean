module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSystemPairing
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The one-step extension of the system of Stacks 0CBE

The lemma of Stacks 0CBE needs a system

`Φ = (Λ, Jᵢ ⊂ Λ, (Mᵢ))`

over a directed index `I`: an augmented `K`-algebra `Λ`, square-zero ideals `Jᵢ` decreasing
along `I`, and an inverse system of `Λ`-modules `Mᵢ` with `Jⱼ Mᵢ ⊂ Ker(Mᵢ → Mⱼ)` for `i > j`,
*such that* `Mⱼ = Mᵢ/Jⱼ Mᵢ`. The discussion of that tag produces one by starting from
`Φ₀ = (K, (0), (Vᵢ))` and iterating a step `Φ ↦ Φ'` which makes every element of a kernel
`Ker(Mᵢ → Mⱼ)` divisible: it adjoins a variable `x_u` to `Λ` and a vector `ε_{i,u}` to `Mᵢ`
for each triple `u = (i, j, ξ)` with `ξ ∈ Ker(Mᵢ → Mⱼ)`, subject to `x_u ε_{i,u} = ξ`.

This file is that single step, as algebra: `IsSystem` is the datum `Φ`, the definitions
`augExt`, `Jext`, `pair` and `trExt` are the step `Φ ↦ Φ'`, `isSystem_ext` says that `Φ'` is
again such a datum, and `mk_mem_Jext_smul_top` is the point of the step — the image of
`Ker(Mᵢ → Mⱼ)` in `M'ᵢ` lies in `J'ⱼ M'ᵢ`, so it dies in `M'ᵢ/J'ⱼM'ᵢ`.

## Implementation notes

The source has to be corrected in two places.

*The new variables must kill the augmentation ideal.* Stacks takes
`Λ' = Λ[x_u; u ∈ U]/(x_u x_{u'})`, which as a `Λ`-module is `Λ ⊕ ⨁_u Λ x_u`, so that `λ x_u`
vanishes only for `λ = 0`. With that ring `J'ₖ = JₖΛ' + (x_u; t(u) ≥ k)` is **not** of square
zero: `λ ∈ Jₖ` and `x_u` with `t(u) ≥ k` both lie in it and their product `λ x_u` is nonzero
whenever `λ ≠ 0`. So `Φ'` is not a system and the iteration leaves the class of data it is
supposed to stay in. (At the first step all `Jᵢ` are zero and nothing is visible; from the
second step on the ideals are nonzero and the failure is there, as soon as some adjoined
variable has `t(u) ≥ k`.) Here `Λ'` is the quotient `Λ ⊕ K^{(U)}` of that ring in which the
augmentation ideal annihilates every `x_u`, which is the trivial square-zero extension of `Λ`
by the `Λ`-module `K^{(U)}`, and then `J'ₖ` is of square zero.

*The data must carry one extra property.* For `Mᵢ ⊕ K^{(U)}` to be a module over `Λ'` at all,
the action of `Λ` on the elements `ξ_u` must factor through the augmentation: `x_u ε_{i,u}` is
`ξ_u`, so `λ x_u ε_{i,u}` forces `λ ξ_u = aug(λ) ξ_u`. So `IsSystem` demands that the
augmentation ideal annihilate every kernel `Ker(Mᵢ → Mⱼ)`, which `Φ₀` satisfies (there
`Λ = K` and the augmentation ideal is zero) and which the step preserves
(`isSystem_ext`). Without it the step is not even well defined; Stacks does not mention it.

*What the step does not give.* The transition maps of `Φ'` are **not** surjective even when
those of `Φ` are: the stage `M'ⱼ` acquires a vector `ε_{j,u}` for every `u` with `s(u) ≥ j`,
while the image of `M'ᵢ` contains only those with `s(u) ≥ i`. The restriction to `s(u) ≥ i`
cannot be dropped — without it the transition is not `Λ'`-linear, since `x_u` acts by `ξ_u` on
one side and by `0` on the other. So the step kills the kernel of `Mᵢ/JⱼMᵢ → Mⱼ` but does not
make that map onto, and the equality `Mⱼ = Mᵢ/JⱼMᵢ` which the lemma of Stacks 0CBE rests on
needs a second, cokernel-filling construction that the source does not give. The lemma itself
is proved, by a system with idempotent rather than square-zero ideals, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverMcQuillan`.

## Main definitions

* `Stacks.CBESystem.AugSpan`: the free `K`-vector space on a type, as a `Λ`-module through an
  augmentation `aug : Λ →+* K`; this is where the new variables `x_u` and the new vectors
  `ε_{i,u}` live.
* `Stacks.CBESystem.IsSystem`: the datum `Φ` of the discussion of Stacks 0CBE.
* `Stacks.CBESystem.Triple` and `Stacks.CBESystem.Cone`: the triples `u = (i, j, ξ)` indexing
  the new variables, and those of them which contribute a vector to the stage `i`.
* `Stacks.CBESystem.pair`: the pairing `x_u ε_{i,u} = ξ_u`, as a `Λ`-bilinear map.
* `Stacks.CBESystem.ExtRing`, `Stacks.CBESystem.augExt`, `Stacks.CBESystem.unitExt`,
  `Stacks.CBESystem.Jext` and `Stacks.CBESystem.trExt`: the extended augmented algebra, its
  ideals and the transition maps of the extended system; its stage modules are
  `Stacks.SqZeroExtension.Paired (pair h i)`.

## Main results

* `Stacks.CBESystem.isSystem_ext`: **the one-step extension is again a system.**
* `Stacks.CBESystem.mk_mem_Jext_smul_top`: **the point of the step.** For `j < i`, every
  element of `Ker(Mᵢ → Mⱼ)` lands in `J'ⱼ M'ᵢ`, so it dies in `M'ᵢ/J'ⱼM'ᵢ`; the witness is the
  Stacks identity `ξ = x_{(i,j,ξ)} ε_{i,(i,j,ξ)}` of `inr_single_smul_mk`.
* `Stacks.CBESystem.trExt_mk` and `Stacks.CBESystem.unitExt_smul_mk`: the maps `Mᵢ → M'ᵢ`
  commute with the transitions and with the scalars, i.e. `Φ → Φ'` is a morphism of systems.
* `Stacks.CBESystem.Jext_eq`: the extended ideals are the ones of Stacks 0CBE, namely
  `J'ₖ = JₖΛ' + (x_u; t(u) ≥ k)`.
* `Stacks.CBESystem.isSystem_initial`: the datum `Φ₀ = (K, (0), (Vᵢ))` the iteration starts
  from is a system, so the class of data the step runs in is not empty.

## References

* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public section

namespace Stacks.CBESystem

universe u

open TrivSqZeroExt Stacks.SqZeroExtension

noncomputable section

/-! ### The span of the new variables -/

section AugSpan

variable {K Λ : Type u} [Field K] [CommRing Λ]

/-- The free `K`-vector space on a type `U`, regarded as a `Λ`-module through an augmentation
`aug : Λ →+* K`. In the step of Stacks 0CBE this is the span of the new variables `x_u`,
which is the square-zero part of the extended algebra, and also the span of the new vectors
`ε_{i,u}`, on which `Λ` acts through the augmentation. -/
def AugSpan (_aug : Λ →+* K) (U : Type u) : Type u := U →₀ K

namespace AugSpan

variable {aug : Λ →+* K} {U U' : Type u}

/-- The additive group structure of the span is that of `U →₀ K`. -/
instance : AddCommGroup (AugSpan aug U) := inferInstanceAs (AddCommGroup (U →₀ K))

/-- The span is a `K`-vector space as `U →₀ K` is. -/
instance : Module K (AugSpan aug U) := inferInstanceAs (Module K (U →₀ K))

/-- The span is a `Λ`-module through the augmentation `aug : Λ →+* K`. -/
instance : Module Λ (AugSpan aug U) := Module.compHom _ aug

/-- The span is a `Λᵐᵒᵖ`-module through the augmentation, with the same action as on the left. -/
instance : Module Λᵐᵒᵖ (AugSpan aug U) :=
  Module.compHom _ (aug.comp (RingEquiv.toOpposite Λ).symm.toRingHom)

/-- The left and right actions of `Λ` on the span agree. -/
instance : IsCentralScalar Λ (AugSpan aug U) := ⟨fun _ _ => rfl⟩

/-- An element of the span, as the finitely supported function it is. -/
def toFinsupp (w : AugSpan aug U) : U →₀ K := w

/-- The zero of the span is the zero function. -/
@[simp] theorem toFinsupp_zero : toFinsupp (0 : AugSpan aug U) = 0 := rfl

/-- `toFinsupp` is additive. -/
@[simp] theorem toFinsupp_add (w w' : AugSpan aug U) :
    toFinsupp (w + w') = toFinsupp w + toFinsupp w' := rfl

/-- An element `a : Λ` acts on the span as the scalar `aug a : K`. -/
@[simp] theorem toFinsupp_smul (a : Λ) (w : AugSpan aug U) :
    toFinsupp (a • w) = aug a • toFinsupp w := rfl

/-- `toFinsupp` is `K`-linear. -/
@[simp] theorem toFinsupp_kSmul (c : K) (w : AugSpan aug U) :
    toFinsupp (c • w) = c • toFinsupp w := rfl

/-- The vector of the span attached to an element of its index type. -/
def single (aug : Λ →+* K) (x : U) : AugSpan aug U := Finsupp.single x 1

/-- The vector attached to `x` is the indicator function `Finsupp.single x 1`. -/
@[simp] theorem toFinsupp_single (x : U) :
    toFinsupp (single aug x) = Finsupp.single x (1 : K) := rfl

/-- A finitely supported function, as an element of the span. -/
def ofFinsupp (aug : Λ →+* K) (w : U →₀ K) : AugSpan aug U := w

/-- The zero function is the zero of the span. -/
@[simp] theorem ofFinsupp_zero : ofFinsupp aug (0 : U →₀ K) = 0 := rfl

/-- `ofFinsupp` is additive. -/
@[simp] theorem ofFinsupp_add (w w' : U →₀ K) :
    ofFinsupp aug (w + w') = ofFinsupp aug w + ofFinsupp aug w' := rfl

/-- The function `Finsupp.single x b` is `b` times the vector attached to `x`. -/
@[simp] theorem ofFinsupp_single (x : U) (b : K) :
    ofFinsupp aug (Finsupp.single x b) = b • single aug x := by
  show (Finsupp.single x b : U →₀ K) = b • (Finsupp.single x 1 : U →₀ K)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The `Λ`-action on the span is the `K`-action through the augmentation. -/
theorem smul_eq (a : Λ) (w : AugSpan aug U) : a • w = aug a • w := rfl

/-- A `K`-linear map of free vector spaces is `Λ`-linear for the actions through the
augmentation. -/
def ofKLinear (f : (U →₀ K) →ₗ[K] (U' →₀ K)) : AugSpan aug U →ₗ[Λ] AugSpan aug U' where
  toFun w := (f (toFinsupp w) : U' →₀ K)
  map_add' w w' := map_add f (toFinsupp w) (toFinsupp w')
  map_smul' a w := map_smul f (aug a) (toFinsupp w)

/-- The map `ofKLinear f` is `f` on the underlying finitely supported functions. -/
@[simp] theorem toFinsupp_ofKLinear (f : (U →₀ K) →ₗ[K] (U' →₀ K)) (w : AugSpan aug U) :
    toFinsupp (ofKLinear (aug := aug) f w) = f (toFinsupp w) := rfl

end AugSpan

end AugSpan

/-! ### The datum `Φ` -/

section System

variable {K Λ I : Type u} [Field K] [CommRing Λ] [Preorder I]
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]

/-- The datum `Φ = (Λ, Jᵢ ⊂ Λ, (Mᵢ))` of the discussion of Stacks 0CBE: `aug` and `unit`
present `Λ` as an augmented `K`-algebra, the `Jᵢ` are square-zero ideals decreasing along the
index, the `Mᵢ` form an inverse system of `Λ`-modules whose transition maps kill `Jⱼ Mᵢ` for
`i > j`, and the augmentation ideal annihilates every kernel `Ker(Mᵢ → Mⱼ)`.

The last condition is not in the source; it is what makes the step `Φ ↦ Φ'` well defined, the
initial datum `Φ₀ = (K, (0), (Vᵢ))` satisfies it, and `isSystem_ext` shows the step preserves
it. The surjections `Mᵢ → Vᵢ` of the source onto a system of vector spaces with vanishing
limit are not part of the datum here: they play no role in the step, which does not change the
index or the quotients `Mᵢ ↠ Vᵢ` would be taken along. -/
structure IsSystem (aug : Λ →+* K) (unit : K →+* Λ) (J : I → Ideal Λ)
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
  /-- The ideals decrease along the index, so that the `Λ/Jᵢ` form an inverse system. -/
  antitone : ∀ {i j : I}, j ≤ i → J i ≤ J j
  /-- `Jⱼ Mᵢ` is killed by the transition map `Mᵢ → Mⱼ` for `i > j`. -/
  smul_tr : ∀ {i j : I} (hji : j < i) {a : Λ}, a ∈ J j → ∀ m : M i, tr hji.le (a • m) = 0
  /-- The augmentation ideal annihilates `Ker(Mᵢ → Mⱼ)` for `i > j`. -/
  aug_ann : ∀ {i j : I} (hji : j < i) {a : Λ}, aug a = 0 → ∀ m : M i,
    tr hji.le m = 0 → a • m = 0

variable {aug : Λ →+* K} {unit : K →+* Λ} {J : I → Ideal Λ}
  {tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j}

/-- A square-zero ideal of an augmented algebra over a field lies in the augmentation ideal. -/
theorem IsSystem.aug_eq_zero (h : IsSystem aug unit J tr) {k : I} {a : Λ} (ha : a ∈ J k) :
    aug a = 0 := by
  have h2 : a * a ∈ J k * J k := Ideal.mul_mem_mul ha ha
  rw [h.sq_zero k, Submodule.mem_bot] at h2
  exact mul_self_eq_zero.mp (by rw [← map_mul, h2, map_zero])

/-- An element of a square-zero ideal acts by zero on the span of the new vectors. -/
private theorem IsSystem.smul_span_eq_zero (h : IsSystem aug unit J tr) {k : I} {a : Λ}
    (ha : a ∈ J k) {U : Type u} (w : AugSpan aug U) : a • w = 0 := by
  rw [AugSpan.smul_eq, h.aug_eq_zero ha, zero_smul]

/-! ### The triples indexing the new variables -/

/-- A triple `u = (i, j, ξ)` with `i > j` and `ξ ∈ Ker(Mᵢ → Mⱼ)`: one of these is adjoined to
`Λ` as a variable `x_u` by the step of Stacks 0CBE. -/
structure Triple (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) : Type u where
  /-- The index `i`, written `s(u)` in Stacks 0CBE. -/
  src : I
  /-- The index `j`, written `t(u)` in Stacks 0CBE. -/
  tgt : I
  /-- The two indices satisfy `i > j`. -/
  lt : tgt < src
  /-- The element `ξ` of `Mᵢ`, written `ξ_u` in Stacks 0CBE. -/
  elt : M src
  /-- The element lies in the kernel of the transition map `Mᵢ → Mⱼ`. -/
  mem : tr lt.le elt = 0

/-- The triples contributing a new vector `ε_{i,u}` to the stage `i`, namely those with
`s(u) ≥ i`. -/
abbrev Cone (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) (i : I) : Type u :=
  {u : Triple tr // i ≤ u.src}

/-- The image of `ξ_u` in `Mᵢ`, which is the value of `x_u ε_{i,u}`. -/
def xi {i : I} (u : Cone tr i) : M i := tr u.2 u.1.elt

/-- The inclusion of the triples contributing to the stage `i` into those contributing to a
smaller stage `j`; it is along this inclusion that `ε_{i,u} ↦ ε_{j,u}`. -/
def coneIncl {i j : I} (hji : j ≤ i) (u : Cone tr i) : Cone tr j := ⟨u.1, hji.trans u.2⟩

/-- The inclusion `coneIncl` of triples is injective. -/
theorem coneIncl_injective {i j : I} (hji : j ≤ i) :
    Function.Injective (coneIncl (tr := tr) hji) := fun _ _ huu' =>
  Subtype.ext (congrArg (fun v : Cone tr j => v.1) huu')

/-- The transition maps of the system send `ξ_u` at the stage `i` to `ξ_u` at the stage `j`. -/
theorem tr_xi (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i) (u : Cone tr i) :
    tr hji (xi u) = xi (coneIncl hji u) := h.tr_tr u.2 hji u.1.elt

/-- Once the transition map has passed the index `t(u)`, the element `ξ_u` has become zero. -/
theorem tr_xi_eq_zero (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i) (u : Cone tr i)
    (hj : j ≤ u.1.tgt) : tr hji (xi u) = 0 :=
  calc tr hji (xi u) = tr (hji.trans u.2) u.1.elt := h.tr_tr u.2 hji u.1.elt
    _ = tr (hj.trans u.1.lt.le) u.1.elt := rfl
    _ = tr hj (tr u.1.lt.le u.1.elt) := (h.tr_tr u.1.lt.le hj u.1.elt).symm
    _ = 0 := by rw [u.1.mem, map_zero]

/-- The augmentation ideal annihilates `ξ_u`. -/
theorem smul_xi_eq_zero (h : IsSystem aug unit J tr) {i : I} (u : Cone tr i) {a : Λ}
    (ha : aug a = 0) : a • xi u = 0 := by
  rw [xi, ← map_smul, h.aug_ann u.1.lt ha u.1.elt u.1.mem, map_zero]

/-! ### The pairing `x_u ε_{i,u} = ξ_u` -/

/-- The pairing of the step of Stacks 0CBE: the variable `x_u` paired with the vector
`ε_{i,u}` is the image `ξ_u` of the third component of `u` in `Mᵢ`, extended bilinearly. -/
def pairFun (unit : K →+* Λ) {i : I} (c : AugSpan aug (Triple tr))
    (e : AugSpan aug (Cone tr i)) : M i :=
  (AugSpan.toFinsupp e).sum fun u d => unit (AugSpan.toFinsupp c u.1 * d) • xi u

/-- The pairing is additive in its first argument. -/
theorem pairFun_add_left {i : I} (c c' : AugSpan aug (Triple tr))
    (e : AugSpan aug (Cone tr i)) :
    pairFun unit (c + c') e = pairFun unit c e + pairFun unit c' e := by
  simp only [pairFun, AugSpan.toFinsupp_add, Finsupp.add_apply, add_mul, map_add, add_smul,
    Finsupp.sum]
  exact Finset.sum_add_distrib

/-- The pairing is additive in its second argument. -/
theorem pairFun_add_right {i : I} (c : AugSpan aug (Triple tr))
    (e e' : AugSpan aug (Cone tr i)) :
    pairFun unit c (e + e') = pairFun unit c e + pairFun unit c e' := by
  simp only [pairFun, AugSpan.toFinsupp_add]
  refine Finsupp.sum_add_index' (fun u => ?_) (fun u d d' => ?_)
  · simp
  · rw [mul_add, map_add, add_smul]

/-- The augmentation ideal annihilates every value of the pairing. -/
theorem smul_pairFun_eq_zero (h : IsSystem aug unit J tr) {i : I}
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i)) {a : Λ} (ha : aug a = 0) :
    a • pairFun unit c e = 0 := by
  rw [pairFun, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [smul_comm, smul_xi_eq_zero h u ha, smul_zero]

/-- The action of `Λ` on a value of the pairing factors through the augmentation; this is what
makes the pairing `Λ`-bilinear and the extended module a module over the extended ring. -/
theorem smul_pairFun (h : IsSystem aug unit J tr) (a : Λ) {i : I}
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i)) :
    a • pairFun unit c e = unit (aug a) • pairFun unit c e := by
  have haug : aug (a - unit (aug a)) = 0 := by
    rw [map_sub, h.aug_unit, sub_self]
  have := smul_pairFun_eq_zero h c e haug
  rwa [sub_smul, sub_eq_zero] at this

/-- The pairing is `Λ`-linear in its first argument. -/
theorem pairFun_smul_left (h : IsSystem aug unit J tr) (a : Λ) {i : I}
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i)) :
    pairFun unit (a • c) e = a • pairFun unit c e := by
  rw [smul_pairFun h]
  simp only [pairFun, AugSpan.toFinsupp_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← smul_assoc, smul_eq_mul, ← map_mul, mul_assoc]

/-- The pairing is `Λ`-linear in its second argument. -/
theorem pairFun_smul_right (h : IsSystem aug unit J tr) (a : Λ) {i : I}
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i)) :
    pairFun unit c (a • e) = a • pairFun unit c e := by
  rw [smul_pairFun h]
  simp only [pairFun, AugSpan.toFinsupp_smul]
  rw [Finsupp.sum_smul_index' (fun u => by simp), Finsupp.sum,
    Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_eq_mul, ← smul_assoc, smul_eq_mul, ← map_mul, mul_left_comm]

/-- The pairing of the step of Stacks 0CBE as a `Λ`-bilinear map: the variable `x_u` paired
with the vector `ε_{i,u}` is the image of `ξ_u` in `Mᵢ`. -/
def pair (h : IsSystem aug unit J tr) (i : I) :
    AugSpan aug (Triple tr) →ₗ[Λ] AugSpan aug (Cone tr i) →ₗ[Λ] M i :=
  LinearMap.mk₂ Λ (pairFun unit) (pairFun_add_left (unit := unit))
    (fun a c e => pairFun_smul_left h a c e) (pairFun_add_right (unit := unit))
    (fun a c e => pairFun_smul_right h a c e)

/-- The bilinear map `pair h i` evaluates to `pairFun`. -/
@[simp] theorem pair_apply (h : IsSystem aug unit J tr) (i : I)
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i)) :
    pair h i c e = pairFun unit c e := rfl

/-- The value of the pairing on the two vectors attached to one triple is `ξ_u`: this is the
identity `x_u ε_{i,u} = ξ_u` of Stacks 0CBE. -/
theorem pair_single_single (h : IsSystem aug unit J tr) {i : I} (u : Cone tr i) :
    pair h i (AugSpan.single aug u.1) (AugSpan.single aug u) = xi u := by
  rw [pair_apply, pairFun, AugSpan.toFinsupp_single, Finsupp.sum_single_index
    (by simp), AugSpan.toFinsupp_single,
    Finsupp.single_eq_same, mul_one, map_one, one_smul]

/-- A value of the pairing dies in `Mⱼ` as soon as every variable occurring in it has
`t(u) ≥ j`. -/
theorem tr_pairFun_eq_zero (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i))
    (hc : ∀ u : Triple tr, AugSpan.toFinsupp c u ≠ 0 → j ≤ u.tgt) :
    tr hji (pairFun unit c e) = 0 := by
  rw [pairFun, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rcases eq_or_ne (AugSpan.toFinsupp c u.1) 0 with hu | hu
  · rw [hu, zero_mul, map_zero, zero_smul, map_zero]
  · rw [map_smul, tr_xi_eq_zero h hji u (hc u.1 hu), smul_zero]

/-- The pairing is compatible with the transition maps of the system and the inclusion
`ε_{i,u} ↦ ε_{j,u}` of the new vectors; this is what makes the transition maps of the extended
system linear over the extended ring. -/
theorem tr_pairFun (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (c : AugSpan aug (Triple tr)) (e : AugSpan aug (Cone tr i)) :
    tr hji (pairFun unit c e) =
      pairFun unit c
        (AugSpan.ofKLinear (Finsupp.lmapDomain K K (coneIncl (tr := tr) hji)) e) := by
  rw [pairFun, pairFun, map_finsuppSum, AugSpan.toFinsupp_ofKLinear,
    Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index_inj (coneIncl_injective hji)]
  refine Finsupp.sum_congr fun u _ => ?_
  rw [map_smul, tr_xi h hji u]
  rfl

/-! ### The extended augmented algebra and its ideals -/

/-- The extended algebra `Λ' = Λ ⊕ K^{(U)}` of the step of Stacks 0CBE, in which the new
variables `x_u` have `x_u x_{u'} = 0` and are annihilated by the augmentation ideal. -/
abbrev ExtRing (aug : Λ →+* K) (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) : Type u :=
  TrivSqZeroExt Λ (AugSpan aug (Triple tr))

/-- The augmentation of the extended algebra. -/
def augExt (aug : Λ →+* K) (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) : ExtRing aug tr →+* K :=
  aug.comp (TrivSqZeroExt.fstHom Λ Λ (AugSpan aug (Triple tr))).toRingHom

/-- The unit of the extended algebra. -/
def unitExt (unit : K →+* Λ) (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) :
    K →+* ExtRing aug tr :=
  (TrivSqZeroExt.inlHom Λ (AugSpan aug (Triple tr))).comp unit

/-- The augmentation of the extended algebra is `aug` on the first component. -/
@[simp] theorem augExt_apply (x : ExtRing aug tr) :
    augExt aug tr x = aug (TrivSqZeroExt.fst x) := rfl

/-- The unit of the extended algebra is `unit` followed by the inclusion of `Λ`. -/
@[simp] theorem unitExt_apply (c : K) :
    unitExt (aug := aug) unit tr c = TrivSqZeroExt.inl (unit c) := rfl

/-- The extended ideal `J'ₖ = JₖΛ' + (x_u; t(u) ≥ k)` of the step of Stacks 0CBE, described by
its elements: the first component lies in `Jₖ` and only variables with `t(u) ≥ k` occur in the
second. -/
def Jext (h : IsSystem aug unit J tr) (k : I) : Ideal (ExtRing aug tr) where
  carrier := {x : ExtRing aug tr | TrivSqZeroExt.fst x ∈ J k ∧
    ∀ u : Triple tr, AugSpan.toFinsupp (TrivSqZeroExt.snd x) u ≠ 0 → k ≤ u.tgt}
  add_mem' {x y} hx hy := by
    refine ⟨?_, fun u hu => ?_⟩
    · exact (TrivSqZeroExt.fst_add x y) ▸ Ideal.add_mem _ hx.1 hy.1
    · rw [TrivSqZeroExt.snd_add, AugSpan.toFinsupp_add, Finsupp.add_apply] at hu
      rcases eq_or_ne (AugSpan.toFinsupp (TrivSqZeroExt.snd x) u) 0 with hx' | hx'
      · exact hy.2 u fun hy' => hu (by rw [hx', hy', add_zero])
      · exact hx.2 u hx'
  zero_mem' := ⟨Submodule.zero_mem _, fun _ hu => absurd rfl hu⟩
  smul_mem' c {x} hx := by
    refine ⟨?_, fun u hu => ?_⟩
    · rw [smul_eq_mul, TrivSqZeroExt.fst_mul]
      exact Ideal.mul_mem_left _ _ hx.1
    · rw [smul_eq_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, AugSpan.toFinsupp_add,
        AugSpan.toFinsupp_smul, AugSpan.toFinsupp_smul, h.aug_eq_zero hx.1, zero_smul,
        add_zero, Finsupp.smul_apply, smul_eq_mul] at hu
      exact hx.2 u fun hu' => hu (by rw [hu', mul_zero])
  -- the carrier is the ideal `JₖΛ' + (x_u; t(u) ≥ k)` because `Jₖ` lies in the augmentation
  -- ideal, so `Jₖ` already annihilates the new variables.

/-- An element lies in `J'ₖ` if and only if its first component lies in `Jₖ` and only
variables with `t(u) ≥ k` occur in its second component. -/
theorem mem_Jext_iff (h : IsSystem aug unit J tr) (k : I) (x : ExtRing aug tr) :
    x ∈ Jext h k ↔ TrivSqZeroExt.fst x ∈ J k ∧
      ∀ u : Triple tr, AugSpan.toFinsupp (TrivSqZeroExt.snd x) u ≠ 0 → k ≤ u.tgt :=
  Iff.rfl

/-- An element of `Jₖ` lies in `J'ₖ`. -/
theorem inl_mem_Jext (h : IsSystem aug unit J tr) {k : I} {a : Λ} (ha : a ∈ J k) :
    (TrivSqZeroExt.inl a : ExtRing aug tr) ∈ Jext h k :=
  ⟨ha, fun _ hu => absurd rfl hu⟩

/-- A new variable `x_u` lies in `J'ₖ` as soon as `t(u) ≥ k`. -/
theorem inr_single_mem_Jext (h : IsSystem aug unit J tr) {k : I} (u : Triple tr)
    (hk : k ≤ u.tgt) :
    (TrivSqZeroExt.inr (AugSpan.single aug u) : ExtRing aug tr) ∈ Jext h k := by
  refine ⟨Submodule.zero_mem _, fun v hv => ?_⟩
  rw [TrivSqZeroExt.snd_inr, AugSpan.toFinsupp_single] at hv
  rcases eq_or_ne v u with rfl | hvu
  · exact hk
  · exact absurd (Finsupp.single_eq_of_ne hvu : (Finsupp.single u (1 : K)) v = 0) hv

/-- The new variables `x_u` with `t(u) ≥ k`: together with the image of `Jₖ` they generate the
ideal `J'ₖ`. -/
def newVars (aug : Λ →+* K) (tr : ∀ {i j : I}, j ≤ i → M i →ₗ[Λ] M j) (k : I) :
    Set (ExtRing aug tr) :=
  {x | ∃ u : Triple tr, k ≤ u.tgt ∧ x = TrivSqZeroExt.inr (AugSpan.single aug u)}

/-- An element of the square-zero part of the extended algebra in which only variables with
`t(u) ≥ k` occur is a combination of those variables. -/
theorem inr_mem_span_newVars (h : IsSystem aug unit J tr) (k : I) :
    ∀ w : Triple tr →₀ K, (∀ u : Triple tr, w u ≠ 0 → k ≤ u.tgt) →
      (TrivSqZeroExt.inr (AugSpan.ofFinsupp aug w) : ExtRing aug tr) ∈
        Ideal.span (newVars aug tr k) := by
  intro w
  induction w using Finsupp.induction with
  | zero =>
    intro _
    rw [AugSpan.ofFinsupp_zero, TrivSqZeroExt.inr_zero]
    exact Submodule.zero_mem _
  | single_add a b f ha hb ih =>
    intro hw
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have hka : k ≤ a.tgt := hw a (by
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero])
    have hwf : ∀ u : Triple tr, f u ≠ 0 → k ≤ u.tgt := fun u hu => hw u (by
      rcases eq_or_ne u a with rfl | hua
      · exact absurd hfa hu
      · rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hua, zero_add])
    rw [AugSpan.ofFinsupp_add, TrivSqZeroExt.inr_add]
    refine Submodule.add_mem _ ?_ (ih hwf)
    have hsingle :
        (TrivSqZeroExt.inr (AugSpan.ofFinsupp aug (Finsupp.single a b)) : ExtRing aug tr)
          = TrivSqZeroExt.inl (unit b) * TrivSqZeroExt.inr (AugSpan.single aug a) := by
      rw [AugSpan.ofFinsupp_single, TrivSqZeroExt.inl_mul_inr, AugSpan.smul_eq, h.aug_unit]
    rw [hsingle]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, hka, rfl⟩)

/-- **The extended ideal is the one of Stacks 0CBE:** `J'ₖ = JₖΛ' + (x_u; t(u) ≥ k)`. -/
theorem Jext_eq (h : IsSystem aug unit J tr) (k : I) :
    Jext h k = Ideal.map (TrivSqZeroExt.inlHom Λ (AugSpan aug (Triple tr))) (J k)
      ⊔ Ideal.span (newVars aug tr k) := by
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
  · rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hx.1))
      (Submodule.mem_sup_right (inr_mem_span_newVars h k _ hx.2))
  · exact Ideal.map_le_iff_le_comap.mpr fun _ ha => inl_mem_Jext h ha
  · rw [Ideal.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact inr_single_mem_Jext h u hu

/-! ### The extended system -/

/-- The transition map of the extended system: the given transition on the stage module and
the inclusion `ε_{i,u} ↦ ε_{j,u}` on the new vectors. Both stages are modules over the *same*
extended ring, so this is linear and not merely semilinear. -/
def trExt (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i) :
    Paired (pair h i) →ₗ[ExtRing aug tr] Paired (pair h j) :=
  Paired.map (tr hji) (AugSpan.ofKLinear (Finsupp.lmapDomain K K (coneIncl (tr := tr) hji)))
    (fun c e => tr_pairFun h hji c e)

/-- On the stage module, the extended transition map is the given transition map. -/
@[simp] theorem fst_trExt (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (z : Paired (pair h i)) :
    Paired.fst (trExt h hji z) = tr hji (Paired.fst z) := rfl

/-- On the new vectors, the extended transition map is the inclusion `ε_{i,u} ↦ ε_{j,u}`. -/
@[simp] theorem snd_trExt (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i)
    (z : Paired (pair h i)) :
    AugSpan.toFinsupp (Paired.snd (trExt h hji z)) =
      Finsupp.mapDomain (coneIncl (tr := tr) hji) (AugSpan.toFinsupp (Paired.snd z)) := rfl

/-- The map `Mᵢ → M'ᵢ` of the step commutes with the transition maps: `Φ → Φ'` is a morphism
of systems. -/
theorem trExt_mk (h : IsSystem aug unit J tr) {i j : I} (hji : j ≤ i) (m : M i) :
    trExt h hji (Paired.mk (pair h i) m 0) = Paired.mk (pair h j) (tr hji m) 0 := by
  refine Paired.ext rfl ?_
  show AugSpan.ofKLinear (Finsupp.lmapDomain K K (coneIncl (tr := tr) hji)) 0 = 0
  rw [map_zero]

/-- The map `Mᵢ → M'ᵢ` of the step is compatible with the scalars `K`. -/
theorem unitExt_smul_mk (h : IsSystem aug unit J tr) {i : I} (c : K) (m : M i) :
    (unitExt (aug := aug) unit tr c) • Paired.mk (pair h i) m 0 =
      Paired.mk (pair h i) (unit c • m) 0 := by
  rw [unitExt_apply, Paired.inl_smul, Paired.fst_mk, Paired.snd_mk, smul_zero]

/-- **The identity that kills the obstruction.** For `j < i` and `ξ ∈ Ker(Mᵢ → Mⱼ)`, the new
variable `x_u` of the triple `u = (i, j, ξ)` sends the new vector `ε_{i,u}` to `ξ`; this is
the formula `ξ = x_{(i,j,ξ)} ε_{i,(i,j,ξ)}` of Stacks 0CBE. -/
theorem inr_single_smul_mk (h : IsSystem aug unit J tr) {i j : I} (hji : j < i) (m : M i)
    (hm : tr hji.le m = 0) :
    (TrivSqZeroExt.inr (AugSpan.single aug ⟨i, j, hji, m, hm⟩) : ExtRing aug tr) •
        Paired.mk (pair h i) 0 (AugSpan.single aug ⟨⟨i, j, hji, m, hm⟩, le_refl i⟩) =
      Paired.mk (pair h i) m 0 := by
  rw [Paired.inr_smul, Paired.snd_mk,
    pair_single_single h (⟨⟨i, j, hji, m, hm⟩, le_refl i⟩ : Cone tr i), xi]
  exact congrArg (fun x => Paired.mk (pair h i) x 0) (h.tr_self m)

/-- **The point of the step of Stacks 0CBE.** For `j < i`, every element of `Ker(Mᵢ → Mⱼ)`
lies in `J'ⱼ M'ᵢ`, hence maps to zero in `M'ᵢ/J'ⱼM'ᵢ`: the obstruction to `Mⱼ = Mᵢ/JⱼMᵢ`
present at the stage `Φ` has been killed at the stage `Φ'`. -/
theorem mk_mem_Jext_smul_top (h : IsSystem aug unit J tr) {i j : I} (hji : j < i) (m : M i)
    (hm : tr hji.le m = 0) :
    Paired.mk (pair h i) m 0 ∈
      (Jext h j) • (⊤ : Submodule (ExtRing aug tr) (Paired (pair h i))) := by
  rw [← inr_single_smul_mk h hji m hm]
  exact Submodule.smul_mem_smul (inr_single_mem_Jext h ⟨i, j, hji, m, hm⟩ (le_refl j))
    Submodule.mem_top

/-- **The one-step extension of a system is again a system.** The extended ideals are of
square zero and still decrease, the extended transition maps still kill `J'ⱼ M'ᵢ`, and the
extended augmentation ideal still annihilates the kernels — the property which makes a further
step possible. -/
theorem isSystem_ext (h : IsSystem aug unit J tr) :
    IsSystem (M := fun i => Paired (pair h i)) (augExt aug tr) (unitExt unit tr) (Jext h)
      (fun {_ _} hji => trExt h hji) where
  aug_unit c := by rw [augExt_apply, unitExt_apply, TrivSqZeroExt.fst_inl, h.aug_unit]
  tr_self {i} z := by
    refine Paired.ext (h.tr_self (Paired.fst z)) ?_
    show AugSpan.ofKLinear (Finsupp.lmapDomain K K (coneIncl (tr := tr) (le_refl i)))
      (Paired.snd z) = Paired.snd z
    have hid : coneIncl (tr := tr) (le_refl i) = id := rfl
    rw [hid]
    exact Finsupp.mapDomain_id
  tr_tr {i j k} hji hkj z := by
    refine Paired.ext (h.tr_tr hji hkj (Paired.fst z)) ?_
    show Finsupp.mapDomain (coneIncl (tr := tr) hkj)
        (Finsupp.mapDomain (coneIncl (tr := tr) hji) (AugSpan.toFinsupp (Paired.snd z)))
      = Finsupp.mapDomain (coneIncl (tr := tr) (hkj.trans hji))
        (AugSpan.toFinsupp (Paired.snd z))
    rw [← Finsupp.mapDomain_comp]
    rfl
  sq_zero i := by
    refine le_antisymm (Ideal.mul_le.mpr fun x hx y hy => ?_) bot_le
    rw [Submodule.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_zero]
      simpa [h.sq_zero i] using Ideal.mul_mem_mul hx.1 hy.1
    · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_zero, op_smul_eq_smul,
        h.smul_span_eq_zero hx.1, h.smul_span_eq_zero hy.1, add_zero]
  antitone {i j} hji := fun x hx =>
    ⟨h.antitone hji hx.1, fun u hu => hji.trans (hx.2 u hu)⟩
  smul_tr {i j} hji {a} ha z := by
    refine (Paired.map_eq_zero_iff _ _ _).mpr ⟨?_, ?_⟩
    · rw [Paired.fst_smul, map_add, pair_apply, h.smul_tr hji ha.1 (Paired.fst z), zero_add]
      exact tr_pairFun_eq_zero h hji.le _ _ ha.2
    · show AugSpan.ofKLinear (Finsupp.lmapDomain K K (coneIncl (tr := tr) hji.le))
        (Paired.snd ((a : ExtRing aug tr) • z)) = 0
      rw [Paired.snd_smul, h.smul_span_eq_zero ha.1, map_zero]
  aug_ann {i j} hji {a} ha z hz := by
    obtain ⟨hz1, hz2⟩ := (Paired.map_eq_zero_iff _ _ _).mp hz
    have hsnd : Paired.snd z = 0 :=
      (Finsupp.mapDomain_injective (coneIncl_injective hji.le) (by
        rw [Finsupp.mapDomain_zero]
        exact congrArg AugSpan.toFinsupp hz2) : AugSpan.toFinsupp (Paired.snd z) = 0)
    refine Paired.ext ?_ ?_
    · rw [Paired.fst_smul, hsnd, map_zero, add_zero, Paired.fst_zero]
      exact h.aug_ann hji ha (Paired.fst z) hz1
    · rw [Paired.snd_smul, hsnd, smul_zero, Paired.snd_zero]

/-- **The initial datum `Φ₀ = (K, (0), (Vᵢ))` of Stacks 0CBE is a system.** Any inverse system
of `K`-vector spaces over the index is one, with `Λ = K` and all ideals zero; in particular the
class of data `IsSystem` describes is not empty, and the extra condition on the augmentation
ideal does not empty it either, since over `K` itself that ideal is zero. -/
theorem isSystem_initial {K I : Type u} [Field K] [Preorder I] {V : I → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (trV : ∀ {i j : I}, j ≤ i → V i →ₗ[K] V j)
    (htr : ∀ {i : I} (m : V i), trV (le_refl i) m = m)
    (htr' : ∀ {i j k : I} (hji : j ≤ i) (hkj : k ≤ j) (m : V i),
      trV hkj (trV hji m) = trV (hkj.trans hji) m) :
    IsSystem (RingHom.id K) (RingHom.id K) (fun _ : I => (⊥ : Ideal K)) trV where
  aug_unit _ := rfl
  tr_self := htr
  tr_tr := htr'
  sq_zero _ := Ideal.mul_bot _
  antitone _ := le_refl _
  smul_tr := by
    intro _ _ _ a ha m
    rw [show a = (0 : K) from (Submodule.mem_bot K).mp ha, zero_smul, map_zero]
  aug_ann := by
    intro _ _ _ a ha m _
    rw [show a = (0 : K) from ha, zero_smul]

end System

end

end Stacks.CBESystem

end
