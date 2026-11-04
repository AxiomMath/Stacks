module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGeneralPosition

/-!
# The `1`-jet of a member of a subsystem cut out by linear conditions

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and let `x` be a
closed point of `X`. The proof of [Stacks, Tag 0FH7] replaces the linear system by the subspace
of members vanishing at two chosen closed points `x` and `x'`, and then asserts that a general
member of *that* subspace still has nonzero `1`-jet at `x` — that its germ avoids `𝔪_x²ℒ_x`.
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero`
reduces the assertion to the single hypothesis `ev_x ≠ 0` for the subspace. This module supplies
that hypothesis.

The content is that the linear conditions imposed are *independent* of the `1`-jet condition at
`x`. That is a dimension count and nothing more. Where the whole system generates `ℒ` and the
morphism `φ_{ℒ,ψ} : X → 𝐏(V)` it determines is an immersion, the evaluation

`ev_x : V ⟶ ℒ_x/𝔪_x²ℒ_x`

is *surjective* at a closed point
(`Stacks.ImmersionEvaluationSurjective.surjective_evalQuotient_of_isClosed`), and its target has
dimension `dim_x X + 1` (`Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`). A subspace cut
out as the kernel of a map `T : V ⟶ M` therefore still meets the complement of `ker ev_x` as soon
as `dim_k M < dim_x X + 1`: pick `dim_k M + 1` members whose evaluations are linearly
independent, and the map sending a coefficient tuple to the `T`-image of the corresponding
combination has a larger source than target, hence a nonzero kernel; a nonzero tuple in it gives
a member killed by `T` whose evaluation, being a nontrivial combination of independent vectors,
is nonzero.

For [Stacks, Tag 0FH7] the two conditions are vanishing at `x` and vanishing at `x'`, so
`dim_k M = 2` and the hypothesis is `2 ≤ dim_x X` — the dimension range of the Bertini branch of
that proof, whose curve case the source treats separately. The count is therefore not a defect of
this argument but the same case division the source makes.

What this does **not** give is the surjection of the subsystem onto the whole of
`𝔪_xℒ_x/𝔪_x²ℒ_x`. Cutting by two conditions loses at most two dimensions of a space of
dimension `dim_x X + 1`, which leaves the image of the subsystem of codimension at most one in
`𝔪_xℒ_x/𝔪_x²ℒ_x`; nonvanishing is what the consumer needs and what is proved here.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.restrictSystem` is the standing situation obtained by replacing
  the linear system `V` by a subspace `W` of it, keeping the scheme, the invertible module and
  the presentation `ψ`. It is reducible: the base field, the linear system, the scheme, the
  module and `ψ` are wanted transparently, so that the evaluation of the subsystem at a point
  *is* the evaluation of the system restricted to the subspace, and so that the parameter space
  of the subsystem is the one its own dimension determines.

## Main results

* `Stacks.Bertini.FamilyDivisors.exists_eq_zero_apply_ne_zero`: the linear-algebra heart, with no
  geometry in it — a surjection whose target has dimension exceeding that of `M` is nonzero on
  the kernel of any `M`-valued map.
* `Stacks.Bertini.FamilyDivisors.surjective_evalVector_of_isImmersive`: the evaluation is
  surjective as a map on `V` itself, under hypotheses (2) and (3) of [Stacks, Tag 0FD6] at a
  closed point.
* `Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_restrictSystem_ker`: **the `1`-jet surjection
  for a subsystem cut out by linear conditions**, the hypothesis the general-position step of
  [Stacks, Tag 0FH7] rests on.
* `Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_restrictSystem_inf_ker`: the same for the
  two conditions of that proof, vanishing at `x` and at `x'`, under `2 ≤ dim_x X`.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_restrictSystem` and
  `…exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_restrictSystem`: the general-position open
  of the subsystem, and a single nonzero member of the subsystem whose divisor is smooth and
  whose `1`-jet at `x` is nonzero.

## Implementation notes

The condition map is `M`-valued rather than a tuple of linear forms because the subspace it is
wanted for is already presented as a kernel: the linear system of [Stacks, Tag 0FH7] is
`Stacks.SectionsVanishingOnSubscheme.vanishingSections`, which *is* the kernel of the restriction
map to the closed subscheme being avoided. A tuple-of-forms version would force that kernel to be
re-presented. `Module.Finite D.k M` is a hypothesis rather than a consequence: only the
non-injectivity of a map out of a space of dimension `dim_k M + 1` is used, and that needs the
target finite.

The dimension of `X` at the point enters as `AlgebraicGeometry.topologicalKrullDimAt`, exactly as
in `Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`, and
`Stacks.Bertini.FamilyDivisors.exists_natCast_eq_topologicalKrullDimAt_of_isClosed` says such a
natural number exists at every closed point of a smooth `X`, so assuming one costs nothing.

Surjectivity of the evaluation is read off the coordinate form through
`Stacks.Bertini.FamilyDivisors.range_evalCoord_sectionOf`, which identifies the two ranges, so
the basis at which hypothesis (3) is taken and the conclusion are decoupled, as they already are
in `Stacks.Bertini.FamilyDivisors.surjective_evalCoord_sectionOf_of_isClosed`.

**No `@[stacks]` attribute is attached.** This is the input to the step the proof of
[Stacks, Tag 0FH7] omits, not the assertion of a tag.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ImmersionEvaluationSurjective

universe u v

namespace Stacks.Bertini.FamilyDivisors

/-! ### The linear-algebra heart -/

/-- **A surjection survives a smaller family of linear conditions.** Let `φ : W → Q` be a
surjection of vector spaces over a field, let `T : W → M` be linear with `M` finite dimensional,
and suppose `dim M < dim Q`. Then `φ` does not vanish on `ker T`.

Choose `dim M + 1` vectors of `Q` that are linearly independent and lift them along `φ`. The map
sending a coefficient tuple to the `T`-image of the corresponding combination of the lifts has
source of dimension `dim M + 1` and target of dimension `dim M`, so it is not injective; a
nonzero tuple in its kernel gives a vector of `ker T` whose image under `φ` is a nontrivial
combination of the independent vectors, hence nonzero. -/
theorem exists_eq_zero_apply_ne_zero {K W Q M : Type*} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup Q] [Module K Q]
    [AddCommGroup M] [Module K M] [Module.Finite K M]
    (φ : W →ₗ[K] Q) (hφ : Function.Surjective φ) (T : W →ₗ[K] M)
    (hdim : Module.finrank K M + 1 ≤ Module.finrank K Q) :
    ∃ w : W, T w = 0 ∧ φ w ≠ 0 := by
  classical
  obtain ⟨q, hq⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := Q) hdim
  choose w hw using fun j => hφ (q j)
  set c : (Fin (Module.finrank K M + 1) → K) →ₗ[K] W := Fintype.linearCombination K w with hc
  have hnotinj : ¬ Function.Injective (T.comp c) := by
    intro h
    have hle := LinearMap.finrank_le_finrank_of_injective (f := T.comp c) h
    rw [Module.finrank_fin_fun] at hle
    omega
  obtain ⟨a, ha, ha0⟩ : ∃ a, (T.comp c) a = 0 ∧ a ≠ 0 := by
    rw [← LinearMap.ker_eq_bot] at hnotinj
    obtain ⟨a, haker, ha0⟩ := Submodule.ne_bot_iff _ |>.mp hnotinj
    exact ⟨a, haker, ha0⟩
  refine ⟨c a, ha, ?_⟩
  have hφc : φ (c a) = ∑ j, a j • q j := by
    rw [hc, Fintype.linearCombination_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hw j]
  rw [hφc]
  intro h0
  exact ha0 (funext (Fintype.linearIndependent_iff.mp hq a h0))

variable (D : FamilyDivisors.{u, u})

/-! ### The evaluation of the whole system is surjective -/

/-- **The evaluation `ev_x : V → ℒ_x/𝔪_x²ℒ_x` is surjective as a map on `V` itself**, at a closed
point of a scheme locally of finite type over an algebraically closed field, under hypotheses (2)
and (3) of [Stacks, Tag 0FD6].

This is `Stacks.Bertini.FamilyDivisors.surjective_evalCoord_sectionOf_of_isClosed` read through
`Stacks.Bertini.FamilyDivisors.range_evalCoord_sectionOf`, which says the coordinate form of the
evaluation and the basis-free one have the same range; the basis at which hypothesis (3) is taken
is therefore immaterial. -/
theorem surjective_evalVector_of_isImmersive [IsAlgClosed D.k] [LocallyOfFiniteType D.toBase]
    {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X)) :
    Function.Surjective (D.evalVector x) := by
  rw [← LinearMap.range_eq_top, ← D.range_evalCoord_sectionOf b x, LinearMap.range_eq_top]
  exact D.surjective_evalCoord_sectionOf_of_isClosed himm b hx

/-- **A member killed by the linear conditions whose `1`-jet at `x` is nonzero.** At a closed
point `x` of a smooth `X` of dimension `n` there, over an algebraically closed field, under
hypotheses (2) and (3) of [Stacks, Tag 0FD6], and for a linear map `T : V → M` with
`dim_k M ≤ n`, some member of `ker T` has germ at `x` outside `𝔪_x²ℒ_x`.

The target of the evaluation has dimension `n + 1`
(`Stacks.JetFinrank.finrank_evalQuotient_of_isClosed`) and the evaluation is surjective onto it,
so `Stacks.Bertini.FamilyDivisors.exists_eq_zero_apply_ne_zero` applies. -/
theorem exists_eq_zero_evalVector_ne_zero [IsAlgClosed D.k] [Smooth D.toBase]
    {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    {n : ℕ} (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    {M : Type u} [AddCommGroup M] [Module D.k M] [Module.Finite D.k M]
    (T : D.V →ₗ[D.k] M) (hM : Module.finrank D.k M ≤ n) :
    ∃ v : D.V, T v = 0 ∧ D.evalVector x v ≠ 0 :=
  exists_eq_zero_apply_ne_zero (D.evalVector x)
    (D.surjective_evalVector_of_isImmersive himm hx) T
    (by rw [Stacks.JetFinrank.finrank_evalQuotient_of_isClosed D.toBase x hx hdim]; omega)

/-! ### The standing situation on a subspace of the linear system -/

/-- **The standing situation of the Bertini theorems on a subspace of the linear system.** The
scheme, the invertible module and the presentation `ψ` are unchanged; the linear system is
replaced by a subspace `W` of it and the basis by a basis of `W`.

Reducible on purpose. Everything a consumer asks of the subsystem is asked of the data it shares
with the system it came from: that the evaluation of the subsystem at a point is the evaluation
of the system restricted to `W`
(`Stacks.Bertini.FamilyDivisors.restrictSystem_evalVector`), and that the parameter space is the
affine space on `dim_k W` coordinates over the same field. Both are definitional, and instance
search has to see through the construction to find them. -/
@[reducible]
def restrictSystem (W : Submodule D.k D.V) : FamilyDivisors.{u, u} where
  k := D.k
  V := W
  X := D.X
  toBase := D.toBase
  L := D.L
  ψ := D.ψ ∘ₗ W.subtype
  basis := Module.finBasis D.k W

/-- **The section of a member of the subsystem is its section as a member of the system.** -/
theorem restrictSystem_sectionOf (W : Submodule D.k D.V) (w : W) :
    (D.restrictSystem W).sectionOf w = D.sectionOf (w : D.V) := rfl

/-- **The evaluation of the subsystem is the evaluation of the system restricted to `W`.** -/
theorem restrictSystem_evalVector (W : Submodule D.k D.V) (x : D.X) (w : W) :
    (D.restrictSystem W).evalVector x w = D.evalVector x (w : D.V) := rfl

/-! ### The 1-jet surjection for the subsystem -/

/-- **The `1`-jet surjection for a subsystem cut out by linear conditions.** Let `X` be smooth
over an algebraically closed field and of dimension `n` at a closed point `x`, let the linear
system generate `ℒ` and define an immersion `X → 𝐏(V)` — hypotheses (2) and (3) of
[Stacks, Tag 0FD6] — and let `T : V → M` be linear with `M` of dimension at most `n`. Then the
evaluation of the subsystem `ker T` at `x` is not identically zero.

This is the hypothesis that
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero`
turns into the general-position assertion of [Stacks, Tag 0FH7]. For that proof `ker T` is the
space of sections vanishing at the two closed points being separated — the kernel of the
restriction map to those points — so `dim_k M = 2` and the hypothesis reads `2 ≤ n`. -/
theorem evalVector_ne_zero_restrictSystem_ker [IsAlgClosed D.k] [Smooth D.toBase]
    {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    {n : ℕ} (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    {M : Type u} [AddCommGroup M] [Module D.k M] [Module.Finite D.k M]
    (T : D.V →ₗ[D.k] M) (hM : Module.finrank D.k M ≤ n) :
    (D.restrictSystem (LinearMap.ker T)).evalVector x ≠ 0 := by
  obtain ⟨v, hv0, hvne⟩ := D.exists_eq_zero_evalVector_ne_zero himm hx hdim T hM
  intro h0
  have h : (D.restrictSystem (LinearMap.ker T)).evalVector x ⟨v, hv0⟩ = 0 := by rw [h0]; rfl
  exact hvne h

/-- **The `1`-jet surjection for the subsystem cut out by two linear conditions**, which is the
shape [Stacks, Tag 0FH7] uses: the members vanishing at `x` and at `x'`. The hypothesis is
`2 ≤ n`, the dimension range of the Bertini branch of that proof. -/
theorem evalVector_ne_zero_restrictSystem_inf_ker [IsAlgClosed D.k] [Smooth D.toBase]
    {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) (l₁ l₂ : D.V →ₗ[D.k] D.k) {x : D.X}
    (hx : IsClosed ({x} : Set D.X)) {n : ℕ}
    (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) (hn : 2 ≤ n) :
    (D.restrictSystem (LinearMap.ker l₁ ⊓ LinearMap.ker l₂)).evalVector x ≠ 0 := by
  rw [← LinearMap.ker_prod l₁ l₂]
  exact D.evalVector_ne_zero_restrictSystem_ker himm hx hdim (l₁.prod l₂)
    (by rw [Module.finrank_prod, Module.finrank_self]; exact hn)

/-! ### The general-position open of the subsystem -/

/-- **The general-position assertion of [Stacks, Tag 0FH7] for a subsystem cut out by linear
conditions.** There is a nonempty open of the parameter space `𝔸^{dim W}_k` of the subsystem at
every `k`-rational parameter of which the corresponding member of the subsystem has germ at `x`
outside `𝔪_x²ℒ_x`.

The two halves are
`Stacks.Bertini.FamilyDivisors.evalVector_ne_zero_restrictSystem_ker`, the `1`-jet surjection,
and `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_`
`zero`, the openness. -/
theorem exists_nonempty_opens_notMem_maximalSqSmul_restrictSystem [IsAlgClosed D.k]
    [Smooth D.toBase] {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    {n : ℕ} (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    {M : Type u} [AddCommGroup M] [Module D.k M] [Module.Finite D.k M]
    (T : D.V →ₗ[D.k] M) (hM : Module.finrank D.k M ≤ n) :
    ∃ U : (D.restrictSystem (LinearMap.ker T)).parameterBase.Opens,
      (U : Set (D.restrictSystem (LinearMap.ker T)).parameterBase).Nonempty ∧
      ∀ c : Fin (Module.finrank D.k (LinearMap.ker T)) → D.k,
        (∀ q : Spec (.of D.k), (D.restrictSystem (LinearMap.ker T)).parameterPoint c q ∈ U) →
          (D.L.presheaf.Γgerm x).hom
            ((D.restrictSystem (LinearMap.ker T)).constCoeffSection c) ∉ maximalSqSmul D.L x :=
  FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_of_evalVector_ne_zero
    (D.restrictSystem (LinearMap.ker T))
    (D.evalVector_ne_zero_restrictSystem_ker himm hx hdim T hM)

/-- **A nonzero member of the subsystem whose divisor is smooth and whose `1`-jet at `x` is
nonzero.** The smoothness comes from a
`Stacks.Bertini.FamilyDivisors.ForGeneral` conclusion of [Stacks, Tag 0FD6] for the subsystem and
the `1`-jet from the general-position open above; the parameter space is irreducible, so the two
nonempty opens meet.

This is the conjunction the Bertini step of [Stacks, Tag 0FH7] needs for the subsystem of
sections vanishing at the points being separated: the smoothness conclusion alone leaves the
divisor smooth only away from those points. -/
theorem exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_restrictSystem [IsAlgClosed D.k]
    [Smooth D.toBase] {p : ℕ} {b : Module.Basis (Fin (p + 1)) D.k D.V} {hb : D.GeneratesBy b}
    (himm : D.IsImmersive b hb) {x : D.X} (hx : IsClosed ({x} : Set D.X))
    {n : ℕ} (hdim : topologicalKrullDimAt D.X x = (n : WithBot ℕ∞))
    {M : Type u} [AddCommGroup M] [Module D.k M] [Module.Finite D.k M]
    (T : D.V →ₗ[D.k] M) (hM : Module.finrank D.k M ≤ n)
    (h : (D.restrictSystem (LinearMap.ker T)).ForGeneral fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k (LinearMap.ker T)) → K,
        w = ∑ i, TensorProduct.tmul D.k
            ((D.restrictSystem (LinearMap.ker T)).basis i) (a i) →
          Smooth (((D.restrictSystem (LinearMap.ker T)).specializedDivisor K a).subschemeι ≫
            (D.restrictSystem (LinearMap.ker T)).baseChangeToSpec K)) :
    ∃ w : LinearMap.ker T, w ≠ 0 ∧
      Smooth (((D.restrictSystem (LinearMap.ker T)).divisor w).subschemeι ≫ D.toBase) ∧
      (D.L.presheaf.Γgerm x).hom (D.sectionOf (w : D.V)) ∉ maximalSqSmul D.L x :=
  FamilyDivisors.exists_ne_zero_smooth_divisor_notMem_maximalSqSmul_of_evalVector_ne_zero
    (D.restrictSystem (LinearMap.ker T))
    (D.evalVector_ne_zero_restrictSystem_ker himm hx hdim T hM) h

end Stacks.Bertini.FamilyDivisors

end
