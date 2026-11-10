module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage

/-!
# Adjoining a set of graded divided power variables of prescribed degrees

Let `A` be a strictly graded-commutative nonnegatively graded algebra with divided powers on its
positive even part, let `J` be an arbitrary index set and let `deg : J → ℕ` assign a positive
degree to each index. This file constructs the graded algebra with divided powers obtained from
`A` by adjoining one variable of degree `deg j` for each `j : J`: an exterior variable when
`deg j` is odd, and a divided-power variable when `deg j` is even. The result is characterized
by a universal property among graded algebras with divided powers — a coefficient map and a
family of elements of the target, the one indexed by `j` homogeneous of degree `deg j`,
determine a unique map out of the construction preserving the grading and the divided powers —
and it is presented as the union of its finite-variable stages, each of which is the extension
of its predecessor by a single variable.

The construction proceeds in three steps. Adjoining a finite set of variables is the iteration
of the one-variable extensions, which are the exterior extension in odd degree and the
divided-power extension in even degree; both satisfy the same one-variable universal property,
so the iteration does too. These finite extensions form a directed system indexed by the finite
subsets of `J`, whose transition maps are the unique maps fixing the coefficients and matching
up the variables. The set-indexed extension is the direct limit of that system, graded by the
elements that come from a homogeneous element of some stage and equipped with the unique divided
powers compatible with those of the stages.

The degrees are allowed to vary from variable to variable, which is what makes a single
application of the construction produce an algebra with variables in every positive degree, as
needed for a Tate resolution; the fixed-degree statement of Tag 0F4I is the special case of a
constant `deg`. Nothing in the argument uses constancy: the iterated extension carries the
degrees of its variables in a function `dg : ℕ → ℕ`, shifted at each step so that the variable
with index `i` has degree `dg i`, and a finite stage reads its degrees off through the chosen
enumeration of its indexing set (`stageDeg`).

## Main definitions

* `DividedPowers.TateResolution.GradedDPAlgebra` and
  `DividedPowers.TateResolution.GradedDPHom` — the bundled vocabulary for a graded divided power
  algebra and a morphism of such. These are the public names for the notion: a colimit has to be
  taken over a diagram of them, so the notion has to be quantifiable over, and bundling is what
  makes that possible. Downstream developments should use these rather than introduce a second
  bundled form.
* `DividedPowers.TateResolution.gradedDirectLimit` — the colimit of a diagram of graded divided
  power algebras indexed by a nonempty directed preorder, with `gradedDirectLimitInclusion` its
  structure maps and `gradedDirectLimit_existsUnique_lift` its universal property.

## Main results

* `DividedPowers.TateResolution.exists_setVariableDividedPowerExtension` — existence of the
  graded algebra with divided powers on a set of variables of prescribed positive degrees, with
  its injective coefficient map, its homogeneous variables, the presentation of each of its
  elements inside a finite-variable stage, the identification of each successor stage with a
  one-variable extension of its predecessor, and the universal mapping property.

## Implementation notes

The colimit diagram is indexed by an arbitrary nonempty directed preorder, matching the indexing
of `existsUnique_dividedPowerStructure_of_finiteStages` and `exists_lift_positiveEvenPart` of
`SetVariableExtension/FiniteStage.lean`, through which the colimit proofs go. The finite subsets
of `J` ordered by inclusion, which is the indexing the set-variable construction itself uses, are
the special case `I = Finset J`, and an `ω`-chain is the case `I = ℕ`.

The one-variable extensions are packaged through the auxiliary bundles `GradedDPAlgebra`,
`GradedDPHom` and `OneVariableExtension`, which carry a graded algebra together with its
grading, strict graded commutativity and divided powers in a single object. Bundling is what
makes the iteration over a finite set expressible as a function `ℕ → GradedDPAlgebra R`: the
instances on the `n`-th stage depend on `n`, so they cannot be supplied by the ambient instance
cache, and the odd and even one-variable extensions have different carriers but the same
universal property, which the bundle lets us state once.

The direct limit of the finite stages lives in a universe `max v w`, where `v` is the universe of
`A` and `w` that of `J`, whereas the statement of the main result needs a carrier in
`max u v w`. Rather than rebuilding the colimit at the larger universe, the finished graded
algebra with divided powers is transported along the `ULift` ring equivalence: `transportedGrade`
and `transportedDPAlgebra` move a grading, strict graded commutativity and a divided power
structure across any algebra equivalence, so the transport is purely universe bookkeeping and
the mathematics happens once, at the smaller universe.

Each finite stage of the construction is identified with the corresponding finite-variable
subring of the limit by a ring equivalence rather than by an equality of types, and the
successor-stage statement is phrased as the existence of a ring equivalence from the
one-variable extension of a stage to the next stage, together with the compatibilities that
pin it down: it fixes the coefficients, sends the adjoined variable to the new variable, detects
the grading, and commutes with divided powers.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section

open OddVariableExtension
attribute [local implicit_reducible] TwistedModule
variable {R : Type u} {A : Type v} {D : Type z}
variable [CommRing R] [Ring A] [Ring D] [Algebra R A] [Algebra R D]

private theorem homogeneous_mul_map_sign
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (f : A →ₐ[R] D) (hf : ∀ m a, a ∈ Aᵢ m → f a ∈ Dᵢ m)
    (d : ℕ) {t : D} (ht : t ∈ Dᵢ d) (a : A) :
    t * f a = f (signRingEquiv Aᵢ d a) * t := by
  classical
  induction a using DirectSum.Decomposition.inductionOn Aᵢ with
  | zero => simp
  | @homogeneous m a =>
    rw [signRingEquiv_of_mem Aᵢ d m a.property, map_smul, smul_mul_assoc]
    exact IsStrictlyGradedComm.graded_comm ht (hf m a a.property)
  | add a b ha hb => simp only [map_add, mul_add, add_mul, ha, hb]

private theorem exists_oddVariable_lift
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (f : A →ₐ[R] D) (hf : ∀ m a, a ∈ Aᵢ m → f a ∈ Dᵢ m)
    (d : ℕ) (hd : Odd d) (t : D) (ht : t ∈ Dᵢ d) :
    ∃! g : OddVariableExtension Aᵢ d →ₐ[R] D,
      (∀ a, g (inclusion Aᵢ d a) = f a) ∧
      g (generator Aᵢ d) = t ∧
      (∀ m x, x ∈ grade Aᵢ d m → g x ∈ Dᵢ m) := by
  classical
  have ht2 : t * t = 0 := by
    obtain ⟨e, he⟩ := hd
    exact pow_two t ▸ IsStrictlyGradedComm.odd_sq_zero (he ▸ ht)
  let q := coefficients Aᵢ d
  let g : OddVariableExtension Aᵢ d →ₐ[R] D :=
    { toFun := fun x => f (q x).1 + f (q x).2 * t
      map_zero' := by simp [q]
      map_one' := by change f 1 + f 0 * t = 1; simp
      map_add' := by intro x y; simp [q, map_add, add_mul]; abel
      map_mul' := by
        intro x y
        simp only [q, coefficients_mul, map_add, map_mul]
        simp only [add_mul, mul_add]
        rw [mul_assoc (f (coefficients Aᵢ d x).2) t (f (coefficients Aᵢ d y).1),
          homogeneous_mul_map_sign Aᵢ Dᵢ f hf d ht]
        have hz : f (coefficients Aᵢ d x).2 * t * (f (coefficients Aᵢ d y).2 * t) = 0 := by
          rw [mul_assoc, ← mul_assoc t,
            homogeneous_mul_map_sign Aᵢ Dᵢ f hf d ht,
            mul_assoc, ht2, mul_zero, mul_zero]
        rw [hz]
        simp only [add_zero, mul_assoc]
        abel
      commutes' := by
        intro r
        change f (algebraMap R A r) + f 0 * t = algebraMap R D r
        simp }
  have hi (a : A) : g (inclusion Aᵢ d a) = f a := by simp [g, q]
  have hg : g (generator Aᵢ d) = t := by simp [g, q]
  refine ⟨g, ⟨hi, hg, ?_⟩, ?_⟩
  · intro m x hx
    obtain ⟨h0, h1⟩ := (mem_grade_coefficients_iff Aᵢ d m x).mp hx
    apply (Dᵢ m).add_mem (hf m _ h0)
    by_cases hdm : d ≤ m
    · rw [ite_eq_left hdm] at h1
      have hm := SetLike.mul_mem_graded (hf (m-d) _ h1) ht
      simpa only [Nat.sub_add_cancel hdm] using hm
    · rw [ite_eq_right hdm, Submodule.mem_bot] at h1
      simp only [q, h1, map_zero, zero_mul]
      exact (Dᵢ m).zero_mem
  · intro k hk
    ext x
    rw [← inclusion_fst_add_inclusion_snd_mul_generator Aᵢ d x]
    simp only [map_add, map_mul, hk.1, hk.2.1, hi, hg]

end

section

open EvenVariableAlgebra
variable {R : Type u} {A : Type v} {D : Type z}
variable [CommRing R] [Ring A] [Ring D] [Algebra R A] [Algebra R D]

private theorem evenPart_commute
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    {x : D} (hx : x ∈ evenPart Dᵢ) (y : D) : Commute x y := by
  classical
  refine Submodule.iSup_induction (p := fun k : ℕ => Dᵢ (2*k))
    (motive := fun x => Commute x y) hx ?_ ?_ ?_
  · intro k x hx
    induction y using DirectSum.Decomposition.inductionOn Dᵢ with
    | zero => exact Commute.zero_right _
    | @homogeneous m y =>
      change x * y = y * x
      rw [IsStrictlyGradedComm.graded_comm hx y.property]
      simp [mul_assoc, pow_mul]
    | add a b ha hb => exact ha.add_right hb
  · exact Commute.zero_left _
  · intro x y hx hy; exact hx.add_left hy

/-- A homogeneous element of positive even degree lies in the positive even part. -/
private theorem mem_positiveEvenPart_of_even_degree
    (Dᵢ : ℕ → Submodule R D) {d : ℕ} (hd : 0 < d) (he : Even d) {t : D} (ht : t ∈ Dᵢ d) :
    t ∈ positiveEvenPart Dᵢ := by
  obtain ⟨e, rfl⟩ := he
  exact mem_positiveEvenPart_of_mem_grade Dᵢ (d := e) (by omega) (by rwa [two_mul])

private theorem exists_evenVariable_lift
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (ε : DividedPowerStructure Dᵢ)
    (f : A →ₐ[R] D) (hf : ∀ m a, a ∈ Aᵢ m → f a ∈ Dᵢ m)
    (d : ℕ) (hd : 0 < d) (he : Even d) (t : D) (ht : t ∈ Dᵢ d) :
    ∃ g : EvenVariableAlgebra A →ₐ[R] D,
      (∀ n a, g (monomial n a) = f a * ε.dpow n t) ∧
      (∀ m x, x ∈ grade Aᵢ d m → g x ∈ Dᵢ m) := by
  classical
  have hp := mem_positiveEvenPart_of_even_degree Dᵢ hd he ht
  obtain ⟨e, he⟩ := he
  have he' : d = 2 * e := by omega
  have hdeg (n : ℕ) : ε.dpow n t ∈ Dᵢ (n * d) := by
    by_cases hn : n = 0
    · subst n; simpa [ε.dpow_zero hp] using
        (SetLike.GradedOne.one_mem : (1 : D) ∈ Dᵢ 0)
    · have h := ε.dpow_mem_grade hn hp (he' ▸ ht)
      simpa [he', mul_assoc, mul_left_comm] using h
  have hcomm (n : ℕ) (x : D) : Commute (ε.dpow n t) x := by
    apply evenPart_commute Dᵢ
    apply Submodule.mem_iSup_of_mem (n * e)
    simpa [he', mul_assoc, mul_left_comm] using hdeg n
  let c : EvenVariableAlgebra A →ₗ[R] (ℕ →₀ A) :=
    { toFun := fun x => x.coeff
      map_add' := fun _ _ => rfl
      map_smul' := by intro r x; simp }
  let q : EvenVariableAlgebra A →ₗ[R] D :=
    (Finsupp.lsum R (fun n => (LinearMap.mulRight R (ε.dpow n t)).comp f.toLinearMap)).comp c
  have hq (n : ℕ) (a : A) : q (monomial n a) = f a * ε.dpow n t := by
    change Finsupp.lsum R _ (Finsupp.single n a) = _
    rw [Finsupp.lsum_single]; rfl
  have hmul (x y : EvenVariableAlgebra A) : q (x*y) = q x * q y := by
    induction x using EvenVariableAlgebra.induction_on generalizing y with
    | zero => simp
    | add n a x hx =>
      rw [add_mul, map_add, map_add, add_mul, hx]
      clear hx
      congr 1
      induction y using EvenVariableAlgebra.induction_on with
      | zero => simp
      | add m b y hy =>
        rw [mul_add, map_add, map_add, mul_add, hy]
        congr 1
        rw [monomial_mul_monomial, hq, hq, hq, map_nsmul, map_mul]
        calc
          (Nat.choose (n + m) n • (f a * f b)) * ε.dpow (n+m) t =
              (f a * f b) * (ε.dpow n t * ε.dpow m t) := by
            rw [ε.dpow_mul hp]
            simp only [nsmul_eq_mul, Nat.cast_comm, mul_assoc]
          _ = f a * ε.dpow n t * (f b * ε.dpow m t) := by
            rw [mul_assoc, ← mul_assoc (f b), ← (hcomm n (f b)).eq]
            simp only [mul_assoc]
  let g : EvenVariableAlgebra A →ₐ[R] D :=
    { toFun := q
      map_zero' := map_zero q
      map_add' := map_add q
      map_one' := by
        change q (monomial 0 1) = 1
        rw [hq, map_one, ε.dpow_zero hp, one_mul]
      map_mul' := hmul
      commutes' := by
        intro r
        rw [EvenVariableAlgebra.algebraMap_apply, hq, ε.dpow_zero hp, mul_one, f.commutes] }
  refine ⟨g, hq, ?_⟩
  intro m x hx
  refine EvenVariableAlgebra.homogeneous_induction_on
    (P := fun x => g x ∈ Dᵢ m) hx ?_ ?_ ?_
  · simp
  · intro n a hn ha
    change q (monomial n a) ∈ Dᵢ m
    rw [hq]
    simpa only [Nat.sub_add_cancel hn] using
      SetLike.mul_mem_graded (hf (m-n*d) a ha) (hdeg n)
  · intro x y hx hy hx' hy'
    simpa only [map_add] using (Dᵢ m).add_mem hx' hy'

end

section

open scoped DirectSum
variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- The grading of a product of two nonnegatively graded algebras. -/
@[instance_reducible] noncomputable def prodGradedAlgebra
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Bᵢ : ℕ → Submodule R B) [GradedAlgebra Bᵢ] :
    GradedAlgebra (fun m => (Aᵢ m).prod (Bᵢ m)) := by
  classical
  let P := fun m => (Aᵢ m).prod (Bᵢ m)
  let l (m : ℕ) : Aᵢ m →+ P m :=
    { toFun := fun x => ⟨(x, 0), x.property, (Bᵢ m).zero_mem⟩
      map_zero' := rfl
      map_add' := by intros; apply Subtype.ext; exact Prod.ext (by simp) (by simp) }
  let r (m : ℕ) : Bᵢ m →+ P m :=
    { toFun := fun x => ⟨(0, x), (Aᵢ m).zero_mem, x.property⟩
      map_zero' := rfl
      map_add' := by intros; apply Subtype.ext; exact Prod.ext (by simp) (by simp) }
  let dl : A →+ ⨁ m, P m :=
    (DirectSum.toAddMonoid fun m => (DirectSum.of _ m).comp (l m)).comp
      (DirectSum.decomposeAddEquiv Aᵢ).toAddMonoidHom
  let dr : B →+ ⨁ m, P m :=
    (DirectSum.toAddMonoid fun m => (DirectSum.of _ m).comp (r m)).comp
      (DirectSum.decomposeAddEquiv Bᵢ).toAddMonoidHom
  have hl {m : ℕ} {a : A} (ha : a ∈ Aᵢ m) :
      dl a = DirectSum.of _ m (l m ⟨a, ha⟩) := by
    change DirectSum.toAddMonoid _ (DirectSum.decompose Aᵢ a) = _
    rw [DirectSum.decompose_of_mem Aᵢ ha, DirectSum.toAddMonoid_of]; rfl
  have hr {m : ℕ} {b : B} (hb : b ∈ Bᵢ m) :
      dr b = DirectSum.of _ m (r m ⟨b, hb⟩) := by
    change DirectSum.toAddMonoid _ (DirectSum.decompose Bᵢ b) = _
    rw [DirectSum.decompose_of_mem Bᵢ hb, DirectSum.toAddMonoid_of]; rfl
  have hl' (a : A) : DirectSum.coeAddMonoidHom P (dl a) = (a, 0) := by
    induction a using DirectSum.Decomposition.inductionOn Aᵢ with
    | zero => simp only [map_zero]; rfl
    | homogeneous a => rw [hl a.property, DirectSum.coeAddMonoidHom_of]; rfl
    | add a b ha hb => simp [ha, hb]
  have hr' (b : B) : DirectSum.coeAddMonoidHom P (dr b) = (0, b) := by
    induction b using DirectSum.Decomposition.inductionOn Bᵢ with
    | zero => simp only [map_zero]; rfl
    | homogeneous b => rw [hr b.property, DirectSum.coeAddMonoidHom_of]; rfl
    | add a b ha hb => simp [ha, hb]
  let dc : A × B →+ ⨁ m, P m := dl.coprod dr
  let dec : DirectSum.Decomposition P := DirectSum.Decomposition.ofAddHom P dc
    (by
      apply AddMonoidHom.ext
      intro x
      change DirectSum.coeAddMonoidHom P (dl x.1 + dr x.2) = x
      rw [map_add, hl', hr']
      exact Prod.ext (add_zero _) (zero_add _))
    (by
      apply DirectSum.addHom_ext
      intro m x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      change dl x.val.1 + dr x.val.2 = DirectSum.of _ m x
      rw [hl x.property.1, hr x.property.2, ← map_add]
      congr 1
      exact Subtype.ext (Prod.ext (add_zero _) (zero_add _)))
  exact
    { dec with
      one_mem := ⟨SetLike.GradedOne.one_mem, SetLike.GradedOne.one_mem⟩
      mul_mem := by
        intro i j x y hx hy
        exact ⟨SetLike.mul_mem_graded hx.1 hy.1, SetLike.mul_mem_graded hx.2 hy.2⟩ }

attribute [local instance] prodGradedAlgebra

/-- Strict graded commutativity is inherited by a product. -/
theorem prodStrictlyGradedComm
    (Aᵢ : ℕ → Submodule R A) [IsStrictlyGradedComm Aᵢ]
    (Bᵢ : ℕ → Submodule R B) [IsStrictlyGradedComm Bᵢ] :
    IsStrictlyGradedComm (fun m => (Aᵢ m).prod (Bᵢ m)) where
  graded_comm hx hy := Prod.ext
    (IsStrictlyGradedComm.graded_comm hx.1 hy.1)
    (IsStrictlyGradedComm.graded_comm hx.2 hy.2)
  odd_sq_zero hx := Prod.ext
    (IsStrictlyGradedComm.odd_sq_zero hx.1)
    (IsStrictlyGradedComm.odd_sq_zero hx.2)

attribute [local instance] prodStrictlyGradedComm

/-- A supremum of products of homogeneous pieces is the product of the two suprema.
Applied to `fun n => 2 * (n + 1)` this identifies the positive even part of a product, and
applied to `fun n => 2 * n` it identifies the even part. -/
theorem prodGrade_iSup (Aᵢ : ℕ → Submodule R A) (Bᵢ : ℕ → Submodule R B)
    (q : ℕ → ℕ) :
    (⨆ n, (Aᵢ (q n)).prod (Bᵢ (q n))) = (⨆ n : ℕ, Aᵢ (q n)).prod (⨆ n : ℕ, Bᵢ (q n)) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact Submodule.prod_mono (le_iSup (fun n : ℕ => Aᵢ (q n)) n)
      (le_iSup (fun n : ℕ => Bᵢ (q n)) n)
  · rintro ⟨a,b⟩ ⟨ha,hb⟩
    have hleft : (a, (0 : B)) ∈ ⨆ n, (Aᵢ (q n)).prod (Bᵢ (q n)) := by
      refine Submodule.iSup_induction (p := fun n : ℕ => Aᵢ (q n))
        (motive := fun x => (x, (0 : B)) ∈ _) ha ?_ ?_ ?_
      · intro n x hx; exact Submodule.mem_iSup_of_mem n ⟨hx, (Bᵢ (q n)).zero_mem⟩
      · exact Submodule.zero_mem _
      · intro x y hx hy; simpa using Submodule.add_mem _ hx hy
    have hright : ((0 : A), b) ∈ ⨆ n, (Aᵢ (q n)).prod (Bᵢ (q n)) := by
      refine Submodule.iSup_induction (p := fun n : ℕ => Bᵢ (q n))
        (motive := fun x => ((0 : A), x) ∈ _) hb ?_ ?_ ?_
      · intro n x hx; exact Submodule.mem_iSup_of_mem n ⟨(Aᵢ (q n)).zero_mem, hx⟩
      · exact Submodule.zero_mem _
      · intro x y hx hy; simpa using Submodule.add_mem _ hx hy
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      Submodule.add_mem _ hleft hright

/-- The divided power structure on a product of two graded divided power algebras. -/
noncomputable def prodDividedPowerStructure
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (Bᵢ : ℕ → Submodule R B) [GradedAlgebra Bᵢ] [IsStrictlyGradedComm Bᵢ]
    (γ : DividedPowerStructure Aᵢ) (δ : DividedPowerStructure Bᵢ) :
    DividedPowerStructure (fun m => (Aᵢ m).prod (Bᵢ m)) := by
  classical
  let P := fun m => (Aᵢ m).prod (Bᵢ m)
  have hpos : positiveEvenPart P = (positiveEvenPart Aᵢ).prod (positiveEvenPart Bᵢ) :=
    prodGrade_iSup Aᵢ Bᵢ (fun n => 2 * (n + 1))
  have heven : evenPart P = (evenPart Aᵢ).prod (evenPart Bᵢ) :=
    prodGrade_iSup Aᵢ Bᵢ (fun n => 2 * n)
  let dp (n : ℕ) (x : A × B) := if x ∈ positiveEvenPart P then
    (γ.dpow n x.1, δ.dpow n x.2) else 0
  have hd (n : ℕ) {x : A × B} (hx : x ∈ positiveEvenPart P) :
      dp n x = (γ.dpow n x.1, δ.dpow n x.2) := ite_eq_left hx
  have hp {x : A × B} (hx : x ∈ positiveEvenPart P) :
      x.1 ∈ positiveEvenPart Aᵢ ∧ x.2 ∈ positiveEvenPart Bᵢ := by
    simpa only [hpos, Submodule.mem_prod] using hx
  have hm {n : ℕ} {x : A × B} (hn : n ≠ 0) (hx : x ∈ positiveEvenPart P) :
      dp n x ∈ positiveEvenPart P := by
    rw [hd n hx, hpos]
    exact ⟨γ.dpow_mem hn (hp hx).1, δ.dpow_mem hn (hp hx).2⟩
  exact {
    dpow := dp
    dpow_null := fun hx => ite_eq_right hx
    dpow_zero := fun hx => by
      rw [hd 0 hx]
      exact Prod.ext (γ.dpow_zero (hp hx).1) (δ.dpow_zero (hp hx).2)
    dpow_one := fun hx => by
      rw [hd 1 hx]
      exact Prod.ext (γ.dpow_one (hp hx).1) (δ.dpow_one (hp hx).2)
    dpow_mem := hm
    dpow_mem_grade := fun hn hx hdg => by
      rw [hd _ hx]
      exact ⟨γ.dpow_mem_grade hn (hp hx).1 hdg.1,
        δ.dpow_mem_grade hn (hp hx).2 hdg.2⟩
    dpow_mul := fun hx => by
      simp only [hd _ hx]
      exact Prod.ext (γ.dpow_mul (hp hx).1) (δ.dpow_mul (hp hx).2)
    dpow_mul_even := fun hn hx hy => by
      rw [hd _ (evenPart_mul_positiveEvenPart P hx hy), hd _ hy]
      rw [heven] at hx
      exact Prod.ext (γ.dpow_mul_even hn hx.1 (hp hy).1)
        (δ.dpow_mul_even hn hx.2 (hp hy).2)
    dpow_mul_odd := fun hn hx hy => by
      dsimp only [dp]
      split_ifs with h
      · exact Prod.ext (γ.dpow_mul_odd hn hx.1 hy.1)
          (δ.dpow_mul_odd hn hx.2 hy.2)
      · rfl
    dpow_add := fun hx hy => by
      simp only [hd _ hx, hd _ hy, hd _ ((positiveEvenPart P).add_mem hx hy)]
      apply Prod.ext
      · simpa only [Prod.fst_sum, Prod.fst_mul, Prod.fst_add] using γ.dpow_add (hp hx).1 (hp hy).1
      · simpa only [Prod.snd_sum, Prod.snd_mul, Prod.snd_add] using δ.dpow_add (hp hx).2 (hp hy).2
    dpow_dpow := fun hm' hn hx => by
      rw [hd _ (hm hm' hx), hd _ hx, hd _ hx]
      exact Prod.ext (γ.dpow_dpow hm' hn (hp hx).1)
        (δ.dpow_dpow hm' hn (hp hx).2) }

end

attribute [local instance] prodGradedAlgebra prodStrictlyGradedComm

/-- On the positive even part, the divided powers of a product are computed componentwise. -/
theorem prodDividedPowerStructure_dpow
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (Bᵢ : ℕ → Submodule R B) [GradedAlgebra Bᵢ] [IsStrictlyGradedComm Bᵢ]
    (γ : DividedPowerStructure Aᵢ) (δ : DividedPowerStructure Bᵢ)
    (n : ℕ) {x : A × B}
    (hx : x ∈ positiveEvenPart (fun m => (Aᵢ m).prod (Bᵢ m))) :
    (prodDividedPowerStructure Aᵢ Bᵢ γ δ).dpow n x =
      (γ.dpow n x.1, δ.dpow n x.2) := by
  classical
  change (if x ∈ positiveEvenPart (fun m => (Aᵢ m).prod (Bᵢ m)) then _ else _) = _
  exact ite_eq_left hx

private theorem map_dpow_of_finiteVariableStage
    {R : Type u} {A : Type v} {C : Type z} {D : Type*} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Ring D]
    [Algebra R A] [Algebra R C] [Algebra R D]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (δ : DividedPowerStructure Cᵢ) (ε : DividedPowerStructure Dᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (S : Finset J) (d : ℕ)
    (hgrade : ∀ m a, a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j, T j ∈ Cᵢ d)
    (hclosed : ∀ n a, ι a ∈ positiveEvenPart Cᵢ → δ.dpow n (ι a) ∈ Set.range ι)
    (f : C →ₐ[R] D) (hf : ∀ m x, x ∈ Cᵢ m → f x ∈ Dᵢ m)
    (hcoeff : ∀ n a, ι a ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (ι a)) = f (δ.dpow n (ι a)))
    (hgen : ∀ n j, T j ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f (T j)) = f (δ.dpow n (T j)))
    {x : C} (hx : x ∈ finiteVariableStage δ ι T S)
    (hp : x ∈ positiveEvenPart Cᵢ) (n : ℕ) :
    ε.dpow n (f x) = f (δ.dpow n x) := by
  classical
  let P := fun m => (Cᵢ m).prod (Dᵢ m)
  let η := prodDividedPowerStructure Cᵢ Dᵢ δ ε
  let k : C →ₐ[R] C × D := (AlgHom.id R C).prod f
  have hk (m : ℕ) (x : C) (hx : x ∈ Cᵢ m) : k x ∈ P m := ⟨hx, hf m x hx⟩
  have hkpos {x : C} (hx : x ∈ positiveEvenPart Cᵢ) : k x ∈ positiveEvenPart P :=
    algHom_mem_positiveEvenPart Cᵢ P k hk hx
  have hfst {p : C × D} (hp : p ∈ positiveEvenPart P) :
      p.1 ∈ positiveEvenPart Cᵢ := by
    rw [show positiveEvenPart P = (positiveEvenPart Cᵢ).prod (positiveEvenPart Dᵢ) from
      prodGrade_iSup Cᵢ Dᵢ (fun n => 2*(n+1))] at hp
    exact hp.1
  have hdp {x : C} (he : ∀ n, x ∈ positiveEvenPart Cᵢ →
      ε.dpow n (f x) = f (δ.dpow n x)) (n : ℕ) : η.dpow n (k x) = k (δ.dpow n x) := by
    by_cases hp : x ∈ positiveEvenPart Cᵢ
    · rw [prodDividedPowerStructure_dpow Cᵢ Dᵢ δ ε n (hkpos hp)]
      exact Prod.ext rfl (he n hp)
    · rw [η.dpow_null (fun h => hp (hfst h)), δ.dpow_null hp, map_zero]
  have hdpgen (n : ℕ) (j : J) : η.dpow n (k (T j)) = k (δ.dpow n (T j)) :=
    hdp (fun n hp => hgen n j hp) n
  let Q := finiteVariableStage η (k.comp ι) (fun j => k (T j)) S
  have hxQ : k x ∈ Q := by
    clear hp
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨j, hj, rfl | ⟨m, rfl⟩⟩
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)
      · rw [← hdpgen]
        exact Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨m, rfl⟩⟩)
    | zero => simp
    | one => simp
    | add a b ha hb ha' hb' => simpa only [map_add] using Q.add_mem ha' hb'
    | neg a ha ha' => simpa only [map_neg] using Q.neg_mem ha'
    | mul a b ha hb ha' hb' => simpa only [map_mul] using Q.mul_mem ha' hb'
  have hdQ : η.dpow n (k x) ∈ Q := finiteVariableStage_dpow_mem Aᵢ P η
    (k.comp ι) (fun j => k (T j)) S (fun _ => d)
    (fun m a ha => hk m _ (hgrade m a ha)) (fun j => hk d _ (hT j))
    (by
      intro m a ha
      have hp := hfst ha
      obtain ⟨b, hb⟩ := hclosed m a hp
      refine ⟨b, ?_⟩
      change k (ι b) = η.dpow m (k (ι a))
      rw [hdp (fun n hp => hcoeff n a hp), hb]) n (k x) hxQ (hkpos hp)
  let G : Subring (C × D) :=
    { carrier := {p | f p.1 = p.2}
      zero_mem' := map_zero f
      one_mem' := map_one f
      add_mem' := fun ha hb => (map_add f _ _).trans (congrArg₂ (· + ·) ha hb)
      neg_mem' := fun ha => (map_neg f _).trans (congrArg Neg.neg ha)
      mul_mem' := fun ha hb => (map_mul f _ _).trans (congrArg₂ (· * ·) ha hb) }
  have hQG : Q ≤ G := by
    apply Subring.closure_le.mpr
    rintro p (⟨a, rfl⟩ | ⟨j, hj, rfl | ⟨m, rfl⟩⟩)
    · rfl
    · rfl
    · rw [hdpgen]; rfl
  have heq := hQG hdQ
  rw [prodDividedPowerStructure_dpow Cᵢ Dᵢ δ ε n (hkpos hp)] at heq
  exact heq.symm

/-- Divided powers of zero are matched by any algebra homomorphism, with no compatibility
hypothesis: both sides are `1` in degree `0` and vanish above it. -/
theorem map_dpow_zero
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    {Aᵢ : ℕ → Submodule R A} [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    {Bᵢ : ℕ → Submodule R B} [GradedAlgebra Bᵢ] [IsStrictlyGradedComm Bᵢ]
    (γ : DividedPowerStructure Aᵢ) (δ : DividedPowerStructure Bᵢ)
    (f : A →ₐ[R] B) (n : ℕ) : δ.dpow n (f 0) = f (γ.dpow n 0) := by
  rw [map_zero]
  by_cases hn : n = 0
  · subst n; rw [γ.dpow_zero (Submodule.zero_mem _),
      δ.dpow_zero (Submodule.zero_mem _), map_one]
  · have hγ := γ.dpow_mul_even (n := n) hn (x := 0) (y := 0)
      (Submodule.zero_mem _) (Submodule.zero_mem _)
    have hδ := δ.dpow_mul_even (n := n) hn (x := 0) (y := 0)
      (Submodule.zero_mem _) (Submodule.zero_mem _)
    simp only [zero_mul, zero_pow hn] at hγ hδ
    rw [hγ, hδ, map_zero]

section
open OddVariableExtension
attribute [local implicit_reducible] TwistedModule

/-- Universal property of adjoining an odd-degree variable to a graded divided power algebra: a
graded algebra map `f : A → D` compatible with divided powers, together with an element `t` of
degree `d` in `D`, extends uniquely to a graded algebra map out of `OddVariableExtension Aᵢ d`
sending the generator to `t` and compatible with divided powers. -/
public theorem existsUnique_oddVariable_dividedPower_lift
    {R : Type u} {A : Type v} {D : Type z}
    [CommRing R] [Ring A] [Ring D] [Algebra R A] [Algebra R D]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (γ : DividedPowerStructure Aᵢ)
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (ε : DividedPowerStructure Dᵢ)
    (f : A →ₐ[R] D) (hf : ∀ m a, a ∈ Aᵢ m → f a ∈ Dᵢ m)
    (hfDP : ∀ n a, a ∈ positiveEvenPart Aᵢ → ε.dpow n (f a) = f (γ.dpow n a))
    (d : ℕ) (hd : 0 < d) (hodd : Odd d) (t : D) (ht : t ∈ Dᵢ d) :
    ∃! g : OddVariableExtension Aᵢ d →ₐ[R] D,
      (∀ a, g (inclusion Aᵢ d a) = f a) ∧
      g (generator Aᵢ d) = t ∧
      (∀ m x, x ∈ grade Aᵢ d m → g x ∈ Dᵢ m) ∧
      (∀ n x, x ∈ positiveEvenPart (grade Aᵢ d) →
        ε.dpow n (g x) =
          g ((oddVariableDividedPowerStructure Aᵢ γ d hd hodd).dpow n x)) := by
  classical
  obtain ⟨g, hg, huniq⟩ := exists_oddVariable_lift Aᵢ Dᵢ f hf d hodd t ht
  obtain ⟨r, hr, _⟩ := exists_oddVariable_lift Aᵢ Aᵢ (AlgHom.id R A)
    (fun m a ha => ha) d hodd 0 (Submodule.zero_mem _)
  have hreflect (a : A) (ha : inclusion Aᵢ d a ∈ positiveEvenPart (grade Aᵢ d)) :
      a ∈ positiveEvenPart Aᵢ := by
    have h := algHom_mem_positiveEvenPart (grade Aᵢ d) Aᵢ r hr.2.2 ha
    simpa only [hr.1, AlgHom.id_apply] using h
  let δ := oddVariableDividedPowerStructure Aᵢ γ d hd hodd
  let ι := inclusionAlgHom Aᵢ d
  let T : Unit → OddVariableExtension Aᵢ d := fun _ => generator Aᵢ d
  have hcoeff (n : ℕ) (a : A) (ha : ι a ∈ positiveEvenPart (grade Aᵢ d)) :
      δ.dpow n (ι a) = ι (γ.dpow n a) :=
    oddVariableDividedPowerStructure_isExtension Aᵢ γ d hd hodd
      n a (hreflect a ha)
  have hfinite (x : OddVariableExtension Aᵢ d) : x ∈ finiteVariableStage δ ι T {()} := by
    rw [← inclusion_fst_add_inclusion_snd_mul_generator Aᵢ d x]
    apply Subring.add_mem
    · exact Subring.subset_closure (Or.inl ⟨x.fst, rfl⟩)
    · apply Subring.mul_mem
      · exact Subring.subset_closure (Or.inl ⟨x.snd, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨(), by simp, Or.inl rfl⟩)
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2, ?_⟩, ?_⟩
  · intro n x hx
    apply map_dpow_of_finiteVariableStage Aᵢ (grade Aᵢ d) Dᵢ δ ε ι T {()} d
      (fun m a ha => inclusion_mem_grade Aᵢ d m ha)
      (fun _ => generator_mem_grade Aᵢ d)
      (fun n a ha => ⟨γ.dpow n a, (hcoeff n a ha).symm⟩)
      g hg.2.2
      (fun n a ha => by
        rw [hcoeff n a ha]
        change ε.dpow n (g (inclusion Aᵢ d a)) = g (inclusion Aᵢ d (γ.dpow n a))
        rw [hg.1, hg.1]
        exact hfDP n a (hreflect a ha))
      (fun n j hj => ?_) (hfinite x) hx n
    have hz : T j = 0 := by
      rcases positiveEven_homogeneous_eq_zero_or_grade (grade Aᵢ d)
        (generator_mem_grade Aᵢ d) hj with h | ⟨e, he⟩
      · exact h
      · obtain ⟨k, hk⟩ := hodd; omega
    rw [hz]
    exact map_dpow_zero δ ε g n
  · intro k hk
    exact huniq k ⟨hk.1, hk.2.1, hk.2.2.1⟩
end

section
open EvenVariableAlgebra

private theorem evenVariable_dpow_generator
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (γ : DividedPowerStructure Aᵢ) (d : ℕ) (hd : 0 < d) [Fact (Even d)] (n : ℕ) :
    (evenVariableDividedPowerStructure d hd γ).dpow n (monomial 1 1) =
      monomial n (1 : A) := by
  simpa [dividedPowerMonomialCoefficient, Nat.div_self (Nat.factorial_pos n)] using
    dpow_monomial_one
      d hd γ n 1 (by omega)

/-- Universal property of adjoining an even-degree divided power variable to a graded divided
power algebra: a graded algebra map `f : A → D` compatible with divided powers, together with an
element `t` of degree `d` in `D`, extends uniquely to a graded algebra map out of
`EvenVariableAlgebra A` sending `monomial 1 1` to `t` and compatible with divided powers. -/
public theorem existsUnique_evenVariable_dividedPower_lift
    {R : Type u} {A : Type v} {D : Type z}
    [CommRing R] [Ring A] [Ring D] [Algebra R A] [Algebra R D]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (γ : DividedPowerStructure Aᵢ)
    (Dᵢ : ℕ → Submodule R D) [GradedAlgebra Dᵢ] [IsStrictlyGradedComm Dᵢ]
    (ε : DividedPowerStructure Dᵢ)
    (f : A →ₐ[R] D) (hf : ∀ m a, a ∈ Aᵢ m → f a ∈ Dᵢ m)
    (hfDP : ∀ n a, a ∈ positiveEvenPart Aᵢ → ε.dpow n (f a) = f (γ.dpow n a))
    (d : ℕ) (hd : 0 < d) [Fact (Even d)] (t : D) (ht : t ∈ Dᵢ d) :
    ∃! g : EvenVariableAlgebra A →ₐ[R] D,
      (∀ a, g (coeffEmbedding a) = f a) ∧
      g (monomial 1 1) = t ∧
      (∀ m x, x ∈ grade Aᵢ d m → g x ∈ Dᵢ m) ∧
      (∀ n x, x ∈ positiveEvenPart (grade Aᵢ d) →
        ε.dpow n (g x) = g ((evenVariableDividedPowerStructure d hd γ).dpow n x)) := by
  classical
  have hp := mem_positiveEvenPart_of_even_degree Dᵢ hd Fact.out ht
  obtain ⟨g, hg, hggrade⟩ := exists_evenVariable_lift Aᵢ Dᵢ ε f hf d hd Fact.out t ht
  have hgcoeff (a : A) : g (coeffEmbedding a) = f a := by
    rw [coeffEmbedding_apply, hg, ε.dpow_zero hp, mul_one]
  have hgT : g (monomial 1 1) = t := by rw [hg, map_one, ε.dpow_one hp, one_mul]
  obtain ⟨r, hr, hrgrade⟩ := exists_evenVariable_lift Aᵢ Aᵢ γ (AlgHom.id R A)
    (fun m a ha => ha) d hd Fact.out 0 (Submodule.zero_mem _)
  have hreflect (a : A) (ha : coeffEmbedding a ∈ positiveEvenPart (grade Aᵢ d)) :
      a ∈ positiveEvenPart Aᵢ := by
    have h := algHom_mem_positiveEvenPart (grade Aᵢ d) Aᵢ r hrgrade ha
    simpa only [coeffEmbedding_apply, hr, γ.dpow_zero (Submodule.zero_mem _),
      mul_one, AlgHom.id_apply] using h
  let δ := evenVariableDividedPowerStructure d hd γ
  let ι := coeffAlgHom (R := R) (A := A)
  let T : Unit → EvenVariableAlgebra A := fun _ => monomial 1 1
  have hcoeff (n : ℕ) (a : A) (ha : ι a ∈ positiveEvenPart (grade Aᵢ d)) :
      δ.dpow n (ι a) = ι (γ.dpow n a) :=
    dpow_coeffEmbedding
      d hd γ n (hreflect a ha)
  have hδT (n : ℕ) (j : Unit) : δ.dpow n (T j) = monomial n 1 :=
    evenVariable_dpow_generator Aᵢ γ d hd n
  have hmon (n : ℕ) (a : A) : monomial n a = ι a * δ.dpow n (T ()) := by
    rw [hδT n ()]
    change monomial n a = monomial 0 a * monomial n 1
    simp [monomial_mul_monomial]
  have hfinite (x : EvenVariableAlgebra A) : x ∈ finiteVariableStage δ ι T {()} := by
    induction x using EvenVariableAlgebra.induction_on with
    | zero => exact Subring.zero_mem _
    | add n a x hx =>
      apply Subring.add_mem _ _ hx
      rw [hmon]
      apply Subring.mul_mem
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨(), by simp, Or.inr ⟨n, rfl⟩⟩)
  have hT : monomial 1 1 ∈ grade Aᵢ d d := by
    simpa only [one_mul] using monomial_one_mem_grade Aᵢ d 1
  have hgDP (n : ℕ) (x : EvenVariableAlgebra A)
      (hx : x ∈ positiveEvenPart (grade Aᵢ d)) : ε.dpow n (g x) = g (δ.dpow n x) := by
    apply map_dpow_of_finiteVariableStage Aᵢ (grade Aᵢ d) Dᵢ δ ε ι T {()} d
      (fun m a ha => (coeffEmbedding_mem_grade_iff Aᵢ d m a).mpr ha)
      (fun _ => hT)
      (fun n a ha => ⟨γ.dpow n a, (hcoeff n a ha).symm⟩) g hggrade
      (fun n a ha => by
        rw [hcoeff n a ha]
        change ε.dpow n (g (coeffEmbedding a)) = g (coeffEmbedding (γ.dpow n a))
        rw [hgcoeff, hgcoeff]
        exact hfDP n a (hreflect a ha))
      (fun n j hj => by
        rw [hδT n j]
        change ε.dpow n (g (monomial 1 1)) = g (monomial n 1)
        rw [hgT, hg, map_one, one_mul]) (hfinite x) hx n
  refine ⟨g, ⟨hgcoeff, hgT, hggrade, hgDP⟩, ?_⟩
  intro k hk
  have hTp : T () ∈ positiveEvenPart (grade Aᵢ d) :=
    mem_positiveEvenPart_of_even_degree _ hd Fact.out hT
  ext x
  induction x using EvenVariableAlgebra.induction_on with
  | zero => simp
  | add n a x hx =>
    rw [map_add, map_add, hx]
    congr 1
    rw [hmon, map_mul, map_mul]
    change k (coeffEmbedding a) * k (δ.dpow n (T ())) =
      g (coeffEmbedding a) * g (δ.dpow n (T ()))
    rw [hk.1, hgcoeff, ← hk.2.2.2 n (T ()) hTp, ← hgDP n (T ()) hTp]
    change f a * ε.dpow n (k (monomial 1 1)) = f a * ε.dpow n (g (monomial 1 1))
    rw [hk.2.1, hgT]
end

end DividedPowers.TateResolution
