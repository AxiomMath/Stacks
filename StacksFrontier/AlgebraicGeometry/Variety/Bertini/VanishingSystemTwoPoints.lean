module

public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorRationalPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemFiniteness

/-!
# The linear system of the sections vanishing at two closed points

The Bertini step of [Stacks, Tag 0FH7] is
`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair_rationalPoints`: for a
quasi-coherent sheaf of ideals `I` whose closed subscheme `Z = V(I)` has `|Z| = {x, x'}`, it
produces a nonzero member of `V_n` whose divisor on `X` is smooth over `k` and through which both
`k`-rational points factor. Its hypotheses are the conclusions of [Stacks, Tag 0FD5] together
with the two inclusions between `|Z|` and `{x, x'}`, three finiteness facts and a dimension
bound. Nothing supplied the `I`.

The `I` is the vanishing ideal sheaf of the closed set `{x, x'}`, which is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` at the closed set `{x} ∪ {x'}`: its
closed subscheme is the reduced one (`isReduced_subscheme_vanishingIdeal`, registered for
[Stacks, Tag 01J3]), and its support is *equal* to `{x, x'}`, which is
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` and discharges both
inclusions at once. With the finiteness instances of
`StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemFiniteness` in scope, and
generation and the immersion taken from [Stacks, Tag 0FD5], the Bertini step applies with three
hypotheses left: a basis of `V_n`, the ambient immersion of [Stacks, Tag 0FD6], and the bound
`dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ m`.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.isFinite_subschemeι_comp_of_coe_support_eq_pair`: **the
  closed subscheme on two closed points is finite over `k`.** Its space embeds in `{x, x'}`,
  which is a two-point discrete space and so has topological Krull dimension zero, and a proper
  morphism with zero-dimensional source is finite.
* `Stacks.SectionsVanishingOnSubscheme.exists_bound_forall_exists_ne_zero_smooth_divisorOnX_pair`:
  the Bertini step for **any** `I` whose support is exactly `{x, x'}`, with generation, the
  immersion of `X ∖ Z ⟶ 𝐏(V_n)`, the smoothness on the open complement and the three finiteness
  facts all discharged.
* `exists_bound_forall_exists_ne_zero_smooth_divisorOnX_vanishingIdeal_pair` (in the same
  namespace): the same at the vanishing ideal sheaf of `{x, x'}`, so that the ideal sheaf is
  produced rather than assumed.

## Implementation notes

**What is still assumed, and why.** Three of the Bertini step's hypotheses are not discharged
here and appear inside the `∀ n` of the conclusion.

1. A basis `b : Module.Basis (Fin (N + 1)) k V_n`. [Stacks, Tag 0FD5] is formalized in the form "for
   every basis of `V_n` the morphism built from it is an immersion", because the presentation of
   `𝐏(V_n)` as `ℙᴺ_k` needs one; it does not assert that `V_n ≠ 0`, and `Fin (N + 1)` is
   nonempty, so the basis cannot be produced from finite-dimensionality alone.
2. The ambient immersion `(ambientFamilyDivisors k f n).IsImmersive b' hb'`. This is hypotheses
   (2) and (3) of [Stacks, Tag 0FD6] for the full space of sections — `ℒ ^⊗ n` very ample on `X`
   with `Γ(X, ℒ ^⊗ n)` — and is recorded in
   `StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisorsOnX` as the one input of
   the general-position step of [Stacks, Tag 0FH7] carried as a hypothesis: what this repository
   proves from ampleness is [Stacks, Tag 0FD5], which gives an immersion on the open complement of
   `Z` rather than on `X`, so the two do not compose.
3. The bound `Module.finrank k Γ(Z, ℒ ^⊗ n|_Z) ≤ m`. For `Z` the reduced subscheme on two closed
   points of a scheme locally of finite type over an algebraically closed field the left side is
   `2`, so this is `2 ≤ m` — the dimension range of the Bertini branch of [Stacks, Tag 0FH7].
   Computing it needs the global sections of an *invertible module* on a scheme finite over a
   field; what is available, `AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk`, is
   the structure-sheaf case, and the finiteness of `Z` over `k` that it consumes is the first
   result above.

**The two-point set.** `{x, x'}` is closed as the union of two closed singletons, and as a
subspace it is finite and `T1` — each of its singletons is the preimage of a closed singleton of
`X` under the inclusion — hence discrete, hence of Krull dimension zero by
`topologicalKrullDim_eq_zero_of_discreteTopology_nonempty`.

No `@[stacks]` attribute is attached. [Stacks, Tag 0FH7] asserts a divisibility of zero-cycle
classes after a finite separable extension; what is assembled here is the input side of its
Bertini reduction, and the tag's remaining steps — the induction on `dim X`, the curve case and
the Jacobian of [Stacks, Tag 0BA0] — are not available. [Stacks, Tag 01J3] is already registered
against the construction this uses.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.ImmersionEvaluationSurjective

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The closed subscheme on two closed points is finite over the base field.** The range of its
inclusion is its support, so its space embeds in `{x, x'}`; that subspace is finite and `T1`,
hence discrete, hence of topological Krull dimension zero, and a proper morphism whose source is
zero dimensional is finite
(`AlgebraicGeometry.isFinite_of_isProper_of_topologicalKrullDim_le_zero`).

This is what `AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk` consumes, and so
the first step towards the dimension bound `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ m` that the Bertini step
below still assumes. -/
theorem isFinite_subschemeι_comp_of_coe_support_eq_pair [IsProper f] (I : X.IdealSheafData)
    {x x' : X} (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X))
    (hZ : (I.support : Set X) = {x, x'}) : IsFinite (I.subschemeι ≫ f) := by
  have hpair : topologicalKrullDim ({x, x'} : Set X) = 0 := by
    have : Finite ({x, x'} : Set X) := ((Set.finite_singleton x').insert x).to_subtype
    have : T1Space ({x, x'} : Set X) := by
      refine ⟨fun z => ?_⟩
      have hz : IsClosed ({(z : X)} : Set X) := by
        rcases z.2 with h | h
        · rw [h]; exact hx
        · rw [Set.eq_of_mem_singleton h]; exact hx'
      have hpre : ({z} : Set ({x, x'} : Set X)) = Subtype.val ⁻¹' ({(z : X)} : Set X) := by
        ext w; simp [Subtype.ext_iff]
      rw [hpre]
      exact hz.preimage continuous_subtype_val
    have : Nonempty ({x, x'} : Set X) := ⟨⟨x, Set.mem_insert _ _⟩⟩
    exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
  refine AlgebraicGeometry.isFinite_of_isProper_of_topologicalKrullDim_le_zero _ ?_
  refine le_trans (AlgebraicGeometry.topologicalKrullDim_le_of_range_subset I.subschemeι
    ({x, x'} : Set X) ?_) hpair.le
  rw [I.range_subschemeι, hZ]

/-- **The Bertini step of [Stacks, Tag 0FH7] at a closed subscheme supported on two closed
points.** For `X` smooth and proper over an algebraically closed field `k`, `ℒ` ample, and `I` a
quasi-coherent sheaf of ideals whose support is exactly `{x, x'}`, there is a bound `n₀` such that
for every `n ≥ n₀`, every basis `b` of `V_n`, the dimension bound on `Γ(Z, ℒ ^⊗ n|_Z)` and the
ambient immersion of [Stacks, Tag 0FD6], some nonzero `v ∈ V_n` has `H_v ⊆ X` smooth over `k`,
germs at `x` and `x'` outside `𝔪ₓ²ℒₓ` and `𝔪ₓ'²ℒₓ'`, and both `k`-rational points factoring
through `H_v` as sections of `H_v ⟶ Spec k`.

Against
`Stacks.SectionsVanishingOnSubscheme.exists_ne_zero_smooth_divisorOnX_pair_rationalPoints` the
hypotheses discharged here are: generation off `Z` and the immersion `X ∖ Z ⟶ 𝐏(V_n)`, which are
the two conclusions of [Stacks, Tag 0FD5]; the smoothness of `X ∖ Z` over `k`, which is the
smoothness of `f` along an open immersion; the three finiteness facts, which are Serre finiteness
in degree zero; and the two inclusions between `|Z|` and `{x, x'}`, which are the two halves of
the hypothesis `hZ`. -/
theorem exists_bound_forall_exists_ne_zero_smooth_divisorOnX_pair [IsAlgClosed k] [Smooth f]
    [IsProper f] (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L]
    (hL : IsAmple X L) {x x' : X} (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X))
    (hZ : (I.support : Set X) = {x, x'})
    {m : ℕ} (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hdim' : topologicalKrullDimAt X x' = (m : WithBot ℕ∞)) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      ∀ (N : ℕ) (_b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n)),
        Module.finrank k (subschemeSections k f I (L := L) n) ≤ m →
        ∀ {p : ℕ} {b' : Module.Basis (Fin (p + 1)) k
            (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
          {hb' : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b'},
          (ambientFamilyDivisors k f (L := L) n).IsImmersive b' hb' →
        ∃ w : vanishingSections k f I L n, w ≠ 0 ∧
          Smooth (((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f) ∧
          ((tensorPowModule X L n).presheaf.Γgerm x).hom
              ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
            maximalSqSmul (tensorPowModule X L n) x ∧
          ((tensorPowModule X L n).presheaf.Γgerm x').hom
              ((familyDivisorsOnX k f I (L := L) n).sectionOf w) ∉
            maximalSqSmul (tensorPowModule X L n) x' ∧
          ∃ ξH ξH' : Spec (.of k) ⟶ ((familyDivisorsOnX k f I (L := L) n).divisor w).subscheme,
            ξH ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι =
                AlgebraicGeometry.pointOfClosedPoint f x hx ∧
              ξH' ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι =
                AlgebraicGeometry.pointOfClosedPoint f x' hx' ∧
              ξH ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f =
                𝟙 (Spec (.of k)) ∧
              ξH' ≫ ((familyDivisorsOnX k f I (L := L) n).divisor w).subschemeι ≫ f =
                𝟙 (Spec (.of k)) := by
  obtain ⟨n₀, hn₀⟩ := exists_bound_generatesOffSupport_and_isImmersion k f I hL
  refine ⟨n₀, fun n hn N b hcond p b' hb' himm' => ?_⟩
  obtain ⟨hgen, hbasis⟩ := hn₀ n hn
  exact exists_ne_zero_smooth_divisorOnX_pair_rationalPoints k f I n inferInstance b hgen
    (hbasis N b).1 himm' hx hx' hdim hdim' hcond hZ.le hZ.ge

/-- **The Bertini step of [Stacks, Tag 0FH7] at the reduced closed subscheme on two closed
points.** This is the previous statement at `I` the vanishing ideal sheaf of `{x, x'}`, whose
support is that closed set by
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal` and whose closed subscheme is
reduced by `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`. So the
ideal sheaf the Bertini step needs is produced, not assumed. -/
theorem exists_bound_forall_exists_ne_zero_smooth_divisorOnX_vanishingIdeal_pair [IsAlgClosed k]
    [Smooth f] [IsProper f] {L : X.Modules} [IsInvertibleModule X L] (hL : IsAmple X L)
    {x x' : X} (hx : IsClosed ({x} : Set X)) (hx' : IsClosed ({x'} : Set X))
    {m : ℕ} (hdim : topologicalKrullDimAt X x = (m : WithBot ℕ∞))
    (hdim' : topologicalKrullDimAt X x' = (m : WithBot ℕ∞)) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      ∀ (N : ℕ) (_b : Module.Basis (Fin (N + 1)) k (vanishingSections k f
          (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩) L n)),
        Module.finrank k (subschemeSections k f
            (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩) (L := L) n) ≤ m →
        ∀ {p : ℕ} {b' : Module.Basis (Fin (p + 1)) k
            (Stacks.Bertini.globalSections k f (tensorPowModule X L n))}
          {hb' : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b'},
          (ambientFamilyDivisors k f (L := L) n).IsImmersive b' hb' →
        ∃ w : vanishingSections k f
            (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩) L n, w ≠ 0 ∧
          Smooth (((familyDivisorsOnX k f
              (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
              (L := L) n).divisor w).subschemeι ≫ f) ∧
          ((tensorPowModule X L n).presheaf.Γgerm x).hom
              ((familyDivisorsOnX k f
                (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
                (L := L) n).sectionOf w) ∉
            maximalSqSmul (tensorPowModule X L n) x ∧
          ((tensorPowModule X L n).presheaf.Γgerm x').hom
              ((familyDivisorsOnX k f
                (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
                (L := L) n).sectionOf w) ∉
            maximalSqSmul (tensorPowModule X L n) x' ∧
          ∃ ξH ξH' : Spec (.of k) ⟶ ((familyDivisorsOnX k f
              (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
              (L := L) n).divisor w).subscheme,
            ξH ≫ ((familyDivisorsOnX k f
                (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
                (L := L) n).divisor w).subschemeι =
                AlgebraicGeometry.pointOfClosedPoint f x hx ∧
              ξH' ≫ ((familyDivisorsOnX k f
                  (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
                  (L := L) n).divisor w).subschemeι =
                AlgebraicGeometry.pointOfClosedPoint f x' hx' ∧
              ξH ≫ ((familyDivisorsOnX k f
                  (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
                  (L := L) n).divisor w).subschemeι ≫ f = 𝟙 (Spec (.of k)) ∧
              ξH' ≫ ((familyDivisorsOnX k f
                  (Scheme.IdealSheafData.vanishingIdeal ⟨{x, x'}, hx.union hx'⟩)
                  (L := L) n).divisor w).subschemeι ≫ f = 𝟙 (Spec (.of k)) :=
  exists_bound_forall_exists_ne_zero_smooth_divisorOnX_pair k f _ hL hx hx'
    (AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _) hdim hdim'

end Stacks.SectionsVanishingOnSubscheme

end
