module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.H1Twist
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.SectionSelection

/-!
# Enriques–Severi–Zariski: `H¹` of a twist vanishes in all sufficiently negative degrees

Let `k` be a field, `X` a proper scheme over `k`, `ℒ` an ample invertible `𝒪_X`-module and `ℱ` a
coherent `𝒪_X`-module whose stalk has depth at least two at every closed point.  Then

`H¹(X, ℱ ⊗_{𝒪_X} ℒ^{⊗ m}) = 0` for all `m ≪ 0`.

This is [Stacks, Tag 0FD8].  Everything it rests on is proved elsewhere; this file is the
assembly, and all it does is choose the three integers the argument needs.

The Stacks Project's proof runs as follows.  Ampleness gives a section `σ` of some `ℒ^{⊗ e}`,
`e ≥ 1`, vanishing at no associated point of `ℱ`; multiplication by `σ` is then injective on `H¹`
in all sufficiently negative twists, because its cokernel is a single module's twists and
[Stacks, Tag 0FD7] kills their `H⁰` (`H1Twist.lean`).  Along the arithmetic progression
`m, m - e, m - 2e, …` the dimensions of `H¹` are therefore non-increasing, hence eventually equal
to some `N`.  Now a *second* section is chosen: in degree `d` large, the sections annihilating
`H¹` form a subspace of codimension at most `N²`, while the sections vanishing at a given
associated point have codimension tending to infinity with `d` (`SectionSelection.lean`, which
needs those points to be non-closed — that is what the depth hypothesis is for).  So for `d` large
there is a section `v` of `ℒ^{⊗ d}` which annihilates `H¹` and vanishes at no associated point of
`ℱ`.  Multiplication by `v` is then both zero and, far enough down, injective, so `H¹` vanishes
somewhere along the progression; by eventual constancy `N = 0`, and the progression through `m`
consists of zeros.  Finitely many progressions cover the negative integers.

## Main results

In the namespace `Stacks.EnriquesSeveriZariski`:

* `exists_forall_le_isZero_cohomologyOverField_one_twistPow_residue`: the vanishing along one
  arithmetic progression of twist degrees, which is where the choice of `d` and the two section
  selections happen.
* `exists_forall_le_isZero_cohomologyOverField_one_twistedGradedModuleTwist`:
  **[Stacks, Tag 0FD8]**.

## Implementation notes

Neither `IsLocallyNoetherian X`, nor `CompactSpace X`, nor
`AlgebraicGeometry.Scheme.Modules.IsAmple X ℒ` is a hypothesis of the tag: the first follows from
properness by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, the second is
`Stacks.Ample.IsAmple.compactSpace`, and the third is the ampleness hypothesis read through
`Stacks.AmpleBridge.isAmple_iff_isAmple`.  All three are derived inside the proofs.

The twist is written `Stacks.Cohomology.TwistedGradedModule.twist`, the spelling the graded
twisted-cohomology machinery is typed against; `Stacks.Divisors.twistPow`, the spelling
multiplication by a section is stated over, is the same object by `rfl`, so the final step needs
no comparison of twists.  This is unlike `Stacks.EnriquesSeveriZariski.twist`, whose tensor power
is a different construction and only isomorphic to these two
(`Stacks.EnriquesSeveriZariski.twistedGradedModuleTwistIso`).

The degrees are chosen as follows.  With `J` and `N` the eventual-constancy data for the
progression through `m`, and `D x` the degree past which the sections vanishing at `x` have
codimension at least `(Ass ℱ).card + N²`, put `A := sup_{x ∈ Ass ℱ} D x`, `d := A e` and
`j₁ := m - (J + A) e`.  Then `d ≥ A` because `e ≥ 1`, so the codimension bound holds in degree
`d`; and `d + j₁ = m - J e`, so `H¹` has dimension `N` at both ends of multiplication by a section
of `ℒ^{⊗ d}` in degree `j₁` — which is what makes `N²` the right codimension to allow for.

## References

* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.EnriquesSeveriZariski

attribute [local instance] HasDerivedCategory.standard

section Residue

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The vanishing of `H¹` along one arithmetic progression of twist degrees.**  Let `σ` be a
section of `ℒ^{⊗ e}` vanishing at no associated point of `ℱ` and let `j₀` be a degree below which
multiplication by `σ` is injective on `H¹`.  Then for any start `m ≤ j₀` there is a `J` with

`H¹(X, ℱ ⊗ ℒ^{⊗ (m - i e)}) = 0` for every `i ≥ J`.

The dimensions along the progression are eventually equal to some `N`
(`exists_forall_eq_finrank_cohomologyOverField_twistPow`), and a second section — annihilating
`H¹` in one degree and vanishing at no associated point of `ℱ` — forces `N = 0`. -/
theorem exists_forall_le_isZero_cohomologyOverField_one_twistPow_residue (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hL : Stacks.Ample.IsAmple X L) (F : X.Modules)
    [F.IsCoherent]
    (hdepth : ∀ y : X, IsClosed ({y} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y))
    {e : ℕ} (he : 1 ≤ e) (σ : Stacks.Divisors.powSection L (e : ℤ)) (j₀ : ℤ)
    (hinj : ∀ j : ℤ, j ≤ j₀ → Function.Injective (AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F (e : ℤ) j σ) 1))
    (m : ℤ) (hm : m ≤ j₀) :
    ∃ J : ℕ, ∀ i : ℕ, J ≤ i →
      IsZero (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Divisors.twistPow L F (m - (i : ℤ) * (e : ℤ))) 1) := by
  classical
  have : AlgebraicGeometry.IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := hL.compactSpace
  have hfd := AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper k f
  have hz : ∀ n : ℤ, IsZero (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F n) 1) ↔ Module.finrank k (AlgebraicGeometry.cohomologyOverField
        k f (Stacks.Divisors.twistPow L F n) 1) = 0 := fun n => by
    have := hfd (Stacks.Divisors.twistPow L F n) (Stacks.Divisors.isCoherent_twistPow L F _) 1
    rw [ModuleCat.isZero_iff_subsingleton, Module.finrank_zero_iff]
  obtain ⟨J, N, hJN⟩ :=
    exists_forall_eq_finrank_cohomologyOverField_twistPow L k f F he σ j₀ m hm hinj
  have hN : N = 0 := by
    have hLmod : Scheme.Modules.IsAmple X L := (Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 hL
    set t : Finset X := (AlgebraicGeometry.associatedPoints_finite F).toFinset
    have hmem : ∀ x : X, x ∈ t ↔ x ∈ Stacks.Divisors.associatedPoints F := fun x =>
      Set.Finite.mem_toFinset _
    have hex : ∀ x : X, ∃ d₀ : ℕ, x ∈ t → ∀ d : ℕ, d₀ ≤ d →
        t.card + N * N + Module.finrank k (vanishingSubmodule k f L (d : ℤ) x) ≤
          Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f
            (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))) := by
      intro x
      by_cases hx : x ∈ t
      · exact (exists_forall_le_codim_vanishingSubmodule k f L hLmod x
          (Stacks.Divisors.not_isClosed_singleton_of_mem_associatedPoints F hdepth
            ((hmem x).1 hx)) (t.card + N * N)).imp fun _ hd₀ _ => hd₀
      · exact ⟨0, fun hx' => absurd hx' hx⟩
    choose D hD using hex
    set A : ℕ := t.sup D
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = A * e := ⟨_, rfl⟩
    obtain ⟨j₁, hj₁⟩ : ∃ j₁ : ℤ, j₁ = m - ((J + A : ℕ) : ℤ) * (e : ℤ) := ⟨_, rfl⟩
    have hdj : (d : ℤ) + j₁ = m - (J : ℤ) * (e : ℤ) := by subst hd hj₁; push_cast; ring
    have hW : ∀ x ∈ t, t.card +
        Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
          (Stacks.Divisors.twistPow L F j₁) 1) *
        Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
          (Stacks.Divisors.twistPow L F ((d : ℤ) + j₁)) 1) +
        Module.finrank k (vanishingSubmodule k f L (d : ℤ) x) ≤
          Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f
            (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))) := by
      intro x hx
      rw [hdj, hj₁, hJN (J + A) (by omega), hJN J le_rfl]
      exact hD x hx d (hd ▸ (Finset.le_sup hx).trans (Nat.le_mul_of_pos_right A he))
    obtain ⟨v, hv0, hvW⟩ := exists_annihilating_regular_section L k f F (d : ℤ) j₁ t
      (fun x => vanishingSubmodule k f L (d : ℤ) x) hW
    have hsv : AlgebraicGeometry.restrictTerminalTopEquiv
        (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))
        ((AlgebraicGeometry.restrictTerminalTopEquiv
          (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))).symm v) = v :=
      (AlgebraicGeometry.restrictTerminalTopEquiv _).apply_symm_apply v
    have hsreg : ∀ x ∈ Stacks.Divisors.associatedPoints F,
        x ∈ Stacks.Ample.nonvanishingLocus
          (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))
          (AlgebraicGeometry.restrictTerminalTopEquiv _
            ((AlgebraicGeometry.restrictTerminalTopEquiv
              (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))).symm v)) := by
      intro x hx
      rw [hsv]
      exact (notMem_vanishingSubmodule_iff k f L (d : ℤ) x v).1 (hvW x ((hmem x).2 hx))
    have hann : AlgebraicGeometry.cohomologyOverFieldMap k f
        (Stacks.Divisors.actionPow L F (d : ℤ) j₁
          ((AlgebraicGeometry.restrictTerminalTopEquiv
            (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))).symm v)) 1 = 0 := by
      refine ModuleCat.hom_ext ?_
      rw [ModuleCat.hom_zero]
      exact (h1Pairing_apply L k f F (d : ℤ) j₁ v).symm.trans hv0
    have hj₁le : (d : ℤ) + j₁ ≤ j₀ := by
      rw [hdj]
      linarith [mul_nonneg (Int.natCast_nonneg J) (Int.natCast_nonneg e)]
    obtain ⟨a, ha⟩ := exists_isZero_cohomologyOverField_of_annihilating L k f hL F hdepth he σ j₀
      hinj (d : ℤ) _ hsreg j₁ hj₁le hann
    have hdeg : j₁ - (a : ℤ) * (e : ℤ) = m - ((J + A + a : ℕ) : ℤ) * (e : ℤ) := by
      subst hj₁; push_cast; ring
    rw [hdeg] at ha
    exact (hJN (J + A + a) (by omega)).symm.trans ((hz _).1 ha)
  refine ⟨J, fun i hi => ?_⟩
  exact (hz _).2 ((hJN i hi).trans hN)

end Residue

/-- **[Stacks, Tag 0FD8].**  Let `k` be a field, let `X` be a scheme proper over `k`, let `ℒ` be
an ample invertible `𝒪_X`-module and let `ℱ` be a coherent `𝒪_X`-module.  If the stalk of `ℱ` has
depth at least two at every closed point of `X`, then

`H¹(X, ℱ ⊗_{𝒪_X} ℒ^{⊗ m}) = 0`

for all `m ≪ 0`. -/
@[stacks 0FD8]
theorem exists_forall_le_isZero_cohomologyOverField_one_twistedGradedModuleTwist (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) (F : X.Modules)
    [F.IsCoherent]
    (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m ≤ m₀ →
      IsZero (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Cohomology.TwistedGradedModule.twist X L F m) 1) := by
  have : AlgebraicGeometry.IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := hL.compactSpace
  obtain ⟨e, he, σ, hσ⟩ := exists_regular_powSection L hL F
  obtain ⟨j₀, hj₀⟩ := exists_forall_le_injective_cohomologyOverFieldMap_actionPow L k f hL F
    (e : ℤ) σ hσ hdepth
  have hstart : ∀ m : ℤ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      IsZero (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Divisors.twistPow L F (m - (j : ℤ) * (e : ℤ))) 1) := by
    intro m
    have hple : m - (((m - j₀).toNat : ℕ) : ℤ) * (e : ℤ) ≤ j₀ := by
      nlinarith [Int.self_le_toNat (m - j₀), Int.natCast_nonneg (m - j₀).toNat,
        (by exact_mod_cast he : (1 : ℤ) ≤ e)]
    obtain ⟨J, hJ⟩ := exists_forall_le_isZero_cohomologyOverField_one_twistPow_residue L k f hL F
      hdepth he σ j₀ hj₀ (m - (((m - j₀).toNat : ℕ) : ℤ) * (e : ℤ)) hple
    refine ⟨J + (m - j₀).toNat, fun j hj => ?_⟩
    have hdeg : m - (j : ℤ) * (e : ℤ) =
        m - (((m - j₀).toNat : ℕ) : ℤ) * (e : ℤ) -
          ((j - (m - j₀).toNat : ℕ) : ℤ) * (e : ℤ) := by
      rw [Nat.cast_sub (by omega : (m - j₀).toNat ≤ j)]
      ring
    rw [hdeg]
    exact hJ (j - (m - j₀).toNat) (by omega)
  exact exists_forall_le_isZero_of_forall_residue_start L k f F he hstart

end Stacks.EnriquesSeveriZariski

end
