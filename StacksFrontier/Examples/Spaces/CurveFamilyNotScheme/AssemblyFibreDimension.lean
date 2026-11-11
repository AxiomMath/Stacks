module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyAlgebraization
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyStalkDimension
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The fibres of the blown-up cubic surface over the line are curves

In the construction of [Stacks, Tag 0D5E], `Z` is the blowup of the cubic surface `Y` at the
chosen point `y` of the central fibre, and `Z ⟶ A¹_k` the composite of the blowup `π : Z ⟶ Y`
with `Y ⟶ A¹_k`. This file shows that every fibre of `Z ⟶ A¹_k` has dimension at most one at
each of its points.

The general input is `Stacks.EtaleCohomology.topologicalKrullDim_fiber_add_one_le_of_isDominant`:
the fibres of a dominant morphism, locally of finite type, from an irreducible Noetherian scheme
to a Jacobson scheme with at least two points have dimension strictly smaller than the source.
Here `Z` is integral of dimension two, `A¹_k = Spec k[t]` is Jacobson with at least two points,
and `Z ⟶ A¹_k` is dominant: `π` is birational, and `Y ⟶ A¹_k` is a flat morphism of irreducible
schemes.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.topologicalKrullDimAt_fiber_le_of_isDominant`: the
  general bound `dim_x(X_{f(x)}) ≤ n` when `dim X ≤ n + 1`.
* `Stacks.Examples.CurveFamilyNotScheme.topologicalKrullDimAt_fiber_cubicToLine_le_one`: every
  fibre of `Z ⟶ A¹_k` has dimension at most one at each of its points.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

/-- **Fibres of a dominant morphism drop dimension, pointwise.** Let `f : X ⟶ S` be dominant and
locally of finite type, with `X` irreducible, quasi-compact and Noetherian of dimension at most
`n + 1`, and `S` a Jacobson scheme with at least two points. Then every fibre of `f` has
dimension at most `n` at each of its points. -/
theorem topologicalKrullDimAt_fiber_le_of_isDominant {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] [CompactSpace X] [NoetherianSpace X] [JacobsonSpace S]
    [LocallyOfFiniteType f] [IsDominant f] (hS : ¬ Subsingleton S) {n : ℕ}
    (hX : topologicalKrullDim X ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (n : WithBot ℕ∞) := by
  refine (topologicalKrullDimAt_le_topologicalKrullDim _).trans ?_
  have h := (Stacks.EtaleCohomology.topologicalKrullDim_fiber_add_one_le_of_isDominant f hS
    (f x)).trans hX
  generalize topologicalKrullDim (f.fiber (f x)) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
        have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
        rwa [this] at h
      exact absurd (WithBot.coe_le_coe.1 h') (by simp)
    | coe m =>
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : m ≤ n)

variable (k : Type u) [Field k]

/-- The affine line `A¹_k = Spec k[t]` has at least two points: the generic point and the
origin. -/
theorem not_subsingleton_affineLine : ¬ Subsingleton (affineLine k) := by
  intro h
  have h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial k)) = originPoint k :=
    @Subsingleton.elim _ h _ _
  have hX : (Polynomial.X : Polynomial k) ∈ (originPoint k).asIdeal :=
    Ideal.subset_span rfl
  rw [← h0] at hX
  exact Polynomial.X_ne_zero ((Submodule.mem_bot _).1 hX)

variable [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-- The structure morphism `Z ⟶ A¹_k` of the blown-up cubic surface is dominant: the blowup
`π : Z ⟶ Y` is birational, and `Y ⟶ A¹_k` is a flat morphism of irreducible schemes. -/
instance isDominant_cubicToLine : IsDominant (cubicToLine k h3) := by
  have := (isBirational_cubicBlowupToBase k h3).isDominant
  have := irreducibleSpace_cubicSurface k
  have := Stacks.Chow.isDominant_of_flat (cubicSurfaceToLine k)
  unfold cubicToLine
  infer_instance

/-- **The fibres of `Z ⟶ A¹_k` are curves**: every fibre of the structure morphism of the
blown-up cubic surface has dimension at most one at each of its points. -/
theorem topologicalKrullDimAt_fiber_cubicToLine_le_one (z : cubicBlowup k h3) :
    topologicalKrullDimAt ((cubicToLine k h3).fiber (cubicToLine k h3 z))
      ((cubicToLine k h3).asFiber z) ≤ 1 := by
  have : CompactSpace (cubicBlowup k h3) :=
    QuasiCompact.compactSpace_of_compactSpace (cubicToLine k h3)
  have : IsNoetherian (cubicBlowup k h3) := {}
  have : JacobsonSpace (affineLine k) := inferInstanceAs (JacobsonSpace (PrimeSpectrum _))
  have h := topologicalKrullDimAt_fiber_le_of_isDominant (cubicToLine k h3)
    (not_subsingleton_affineLine k) (n := 1)
    (by rw [topologicalKrullDim_cubicBlowup k h3]; rfl) z
  exact_mod_cast h

end Stacks.Examples.CurveFamilyNotScheme

end
