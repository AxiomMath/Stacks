module

public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorIrreducible
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemTwoPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# The one-step dimension reduction of the Bertini step

The induction on `dim X` of [Stacks, Tag 0FH7] consumes a single geometric statement: on a proper
smooth geometrically irreducible `X` of dimension `d + 1 ≥ 2` carrying two `k`-rational points
there is a closed subscheme `H ⊆ X`, again smooth and geometrically irreducible over `k` and of
dimension exactly `d`, through which both points factor. This file proves that conclusion from the
pieces the Bertini files land, and the statement it proves differs from the one the induction
consumes in exactly one way: the linear system producing `H` is not reconstructible from `X`, so
the ample invertible module, the basis of `V_n`, the ambient immersion and the numerical bound
appear as hypotheses.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field`: a scheme smooth over a
  field is reduced.
* `Stacks.SectionsVanishingOnSubscheme.isIntegral_of_smooth_of_geometricallyIrreducible`: a scheme
  smooth and geometrically irreducible over a field is integral.
* `Stacks.SectionsVanishingOnSubscheme.topologicalKrullDimAt_eq_of_smooth_of_irreducibleSpace`: on
  an irreducible scheme locally of finite type over a field the local dimension at every point is
  the dimension of the scheme.
* `exists_bound_forall_exists_smooth_geometricallyIrreducible_divisorOnX_pair`:
  **the one-step reduction.** For `X` proper, smooth and geometrically irreducible over an
  algebraically closed `k` of dimension `d + 1` with `1 ≤ d`, `ℒ` ample and two `k`-rational
  points of `X` at the closed points `z`, `z'`, there is a bound `n₀ ≥ 1` such that for every
  `n ≥ n₀`, every basis of `V_n`, the bound `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ 2` and the ambient immersion
  of [Stacks, Tag 0FD6] there is a closed immersion `ι : H ⟶ X` with `H` smooth and geometrically
  irreducible over `k`, `dim H = d`, and both points factoring through `ι`.

## What this discharges, and what it does not

The conclusion is that of `Stacks.WeilCohomology.BertiniDivisorReduction` verbatim, so each of its
five obligations is met: the closed immersion and the smoothness come from
`exists_bound_forall_exists_ne_zero_smooth_divisorOnX_vanishingIdeal_pair`,
the geometric irreducibility from `geometricallyIrreducible_divisorOnX_of_isAmple`, the dimension
from `topologicalKrullDim_divisorOnX_eq`, and the two
factorizations from the same two-point statement, transported from Mathlib's
`AlgebraicGeometry.pointOfClosedPoint` to the given sections by
`AlgebraicGeometry.ext_of_apply_closedPoint_eq`.

What is *not* discharged is the input side. Four data appear here as hypotheses and none of them is
reconstructible from "proper, smooth, geometrically irreducible of dimension `d + 1`":

1. **An ample invertible module `ℒ` on `X`.** This is the projectivity of `X`, which does not
   follow from properness.
2. **A basis of `V_n`.** [Stacks, Tag 0FD5] is proved in the form "for every basis of `V_n` the
   morphism built from it is an immersion"; it does not assert `V_n ≠ 0`, and `Fin (N + 1)` is
   nonempty.
3. **The ambient immersion** `(ambientFamilyDivisors k f n).IsImmersive b' hb'`, which is
   hypotheses (2) and (3) of [Stacks, Tag 0FD6] for the full space of sections.
4. **The bound `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ 2`.** The left side *is* `2` for the reduced subscheme on
   two closed points, and
   `finrank_subschemeSections_eq_finrank_globalSections_of_coe_support_eq_pair`
   reduces it to the structure sheaf of `Z`, but no statement of this library evaluates it. The
   bound is stated at `2` rather than at `dim X` because `2` is its sharp value; the step from `2`
   to the local dimension `d + 1` that the Bertini step asks for is done here, and is where
   `1 ≤ d` is spent.

## The field

The theorem needs `k` **algebraically** closed, where [Stacks, Tag 0FH7] runs over a separable
closure. This is not a weakening that is waiting to be removed.
`Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple` does assume
only `IsSepClosed`, so that half composes; but the smoothness of the divisor rests on the
smoothness of a zero scheme at a closed point, and over a separably closed field that may be
imperfect a closed point of a smooth scheme can have a purely inseparable residue field — over
`k ⊇ 𝔽_p(t)^sep` with `a ∉ k^p` the affine line has the closed point with residue field
`k(a^{1/p})` — so the statement with `IsSepClosed` in place of `PerfectField` is false, not merely
unproved. Adding `PerfectField` is the maximal available weakening, and Mathlib's
`IsSepClosed.isAlgClosed_of_perfectField` returns algebraic closedness from it. Using this
theorem for [Stacks, Tag 0FH7] therefore requires base changing the whole reduction from `k^sep`
to its algebraic closure and descending the conclusion, which is not done here.

No `@[stacks]` attribute is attached. [Stacks, Tag 0FH7] asserts a divisibility of zero-cycle
classes after a finite separable extension; this is the output of its Bertini reduction with the
input linear system assumed, and the tag's remaining steps — the curve case and the Jacobian of
[Stacks, Tag 0BA0] — are not available.

## References

* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections
open Stacks.ImmersionEvaluationSurjective
open Stacks.Chow

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A scheme smooth over a field is reduced.** A smooth morphism is geometrically reduced
(`AlgebraicGeometry.geometricallyReduced_of_smooth`) and flat, and `Spec k` is reduced and locally
noetherian, so `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`
applies. -/
theorem isReduced_of_smooth_over_field [Smooth f] : IsReduced X :=
  have := AlgebraicGeometry.geometricallyReduced_of_smooth f
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

/-- **A scheme smooth and geometrically irreducible over a field is integral.** Geometric
irreducibility over a one-point base gives irreducibility
(`AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace_of_subsingleton`) and smoothness
gives reducedness, and an irreducible reduced scheme is integral.

This is the integrality that
`Stacks.SectionsVanishingOnSubscheme.topologicalKrullDim_divisorOnX_eq` and
`Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple` both assume,
derived from the hypotheses the induction of [Stacks, Tag 0FH7] actually carries. -/
theorem isIntegral_of_smooth_of_geometricallyIrreducible [Smooth f] [GeometricallyIrreducible f] :
    AlgebraicGeometry.IsIntegral X :=
  have : IrreducibleSpace X :=
    AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have : IsReduced X := isReduced_of_smooth_over_field k f
  isIntegral_of_irreducibleSpace_of_isReduced X

/-- **On an irreducible scheme locally of finite type over a field the local dimension at every
point is the dimension of the scheme.** An irreducible space is equidimensional, and on an
equidimensional scheme locally of finite type over a field the local dimension is constant
(`AlgebraicGeometry.topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional`).

This supplies the two hypotheses `topologicalKrullDimAt X z = m = topologicalKrullDimAt X z'` of
the Bertini step from the single hypothesis `topologicalKrullDim X = d + 1` that the induction
of [Stacks, Tag 0FH7] carries, with `m = d + 1`. -/
theorem topologicalKrullDimAt_eq_of_smooth_of_irreducibleSpace [LocallyOfFiniteType f]
    [IrreducibleSpace X] (y : X) : topologicalKrullDimAt X y = topologicalKrullDim X :=
  AlgebraicGeometry.topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k X f
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) y

/-- **The one-step dimension reduction of the Bertini step of [Stacks, Tag 0FH7].** Let `X` be
proper, smooth and geometrically irreducible over an algebraically closed field `k` with
`dim X = d + 1` and `1 ≤ d`, let `ℒ` be an ample invertible module on `X`, and let `x`, `x'` be
`k`-rational points of `X` sitting at the closed points `z`, `z'`. Then there is a bound `n₀ ≥ 1`
such that for every `n ≥ n₀`, every basis of `V_n`, the bound `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ 2` and the
ambient immersion of [Stacks, Tag 0FD6], there is a closed immersion `ι : H ⟶ X` with `H` smooth
and geometrically irreducible over `k`, of dimension exactly `d`, and through which both `x` and
`x'` factor.

The conclusion is that of `Stacks.WeilCohomology.BertiniDivisorReduction` verbatim; the module
documentation lists what the hypotheses add to that statement's, and why none of the four is
reconstructible from `X`.

The closed points `z`, `z'` and their closedness are arguments rather than derived from `x`, `x'`
because the ideal sheaf `Z = V(I)` of `{z, z'}` is named in the statement and so its defining
closed set must be too; `IsClosed {x _}` itself follows from `hx` by
`AlgebraicGeometry.pointEquivClosedPoint`. The passage from the Bertini step's conclusion, which
is about `AlgebraicGeometry.pointOfClosedPoint f z hz`, to the given section `x` is
`AlgebraicGeometry.ext_of_apply_closedPoint_eq`: two sections of `f` agreeing at the closed point
are equal. -/
theorem exists_bound_forall_exists_smooth_geometricallyIrreducible_divisorOnX_pair
    [IsAlgClosed k] [Smooth f] [IsProper f] [GeometricallyIrreducible f]
    {L : X.Modules} [IsInvertibleModule X L] (hL : IsAmple X L)
    {d : ℕ} (hd : 1 ≤ d)
    (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞))
    {z z' : X} (hz : IsClosed ({z} : Set X)) (hz' : IsClosed ({z'} : Set X))
    (x x' : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _)
    (hxz : x (IsLocalRing.closedPoint k) = z)
    (hxz' : x' (IsLocalRing.closedPoint k) = z') :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ (N : ℕ) (_b : Module.Basis (Fin (N + 1)) k (vanishingSections k f
          (Scheme.IdealSheafData.vanishingIdeal ⟨{z, z'}, hz.union hz'⟩) L (n : ℤ))),
        Module.finrank k (subschemeSections k f
            (Scheme.IdealSheafData.vanishingIdeal ⟨{z, z'}, hz.union hz'⟩) (L := L) (n : ℤ)) ≤ 2 →
        ∀ {p : ℕ} {b' : Module.Basis (Fin (p + 1)) k
            (Stacks.Bertini.globalSections k f (tensorPowModule X L (n : ℤ)))}
          {hb' : (ambientFamilyDivisors k f (L := L) (n : ℤ)).GeneratesBy b'},
          (ambientFamilyDivisors k f (L := L) (n : ℤ)).IsImmersive b' hb' →
        ∃ (H : Scheme.{u}) (ι : H ⟶ X) (_ : IsClosedImmersion ι) (_ : Smooth (ι ≫ f))
          (_ : GeometricallyIrreducible (ι ≫ f)),
          topologicalKrullDim H = (d : WithBot ℕ∞) ∧
            ∃ x_H x'_H : Spec (.of k) ⟶ H, x_H ≫ ι = x ∧ x'_H ≫ ι = x' := by
  have : AlgebraicGeometry.IsIntegral X :=
    isIntegral_of_smooth_of_geometricallyIrreducible k f
  have hat : ∀ y : X, topologicalKrullDimAt X y = ((d + 1 : ℕ) : WithBot ℕ∞) := fun y =>
    (topologicalKrullDimAt_eq_of_smooth_of_irreducibleSpace k f y).trans hdim
  have hdim2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [hdim]; exact_mod_cast Nat.succ_le_succ hd
  obtain ⟨m₀, hm₀⟩ :=
    exists_bound_forall_exists_ne_zero_smooth_divisorOnX_vanishingIdeal_pair k f hL hz hz'
      (hat z) (hat z')
  refine ⟨max m₀.toNat 1, le_max_right _ _, fun n hn N b hcond p b' hb' himm' => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnz : m₀ ≤ (n : ℤ) :=
    le_trans (Int.self_le_toNat m₀) (by exact_mod_cast le_trans (le_max_left _ _) hn)
  obtain ⟨w, hw0, hwsm, -, -, ξH, ξH', hξH, hξH', -, -⟩ :=
    hm₀ (n : ℤ) hnz N b (le_trans hcond (by omega)) himm'
  have : Nonempty ((familyDivisorsOnX k f
      (Scheme.IdealSheafData.vanishingIdeal ⟨{z, z'}, hz.union hz'⟩)
      (L := L) (n : ℤ)).divisor w).subscheme :=
    ⟨ξH (IsLocalRing.closedPoint k)⟩
  have hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (tensorPowModule X L (n : ℤ)) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X (tensorPowModule X L (n : ℤ))).1
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn1 hL)
  exact ⟨_, _, inferInstance, hwsm,
    geometricallyIrreducible_divisorOnX_of_isAmple k f _ (n : ℤ) hample hdim2 w hw0 hwsm,
    topologicalKrullDim_divisorOnX_eq k f _ (n : ℤ) w hw0 hdim,
    ξH, ξH',
    hξH.trans (ext_of_apply_closedPoint_eq f (pointOfClosedPoint_comp f z hz) hx
      ((pointOfClosedPoint_apply f z hz _).trans hxz.symm)),
    hξH'.trans (ext_of_apply_closedPoint_eq f (pointOfClosedPoint_comp f z' hz') hx'
      ((pointOfClosedPoint_apply f z' hz' _).trans hxz'.symm))⟩

end Stacks.SectionsVanishingOnSubscheme

end
